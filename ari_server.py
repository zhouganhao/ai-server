#!/usr/bin/env python3
"""
AI 语音客服 - 全双工方案 v13.1 (预缓冲提取修复)

修复: 预缓冲提取用回声基线+小余量, 而非VAD阈值
      保证至少保留1.5秒, 防止裁剪过度丢失语音
"""

import asyncio
import json
import uuid
import logging
import re
import os
import struct
import time
import io
import wave
import socket
import numpy as np
import requests
import websockets
from collections import deque

# ==================== Asterisk ARI 配置 ====================
ASTERISK_HOST = 'localhost'
ASTERISK_PORT = 8088
ASTERISK_USER = 'my_ari_user'
ASTERISK_PASS = '1qaz@WSX3edc$RFV'
STASIS_APP = 'my_ai_agent'
LOCAL_IP = '192.168.102.90'

# ==================== AI 服务配置 ====================
TTS_URL = "http://192.168.102.32:8002/v1/audio/speech"
STT_URL = "http://192.168.102.32:8001/stt"
LLM_URL = "http://192.168.102.32:8000/v1/chat/completions"
LLM_MODEL = "qwen2.5-7b-instruct"
TTS_VOICE = "zf_xiaoxiao"
TTS_SPEED = 1.0

# ==================== RTP 音频配置 ====================
RTP_BASE_PORT = 25000
RTP_PACKET_SIZE = 160
RTP_PACKET_INTERVAL = 0.02

# ==================== 预缓冲配置 ====================
PRE_BUFFER_SECONDS = 4.0
PRE_BUFFER_MAX_FRAMES = int(PRE_BUFFER_SECONDS / 0.02)

# ==================== 回声模式检测 ====================
ECHO_DETECT_DURATION = 3.0
ECHO_CORRELATION_THRESHOLD = 0.5

# ==================== 🎧 耳机模式参数 ====================
HEADSET_PARAMS = {
    'name': '🎧耳机',

    # VAD间距 (阈值 = 动态噪声基线 + 间距)
    'vad_start_margin': 500,        # 开始说话: 噪声+500 (防误触发)
    'vad_end_margin': 250,          # 结束说话: 噪声+250 (灵敏检测)

    # 打断参数
    'bargein_base': 1200,
    'echo_factor': 0.3,             # 耳机只收回声30%
    'echo_margin': 500,
    'bargein_frames': 4,

    # 时序控制
    'post_bargein_wait': 0.05,
    'post_tts_cooldown': 0.15,
    'silence_sec': 1.0,
    'max_speech_sec': 30,

    # 预缓冲
    'keep_prebuffer': True,
    'prebuffer_keep_ms': 500,
}

# ==================== 📡 免提模式参数 ====================
SPEAKER_PARAMS = {
    'name': '📡免提',

    'vad_start_margin': 600,
    'vad_end_margin': 300,

    'bargein_base': 2500,
    'echo_factor': 0.7,
    'echo_margin': 1200,
    'bargein_frames': 8,

    'post_bargein_wait': 0.3,
    'post_tts_cooldown': 0.3,
    'silence_sec': 1.0,
    'max_speech_sec': 30,

    'keep_prebuffer': False,        # 免提: 丢弃预缓冲
    'prebuffer_keep_ms': 500,
}

DEFAULT_PARAMS = SPEAKER_PARAMS
WELCOME_TEXT = "您好，欢迎致电车服云科技。我是智能客服助手，请问有什么可以帮您？"

logging.basicConfig(level=logging.INFO, format='%(asctime)s] [%(levelname)s] %(message)s')
log = logging.getLogger(__name__)
auth = (ASTERISK_USER, ASTERISK_PASS)


# ==================== μ-law 转换表 ====================
_ULAW_DECODE = np.zeros(256, dtype=np.int16)
for _i in range(256):
    _byte = ~_i & 0xFF
    _sign = (_byte & 0x80) >> 7
    _exp = (_byte & 0x70) >> 4
    _mant = _byte & 0x0F
    _sample = ((_mant << 3) + 0x84) << _exp
    _sample -= 0x84
    if _sign:
        _sample = -_sample
    _ULAW_DECODE[_i] = _sample

_ULAW_ENCODE = np.zeros(65536, dtype=np.uint8)
for _i in range(65536):
    _s = _i - 32768
    _sgn = 1 if _s < 0 else 0
    if _sgn:
        _s = -_s
    if _s > 32635:
        _s = 32635
    _s += 0x84
    if _s >= 0x4000:
        _e = 7
    elif _s >= 0x2000:
        _e = 6
    elif _s >= 0x1000:
        _e = 5
    elif _s >= 0x800:
        _e = 4
    elif _s >= 0x400:
        _e = 3
    elif _s >= 0x200:
        _e = 2
    elif _s >= 0x100:
        _e = 1
    else:
        _e = 0
    _m = (_s >> (_e + 3)) & 0x0F
    _ULAW_ENCODE[_i] = (~((_sgn << 7) | (_e << 4) | _m)) & 0xFF


def ulaw_to_pcm(ulaw_bytes):
    return _ULAW_DECODE[np.frombuffer(ulaw_bytes, dtype=np.uint8)].copy()


def pcm_to_ulaw(pcm_int16):
    unsigned = (pcm_int16.astype(np.int32) + 32768).astype(np.uint16)
    return _ULAW_ENCODE[unsigned].tobytes()


def resample_8k_to_16k(pcm_8k):
    pcm = pcm_8k.astype(np.float64)
    indices = np.arange(len(pcm) * 2) / 2.0
    return np.interp(indices, np.arange(len(pcm)), pcm).astype(np.int16)


def resample_16k_to_8k(pcm_16k):
    return pcm_16k[::2].astype(np.int16)


# ==================== ARI 辅助函数 ====================
async def ari_post(path, params=None):
    url = f"http://{ASTERISK_HOST}:{ASTERISK_PORT}{path}"
    loop = asyncio.get_event_loop()
    try:
        resp = await loop.run_in_executor(
            None, lambda: requests.post(url, auth=auth, params=params, timeout=10))
        if resp.status_code >= 400:
            log.error(f"ARI POST {path} -> {resp.status_code}: {resp.text[:300]}")
        resp.raise_for_status()
        return resp.json() if resp.content else None
    except Exception as e:
        log.error(f"ARI POST {path} 异常: {e}")
        return None


async def ari_delete(path):
    url = f"http://{ASTERISK_HOST}:{ASTERISK_PORT}{path}"
    loop = asyncio.get_event_loop()
    try:
        resp = await loop.run_in_executor(
            None, lambda: requests.delete(url, auth=auth, timeout=10))
        if resp.status_code == 404:
            return None
        resp.raise_for_status()
        return resp.json() if resp.content else None
    except:
        return None


# ==================== RTP 传输 ====================
class RTPTransport:
    def __init__(self, local_port):
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.sock.bind(('0.0.0.0', local_port))
        self.sock.setblocking(False)
        self.local_port = local_port
        self.remote_addr = None
        self.send_seq = np.random.randint(0, 65536)
        self.send_ts = np.random.randint(0, 0xFFFFFFFF)
        self.ssrc = uuid.uuid4().int & 0xFFFFFFFF

    def parse_rtp(self, data):
        if len(data) < 12:
            return None
        b0, b1, seq, ts, ssrc = struct.unpack('!BBHII', data[:12])
        cc = b0 & 0x0F
        offset = 12 + cc * 4
        if b0 & 0x10 and len(data) > offset + 4:
            ext_len = struct.unpack('!H', data[offset+2:offset+4])[0]
            offset += 4 + ext_len * 4
        return {'pt': b1 & 0x7F, 'seq': seq, 'ts': ts, 'ssrc': ssrc,
                'payload': data[offset:]}

    def build_rtp(self, payload):
        pkt = struct.pack('!BBHII', 0x80, 0x00,
                          self.send_seq, self.send_ts, self.ssrc)
        self.send_seq = (self.send_seq + 1) & 0xFFFF
        self.send_ts = (self.send_ts + len(payload)) & 0xFFFFFFFF
        return pkt + payload

    async def recv(self):
        loop = asyncio.get_event_loop()
        try:
            data, addr = await asyncio.wait_for(
                loop.sock_recvfrom(self.sock, 4096), timeout=0.05)
            if self.remote_addr is None:
                self.remote_addr = addr
                log.info(f"RTP: 学习到远端地址 {addr}")
            return self.parse_rtp(data)
        except asyncio.TimeoutError:
            return None

    async def send(self, ulaw_payload):
        if self.remote_addr is None:
            return
        pkt = self.build_rtp(ulaw_payload)
        loop = asyncio.get_event_loop()
        await loop.sock_sendto(self.sock, pkt, self.remote_addr)

    def close(self):
        try: self.sock.close()
        except: pass


# ==================== 通话会话 ====================
class CallSession:
    _next_port = RTP_BASE_PORT

    @classmethod
    def _alloc_port(cls):
        p = cls._next_port
        cls._next_port += 2
        return p

    def __init__(self, channel_id, caller='unknown'):
        self.channel_id = channel_id
        self.caller = caller
        self.bridge_id = None
        self.em_channel_id = None
        self.em_expected_id = f"em_{uuid.uuid4().hex[:8]}"
        self.rtp = None
        self.rtp_port = self._alloc_port()

        # VAD状态
        self.audio_buffer_8k = []
        self.is_speaking = False
        self.last_speech_time = 0.0
        self.speech_start = None
        self.processing = False
        self.active = True

        # 动态噪声基线
        self.noise_floor = 500.0
        self.noise_samples = 0
        self.NOISE_DECAY = 0.3
        self.NOISE_RISE = 0.02
        self.NOISE_MIN_FRAMES = 20

        # TTS/打断
        self.is_ai_speaking = False
        self.bargein_count = 0

        # 模式管理
        self.mode_params = DEFAULT_PARAMS
        self.mode_name = DEFAULT_PARAMS['name']
        self.mode_locked = False
        self.welcome_playing = False

        # 预缓冲
        self.pre_buffer = deque(maxlen=PRE_BUFFER_MAX_FRAMES)
        self.pre_buffer_energies = deque(maxlen=PRE_BUFFER_MAX_FRAMES)

        # 回声历史
        self.send_energy_history = deque(maxlen=500)

        # 丢弃控制
        self.discard_until = 0.0

        self._silence_task = None
        self.history = []

    @property
    def p(self):
        return self.mode_params

    def _estimate_echo(self):
        """估算当前回声能量"""
        now = time.monotonic()
        recent = [e for t, e in self.send_energy_history if now - t < 0.5]
        if not recent:
            return 0
        return max(recent) * self.p['echo_factor']

    def _get_bargein_threshold(self):
        echo_est = self._estimate_echo()
        return max(echo_est + self.p['echo_margin'], self.p['bargein_base'])

    def _update_noise_floor(self, energy):
        if energy < self.noise_floor:
            self.noise_floor = self.noise_floor * (1 - self.NOISE_DECAY) + energy * self.NOISE_DECAY
        else:
            self.noise_floor = self.noise_floor * (1 - self.NOISE_RISE) + energy * self.NOISE_RISE
        self.noise_samples += 1

    def _get_vad_start(self):
        return self.noise_floor + self.p['vad_start_margin']

    def _get_vad_end(self):
        return self.noise_floor + self.p['vad_end_margin']

    # 欢迎语模式检测
    async def _detect_mode_from_welcome(self):
        await asyncio.sleep(ECHO_DETECT_DURATION)
        if self.mode_locked:
            return

        if len(self.pre_buffer_energies) < 50 or len(self.send_energy_history) < 50:
            log.info(f"[{self.channel_id[:8]}] 模式检测: 数据不足, 保持{self.mode_name}")
            self.mode_locked = True
            return

        now = time.monotonic()
        recv_energies = []
        send_energies = []

        for i, energy in enumerate(self.pre_buffer_energies):
            frame_time = now - (len(self.pre_buffer_energies) - i) * 0.02
            send_e = [e for t, e in self.send_energy_history if abs(t - frame_time) < 0.25]
            if send_e:
                recv_energies.append(energy)
                send_energies.append(max(send_e))

        if len(recv_energies) < 30:
            log.info(f"[{self.channel_id[:8]}] 模式检测: 匹配不足, 保持{self.mode_name}")
            self.mode_locked = True
            return

        recv_arr = np.array(recv_energies, dtype=np.float64)
        send_arr = np.array(send_energies, dtype=np.float64)
        recv_std = np.std(recv_arr)
        send_std = np.std(send_arr)

        if recv_std < 1 or send_std < 1:
            log.info(f"[{self.channel_id[:8]}] 模式检测: 方差太小, 保持{self.mode_name}")
            self.mode_locked = True
            return

        correlation = float(np.mean(
            (recv_arr - np.mean(recv_arr)) / recv_std *
            (send_arr - np.mean(send_arr)) / send_std
        ))
        correlation = max(-1.0, min(1.0, correlation))

        old_name = self.mode_name
        if correlation > ECHO_CORRELATION_THRESHOLD:
            self.mode_params = SPEAKER_PARAMS
            self.mode_name = SPEAKER_PARAMS['name']
        else:
            self.mode_params = HEADSET_PARAMS
            self.mode_name = HEADSET_PARAMS['name']

        self.mode_locked = True
        log.info(f"[{self.channel_id[:8]}] 🔒 模式锁定: {old_name} → {self.mode_name} "
                 f"(相关度={correlation:.2f}, {len(recv_energies)}组数据)")

    # ★★★ 预缓冲提取 (用回声基线, 非VAD阈值) ★★★
    def _extract_headset_prebuffer(self):
        """
        耳机模式: 保留打断前固定时长
        原理: 打断已确认 = 用户在说话, 直接保留最后N帧即可
        不需要任何阈值判断, 简单可靠
        """
        if not self.pre_buffer:
            return []

        # 保留多少帧 (默认400ms=20帧, 可调)
        keep_ms = self.p.get('prebuffer_keep_ms', 400)
        keep_frames = max(1, int(keep_ms / 20))

        total = len(self.pre_buffer)

        if total <= keep_frames:
            result = list(self.pre_buffer)
        else:
            result = list(self.pre_buffer)[-keep_frames:]

        kept_ms = len(result) * 20
        log.info(f"[{self.channel_id[:8]}] 预缓冲: 保留最后{len(result)}帧({kept_ms}ms) "
                 f"[总共{total}帧]")

        return result
    def _extract_headset_prebuffer_bak(self):
        """
        耳机模式: 从预缓冲提取用户语音

        关键: 不用VAD阈值(太高), 用回声估算+小余量
        因为: 预缓冲 = 回声 + 用户语音, 已知用户在说话(打断确认)
        只需找到energy > 回声的帧, 就是用户语音

        保证: 至少保留 min_keep_frames 帧 (防止裁剪过度)
        """
        if not self.pre_buffer:
            return []

        total_frames = len(self.pre_buffer)
        lead = self.p.get('prebuffer_lead_frames', 25)
        min_keep = self.p.get('prebuffer_min_keep_frames', 75)
        echo_margin = self.p.get('prebuffer_echo_margin', 200)

        # ★ 用回声估算作为基线 (比noise_floor更准确)
        echo_est = self._estimate_echo()

        # 第1轮: 提取阈值 = 回声估算 + 小余量
        extract_th = max(echo_est + echo_margin, 300)

        speech_start_idx = None
        for i, energy in enumerate(self.pre_buffer_energies):
            if energy > extract_th:
                speech_start_idx = i
                break

        # 第2轮: 降低到回声的50% + 100
        if speech_start_idx is None:
            extract_th = max(echo_est * 0.5 + 100, 200)
            for i, energy in enumerate(self.pre_buffer_energies):
                if energy > extract_th:
                    speech_start_idx = i
                    break

        # 第3轮: 兜底, 从最后1.5秒开始
        if speech_start_idx is None:
            speech_start_idx = max(0, total_frames - min_keep)

        # 计算起点: 语音起点 - 前置保留
        start_idx = max(0, speech_start_idx - lead)

        # ★ 保证至少保留 min_keep 帧 (防过度裁剪)
        min_start = max(0, total_frames - min_keep)
        if start_idx > min_start:
            start_idx = min_start
            log.info(f"[{self.channel_id[:8]}] 预缓冲: 裁剪过多, 扩展到保留{min_keep}帧")

        result = list(self.pre_buffer)[start_idx:]

        trim_ms = start_idx * 20
        kept_ms = len(result) * 20
        log.info(f"[{self.channel_id[:8]}] 预缓冲提取: 裁剪{trim_ms}ms, 保留{kept_ms}ms "
                 f"(echo={echo_est:.0f}, 提取阈值={extract_th:.0f}, "
                 f"语音起点帧={speech_start_idx}, 总帧={total_frames})")

        return result

    # ---- 初始化 ----
    async def setup(self):
        await ari_post(f"/ari/channels/{self.channel_id}/answer")

        bid = f"br_{self.channel_id[:8]}"
        result = await ari_post("/ari/bridges", params={'bridgeId': bid, 'type': 'mixing'})
        if not result:
            log.error("建桥失败!")
            return
        self.bridge_id = bid

        await ari_post(f"/ari/bridges/{self.bridge_id}/addChannel",
                       params={'channel': self.channel_id})
        await self._create_external_media()

    async def _create_external_media(self):
        self.rtp = RTPTransport(self.rtp_port)
        log.info(f"[{self.channel_id[:8]}] RTP 监听端口 {self.rtp_port}")

        result = await ari_post("/ari/channels/externalMedia", params={
            'channelId': self.em_expected_id,
            'app': STASIS_APP,
            'external_host': f'{LOCAL_IP}:{self.rtp_port}',
            'encapsulation': 'rtp',
            'transport': 'udp',
            'direction': 'both',
            'format': 'ulaw'
        })

        if result:
            self.em_channel_id = result.get('id', self.em_expected_id)
            log.info(f"[{self.channel_id[:8]}] ExternalMedia 创建成功: {self.em_channel_id}")
        else:
            log.error(f"[{self.channel_id[:8]}] ExternalMedia 创建失败!")

    async def on_em_stasis_start(self, channel_id):
        self.em_channel_id = channel_id
        await ari_post(f"/ari/bridges/{self.bridge_id}/addChannel",
                       params={'channel': channel_id})
        log.info(f"[{self.channel_id[:8]}] ExternalMedia 已加入桥")

        self._silence_task = asyncio.create_task(self._silence_sender())
        asyncio.create_task(self._audio_loop())
        await self._play_welcome_via_rtp()

    async def _play_welcome_via_rtp(self):
        self.welcome_playing = True
        asyncio.create_task(self._detect_mode_from_welcome())
        await self._send_tts(WELCOME_TEXT)
        self.welcome_playing = False
        log.info(f"[{self.channel_id[:8]}] 欢迎语完成, 模式: {self.mode_name}")

    async def _silence_sender(self):
        SILENCE_PKT = b'\xff' * RTP_PACKET_SIZE
        next_time = time.monotonic()
        log.info(f"[{self.channel_id[:8]}] 🔇 静音保活启动")

        while self.active:
            try:
                if not self.is_ai_speaking and self.rtp and self.rtp.remote_addr:
                    await self.rtp.send(SILENCE_PKT)
                next_time += RTP_PACKET_INTERVAL
                now = time.monotonic()
                sleep = next_time - now
                if sleep > 0:
                    await asyncio.sleep(sleep)
                elif sleep < -0.5:
                    next_time = time.monotonic()
            except Exception as e:
                if self.active:
                    log.debug(f"静音发送异常: {e}")
                await asyncio.sleep(0.02)
        log.info(f"[{self.channel_id[:8]}] 静音保活停止")

    # ---- 音频处理主循环 ----
    async def _audio_loop(self):
        log.info(f"[{self.channel_id[:8]}] 🎧 音频循环启动 [{self.mode_name}]")
        _log_counter = 0

        while self.active:
            try:
                now = time.monotonic()

                # 时间差静音检测
                if self.is_speaking and not self.is_ai_speaking:
                    silence_duration = now - self.last_speech_time

                    if silence_duration >= self.p['silence_sec']:
                        duration = now - self.speech_start
                        if duration >= 0.3:
                            buf_frames = len(self.audio_buffer_8k)
                            log.info(f"[{self.channel_id[:8]}] 说话结束 "
                                     f"({duration:.1f}s, {buf_frames}帧, "
                                     f"静音{silence_duration:.1f}s) [{self.mode_name}]")
                            if not self.processing:
                                asyncio.create_task(self._process_speech())
                            else:
                                log.info("正在处理中，忽略")
                                self.audio_buffer_8k.clear()
                        else:
                            log.info(f"说话太短 ({duration:.1f}s)，忽略")
                            self.audio_buffer_8k.clear()

                        self.is_speaking = False
                        self.speech_start = None
                        continue

                    if (now - self.speech_start) >= self.p['max_speech_sec']:
                        log.info(f"[{self.channel_id[:8]}] 说话超时")
                        if not self.processing:
                            asyncio.create_task(self._process_speech())
                        else:
                            self.audio_buffer_8k.clear()
                        self.is_speaking = False
                        self.speech_start = None
                        continue

                # 丢弃期
                if now < self.discard_until:
                    rtp = await self.rtp.recv()
                    if rtp is not None:
                        payload = rtp.get('payload', b'')
                        if len(payload) > 0 and not self.is_speaking:
                            pcm = ulaw_to_pcm(payload)
                            e = np.sqrt(np.mean(pcm.astype(np.float64) ** 2))
                            self._update_noise_floor(e)
                    continue

                # 接收RTP
                rtp = await self.rtp.recv()
                if rtp is None:
                    continue

                payload = rtp.get('payload', b'')
                if len(payload) == 0:
                    continue

                pcm_8k = ulaw_to_pcm(payload)
                energy = np.sqrt(np.mean(pcm_8k.astype(np.float64) ** 2))

                # TTS播放中
                if self.is_ai_speaking:
                    self.pre_buffer.append(pcm_8k)
                    self.pre_buffer_energies.append(energy)

                    if not self.welcome_playing:
                        bargein_threshold = self._get_bargein_threshold()

                        if energy > bargein_threshold:
                            self.bargein_count += 1
                            if self.bargein_count >= self.p['bargein_frames']:
                                log.info(f"[{self.channel_id[:8]}] 🔔 打断! "
                                         f"energy={energy:.0f}, 阈值{bargein_threshold:.0f}")

                                self.is_ai_speaking = False
                                self.bargein_count = 0

                                if self.p['keep_prebuffer']:
                                    clean_frames = self._extract_headset_prebuffer()
                                    self.pre_buffer.clear()
                                    self.pre_buffer_energies.clear()
                                    if clean_frames:
                                        self.audio_buffer_8k = clean_frames
                                        self.is_speaking = True
                                        self.speech_start = time.monotonic() - len(clean_frames) * 0.02
                                        self.last_speech_time = time.monotonic()
                                        log.info(f"[{self.channel_id[:8]}] 🎧 保留预缓冲"
                                                 f"{len(clean_frames)}帧({len(clean_frames)*20}ms)")
                                    else:
                                        log.info(f"[{self.channel_id[:8]}] 🎧 预缓冲无语音")
                                else:
                                    pb_count = len(self.pre_buffer)
                                    self.pre_buffer.clear()
                                    self.pre_buffer_energies.clear()
                                    log.info(f"[{self.channel_id[:8]}] 📡 丢弃预缓冲{pb_count}帧")

                                self.discard_until = time.monotonic() + self.p['post_bargein_wait']
                        else:
                            self.bargein_count = 0

                    continue

                # 非TTS: 动态VAD
                vad_start = self._get_vad_start()
                vad_end = self._get_vad_end()

                if self.is_speaking:
                    is_speech = energy > vad_end
                else:
                    is_speech = energy > vad_start

                if is_speech:
                    self.last_speech_time = time.monotonic()
                    if not self.is_speaking:
                        if self.noise_samples < self.NOISE_MIN_FRAMES:
                            self._update_noise_floor(energy)
                            _log_counter += 1
                            if _log_counter % 50 == 0:
                                log.info(f"[{self.channel_id[:8]}] 噪声校准: "
                                         f"{self.noise_samples}/{self.NOISE_MIN_FRAMES}")
                            continue

                        self.is_speaking = True
                        self.speech_start = time.monotonic()
                        log.info(f"[{self.channel_id[:8]}] 🗣️ 说话 energy={energy:.0f} "
                                 f"(noise={self.noise_floor:.0f}, "
                                 f"阈值={vad_start:.0f}) [{self.mode_name}]")
                    self.audio_buffer_8k.append(pcm_8k)
                else:
                    if self.is_speaking:
                        self.audio_buffer_8k.append(pcm_8k)
                    else:
                        self._update_noise_floor(energy)

                    _log_counter += 1
                    if _log_counter % 250 == 0:
                        log.info(f"[{self.channel_id[:8]}] 📊 噪声={self.noise_floor:.0f}, "
                                 f"energy={energy:.0f}, "
                                 f"VAD>{vad_start:.0f}/>{vad_end:.0f}")

            except Exception as e:
                log.error(f"音频循环异常: {e}")
                await asyncio.sleep(0.01)

        log.info(f"[{self.channel_id[:8]}] 音频循环结束")

    # ---- 语音处理 ----
    async def _process_speech(self):
        if self.processing or not self.active:
            return
        self.processing = True

        if not self.audio_buffer_8k:
            self.processing = False
            return

        pcm_8k = np.concatenate(self.audio_buffer_8k)
        self.audio_buffer_8k.clear()
        pcm_16k = resample_8k_to_16k(pcm_8k)

        wav_buf = io.BytesIO()
        with wave.open(wav_buf, 'wb') as wf:
            wf.setnchannels(1)
            wf.setsampwidth(2)
            wf.setframerate(16000)
            wf.writeframes(pcm_16k.tobytes())
        wav_data = wav_buf.getvalue()

        log.info(f"[{self.channel_id[:8]}] 📤 STT ({len(wav_data)}B, "
                 f"{len(pcm_8k)/8000:.1f}s) [{self.mode_name}]")

        loop = asyncio.get_event_loop()
        try:
            def do_stt():
                return requests.post(STT_URL,
                    files={'file': ('audio.wav', wav_data, 'audio/wav')}, timeout=15)
            resp = await loop.run_in_executor(None, do_stt)
            if resp.status_code != 200:
                log.error(f"STT失败: {resp.status_code}")
                self.processing = False
                return
            text = resp.json().get('text', '').strip()
        except Exception as e:
            log.error(f"STT异常: {e}")
            self.processing = False
            return

        log.info(f"🎤 识别: '{text}'")
        if not text:
            self.processing = False
            return

        reply, action, action_param = await self._llm(text)
        log.info(f"🤖 回复: '{reply}' action={action}")

        if action:
            if action in ('hangup', 'transfer_human'):
                if reply:
                    await self._send_tts(reply)
                await asyncio.sleep(1)
                await self.cleanup()
                self.processing = False
                return

        if reply and self.active:
            await self._send_tts(reply)

        self.history.append({"role": "user", "content": text})
        self.history.append({"role": "assistant", "content": reply or ""})
        if len(self.history) > 10:
            self.history = self.history[-10:]

        self.processing = False

    async def _llm(self, user_text):
        system = """你是「小云」，深圳车服云科技的语音客服助手，声音甜美、耐心、有礼貌。
你的任务是解答路边停车缴费相关的常见问题，**像和朋友聊天一样自然**。

【身份背景】
- 公司：深圳车服云科技，负责路边停车收费助缴。
- 收费：由中标公司收取，价格政府定价。
- 车辆受损：只收公共资源占用费，不包含保管责任，建议报警处理。
- 停车场不开闸：可能因为历史路边欠费未缴清，请重新扫出口码支付本次停车费。
- 手机号来源：是您或亲友在合作停车场缴费时主动绑定。
- 征信影响：目前只是欠费提醒，不影响征信。
- 律师函：仅作提醒，未正式起诉。
- 其他问题：如果不清楚，礼貌引导转人工。

【回答要求】
1. 用口语化、有温度的方式回应。
2. 不要机械重复规则原文，用自己的话解释，核心信息不能错。
3. 回答长度1~3句，保持简洁。
4. 如果用户要挂断，说"好的，感谢您的来电，再见"并用动作标记结束。
5. 如果需要转人工，先安抚，如"我帮您转接人工客服，请稍等"。

【动作标记】（最后一行单独成行）
[ACTION:hangup] - 挂断
[ACTION:transfer_human] - 转人工
[ACTION:register_plate|车牌号] - 登记车牌
[ACTION:sms_link] - 发送短信链接

请你根据以上规则扮演好小云，让对话更自然。"""

        msgs = [{"role": "system", "content": system}] + self.history + \
               [{"role": "user", "content": user_text}]
        payload = {"model": LLM_MODEL, "messages": msgs, "temperature": 0.1, "max_tokens": 500}

        loop = asyncio.get_event_loop()
        try:
            resp = await loop.run_in_executor(
                None, lambda: requests.post(LLM_URL, json=payload, timeout=30))
            if resp.status_code != 200:
                return "系统繁忙，请稍后再拨。", None, None
            full = resp.json()['choices'][0]['message']['content'].strip()

            # ★ 用 re.search 替换 re.match, 匹配行内任意位置
            action, action_param = None, None
            clean_lines = []
            for line in full.split('\n'):
                # search 在行内任意位置查找, match 只查行首
                m = re.search(r'\[ACTION:(\w+)(?:\|(.*?))?\]', line)
                if m:
                    action = m.group(1)
                    action_param = m.group(2)
                    # 从文本中删除 ACTION 标记
                    line = line[:m.start()] + line[m.end():]
                clean_lines.append(line)

            reply = '\n'.join(clean_lines).strip()
            return reply, action, action_param
        except Exception as e:
            log.error(f"LLM异常: {e}")
            return "系统出错，请稍后再试。", None, None


    # ---- TTS → RTP ----
    async def _send_tts(self, text):
        self.is_ai_speaking = True
        self.pre_buffer.clear()
        self.pre_buffer_energies.clear()
        self.send_energy_history.clear()
        loop = asyncio.get_event_loop()

        try:
            resp = await loop.run_in_executor(None, lambda: requests.post(
                TTS_URL, json={"input": text, "voice": TTS_VOICE, "speed": TTS_SPEED},
                timeout=30))
            if resp.status_code != 200:
                log.error(f"TTS失败: {resp.status_code}")
                self.is_ai_speaking = False
                self.discard_until = time.monotonic() + self.p['post_tts_cooldown']
                return
            audio = await loop.run_in_executor(None, lambda: resp.content)
        except Exception as e:
            log.error(f"TTS异常: {e}")
            self.is_ai_speaking = False
            self.discard_until = time.monotonic() + self.p['post_tts_cooldown']
            return

        try:
            with wave.open(io.BytesIO(audio), 'rb') as wf:
                ch = wf.getnchannels()
                fr = wf.getframerate()
                pcm = wf.readframes(wf.getnframes())
        except Exception as e:
            log.error(f"WAV解析失败: {e}")
            self.is_ai_speaking = False
            self.discard_until = time.monotonic() + self.p['post_tts_cooldown']
            return

        if ch == 2:
            pcm_arr = np.frombuffer(pcm, dtype=np.int16)
            pcm_arr = (pcm_arr[0::2].astype(np.int32) + pcm_arr[1::2].astype(np.int32)) // 2
            pcm = pcm_arr.astype(np.int16).tobytes()

        if fr != 8000:
            pcm_arr = np.frombuffer(pcm, dtype=np.int16)
            if fr == 16000:
                pcm_arr = resample_16k_to_8k(pcm_arr)
            elif fr == 22050:
                pcm_arr = pcm_arr[::2]
                pcm_arr = resample_16k_to_8k(pcm_arr) if len(pcm_arr) > 1 else pcm_arr
            elif fr == 44100:
                pcm_arr = pcm_arr[::5]
            else:
                indices = np.arange(int(len(pcm_arr) * 8000 / fr))
                pcm_arr = np.interp(indices, np.arange(len(pcm_arr)),
                                    pcm_arr.astype(np.float64)).astype(np.int16)
            pcm = pcm_arr.tobytes()

        pcm_arr = np.frombuffer(pcm, dtype=np.int16)
        ulaw_data = pcm_to_ulaw(pcm_arr)

        total_ms = len(ulaw_data) / 160 * 20
        log.info(f"[{self.channel_id[:8]}] 🔊 TTS ({total_ms:.0f}ms) [{self.mode_name}]")

        packets = []
        for i in range(0, len(ulaw_data), RTP_PACKET_SIZE):
            chunk = ulaw_data[i:i + RTP_PACKET_SIZE]
            if len(chunk) < RTP_PACKET_SIZE:
                chunk += b'\xff' * (RTP_PACKET_SIZE - len(chunk))
            packets.append(chunk)

        next_send_time = time.monotonic()
        for i, pkt in enumerate(packets):
            if not self.active or not self.is_ai_speaking:
                log.info(f"[{self.channel_id[:8]}] TTS被打断 (已发{i}/{len(packets)})")
                break

            pkt_pcm = ulaw_to_pcm(pkt)
            pkt_energy = np.sqrt(np.mean(pkt_pcm.astype(np.float64) ** 2))
            self.send_energy_history.append((time.monotonic(), pkt_energy))

            await self.rtp.send(pkt)
            next_send_time += RTP_PACKET_INTERVAL

            now = time.monotonic()
            sleep_time = next_send_time - now
            if sleep_time > 0:
                await asyncio.sleep(sleep_time)
            elif sleep_time < -0.1:
                next_send_time = time.monotonic()

        # ★★★ 关键修复: 区分正常结束和被打断 ★★★
        was_bargein = not self.is_ai_speaking

        if was_bargein:
            # ★ 被打断: audio_buffer里有预缓冲, 不能清!
            log.info(f"[{self.channel_id[:8]}] TTS被打断清理: "
                     f"保留audio_buffer ({len(self.audio_buffer_8k)}帧), "
                     f"is_speaking={self.is_speaking}")
        else:
            # 正常结束: 清理状态, 准备下一轮
            self.is_ai_speaking = False
            self.discard_until = time.monotonic() + self.p['post_tts_cooldown']
            self.audio_buffer_8k.clear()
            self.is_speaking = False
            self.speech_start = None

        # 这些始终清理 (TTS相关, 不影响预缓冲)
        self.bargein_count = 0
        self.pre_buffer.clear()
        self.pre_buffer_energies.clear()

        log.info(f"[{self.channel_id[:8]}] TTS结束 [{self.mode_name}]")


    async def on_dtmf(self, digit):
        log.info(f"[{self.channel_id[:8]}] DTMF: {digit}")
        if self.is_ai_speaking:
            self.is_ai_speaking = False
            self.audio_buffer_8k.clear()
            self.is_speaking = False
            self.bargein_count = 0
            self.discard_until = time.monotonic() + self.p['post_bargein_wait']


    async def cleanup(self):
        self.active = False
        self.is_ai_speaking = False
        self.welcome_playing = False
        if self._silence_task:
            self._silence_task.cancel()
            try: await self._silence_task
            except: pass
        if self.rtp:
            self.rtp.close()
        if self.bridge_id:
            await ari_delete(f"/ari/bridges/{self.bridge_id}")
        if self.em_channel_id:
            await ari_delete(f"/ari/channels/{self.em_channel_id}")
        # ★ 挂断原始通话通道
        await ari_delete(f"/ari/channels/{self.channel_id}")

# ==================== ARI 事件主循环 ====================
sessions = {}


async def run():
    ws_url = (f"ws://{ASTERISK_HOST}:{ASTERISK_PORT}/ari/events"
              f"?app={STASIS_APP}&api_key={ASTERISK_USER}:{ASTERISK_PASS}")

    while True:
        try:
            async with websockets.connect(ws_url) as ws:
                log.info("✅ ARI WebSocket 已连接")

                async for raw in ws:
                    try:
                        data = json.loads(raw)
                    except:
                        continue

                    evt = data.get('type', '')
                    ch = data.get('channel', {})
                    chid = ch.get('id', '')
                    chname = ch.get('name', '')

                    if evt == 'StasisStart':
                        matched_em = False
                        for cid, sess in list(sessions.items()):
                            if sess.em_expected_id == chid or sess.em_channel_id == chid:
                                await sess.on_em_stasis_start(chid)
                                matched_em = True
                                break

                        if not matched_em and not chname.startswith('UnicastRTP'):
                            caller = ch.get('caller', {}).get('number', 'unknown')
                            log.info(f"📞 来电 {caller} → {chid[:8]}")
                            sess = CallSession(chid, caller)
                            sessions[chid] = sess
                            await sess.setup()

                    elif evt == 'ChannelDtmfReceived':
                        digit = data.get('digit', '')
                        for cid, sess in sessions.items():
                            if cid == chid:
                                await sess.on_dtmf(digit)
                                break

                    elif evt in ('StasisEnd', 'ChannelDestroyed'):
                        if chid in sessions:
                            log.info(f"📞 通道 {chid[:8]} 已结束")
                            await sessions[chid].cleanup()
                            del sessions[chid]
                        else:
                            for cid, sess in list(sessions.items()):
                                if sess.em_channel_id == chid:
                                    sess.em_channel_id = None
                                    break

        except websockets.exceptions.ConnectionClosed:
            log.warning("ARI WS 断开，5秒后重连...")
            await asyncio.sleep(5)
        except Exception as e:
            log.error(f"ARI WS 异常: {e}", exc_info=True)
            await asyncio.sleep(5)


async def main():
    log.info("=" * 60)
    log.info("🚀 AI语音客服 v13.2 (预缓冲修复: 打断不清)")
    log.info(f"  默认: {DEFAULT_PARAMS['name']}, 检测: {ECHO_DETECT_DURATION}s后锁定")
    log.info(f"")
    log.info(f"  🎧 耳机: VAD=噪声+{HEADSET_PARAMS['vad_start_margin']}/+{HEADSET_PARAMS['vad_end_margin']}, "
             f"预缓冲={HEADSET_PARAMS['prebuffer_keep_ms']}ms, "
             f"打断保留=是")
    log.info(f"  📡 免提: VAD=噪声+{SPEAKER_PARAMS['vad_start_margin']}/+{SPEAKER_PARAMS['vad_end_margin']}, "
             f"预缓冲={SPEAKER_PARAMS['prebuffer_keep_ms']}ms, "
             f"打断保留=否")
    log.info(f"")
    log.info(f"  ★ 噪声基线: 动态追踪 (下降快/上升慢)")
    log.info(f"  ★ 预缓冲: 固定保留打断前{HEADSET_PARAMS['prebuffer_keep_ms']}ms")
    log.info(f"  ★ 打断修复: _send_tts被打断时不清audio_buffer")
    log.info("=" * 60)
    await run()


if __name__ == '__main__':
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        log.info("已停止")

