#!/usr/bin/env python3
"""
AI 语音客服 - 全双工方案 v2 (优化TTS流畅度 + VAD抗噪)
修复: TTS卡顿、VAD误触发、误打断
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

# ==================== 配置 ====================
ASTERISK_HOST = 'localhost'
ASTERISK_PORT = 8088
ASTERISK_USER = 'my_ari_user'
ASTERISK_PASS = '1qaz@WSX3edc$RFV'
STASIS_APP = 'my_ai_agent'
LOCAL_IP = '192.168.102.90'

# AI服务地址
TTS_URL = "http://192.168.102.32:8002/v1/audio/speech"
STT_URL = "http://192.168.102.32:8001/stt"
LLM_URL = "http://192.168.102.32:8000/v1/chat/completions"
LLM_MODEL = "qwen2.5-7b-instruct"
TTS_VOICE = "zf_xiaoxiao"
TTS_SPEED = 1.0

# 音频参数
RTP_BASE_PORT = 25000

# VAD参数 - 大幅优化
VAD_ENERGY_THRESHOLD = 500        # 提高到500 (原来300太敏感)
VAD_SILENCE_SEC = 1.8             # 静音1.8秒认为结束
VAD_SPEECH_MIN_SEC = 0.5          # 最短0.5秒才算有效说话
VAD_BARGEIN_THRESHOLD = 2000      # 打断阈值提高到2000 (原来800)
VAD_BARGEIN_FRAMES = 5           # 连续5帧(100ms)高能量才打断，避免噪声误打断

# RTP参数
RTP_PACKET_SIZE = 160             # ulaw 20ms
RTP_PACKET_INTERVAL = 0.02       # 20ms
RTP_SEND_BUFFER = 5              # 预缓冲5包再开始发

logging.basicConfig(level=logging.INFO, format='%(asctime)s [%(levelname)s] %(message)s')
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
    result = np.interp(indices, np.arange(len(pcm)), pcm)
    return result.astype(np.int16)


def resample_16k_to_8k(pcm_16k):
    return pcm_16k[::2].astype(np.int16)


# ==================== ARI 辅助函数 ====================
async def ari_post(path, params=None):
    url = f"http://{ASTERISK_HOST}:{ASTERISK_PORT}{path}"
    loop = asyncio.get_event_loop()
    try:
        resp = await loop.run_in_executor(
            None, lambda: requests.post(url, auth=auth, params=params, timeout=10)
        )
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
            None, lambda: requests.delete(url, auth=auth, timeout=10)
        )
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
        payload = data[offset:]
        return {'pt': b1 & 0x7F, 'seq': seq, 'ts': ts, 'ssrc': ssrc, 'payload': payload}

    def build_rtp(self, payload):
        pkt = struct.pack('!BBHII',
            0x80, 0x00,
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
        try:
            self.sock.close()
        except:
            pass


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

        self.audio_buffer_8k = []
        self.is_speaking = False
        self.silence_count = 0
        self.speech_start = None
        self.is_ai_speaking = False
        self.processing = False
        self.pending_speech = False   # TTS播放期间用户说话，标记待处理
        self.active = True

        # 打断防抖
        self.bargein_count = 0

        self.history = []
        self.welcome_playback_id = None
        self.welcome_sound_file = None

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

        await self._play_welcome()

    async def _play_welcome(self):
        text = "您好，欢迎致电车服云科技。我是智能客服助手，请问有什么可以帮您？"
        loop = asyncio.get_event_loop()

        try:
            resp = await loop.run_in_executor(None, lambda: requests.post(
                TTS_URL, json={"input": text, "voice": TTS_VOICE, "speed": TTS_SPEED},
                timeout=30))
            if resp.status_code != 200:
                log.error(f"欢迎语TTS失败: {resp.status_code}")
                await self._create_external_media()
                return
            audio = await loop.run_in_executor(None, lambda: resp.content)

            # 确保目录存在
            sound_dir = '/var/lib/asterisk/sounds/custom'
            await loop.run_in_executor(None, lambda: os.makedirs(sound_dir, exist_ok=True))

            fid = uuid.uuid4().hex
            spath = f"{sound_dir}/wel_{fid}.wav"
            await loop.run_in_executor(None, lambda: open(spath, 'wb').write(audio))
            await loop.run_in_executor(None, lambda: os.chmod(spath, 0o666))

            pid = f"pb_wel_{fid}"
            result = await ari_post(f"/ari/channels/{self.channel_id}/play", params={
                'media': f'sound:custom/wel_{fid}', 'playbackId': pid})
            if result:
                self.welcome_playback_id = pid
                self.welcome_sound_file = spath
                log.info(f"[{self.channel_id[:8]}] 欢迎语播放中...")
            else:
                await self._create_external_media()
        except Exception as e:
            log.error(f"欢迎语异常: {e}")
            await self._create_external_media()

    async def _on_welcome_finished(self):
        if self.welcome_sound_file:
            try:
                os.remove(self.welcome_sound_file)
            except:
                pass
            self.welcome_sound_file = None
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
        asyncio.create_task(self._audio_loop())

    # ---- 音频处理主循环 ----
    async def _audio_loop(self):
        log.info(f"[{self.channel_id[:8]}] 🎧 音频处理循环启动")
        SILENCE_FRAMES = int(VAD_SILENCE_SEC / 0.02)

        while self.active:
            try:
                rtp = await self.rtp.recv()
                if rtp is None:
                    continue

                payload = rtp.get('payload', b'')
                if len(payload) == 0:
                    continue

                pcm_8k = ulaw_to_pcm(payload)
                energy = np.sqrt(np.mean(pcm_8k.astype(np.float64) ** 2))

                # ---- 打断检测 (防抖: 连续N帧高能量才打断) ----
                if self.is_ai_speaking:
                    if energy > VAD_BARGEIN_THRESHOLD:
                        self.bargein_count += 1
                        if self.bargein_count >= VAD_BARGEIN_FRAMES:
                            log.info(f"[{self.channel_id[:8]}] 🔔 用户打断! "
                                     f"连续{self.bargein_count}帧高能量, last={energy:.0f}")
                            self.is_ai_speaking = False
                            self.audio_buffer_8k.clear()
                            self.is_speaking = False
                            self.silence_count = 0
                            self.speech_start = None
                            self.bargein_count = 0
                    else:
                        self.bargein_count = 0  # 重置防抖计数

                # ---- VAD ----
                is_speech = energy > VAD_ENERGY_THRESHOLD

                if is_speech:
                    if not self.is_speaking:
                        self.is_speaking = True
                        self.speech_start = time.time()
                        self.silence_count = 0
                        log.info(f"[{self.channel_id[:8]}] 🗣️ 检测到说话 energy={energy:.0f}")
                    else:
                        self.silence_count = 0
                    self.audio_buffer_8k.append(pcm_8k)
                else:
                    if self.is_speaking:
                        self.audio_buffer_8k.append(pcm_8k)
                        self.silence_count += 1

                        if self.silence_count >= SILENCE_FRAMES:
                            duration = time.time() - self.speech_start
                            if duration >= VAD_SPEECH_MIN_SEC:
                                log.info(f"[{self.channel_id[:8]}] 说话结束 ({duration:.1f}s)")
                                if self.processing:
                                    # 正在处理，标记待处理
                                    self.pending_speech = True
                                    log.info("正在处理中，标记待处理")
                                    self.audio_buffer_8k.clear()
                                else:
                                    asyncio.create_task(self._process_speech())
                            else:
                                log.info(f"说话太短 ({duration:.1f}s)，忽略")
                                self.audio_buffer_8k.clear()

                            self.is_speaking = False
                            self.silence_count = 0
                            self.speech_start = None

            except Exception as e:
                log.error(f"音频循环异常: {e}")
                await asyncio.sleep(0.01)

        log.info(f"[{self.channel_id[:8]}] 音频循环结束")

    # ---- 语音处理: STT → LLM → TTS ----
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

        log.info(f"[{self.channel_id[:8]}] 📤 发送STT ({len(wav_data)} bytes)...")

        loop = asyncio.get_event_loop()
        try:
            def do_stt():
                return requests.post(STT_URL,
                    files={'file': ('audio.wav', wav_data, 'audio/wav')}, timeout=15)
            resp = await loop.run_in_executor(None, do_stt)
            if resp.status_code != 200:
                log.error(f"STT失败: {resp.status_code}")
                self.processing = False
                self._check_pending()
                return
            text = resp.json().get('text', '').strip()
        except Exception as e:
            log.error(f"STT异常: {e}")
            self.processing = False
            self._check_pending()
            return

        log.info(f"🎤 识别: '{text}'")
        if not text:
            self.processing = False
            self._check_pending()
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
        self._check_pending()

    def _check_pending(self):
        """检查是否有待处理的语音"""
        if self.pending_speech and not self.is_speaking:
            self.pending_speech = False
            log.info(f"[{self.channel_id[:8]}] 处理待处理的语音")
            # 不立即处理，等用户继续说完

    async def _llm(self, user_text):
        system = """你是深圳市车服云科技有限公司的智能语音客服，处理路边停车缴费问题。回答规则：
- 公司：深圳市车服云科技有限公司，路边停车收费助缴平台。
- 收费：费用进入中标公司账户，政府定价。
- 车辆受损：收取的是公共资源占用费，不含保管责任，请报警。
- 停车场缴费不开闸：补缴的是历史路边欠费，请重新扫出口码缴纳本次停车费。
- 手机号来源：您或亲友在合作停车场缴费时主动绑定车牌。
- 征信影响：目前仅为欠费提醒，不影响征信。
- 律师函：仅提醒，未起诉。
- 其他问题：礼貌回复，如果不知道就说"请您咨询人工客服"。

动作标记(末尾单独一行):
[ACTION:hangup] - 用户要挂断
[ACTION:transfer_human] - 转人工
[ACTION:register_plate|车牌号] - 登记车牌
[ACTION:sms_link] - 发短信链接

直接输出答案，简洁口语化，一句话回答，不超过30字。"""

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

            action, action_param = None, None
            pure = []
            for line in full.split('\n'):
                m = re.match(r'\[ACTION:(\w+)(?:\|(.*))?\]', line)
                if m:
                    action, action_param = m.group(1), m.group(2)
                else:
                    pure.append(line)
            return '\n'.join(pure).strip(), action, action_param
        except Exception as e:
            log.error(f"LLM异常: {e}")
            return "系统出错，请稍后再试。", None, None

    # ---- TTS → RTP 发送 (精确计时) ----
    async def _send_tts(self, text):
        self.is_ai_speaking = True
        loop = asyncio.get_event_loop()

        try:
            resp = await loop.run_in_executor(None, lambda: requests.post(
                TTS_URL, json={"input": text, "voice": TTS_VOICE, "speed": TTS_SPEED},
                timeout=30))
            if resp.status_code != 200:
                log.error(f"TTS失败: {resp.status_code}")
                self.is_ai_speaking = False
                return
            audio = await loop.run_in_executor(None, lambda: resp.content)
        except Exception as e:
            log.error(f"TTS异常: {e}")
            self.is_ai_speaking = False
            return

        try:
            with wave.open(io.BytesIO(audio), 'rb') as wf:
                ch = wf.getnchannels()
                fr = wf.getframerate()
                pcm = wf.readframes(wf.getnframes())
        except Exception as e:
            log.error(f"WAV解析失败: {e}")
            self.is_ai_speaking = False
            return

        # 转换为 8kHz 单声道 16bit
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
        log.info(f"[{self.channel_id[:8]}] 🔊 播放TTS ({total_ms:.0f}ms)")

        # ---- 精确计时发包 ----
        packets = []
        for i in range(0, len(ulaw_data), RTP_PACKET_SIZE):
            chunk = ulaw_data[i:i + RTP_PACKET_SIZE]
            if len(chunk) < RTP_PACKET_SIZE:
                chunk += b'\xff' * (RTP_PACKET_SIZE - len(chunk))
            packets.append(chunk)

        next_send_time = time.monotonic()
        sent_count = 0

        for i, pkt in enumerate(packets):
            if not self.active or not self.is_ai_speaking:
                log.info(f"[{self.channel_id[:8]}] TTS被打断 (已发{i}/{len(packets)})")
                break

            await self.rtp.send(pkt)
            sent_count += 1
            next_send_time += RTP_PACKET_INTERVAL

            # 精确等待: 计算还需要等多久
            now = time.monotonic()
            sleep_time = next_send_time - now

            if sleep_time > 0:
                await asyncio.sleep(sleep_time)
            elif sleep_time < -0.1:
                # 落后太多，重置时间基准 (防止雪崩)
                next_send_time = time.monotonic()

        if sent_count == len(packets):
            log.info(f"[{self.channel_id[:8]}] TTS播放完成")
        self.is_ai_speaking = False

    # ---- DTMF ----
    async def on_dtmf(self, digit):
        log.info(f"[{self.channel_id[:8]}] DTMF: {digit}")
        if self.is_ai_speaking:
            self.is_ai_speaking = False

    # ---- 清理 ----
    async def cleanup(self):
        self.active = False
        self.is_ai_speaking = False
        if self.rtp:
            self.rtp.close()
        if self.bridge_id:
            await ari_delete(f"/ari/bridges/{self.bridge_id}")
        if self.em_channel_id:
            await ari_delete(f"/ari/channels/{self.em_channel_id}")


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
                                log.info(f"[{chid[:8]}] ExternalMedia 进入Stasis")
                                await sess.on_em_stasis_start(chid)
                                matched_em = True
                                break

                        if not matched_em and not chname.startswith('UnicastRTP'):
                            caller = ch.get('caller', {}).get('number', 'unknown')
                            log.info(f"📞 来电 {caller} → {chid[:8]}")
                            sess = CallSession(chid, caller)
                            sessions[chid] = sess
                            await sess.setup()

                    elif evt == 'PlaybackFinished':
                        pb = data.get('playback', {})
                        pid = pb.get('id', '')
                        for cid, sess in sessions.items():
                            if sess.welcome_playback_id == pid:
                                log.info(f"[{cid[:8]}] 欢迎语播放结束")
                                await sess._on_welcome_finished()
                                break

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
                                    log.info(f"ExternalMedia {chid[:8]} 已结束")
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
    log.info("🚀 AI语音客服 - 全双工 v2 (优化流畅度)")
    log.info(f"   RTP端口: {RTP_BASE_PORT}+")
    log.info(f"   本机IP: {LOCAL_IP}")
    log.info(f"   VAD阈值: {VAD_ENERGY_THRESHOLD} (提高抗噪)")
    log.info(f"   打断阈值: {VAD_BARGEIN_THRESHOLD} (连续{VAD_BARGEIN_FRAMES}帧)")
    log.info(f"   静音检测: {VAD_SILENCE_SEC}s")
    log.info(f"   最小说话: {VAD_SPEECH_MIN_SEC}s")
    log.info("=" * 60)
    await run()


if __name__ == '__main__':
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        log.info("已停止")