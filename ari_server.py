#!/usr/bin/env python3
"""
AI 语音客服 - 全双工方案 v17 (车牌纠错+打断安全+状态机)

核心特性:
  1. 车牌纠错: ASR原始文本 → correct_license_plate → 标准格式
  2. 状态机: NORMAL/BUSY_WAIT_WECHAT/BUSY_WAIT_CONTINUE/TRANSFERRING
  3. _send_tts返回True/False, 打断取消action
  4. reply_played标记, 防止未知action导致沉默
  5. action合法性校验
  6. 来电号码直接用, 不问手机号
  7. 桥ID使用随机UUID, 避免冲突
"""

import asyncio
import json
import uuid
import logging
import re
import os
import struct
import subprocess
import time
import io
import wave
import socket
import urllib.parse
import numpy as np
import requests
import websockets
from collections import deque
from typing import List, Tuple, Optional

# ==================== Asterisk ARI 配置 ====================
ASTERISK_HOST = 'localhost'
ASTERISK_PORT = 8088
ASTERISK_USER = 'my_ari_user'
ASTERISK_PASS = '1qaz@WSX3edc$RFV'
STASIS_APP = 'my_ai_agent'
LOCAL_IP = '192.168.102.90'

# ==================== 人工客服分机 ====================
HUMAN_EXTENSION = '1001'
HUMAN_ENDPOINT = f'PJSIP/{HUMAN_EXTENSION}'
HUMAN_WAIT_RETRY = 10
HUMAN_MAX_RETRIES = 3

# ==================== 短信配置 ====================
SMS_API_URL = "http://192.168.101.219:6099/SMS/SendMsg"
SMS_API_KEY = "asdfg"
SMS_SYSTEM_NUM = "31"
SMS_CALLBACK_URL = "www.baidu.com"
SMS_TEMPLATE_PARKING = "65"
SMS_TEMPLATE_WECHAT = "65"

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
    'vad_start_margin': 500,
    'vad_end_margin': 250,
    'bargein_base': 1200,
    'echo_factor': 0.3,
    'echo_margin': 500,
    'bargein_frames': 4,
    'post_bargein_wait': 0.05,
    'post_tts_cooldown': 0.15,
    'silence_sec': 1.0,
    'max_speech_sec': 30,
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
    'keep_prebuffer': False,
    'prebuffer_keep_ms': 500,
}

DEFAULT_PARAMS = SPEAKER_PARAMS
WELCOME_TEXT = "您好，欢迎致电车服云科技。我是智能客服助手，请问有什么可以帮您？"

logging.basicConfig(level=logging.INFO, format='%(asctime)s] [%(levelname)s] %(message)s')
log = logging.getLogger(__name__)
auth = (ASTERISK_USER, ASTERISK_PASS)


# ==================== 车牌文本纠错模块 ====================

PROVINCE_WHITELIST = [
    "京", "沪", "津", "渝", "冀", "晋", "辽", "吉", "黑",
    "苏", "浙", "皖", "闽", "赣", "鲁", "豫", "鄂", "湘",
    "粤", "琼", "川", "贵", "云", "陕", "甘", "青", "蒙",
    "桂", "藏", "宁", "新", "港", "澳", "台"
]

PROVINCE_HOMOPHONE_MAP = {
    "金": "京", "今": "京", "经": "京", "精": "京",
    "户": "沪", "护": "沪", "互": "沪",
    "进": "津",
    "于": "渝", "鱼": "渝", "余": "渝",
    "记": "冀", "几": "冀", "机": "冀",
    "近": "晋",
    "了": "辽", "聊": "辽", "料": "辽",
    "集": "吉",
    "和": "黑", "河": "黑",
    "数": "苏", "书": "苏",
    "泽": "浙", "这": "浙", "者": "浙",
    "晚": "皖", "万": "皖", "完": "皖",
    "民": "闽", "敏": "闽", "门": "闽",
    "干": "赣", "感": "赣", "敢": "赣",
    "路": "鲁", "卢": "鲁",
    "雨": "豫", "与": "豫",
    "恶": "鄂", "俄": "鄂", "额": "鄂",
    "香": "湘", "相": "湘", "箱": "湘", "向": "湘",
    "月": "粤", "越": "粤", "约": "粤",
    "穷": "琼", "群": "琼",
    "穿": "川", "串": "川",
    "归": "贵", "鬼": "贵",
    "运": "云", "允": "云",
    "山": "陕", "闪": "陕", "善": "陕",
    "肝": "甘",
    "清": "青", "情": "青",
    "猛": "蒙", "梦": "蒙",
    "跪": "桂", "柜": "桂", "龟": "桂",
    "脏": "藏", "葬": "藏",
    "凝": "宁", "您": "宁",
    "心": "新", "信": "新"
}

LETTER_MAP = {
    "比": "B", "逼": "B", "币": "B", "宾": "B",
    "西": "C", "吸": "C", "喜": "C",
    "地": "D", "弟": "D",
    "意": "E", "亿": "E", "衣": "E",
    "爱抚": "F",
    "记": "G", "鸡": "G", "及": "G",
    "诶取": "H",
    "解": "J", "节": "J",
    "开": "K", "凯": "K",
    "艾尔": "L",
    "艾木": "M",
    "皮": "P", "批": "P",
    "扣": "Q", "口": "Q",
    "阿": "R", "啊": "R",
    "艾斯": "S",
    "替": "T", "踢": "T",
    "有": "U", "油": "U",
    "维": "V",
    "达不溜": "W",
    "艾克斯": "X", "客": "X",
    "外": "Y", "歪": "Y",
    "贼": "Z"
}

DIGIT_MAP = {
    "零": "0", "〇": "0",
    "一": "1", "壹": "1",
    "二": "2", "贰": "2",
    "三": "3", "叁": "3",
    "四": "4", "肆": "4",
    "五": "5", "伍": "5",
    "六": "6", "陆": "6",
    "七": "7", "柒": "7",
    "八": "8", "捌": "8",
    "九": "9", "玖": "9",
    "幺": "1", "两": "2"
}

_REPLACE_MAP = {**LETTER_MAP, **DIGIT_MAP}
_REPLACE_ITEMS = sorted(_REPLACE_MAP.items(), key=lambda x: -len(x[0]))

FILTER_WORDS = ["啊", "嗯", "哦", "哎", "呀", "呢", "吧", "吗", "哈",
                "然后", "那个", "这个", "麻烦", "请", "我", "的", "是",
                "车", "牌", "号", "号码", "车牌号", "报一下", "说一下",
                "你好", "谢谢", "再见", "对", "不对", "是的", "不是"]

_PLATE_PATTERN = re.compile(
    r'^[' + ''.join(PROVINCE_WHITELIST) + r'][A-HJ-NP-Z][A-HJ-NP-Z0-9]{5,6}$'
)


def _map_chinese_to_alnum(text: str) -> str:
    for ch, target in _REPLACE_ITEMS:
        text = text.replace(ch, target)
    return text


def _clean_text(text: str) -> str:
    text = text.upper()
    text = re.sub(r'[^一-龥A-Z0-9]', '', text)
    for word in FILTER_WORDS:
        text = text.replace(word.upper(), '')
        text = text.replace(word, '')
    return text


def _find_province_candidates(text: str) -> List[Tuple[int, str, int]]:
    candidates = []
    for idx, char in enumerate(text):
        if char in PROVINCE_WHITELIST:
            candidates.append((idx, char, 100))
        elif char in PROVINCE_HOMOPHONE_MAP:
            candidates.append((idx, PROVINCE_HOMOPHONE_MAP[char], 80))
    candidates.sort(key=lambda x: (-x[2], -x[0]))
    return candidates


def _find_second_char(text: str, province_idx: int) -> Optional[Tuple[int, str]]:
    for idx in range(province_idx + 1, len(text)):
        char = text[idx]
        if char in 'ABCDEFGHJKLMNPQRSTUVWXYZ':
            return (idx, char)
    return None


def _extract_following_chars(text: str, second_idx: int) -> str:
    following = text[second_idx + 1:]
    following = re.sub(r'[^A-Z0-9]', '', following)
    return following


def _smart_deduplicate(following: str, max_len: int = 8) -> str:
    if len(following) <= max_len:
        return following
    result = []
    prev = None
    i = 0
    while i < len(following):
        cur = following[i]
        if cur == prev:
            remaining = following[i+1:]
            if len(result) + len(remaining) <= max_len:
                early = ''.join(result) + remaining
                return early
            i += 1
        else:
            result.append(cur)
            prev = cur
            i += 1
    first_pass = ''.join(result)
    if len(first_pass) <= max_len:
        return first_pass
    current = first_pass
    prev_len = -1
    while len(current) != prev_len:
        prev_len = len(current)
        current = re.sub(r'(.+)\1+', r'\1', current)
        if len(current) <= max_len:
            if len(current) >= 7:
                return current
            else:
                return first_pass
    if len(current) < 7:
        return first_pass
    elif len(current) <= max_len:
        return current
    else:
        return current


def correct_license_plate(asr_text: str) -> Tuple[Optional[str], str]:
    """
    车牌文本纠错
    输入: ASR识别的原始文本 (如 "粤 h 三一三 d 区")
    输出: (纠错后的车牌号如"粤H313D", 状态信息)
          如果纠错失败, 返回 (None, 错误信息)
    """
    cleaned = _clean_text(asr_text)
    if not cleaned:
        return None, "清洗后无有效文本"
    mapped = _map_chinese_to_alnum(cleaned)
    province_candidates = _find_province_candidates(mapped)
    if not province_candidates:
        return None, "未识别到省份简称"
    for prov_idx, prov_char, _ in province_candidates[:3]:
        sec = _find_second_char(mapped, prov_idx)
        if not sec:
            continue
        sec_idx, sec_char = sec
        prefix = prov_char + sec_char
        following = _extract_following_chars(mapped, sec_idx)
        combined = _smart_deduplicate(prefix + following, max_len=8)
        if len(combined) not in (7, 8):
            continue
        plate = prefix + combined[len(prefix):]
        if _PLATE_PATTERN.match(plate):
            return plate, "识别成功"
    return None, "未找到符合格式的车牌"


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


async def ari_get(path, params=None):
    url = f"http://{ASTERISK_HOST}:{ASTERISK_PORT}{path}"
    loop = asyncio.get_event_loop()
    try:
        resp = await loop.run_in_executor(
            None, lambda: requests.get(url, auth=auth, params=params, timeout=10))
        if resp.status_code >= 400:
            log.error(f"ARI GET {path} -> {resp.status_code}: {resp.text[:300]}")
            return None
        return resp.json() if resp.content else None
    except Exception as e:
        log.error(f"ARI GET {path} 异常: {e}")
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


# ==================== 短信发送 ====================
def send_sms(tele: str, template_id: str, parameters: str = "") -> bool:
    log.info(f"📤 发送短信: tele={tele}, template={template_id}")
    params = {
        "key": SMS_API_KEY,
        "templateId": template_id,
        "tele": tele,
        "parameters": parameters,
        "systemnum": SMS_SYSTEM_NUM,
        "callbackUrl": SMS_CALLBACK_URL
    }
    try:
        resp = requests.get(SMS_API_URL, params=params, timeout=10)
        if resp.status_code == 200:
            data = resp.json()
            log.info(f"短信接口返回: {data}")
            if data.get("Code") == 110000:
                log.info(f"✅ 短信发送成功: {tele}")
                return True
            else:
                log.error(f"❌ 短信发送失败: {data.get('Message')}")
        else:
            log.error(f"❌ 短信HTTP错误: {resp.status_code}")
    except Exception as e:
        log.error(f"❌ 短信异常: {e}")
    return False


# ==================== 设备状态检测 (CLI备选) ====================
def get_device_state_cli(device_name="PJSIP/1001"):
    try:
        ext = device_name.split("/")[1]
        result = subprocess.run(
            ['asterisk', '-rx', f'pjsip show endpoint {ext}'],
            capture_output=True, text=True, timeout=2)
        output = result.stdout
        if "Not in use" in output:
            return "IDLE"
        elif "In use" in output:
            return "INUSE"
        elif "Unavailable" in output:
            return "UNAVAILABLE"
        return "UNKNOWN"
    except Exception as e:
        log.error(f"CLI设备状态异常: {e}")
        return "UNKNOWN"


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

        # ★ 清洗来电号码
        raw_caller = caller
        if '<' in raw_caller and '>' in raw_caller:
            raw_caller = raw_caller.split('<')[1].rstrip('>')
        elif ' ' in raw_caller:
            raw_caller = raw_caller.split()[0]
        self.caller = raw_caller

        self.bridge_id = f"br_{uuid.uuid4().hex[:8]}"  # ★ 改为随机唯一ID
        self.em_channel_id = None
        self.em_expected_id = f"em_{uuid.uuid4().hex[:8]}"
        self.rtp = None
        self.rtp_port = self._alloc_port()

        # ★★★ 状态机 ★★★
        self.state = 'NORMAL'

        # 转接状态
        self.transfer_channel_id = None
        self.transferred = False
        self._ringback_playback = None
        self._retry_task = None

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

        # ★ 来电号码就是用户手机号
        self.user_phone = None
        if raw_caller and raw_caller != 'unknown':
            digits = re.sub(r'\D', '', raw_caller)
            log.info(f"[{self.channel_id[:8]}] 📱 来电号码: {digits}")
            if len(digits) >= 5:
                self.user_phone = digits
                log.info(f"[{self.channel_id[:8]}] 📱 来电号码: {digits}")

        # ★ 车牌登记流程
        self.pending_plate = None       # 阶段2暂存: 纠错后的车牌
        self.registered_plate = None    # 阶段3完成: 已确认登记的车牌
        self.plate_api_result = None    # 车牌处理API返回结果
        self._plate_api_task = None     # 车牌处理API异步任务

    @property
    def p(self):
        return self.mode_params

    def _estimate_echo(self):
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

    # ==================== ★★★ 状态机辅助 ★★★ ====================

    def _is_affirmative(self, text):
        if not text:
            return False
        negative = ['不', '不要', '不用', '算了', '别', '不用了', '不要了',
                    '不等', '不想等', '不用等', '不需要', '不需要了']
        affirmative = ['是', '好', '对', '要', '行', '可以', '同意', '发',
                       '发送', '需要', '嗯', '是的', '好的', '要的',
                       '发吧', '发给我', '帮我发', '等', '继续等',
                       '等等', '等一下', '我等', '愿意']
        for w in negative:
            if w in text:
                return False
        for w in affirmative:
            if w in text:
                return True
        return False


    # ==================== ★★★ 车牌转语音文本 ★★★ ====================

    @staticmethod
    def _plate_to_speech(plate):
        """
        车牌转TTS友好文本: 粤H313D7 → 粤 H 三 一 三 D 七
        让TTS引擎逐字读出, 而不是读成"三百一十三"
        """
        DIGIT_CN = {
            '0': '零', '1': '一', '2': '二', '3': '三', '4': '四',
            '5': '五', '6': '六', '7': '七', '8': '八', '9': '九',
        }
        parts = []
        for ch in plate:
            if ch in DIGIT_CN:
                parts.append(DIGIT_CN[ch])
            else:
                # 省份简称等, 保持原样
                parts.append(ch)
        return ' '.join(parts)

    # ==================== ★★★ 设备状态检测 ★★★ ====================

    async def _check_extension_state(self):
        device = urllib.parse.quote(HUMAN_ENDPOINT, safe='')
        result = await ari_get(f"/ari/deviceStates/{device}")
        if result:
            state = result.get('state', '')
            log.info(f"[{self.channel_id[:8]}] ARI设备状态: {state}")
            state_map = {
                'NOT_INUSE': 'IDLE', 'INUSE': 'INUSE', 'BUSY': 'INUSE',
                'UNAVAILABLE': 'UNAVAILABLE', 'RINGING': 'INUSE',
                'RINGINUSE': 'INUSE', 'ONHOLD': 'INUSE',
            }
            mapped = state_map.get(state)
            if mapped:
                return mapped
        loop = asyncio.get_event_loop()
        try:
            return await loop.run_in_executor(
                None, lambda: get_device_state_cli(HUMAN_ENDPOINT))
        except:
            return 'UNKNOWN'

    # ==================== ★★★ 转人工 (状态机) ★★★ ====================

    async def _transfer_to_human(self, reply=None):
        # ★★★ 清理打断残留 ★★★
        self.audio_buffer_8k.clear()
        self.is_speaking = False
        self.speech_start = None
        self.bargein_count = 0

        if reply:
            ok = await self._send_tts(reply)
            if not ok:
                log.info(f"[{self.channel_id[:8]}] 转接提示被打断, 取消转接")
                self.state = 'NORMAL'
                return

        self.audio_buffer_8k.clear()
        self.is_speaking = False
        self.speech_start = None

        state = await self._check_extension_state()
        log.info(f"[{self.channel_id[:8]}] 📞 分机{HUMAN_EXTENSION}状态: {state}")

        if state in ('IDLE', 'UNKNOWN'):
            self.state = 'TRANSFERRING'
            await self._do_transfer()
        else:
            self.state = 'BUSY_WAIT_WECHAT'
            await self._send_tts(
                "抱歉，人工客服目前正忙。"
                "您可以关注我们的企业微信进行咨询，"
                "是否需要我把企业微信链接发送到您的手机？")

    async def _handle_busy_wechat_response(self, text):
        log.info(f"[{self.channel_id[:8]}] 💬 企微确认回复: '{text}'")

        if self._is_affirmative(text):
            await self._send_wechat_link()
            self.state = 'NORMAL'
        else:
            self.state = 'BUSY_WAIT_CONTINUE'
            await self._send_tts("好的，是否需要继续等待人工客服？")

    async def _handle_busy_continue_response(self, text):
        log.info(f"[{self.channel_id[:8]}] 💬 等待确认回复: '{text}'")

        if self._is_affirmative(text):
            self.state = 'TRANSFERRING'
            await self._send_tts("好的，请您稍等，我为您等待人工客服。")
            self._retry_task = asyncio.create_task(self._wait_and_retry_transfer())
        else:
            self.state = 'NORMAL'
            await self._send_tts("好的，如果还有其他问题，随时告诉我。")

    async def _wait_and_retry_transfer(self):
        for i in range(HUMAN_MAX_RETRIES):
            await asyncio.sleep(HUMAN_WAIT_RETRY)
            if not self.active:
                return

            state = await self._check_extension_state()
            log.info(f"[{self.channel_id[:8]}] ⏳ 等待{i+1}/{HUMAN_MAX_RETRIES}, "
                     f"状态: {state}")

            if state in ('IDLE', 'UNKNOWN'):
                await self._do_transfer()
                return

            if i < HUMAN_MAX_RETRIES - 1:
                await self._send_tts("客服仍在忙碌，请继续等待。")

        log.info(f"[{self.channel_id[:8]}] ⏳ 等待超时")
        await self._send_tts(
            "抱歉，人工客服暂时无法接听。"
            "我可以帮您发送企业微信链接，方便您后续咨询，是否需要？")
        self.state = 'BUSY_WAIT_WECHAT'

    async def _do_transfer(self):
        log.info(f"[{self.channel_id[:8]}] 📞 开始转接")

        self.active = False
        self.is_ai_speaking = False

        if self._silence_task:
            self._silence_task.cancel()
            try:
                await self._silence_task
            except:
                pass

        if self.em_channel_id:
            await ari_delete(
                f"/ari/bridges/{self.bridge_id}/channels/{self.em_channel_id}")
            await asyncio.sleep(0.1)
            await ari_delete(f"/ari/channels/{self.em_channel_id}")
            self.em_channel_id = None

        if self.rtp:
            self.rtp.close()
            self.rtp = None

        try:
            playback_id = f"ring_{uuid.uuid4().hex[:8]}"
            await ari_post(f"/ari/channels/{self.channel_id}/play",
                           params={'media': 'sound:pbx-transfer',
                                   'playbackId': playback_id})
            self._ringback_playback = playback_id
        except:
            self._ringback_playback = None

        dial_id = f"transfer_{uuid.uuid4().hex[:8]}"
        self.transfer_channel_id = dial_id
        self.transferred = True

        result = await ari_post("/ari/channels", params={
            'endpoint': HUMAN_ENDPOINT,
            'app': STASIS_APP,
            'channelId': dial_id,
            'timeout': '30',
        })

        if not result:
            log.error(f"[{self.channel_id[:8]}] 拨打分机失败!")
            try:
                await ari_post(f"/ari/channels/{self.channel_id}/play",
                               params={'media': 'sound:cannot-complete-inorder'})
            except:
                pass
            await asyncio.sleep(3)
            await self.cleanup()
            return

        actual_id = result.get('id', dial_id)
        log.info(f"[{self.channel_id[:8]}] 📞 已拨打分机 {HUMAN_EXTENSION}, "
                 f"通道: {actual_id}")

    async def on_transfer_channel_start(self, channel_id):
        self.transfer_channel_id = channel_id
        await ari_post(f"/ari/bridges/{self.bridge_id}/addChannel",
                       params={'channel': channel_id})
        log.info(f"[{self.channel_id[:8]}] 📞 分机已加入桥")

    async def on_transfer_answer(self):
        log.info(f"[{self.channel_id[:8]}] 📞 分机已接听!")
        if self._ringback_playback:
            try:
                await ari_delete(f"/ari/playbacks/{self._ringback_playback}")
            except:
                pass
            self._ringback_playback = None

    # ==================== ★★★ 短信 ★★★ ====================

    def _get_user_phone(self):
        return self.user_phone

    async def _send_wechat_link(self):
        phone = self._get_user_phone()
        if not phone:
            await self._send_tts(
                "抱歉，无法获取您的号码，请直接搜索车服云科技关注企业微信。")
            return

        log.info(f"[{self.channel_id[:8]}] 📤 发企微链接 → {phone}")
        loop = asyncio.get_event_loop()
        success = await loop.run_in_executor(
            None, lambda: send_sms(phone, SMS_TEMPLATE_WECHAT))

        if success:
            await self._send_tts(
                "企业微信链接已发送到您的手机，请查收。感谢您的来电，再见。")
            await asyncio.sleep(1)
            await self.cleanup()
        else:
            await self._send_tts(
                "抱歉，短信发送失败，您可以直接搜索车服云科技关注企业微信。")

    async def _send_parking_link(self, phone=None):
        if not phone:
            phone = self._get_user_phone()
        if not phone:
            await self._send_tts("抱歉，无法获取您的号码，无法发送短信。")
            return

        log.info(f"[{self.channel_id[:8]}] 📤 发缴费链接 → {phone}")
        loop = asyncio.get_event_loop()
        success = await loop.run_in_executor(
            None, lambda: send_sms(phone, SMS_TEMPLATE_PARKING))

        if success:
            await self._send_tts("缴费链接已发送到您的手机，请查收。")
        else:
            await self._send_tts("抱歉，短信发送失败，请稍后再试。")

    # ==================== ★★★ 车牌处理API ★★★ ====================

    async def _process_plate(self, plate):
        """
        处理车牌: 调用后端API
        ★ 占位方法, 等你提供API后替换
        """
        log.info(f"[{self.channel_id[:8]}] 📋 调用车牌处理API: {plate}")
        loop = asyncio.get_event_loop()
        try:
            # TODO: 替换为实际API调用
            # result = await loop.run_in_executor(
            #     None, lambda: requests.post(PLATE_API_URL,
            #         json={"plate": plate, "phone": self.user_phone},
            #         timeout=10))
            # data = result.json()
            # self.plate_api_result = data

            # ★ 占位: 模拟成功
            await asyncio.sleep(0.5)
            self.plate_api_result = {
                'success': True,
                'plate': plate,
                'message': '处理成功'
            }
            log.info(f"[{self.channel_id[:8]}] 📋 车牌处理完成: {self.plate_api_result}")

        except Exception as e:
            log.error(f"[{self.channel_id[:8]}] 📋 车牌处理失败: {e}")
            self.plate_api_result = {
                'success': False,
                'plate': plate,
                'message': str(e)
            }

    # ==================== 模式检测 ====================

    async def _detect_mode_from_welcome(self):
        await asyncio.sleep(ECHO_DETECT_DURATION)
        if self.mode_locked:
            return
        if len(self.pre_buffer_energies) < 50 or len(self.send_energy_history) < 50:
            self.mode_locked = True
            return
        now = time.monotonic()
        recv_energies, send_energies = [], []
        for i, energy in enumerate(self.pre_buffer_energies):
            frame_time = now - (len(self.pre_buffer_energies) - i) * 0.02
            send_e = [e for t, e in self.send_energy_history if abs(t - frame_time) < 0.25]
            if send_e:
                recv_energies.append(energy)
                send_energies.append(max(send_e))
        if len(recv_energies) < 30:
            self.mode_locked = True
            return
        recv_arr = np.array(recv_energies, dtype=np.float64)
        send_arr = np.array(send_energies, dtype=np.float64)
        recv_std, send_std = np.std(recv_arr), np.std(send_arr)
        if recv_std < 1 or send_std < 1:
            self.mode_locked = True
            return
        correlation = float(np.mean(
            (recv_arr - np.mean(recv_arr)) / recv_std *
            (send_arr - np.mean(send_arr)) / send_std))
        correlation = max(-1.0, min(1.0, correlation))
        old_name = self.mode_name
        if correlation > ECHO_CORRELATION_THRESHOLD:
            self.mode_params, self.mode_name = SPEAKER_PARAMS, SPEAKER_PARAMS['name']
        else:
            self.mode_params, self.mode_name = HEADSET_PARAMS, HEADSET_PARAMS['name']
        self.mode_locked = True
        log.info(f"[{self.channel_id[:8]}] 🔒 模式: {old_name} → {self.mode_name} "
                 f"(相关度={correlation:.2f})")

    def _extract_headset_prebuffer(self):
        if not self.pre_buffer:
            return []
        keep_ms = self.p.get('prebuffer_keep_ms', 400)
        keep_frames = max(1, int(keep_ms / 20))
        total = len(self.pre_buffer)
        result = list(self.pre_buffer)[-keep_frames:] if total > keep_frames else list(self.pre_buffer)
        log.info(f"[{self.channel_id[:8]}] 预缓冲: 保留{len(result)}帧({len(result)*20}ms)")
        return result

    # ==================== 初始化 ====================

    async def setup(self):
        # 先应答通道
        await ari_post(f"/ari/channels/{self.channel_id}/answer")

        # ★ 先尝试删除可能残留的同名桥（忽略404）
        await ari_delete(f"/ari/bridges/{self.bridge_id}")

        # 创建新桥
        result = await ari_post("/ari/bridges", params={'bridgeId': self.bridge_id, 'type': 'mixing'})
        if not result:
            log.error("建桥失败!")
            await self.cleanup()
            return

        # 加入主通道
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
            log.info(f"[{self.channel_id[:8]}] ExternalMedia 创建成功")
        else:
            log.error(f"[{self.channel_id[:8]}] ExternalMedia 创建失败!")

    async def on_em_stasis_start(self, channel_id):
        self.em_channel_id = channel_id
        await ari_post(f"/ari/bridges/{self.bridge_id}/addChannel",
                       params={'channel': channel_id})
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
            except:
                await asyncio.sleep(0.02)

    # ==================== 音频处理主循环 ====================

    async def _audio_loop(self):
        log.info(f"[{self.channel_id[:8]}] 🎧 音频循环启动 [{self.mode_name}]")
        _log_counter = 0

        while self.active:
            try:
                now = time.monotonic()

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

                if now < self.discard_until:
                    rtp = await self.rtp.recv()
                    if rtp is not None:
                        payload = rtp.get('payload', b'')
                        if len(payload) > 0 and not self.is_speaking:
                            pcm = ulaw_to_pcm(payload)
                            e = np.sqrt(np.mean(pcm.astype(np.float64) ** 2))
                            self._update_noise_floor(e)
                    continue

                rtp = await self.rtp.recv()
                if rtp is None:
                    continue

                payload = rtp.get('payload', b'')
                if len(payload) == 0:
                    continue

                pcm_8k = ulaw_to_pcm(payload)
                energy = np.sqrt(np.mean(pcm_8k.astype(np.float64) ** 2))

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
                                                 f"{len(clean_frames)}帧")
                                else:
                                    pb_count = len(self.pre_buffer)
                                    self.pre_buffer.clear()
                                    self.pre_buffer_energies.clear()
                                    log.info(f"[{self.channel_id[:8]}] 📡 丢弃预缓冲{pb_count}帧")
                                self.discard_until = time.monotonic() + self.p['post_bargein_wait']
                        else:
                            self.bargein_count = 0
                    continue

                vad_start = self._get_vad_start()
                vad_end = self._get_vad_end()
                is_speech = energy > (vad_end if self.is_speaking else vad_start)

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

    # ==================== ★★★ 语音处理 (状态机) ★★★ ====================

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

        log.info(f"🎤 识别: '{text}' [state={self.state}]")
        if not text:
            self.processing = False
            return

        # ★★★ 状态机 ★★★
        if self.state == 'BUSY_WAIT_WECHAT':
            await self._handle_busy_wechat_response(text)
            self.processing = False
            return

        if self.state == 'BUSY_WAIT_CONTINUE':
            await self._handle_busy_continue_response(text)
            self.processing = False
            return

        if self.state == 'TRANSFERRING':
            log.info(f"[{self.channel_id[:8]}] 转接中, 忽略输入")
            self.processing = False
            return

        # ★ NORMAL: 走LLM
        reply, action, action_param, intent = await self._llm(text)
        log.info(f"🤖 回复: '{reply}' action={action} param={action_param}")

        # ★★★ reply播放标记 ★★★
        reply_played = False

        if action:
            if action == 'hangup':
                if reply:
                    ok = await self._send_tts(reply)
                    reply_played = True
                    if not ok:
                        log.info(f"[{self.channel_id[:8]}] 再见语被打断, 取消挂断")
                        self.processing = False
                        return
                await asyncio.sleep(1)
                await self.cleanup()
                self.processing = False
                return

            elif action == 'transfer_human':
                await self._transfer_to_human(reply)
                reply_played = True
                self.processing = False
                return

            elif action == 'sms_link':
                if reply:
                    ok = await self._send_tts(reply)
                    reply_played = True
                    if not ok:
                        self.processing = False
                        return
                await self._send_parking_link(action_param)
                self.processing = False
                return

            elif action in ('wechat_link', 'send_wecom_link'):
                if reply:
                    ok = await self._send_tts(reply)
                    reply_played = True
                    if not ok:
                        self.processing = False
                        return
                await self._send_wechat_link()
                self.processing = False
                return

            elif action == 'request_plate':
                # ★ 阶段1: 索取车牌
                log.info(f"[{self.channel_id[:8]}] 📋 阶段1: 索取车牌")
                if reply:
                    await self._send_tts(reply)
                    reply_played = True
            elif action == 'plate_received':
                # ★ 阶段2: 用户报了车牌 → 用原始ASR文本纠错 → 再回复
                log.info(f"[{self.channel_id[:8]}] 📋 阶段2: 用户报车牌")
                log.info(f"[{self.channel_id[:8]}] 📋 原始ASR: '{text}'")

                corrected_plate, correct_status = correct_license_plate(text)

                if not corrected_plate and action_param:
                    corrected_plate, correct_status = correct_license_plate(action_param)

                if corrected_plate:
                    self.pending_plate = corrected_plate
                    log.info(f"[{self.channel_id[:8]}] 📋 纠错成功: "
                             f"'{text}' → '{corrected_plate}'")
                    speech_plate = self._plate_to_speech(corrected_plate)
                    # ★ 用纠错后的车牌构造确认话术, 不用LLM的reply
                    await self._send_tts(
                        f"我帮你核对一下 您说的是{speech_plate}对吗？")
                    self.plate_api_result = None
                    self._plate_api_task = asyncio.create_task(
                        self._process_plate(self.pending_plate))
                    self.state = 'PLATE_CONFIRMING'
                    self.plate_retry_count = 0
                else:
                    # ★ 纠错失败 → 引导企微
                    log.warning(f"[{self.channel_id[:8]}] 📋 纠错失败: {correct_status}")
                    self.pending_plate = None
                    await self._send_tts(
                        "不好意思，车牌信息没能识别出来，"
                        "我帮您发一个企业微信链接，"
                        "添加后客服可以一对一帮您核对，您看可以吗？")
                    self.state = 'BUSY_WAIT_WECHAT'
                reply_played = True

            elif action == 'register_plate':
                # ★ 阶段3: 确认登记
                if self.pending_plate is None:
                    log.warning(f"[{self.channel_id[:8]}] 📋 ⚠️ 跳过阶段2, 先纠错")
                    corrected_plate, correct_status = correct_license_plate(text)
                    if corrected_plate:
                        self.pending_plate = corrected_plate
                        log.info(f"[{self.channel_id[:8]}] 📋 纠错成功: "
                                 f"'{text}' → '{corrected_plate}'")
                        speech_plate = self._plate_to_speech(corrected_plate)
                        confirm_text = f"好的，您说的是{speech_plate}对吗？"
                        await self._send_tts(confirm_text)
                        reply_played = True
                        self.plate_api_result = None
                        self._plate_api_task = asyncio.create_task(
                            self._process_plate(self.pending_plate))
                        self.processing = False
                        return
                    else:
                        fallback = action_param or ''
                        if fallback:
                            self.pending_plate = fallback
                            log.info(f"[{self.channel_id[:8]}] 📋 LLM兜底: '{fallback}'")
                            speech_plate = self._plate_to_speech(fallback)
                            confirm_text = f"好的，您说的是{speech_plate}对吗？"
                            await self._send_tts(confirm_text)
                            reply_played = True
                            self.plate_api_result = None
                            self._plate_api_task = asyncio.create_task(
                                self._process_plate(self.pending_plate))
                            self.processing = False
                            return
                        else:
                            await self._send_tts(
                                "抱歉，没听清您的车牌号，麻烦您再说一次好吗？")
                            self.processing = False
                            return

                plate = self.pending_plate
                log.info(f"[{self.channel_id[:8]}] 📋 阶段3: 确认登记 '{plate}'")

                if self._plate_api_task:
                    try:
                        await self._plate_api_task
                    except Exception as e:
                        log.error(f"[{self.channel_id[:8]}] 📋 车牌API异常: {e}")

                if self.plate_api_result and not self.plate_api_result.get('success'):
                    err_msg = self.plate_api_result.get('message', '车牌处理遇到问题')
                    await self._send_tts(f"抱歉，{err_msg}，请您稍后再试或转人工处理。")
                    self.pending_plate = None
                    self.processing = False
                    return

                self.registered_plate = plate
                self.pending_plate = None
                log.info(f"[{self.channel_id[:8]}] 📋 ✅ 车牌已登记: {plate}")
                if reply:
                    # ★ 替换reply中的车牌为语音版
                    speech_plate = self._plate_to_speech(plate)
                    reply = reply.replace(plate, speech_plate)
                    # ★ 如果LLM用了带中文数字的版本也替换
                    await self._send_tts(reply)
                    reply_played = True

            else:
                # ★ 未知action: 忽略action, 仍然播放reply
                log.warning(f"[{self.channel_id[:8]}] ⚠️ 未知action: {action}, 忽略")

        # ★ reply没播放过就播放
        if reply and self.active and not reply_played:
            await self._send_tts(reply)

        response_content = json.dumps({"intent": intent, "reply": reply}, ensure_ascii=False)
        self.history.append({"role": "user", "content": text})
        self.history.append({"role": "assistant", "content": response_content})
        if len(self.history) > 100:
            self.history = self.history[-10:]

        self.processing = False

    # ==================== LLM ====================
    async def _llm(self, user_text):
        system = """你是深圳市车服云科技停车欠费智能电话客服。
用户来电主要两种起因：①收到停车欠费提醒短信；②停车场扫码出场时弹出历史欠费弹窗。
你的工作流程：先识别用户核心意图，再匹配对应标准话术回复。

强制输出规则（最高优先级，永久生效）
每次回复仅输出标准合法 JSON，只包含intent、reply两个字段，禁止新增其他字段。
不允许任何额外文字、空格、换行、注释、Markdown，所有对话内容统一放在 reply 字段内。
无论用户输入什么内容，必须先匹配意图再输出 JSON，禁止直接输出自然话术。
无匹配意图统一使用fallback，reply 固定为：这个问题我帮您转人工确认，请稍等。


意图匹配及优先级（从上至下，命中第一条即锁定意图）
用户称车牌已注销、车辆已过户、车牌持有人不符、车场车牌识别字符错误、号码匹配错发 → 非本人车牌、车辆
用户否认欠费、称未到场、已缴费、长期未开车 → 停车欠费短信异议
用户查询欠费金额、停车时间地点、欠费订单详情 → 查询停车欠费订单信息
用户收到欠费短信、频繁收到扣费短信并产生疑问 → 停车欠费短信疑问
用户缴费后道闸不开启、无法驶出停车场 → 扫码缴费后，道闸不开，出不去停车场
用户停车场扫码时弹出历史欠费窗口 → 扫码缴费时，弹出欠费提醒
用户询问公司全称、平台身份 → 公司信息
用户询问平台业务、主营内容 → 公司业务
用户询问平台类型 → 平台信息
用户质疑手机号来源、担忧隐私泄露 → 手机号来源
用户询问亲友为何收到自己车牌欠费短信 → 为何其他人会收到自己车牌的欠费短信
用户质疑短信通知延迟、多年欠费才推送 → 为何短信通知延迟
用户询问欠费是否影响个人征信 → 征信影响
用户提及律师函、询问是否会被起诉 → 律师函影响
用户询问短信内客服链接是什么 → 企业微信信息
用户询问点击链接后的查询操作步骤 → 企业微信公众号操作
用户担心链接有病毒、不安全、不敢点开 → 推送链接疑问
用户同意接收短信链接，回复好的 / 可以 / 发过来 → 同意企业微信链接推送
用户嫌链接麻烦、拒绝推送、要求代办、自行搜索查询 → 拒绝企业微信链接推送
停车场物业 / 管理员咨询助缴相关问题 → 停车场管理方或物业询问
用户反馈多扣费、多出欠费订单 → 多扣了几笔订单
用户质疑停车收费合理性、重复收费、费用去向 → 收费疑问
用户询问停车期间车辆受损责任归属 → 停车期间，车辆受损谁负责
用户申请开具缴费发票 → 开发票
用户申请退费、退款 → 要求退款
用户表示没听清、要求重复讲解 → 没听懂
用户回复无其他问题（承接客服提问）→ 意图结束
用户主动要求转人工、投诉、情绪激动 → 转人工
用户表达感谢、提出结束通话 → 再见
用户打招呼、测试通话（喂、你好、听得见吗）→ 问候
以上全部不匹配 → fallback

意图对应标准回复
"问候": "听得到，您那边是遇到什么问题了吗？",
"公司信息": "我们这里是深圳市车服云科技有限公司，路边停车收费第三方助缴平台。请问有什么可以帮您？",
"公司业务": "我们受全国各地停车运营公司委托，为您提供停车费聚合查询、历史欠费补缴等服务。你那边是遇到了什么问题？",
"平台信息": "我们这里是路边停车收费第三方助缴平台。你那边是遇到了什么问题？",
"停车欠费短信疑问": "这是一条停车欠费补缴的短信通知，可能由于您当时忘记缴纳停车费，受当地停车运营公司委托，我司特发此短信，提醒车主您及时补缴。",
"停车欠费短信异议": "非常理解您对这笔停车欠费有疑问，稍后我将通过短信发送一条企业微信客服链接到您手机号可以吗? 点击链接即可以打开微信客服页面进行核实与反馈。",
"手机号来源": "您的手机号是在我们合作的停车场缴费时，主动绑定车牌后，由停车场系统匹配并推送的。我们作为助缴平台，并未直接获取或存储您的个人号码信息，所有流程均严格遵守隐私保护相关规定，请您放心。",
"为何其他人会收到自己车牌的欠费短信": "这种情况是因为您的朋友或家人，在我们合作的停车场缴费时，主动绑定了您的车牌号，系统会根据车牌匹配到对应的绑定信息，因此欠费提醒就推送到了对方的手机号上。",
"为何短信通知延迟": "由于您当时停车结束时未及时扫码缴费，我们无法直接获取您的联系方式。近期我们通过助缴平台的信息匹配，才成功联系到您，为您发送欠费提醒。",
"征信影响": "目前这只是欠费提醒，不会对您的个人征信、车辆使用等产生任何影响，请您放心。",
"律师函影响": "目前只是发律师函提醒，还未正式起诉，请您放心。",
"查询停车欠费订单信息": "稍后我将通过短信发送一条企业微信链接给您手机号，点击链接后可以联系企业微信在线客服，在上面输入车牌即可查询历史欠费详情，可以吗？",
"企业微信信息": "车服云科技微信客服链接。收到短信后点击短信链接即可打开在线客服页面进行查询处理，稍后我将通过短信发送企业微信链接到您手机号，可以吗？",
"企业微信公众号操作": "收到短信后，点击短信链接即可打开微信在线客服网页，输入您的车牌号即可查询历史欠费详情。稍后我将通过短信发送企业微信链接到您手机号，可以吗？",
"推送链接疑问": "非常理解您的顾虑，这只是一个微信在线客服的链接。您也可以通过微信搜索‘车服云科技’微信公众号进行查询处理。",
"同意企业微信链接推送": "好的，短信已发送，请留意短信信息。收到短信后点击链接即可打开在线客服进行查询处理。请问还有其他问题吗？",
"拒绝企业微信链接推送": "理解您的心情，这边为您转接人工客服处理，可以吗？",
"非本人车牌、车辆": "不好意思，给您造成困扰了，稍后我将通过短信发送一条企业微信客服链接给您手机号可以吗？点击链接后即可访问在线客服进行反馈?",
"扫码缴费时，弹出欠费提醒": "这是路边停车历史欠费的缴费提醒，我们目前与停车场开展联合助缴服务，若您名下有路边停车历史欠费，在驶出合作停车场时，系统会自动弹出缴费提醒，为您提供便捷的补缴渠道。如果您不想补缴，可以点击‘暂不处理’。",
"扫码缴费后，道闸不开，出不去停车场": "您刚刚可能缴纳的是历史欠费订单，而非当前停车场的费用，所以道闸未开启。请重新扫描出口二维码，缴纳本次停车费即可。如果再次弹出历史欠费提醒且您不想补缴，可以点击‘暂不处理’。",
"停车场管理方或物业询问": "我们是跟停车场系统方有合作开展联合助缴服务，若车牌有路边停车历史欠费，在驶出停车场时，系统会自动弹出缴费提醒窗口，为车主提供便捷的补缴渠道。具体可咨询停车场系统方。",
"多扣了几笔订单": "您多缴纳的订单可能是路边停车的历史欠费，我们目前与停车场开展联合助缴服务。如果您不想补缴，可以点击‘暂不处理’。如需退款，这边帮您转人工处理。",
"收费疑问": "若是公共车位收费：可能当时您停在政府规划的停车收费泊位，路段两侧都有停车告示牌，以及车上应该有投放停车小票。若是车船税燃油费重复疑问：路边停车费属于公共资源占用及管理服务费，车船税是针对车辆产权征收的财产税，燃油费主要用于道路建设养护，它们收费性质并不相同，也不存在重复收费。若是费用交给谁：缴纳的费用是进入中标公司的专用账户。我们是政府通过公开招投标选定的合法服务单位，所有收费路段、收费标准均由政府统一制定，相关收益也会按规定上缴财政。",
"停车期间，车辆受损谁负责": "我们收取的是公共资源占用费，不包含车辆保管责任。如果您在停车期间遇到车辆受损的情况，建议您及时报警处理。",
"开发票": "发票问题需要转接人工客服处理，现在帮您转接可以吗？",
"要求退款": "这个问题需要转接人工客服处理，现在帮您转接可以吗？",
"没听懂": "复述上一轮回复核心内容，询问用户是否接收链接或转接人工",
"意图结束": "好的，请问还有其他问题吗？",
"转人工": "好的，正在为您转接人工客服，请稍等。",
"再见": "好的，感谢您的来电，再见。",
"fallback": "这个问题我帮您转人工确认，请稍等。"
硬性约束
全程严格遵守输出规则，所有对话轮次均不可违规，输出格式错误视为无效回复。"""
        
        msgs = [{"role": "system", "content": system}] + self.history + \
               [{"role": "user", "content": user_text}]
        payload = {"model": LLM_MODEL, "messages": msgs, "temperature": 0.0, "max_tokens": 128}

        loop = asyncio.get_event_loop()
        start = time.perf_counter()  # 记录开始时间
        try:
            resp = await loop.run_in_executor(
                None, lambda: requests.post(LLM_URL, json=payload, timeout=30)
            )
            elapsed = time.perf_counter() - start  # 计算耗时
            print(f"LLM请求耗时: {elapsed:.2f}s")  # 打印耗时（保留两位小数）

            if resp.status_code != 200:
                return "系统繁忙，请稍后再拨。", None, None
            full = resp.json()['choices'][0]['message']['content'].strip()

            # ---- 解析 JSON（新格式，兼容前缀文本） ----
            try:
                # 提取 JSON 片段（可能前面有额外文字）
                json_start = full.find('{')
                json_end = full.rfind('}')
                if json_start != -1 and json_end != -1 and json_end > json_start:
                    json_str = full[json_start:json_end+1]
                else:
                    json_str = full

                data = json.loads(json_str)
                reply = data.get('reply', '').strip()
                intent = data.get('intent')
                action_str = data.get('action')
                action = None
                action_param = None
                if action_str and isinstance(action_str, str):
                    m = re.search(r'\[ACTION:(\w+)(?:\|(.*?))?\]', action_str)
                    if m:
                        action = m.group(1)
                        action_param = m.group(2)
                if intent:
                    log.info(f"[{self.channel_id[:8]}] 🧠 用户意图: {intent}")
                else:
                    log.warning(f"[{self.channel_id[:8]}] LLM返回无意图字段")
            except json.JSONDecodeError:
                # 兼容旧格式：逐行查找 [ACTION:...] 标记
                log.warning(f"LLM返回非JSON，尝试旧格式解析: {full[:100]}")
                action, action_param, intent = None, None, None
                clean_lines = []
                for line in full.split('\n'):
                    m = re.search(r'\[ACTION:(\w+)(?:\|(.*?))?\]', line)
                    if m:
                        action, action_param = m.group(1), m.group(2)
                        line = line[:m.start()] + line[m.end():]
                    clean_lines.append(line)
                reply = '\n'.join(clean_lines).strip()

            # ---- 校验 action 合法性 ----
            valid_actions = {
                'hangup', 'transfer_human', 'sms_link',
                'wechat_link', 'send_wecom_link',
                'request_plate', 'plate_received', 'register_plate'
            }
            if action and action not in valid_actions:
                log.warning(f"LLM生成了无效action: {action}, 已忽略")
                action = None
                action_param = None

            return reply, action, action_param, intent

        except Exception as e:
            log.error(f"LLM异常: {e}")
            return "系统出错，请稍后再试。", None, None, None


    # ==================== ★★★ TTS → RTP (返回完成状态) ★★★ ====================

    async def _send_tts(self, text):
        """
        播放TTS语音
        返回: True = 正常播放完成, False = 被打断
        """
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
                return True
            audio = await loop.run_in_executor(None, lambda: resp.content)
        except Exception as e:
            log.error(f"TTS异常: {e}")
            self.is_ai_speaking = False
            self.discard_until = time.monotonic() + self.p['post_tts_cooldown']
            return True

        try:
            with wave.open(io.BytesIO(audio), 'rb') as wf:
                ch, fr = wf.getnchannels(), wf.getframerate()
                pcm = wf.readframes(wf.getnframes())
        except Exception as e:
            log.error(f"WAV解析失败: {e}")
            self.is_ai_speaking = False
            self.discard_until = time.monotonic() + self.p['post_tts_cooldown']
            return True

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

        was_bargein = not self.is_ai_speaking

        if was_bargein:
            log.info(f"[{self.channel_id[:8]}] TTS被打断, 保留audio_buffer "
                     f"({len(self.audio_buffer_8k)}帧)")
        else:
            self.is_ai_speaking = False
            self.discard_until = time.monotonic() + self.p['post_tts_cooldown']
            self.audio_buffer_8k.clear()
            self.is_speaking = False
            self.speech_start = None

        self.bargein_count = 0
        self.pre_buffer.clear()
        self.pre_buffer_energies.clear()

        log.info(f"[{self.channel_id[:8]}] TTS结束 [{self.mode_name}]")
        return not was_bargein

    # ==================== DTMF ====================

    async def on_dtmf(self, digit):
        log.info(f"[{self.channel_id[:8]}] DTMF: {digit}")
        if self.is_ai_speaking:
            self.is_ai_speaking = False
            self.audio_buffer_8k.clear()
            self.is_speaking = False
            self.bargein_count = 0
            self.discard_until = time.monotonic() + self.p['post_bargein_wait']

    # ==================== 清理 ====================

    async def cleanup(self):
        self.active = False
        self.is_ai_speaking = False
        if self._retry_task:
            self._retry_task.cancel()
            try:
                await self._retry_task
            except:
                pass
        if self._plate_api_task:
            self._plate_api_task.cancel()
            try:
                await self._plate_api_task
            except:
                pass
        if self._silence_task:
            self._silence_task.cancel()
            try:
                await self._silence_task
            except:
                pass
        if self.rtp:
            self.rtp.close()
        if self.bridge_id:
            await ari_delete(f"/ari/bridges/{self.bridge_id}")
        if self.em_channel_id:
            await ari_delete(f"/ari/channels/{self.em_channel_id}")
        if self.transfer_channel_id:
            await ari_delete(f"/ari/channels/{self.transfer_channel_id}")
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
                        matched = False

                        for cid, sess in list(sessions.items()):
                            if sess.em_expected_id == chid or sess.em_channel_id == chid:
                                await sess.on_em_stasis_start(chid)
                                matched = True
                                break

                        if not matched:
                            for cid, sess in list(sessions.items()):
                                if sess.transfer_channel_id == chid:
                                    await sess.on_transfer_channel_start(chid)
                                    matched = True
                                    break

                        if not matched and not chname.startswith('UnicastRTP'):
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

                    elif evt == 'ChannelStateChange':
                        channel_data = data.get('channel', {})
                        state = channel_data.get('state', '')
                        changed_chid = channel_data.get('id', '')
                        if state == 'Up':
                            for cid, sess in sessions.items():
                                if sess.transfer_channel_id == changed_chid:
                                    await sess.on_transfer_answer()
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
                                elif sess.transfer_channel_id == chid:
                                    log.info(f"[{cid[:8]}] 📞 分机通道结束")
                                    await sess.cleanup()
                                    if cid in sessions:
                                        del sessions[cid]
                                    break

        except websockets.exceptions.ConnectionClosed:
            log.warning("ARI WS 断开，5秒后重连...")
            await asyncio.sleep(5)
        except Exception as e:
            log.error(f"ARI WS 异常: {e}", exc_info=True)
            await asyncio.sleep(5)


async def main():
    log.info("=" * 60)
    log.info("🚀 AI语音客服 v17 (车牌纠错+打断安全+状态机)")
    log.info(f"  📞 转人工: 分机={HUMAN_EXTENSION}, "
             f"等待{HUMAN_WAIT_RETRY}s×{HUMAN_MAX_RETRIES}次")
    log.info(f"  📤 短信: 缴费模板={SMS_TEMPLATE_PARKING}, "
             f"企微模板={SMS_TEMPLATE_WECHAT}")
    log.info(f"  🎧 耳机: VAD=噪声+{HEADSET_PARAMS['vad_start_margin']}/"
             f"+{HEADSET_PARAMS['vad_end_margin']}, "
             f"预缓冲={HEADSET_PARAMS['prebuffer_keep_ms']}ms")
    log.info(f"  📡 免提: VAD=噪声+{SPEAKER_PARAMS['vad_start_margin']}/"
             f"+{SPEAKER_PARAMS['vad_end_margin']}")
    log.info(f"  📋 车牌纠错 | ASR原始文本→correct_license_plate→标准格式")
    log.info(f"  ★ _send_tts返回True/False | 打断取消action | reply_played标记")
    log.info("=" * 60)
    await run()


if __name__ == '__main__':
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        log.info("已停止")
