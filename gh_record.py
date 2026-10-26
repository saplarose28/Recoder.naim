#!/usr/bin/env python3
"""Runs inside GitHub Actions.
Records an HLS link with ffmpeg -c copy (no quality loss) in ONE continuous stream, cuts it into files at
keyframes every PART_MB megabytes (default 4000 = 4 GB, whatever time that takes) and uploads each finished
file to Gofile while the recording keeps going. Telegram gets the links, the Status / Split / Stop buttons.
  python gh_record.py            record
  python gh_record.py finish     upload anything left over (used by the always() step)"""
import os, re, ssl, sys, json, glob, time, html, queue, signal, shutil, threading, subprocess, urllib.request, urllib.parse, urllib.error

E = os.environ.get
TOKEN, CHAT = E("TG_TOKEN", ""), E("TG_CHAT", "")
REPO, RUN = E("REPO", ""), E("RUN_ID", "local")
URL = E("URL", "")
NAME = re.sub(r"[^\w\-]+", "_", E("NAME") or "ClipByNaim")
MINUTES = float(E("MINUTES") or 0)             # 0 = until Stop
PART_MIN = float(E("PART_MIN") or 0)            # optional: also split every N minutes (0 = off, split by size only)
PART_MAX = min(float(E("PART_MB") or 4000), 5000) * 1e6   # a new file every N MB (4000 = 4 GB)
BACK = E("BACK_SEGS") or "5"                    # start N segments behind live (safety)
OUT = E("OUT_DIR") or "rec"
MP4_DIR = E("MP4_DIR") or OUT                    # finished .mp4 files (a different disk folder from the .ts files)
FAILED = E("FAILED_DIR") or "rec_failed"
DRY = E("DRY") == "1"                           # test mode: no uploads
TEST_ONCE = E("TEST_ONCE") == "1"               # test mode: do not restart when the input ends
GOFILE_URL = E("GOFILE_URL") or "https://upload.gofile.io/uploadfile"
IDLE_STOP = float(E("IDLE_STOP_MIN") or 10)     # stop the job when the stream sends no data for N minutes (saves GitHub minutes), 0 = off
ASKED = False                                   # True when the link came from Telegram (it is kept out of the GitHub page)
RETRY_BASE = float(E("RETRY_BASE") or 30)       # seconds, grows with every upload retry
GF = {"folder": "", "token": ""}
LIMIT = 345 * 60                                # one job runs ~6 h; a new run continues before that
STAMP = time.strftime("%Y%m%d_%H%M%S")
RUN_URL = "https://github.com/%s/actions/runs/%s" % (REPO, RUN)
UA = E("UA") or "Mozilla/5.0 (Linux; Android 13; Pixel 7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0 Mobile Safari/537.36"
REFERER = E("REFERER") or ""
HDR = ["-user_agent", UA]
REQ_HDR = {"User-Agent": UA, "Accept": "*/*", "Accept-Encoding": "identity", "Connection": "keep-alive"}

stop = threading.Event()
S = {"proc": None, "t0": time.time(), "restarts": 0, "done": [], "page": "", "last_data": time.time(), "drops": [], "gap_total": 0.0, "stop_t": 0, "src_done": threading.Event()}
upq = queue.Queue()
SP = None


# ---------------- small helpers ----------------
def esc(t):
    return html.escape(str(t), quote=False)


def human(b):
    return "%.2f GB" % (b / 1e9) if b >= 1e9 else "%.0f MB" % (b / 1e6)


def hms(s):
    s = int(max(0, s))
    return "%02d:%02d:%02d" % (s // 3600, s % 3600 // 60, s % 60)


def mmss(s):
    s = int(max(0, s))
    return "%d:%02d:%02d" % (s // 3600, s % 3600 // 60, s % 60) if s >= 3600 else "%d:%02d" % (s // 60, s % 60)


def mask(t):
    return (t or "").replace(URL, "<link>") if URL else (t or "")


def _origin(u):
    m = re.match(r"^(https?://[^/]+)", u or "")
    return m.group(1) if m else ""


KB = {"inline_keyboard": [[{"text": "📊 Status", "callback_data": "status"},
                           {"text": "✂️ Split", "callback_data": "split"},
                           {"text": "⏹ Stop", "callback_data": "stop"}]]}


def tg(method, **data):
    if not TOKEN or DRY:
        print("[telegram]", method, re.sub(r"<[^>]+>", "", str(data.get("text", ""))).replace("\n", " | "))
        return {}
    try:
        req = urllib.request.Request("https://api.telegram.org/bot%s/%s" % (TOKEN, method), urllib.parse.urlencode(data).encode())
        return json.load(urllib.request.urlopen(req, timeout=40))
    except urllib.error.HTTPError as e:
        try: body = e.read().decode()[:200]
        except Exception: body = ""
        print("Telegram error %s: %s" % (e.code, body), flush=True)
        return {"ok": False, "error_code": e.code}
    except Exception as e:
        print("telegram error:", e)
        return {}


def say(text, buttons=False):
    if not (CHAT or DRY):
        print("[msg]", re.sub(r"<[^>]+>", "", text))
        return
    d = dict(chat_id=CHAT, text=text, parse_mode="HTML", disable_web_page_preview="true")
    if buttons:
        d["reply_markup"] = json.dumps(KB)
    tg("sendMessage", **d)


def detect_chat():
    """If TG_CHAT is empty, use the chat of the latest message sent to the bot (send it 'hi' first)."""
    global CHAT
    if CHAT or not TOKEN or DRY:
        return
    r = tg("getUpdates", timeout=0)
    ids = [((u.get("message") or {}).get("chat") or {}).get("id") for u in r.get("result", [])]
    ids = [i for i in ids if i]
    if ids:
        CHAT = str(ids[-1]); print("Chat detected from the latest message sent to the bot.", flush=True)
    else:
        print("NO CHAT ID: send 'hi' to your bot in Telegram, then run again (within 24 hours).", flush=True)


def summary(text):
    p = E("GITHUB_STEP_SUMMARY")
    if p:
        try:
            with open(p, "a") as f:
                f.write(text + "\n")
        except OSError:
            pass


# ---------------- MPEG-TS splitter (cuts at keyframes, recording never stops) ----------------
def pes_pts(pk):
    afc = (pk[3] >> 4) & 3
    if not afc & 1:
        return None
    p = 4 + ((1 + pk[4]) if afc & 2 else 0)
    if p + 14 > 188 or pk[p] or pk[p + 1] or pk[p + 2] != 1 or not (pk[p + 7] & 0x80):
        return None
    return ((pk[p + 9] >> 1) & 7) * 1073741824 + ((pk[p + 10] << 22) | ((pk[p + 11] >> 1) << 15) | (pk[p + 12] << 7) | (pk[p + 13] >> 1))


def pes_times(pk):
    """(pts, dts) of the PES that starts in this packet; dts falls back to pts."""
    afc = (pk[3] >> 4) & 3
    if not afc & 1:
        return None, None
    p = 4 + ((1 + pk[4]) if afc & 2 else 0)
    if p + 14 > 188 or pk[p] or pk[p + 1] or pk[p + 2] != 1 or not (pk[p + 7] & 0x80):
        return None, None
    def ts(i):
        return ((pk[i] >> 1) & 7) * 1073741824 + ((pk[i + 1] << 22) | ((pk[i + 2] >> 1) << 15) | (pk[i + 3] << 7) | (pk[i + 4] >> 1))
    pts = ts(p + 9)
    dts = ts(p + 14) if (pk[p + 7] & 0x40) and p + 19 <= 188 else pts
    return pts, dts


MASK33 = 0x1FFFFFFFF
ES_TYPES = {0x01, 0x02, 0x03, 0x04, 0x06, 0x0f, 0x10, 0x11, 0x1b, 0x24, 0x81, 0x87}
VIDEO_TYPES = {0x01, 0x02, 0x10, 0x1b, 0x24}


def _rd5(b, i):
    return ((b[i] >> 1) & 7) * 1073741824 + ((b[i + 1] << 22) | ((b[i + 2] >> 1) << 15) | (b[i + 3] << 7) | (b[i + 4] >> 1))


def _wr5(b, i, v):
    v &= MASK33
    b[i] = (b[i] & 0xF0) | (((v >> 30) & 7) << 1) | 1
    b[i + 1] = (v >> 22) & 255
    b[i + 2] = (((v >> 15) & 127) << 1) | 1
    b[i + 3] = (v >> 7) & 255
    b[i + 4] = ((v & 127) << 1) | 1


def shift_pes(b, off):
    """add `off` ticks to the PTS/DTS of the PES header that starts in this packet"""
    afc = (b[3] >> 4) & 3
    p = 4 + ((1 + b[4]) if afc & 2 else 0)
    fl = b[p + 7]
    if fl & 0x80:
        _wr5(b, p + 9, _rd5(b, p + 9) + off)
    if (fl & 0x40) and p + 19 <= 188:
        _wr5(b, p + 14, _rd5(b, p + 14) + off)


def shift_pcr(b, off):
    if (b[3] & 0x20) and b[4] >= 7 and (b[5] & 0x10):
        base = ((b[6] << 25) | (b[7] << 17) | (b[8] << 9) | (b[9] << 1) | (b[10] >> 7))
        base = (base + off) & MASK33
        b[6] = (base >> 25) & 255; b[7] = (base >> 17) & 255; b[8] = (base >> 9) & 255; b[9] = (base >> 1) & 255
        b[10] = ((base & 1) << 7) | (b[10] & 0x7F)


class Splitter:
    """Takes MPEG-TS bytes (from ffmpeg or straight from a link) and writes them to files that are cut at keyframes.
    * a reconnect never starts a new file: timestamps are re-based so the picture simply continues (no freeze, no jump back)
    * the picture that was cut in half by a drop is thrown away (no broken frame)
    * files are only cut when they reach PART_MB (or on the Split button)"""

    def __init__(self, on_done):
        self.on_done = on_done
        self.buf = b""; self.need_sync = True
        self.f = None; self.path = ""
        self.part_no = 0; self.cur_bytes = 0; self.total = 0
        self.start_pts = None; self.last_pts = None
        self.pat = None; self.pmt = None; self.pmt_pid = None; self.vid = None
        self.want_split = False; self.manual_flag = False; self.on_manual = None
        self.hist = []
        self.es = set(); self.aud = set(); self.pcr = None; self.allowed = None
        self.cc = {}; self.last_wr = {}
        self.skip = None; self.dropping = set(); self.drop_bytes = 0; self.deduped = 0
        self.last_write = time.time(); self.last_es = time.time()
        self.need_key = False; self.need_key_until = 0
        self.off = 0; self.last_raw_v = None; self.last_out_v = None; self.max_out_pts = None; self.fd = 3600
        self.rebase_pending = False; self.rebases = 0
        self.held = {}; self.last_out_es = {}; self.drop_pes = set()

    # ---- sessions ----
    def new_session(self, dedupe=True):
        """The source was reconnected."""
        self.buf = b""; self.need_sync = True
        self.held = {}; self.drop_pes = set()                # a picture that was cut in half is dropped
        marks = {k: v for k, v in self.last_wr.items() if v is not None}
        self.skip = dict(marks) if (marks and dedupe) else None   # HLS replays old data: skip what we already have
        self.dropping = set(); self.drop_bytes = 0
        if dedupe:
            self.need_key = False                            # exact continuation of the same timeline
            self.rebase_pending = False
        else:
            self.need_key = self.vid is not None             # a live link resumes mid-picture: wait for a keyframe
            self.need_key_until = time.time() + 20
            self.rebase_pending = self.vid is not None       # and continue the time line right after the last picture

    # ---- output ----
    def _write(self, b):
        pid = ((b[1] & 0x1f) << 8) | b[2]
        if (b[3] >> 4) & 1:                                  # payload: keep the continuity counter unbroken
            c = (self.cc.get(pid, -1) + 1) & 15
            self.cc[pid] = c
        else:
            c = self.cc.get(pid, 0)
        b[3] = (b[3] & 0xF0) | c
        self.f.write(b); self.cur_bytes += 188
        self.last_write = time.time()

    def _flush(self, pid):
        ent = self.held.pop(pid, None)
        if not ent:
            return
        dts, pkts = ent
        if self.f is None:
            return
        for b in pkts:
            self._write(b)
        if dts is not None:
            self.last_wr["v" if pid == self.vid else pid] = dts
        self.last_es = time.time()

    def media_secs(self):
        if self.start_pts is None or self.last_pts is None:
            return 0.0
        return ((self.last_pts - self.start_pts) % (1 << 33)) / 90000.0

    def speed_mbps(self):
        now = time.time()
        self.hist = [h for h in self.hist if now - h[0] <= 12]
        if len(self.hist) < 2:
            return 0.0
        dt = self.hist[-1][0] - self.hist[0][0]
        return (self.hist[-1][1] - self.hist[0][1]) * 8 / dt / 1e6 if dt > 0.5 else 0.0

    def _open(self):
        self.part_no += 1
        self.path = os.path.join(OUT, "%s_%s_part%03d.ts" % (NAME, STAMP, self.part_no))
        self.f = open(self.path, "wb")
        self.cur_bytes = 0
        self.start_pts = self.last_pts
        for p in (self.pat, self.pmt):                       # every file starts with PAT + PMT, then a keyframe
            if p:
                self._write(bytearray(p))

    def _close(self):
        if not self.f:
            return
        self.f.close(); self.f = None
        if self.cur_bytes > 188 * 40:
            self.on_done(self.path)
        else:
            try: os.remove(self.path)
            except OSError: pass

    def finish(self):
        for pid in list(self.held):
            self._flush(pid)
        self._close()

    # ---- tables ----
    def _pat(self, pk):
        self.pat = bytes(pk)
        p = 4 + ((1 + pk[4]) if (pk[3] >> 4) & 2 else 0)
        p += 1 + pk[p]
        sec = ((pk[p + 1] & 15) << 8) | pk[p + 2]
        q, end = p + 8, min(p + 3 + sec - 4, 188)
        while q + 4 <= end:
            if ((pk[q] << 8) | pk[q + 1]) != 0:
                self.pmt_pid = ((pk[q + 2] & 31) << 8) | pk[q + 3]
                break
            q += 4

    def _pmt(self, pk):
        self.pmt = bytes(pk)
        p = 4 + ((1 + pk[4]) if (pk[3] >> 4) & 2 else 0)
        p += 1 + pk[p]
        sec = ((pk[p + 1] & 15) << 8) | pk[p + 2]
        self.pcr = ((pk[p + 8] & 0x1f) << 8) | pk[p + 9]
        info = ((pk[p + 10] & 15) << 8) | pk[p + 11]
        q, end = p + 12 + info, min(p + 3 + sec - 4, 188)
        while q + 5 <= end:
            st = pk[q]; pid = ((pk[q + 1] & 31) << 8) | pk[q + 2]
            if st in ES_TYPES:
                self.es.add(pid)
                if st in VIDEO_TYPES:
                    if self.vid is None:
                        self.vid = pid
                elif st != 0x06:
                    self.aud.add(pid)
            q += 5 + (((pk[q + 3] & 15) << 8) | pk[q + 4])
        self.allowed = {0, self.pmt_pid, self.pcr} | self.es   # everything else (other programs, EPG, ...) is left out

    # ---- timeline ----
    def _video_time(self, pts, dts, key):
        raw = dts
        if self.rebase_pending and key:
            self._rebase(raw, pts); self.rebase_pending = False
        elif self.last_raw_v is not None and not self.rebase_pending:
            dd = (raw - self.last_raw_v) & MASK33
            if dd >= 1 << 32:
                dd -= 1 << 33
            if dd < -90000 or dd > 900000:                    # time jumped inside one connection: continue smoothly
                self._rebase(raw, pts)
            elif 500 <= dd <= 20000:
                self.fd = dd
        self.last_raw_v = raw
        self.last_out_v = (raw + self.off) & MASK33
        self.last_pts = (pts + self.off) & MASK33
        mx = self.last_pts
        if self.max_out_pts is None or 0 < ((mx - self.max_out_pts) & MASK33) < 0x100000000:
            self.max_out_pts = mx

    def _rebase(self, raw, pts):
        """Continue the time line right after the last picture: the new decode time follows the last decode time AND the new
        display time is later than every picture shown so far, so the picture never stutters or steps back."""
        if self.last_out_v is None:
            return
        off1 = (self.last_out_v + self.fd - raw) & MASK33
        off2 = (self.max_out_pts + self.fd - pts) & MASK33 if self.max_out_pts is not None else off1
        self.off = off2 if 0 <= ((off2 - off1) & MASK33) < 0x100000000 else off1
        self.rebases += 1

    def _should_split(self):
        if self.want_split:
            self.want_split = False; self.manual_flag = True
            return True
        return (PART_MIN > 0 and self.media_secs() >= PART_MIN * 60) or self.cur_bytes >= PART_MAX

    # ---- input ----
    def _sync(self, buf):
        n = len(buf)
        for i in range(0, max(0, n - 188 * 2)):
            if buf[i] == 0x47 and buf[i + 188] == 0x47 and buf[i + 376] == 0x47:
                return i
        return -1

    def feed(self, data):
        buf = self.buf + data
        n = len(buf)
        if not self.need_sync and buf and buf[0] != 0x47:
            self.need_sync = True
        i = 0
        if self.need_sync:
            if n < 188 * 3:
                self.buf = buf; return
            i = self._sync(buf)
            if i < 0:
                self.buf = buf[-188 * 3:]; return
            self.need_sync = False
        end = i + ((n - i) // 188) * 188
        for o in range(i, end, 188):
            self._packet(buf[o:o + 188])
        self.total += end - i
        self.buf = buf[end:]
        self.hist.append((time.time(), self.total))

    def _packet(self, pk):
        pid = ((pk[1] & 0x1f) << 8) | pk[2]
        if pid == 0x1fff:
            return                                           # empty padding
        if self.allowed is None:
            if pid != 0 and pid != self.pmt_pid:
                return
        elif pid not in self.allowed:
            return
        pusi = pk[1] & 0x40
        is_es = pid in self.es
        keypk = bool(pid == self.vid and pusi and (pk[3] >> 4) & 2 and pk[4] > 0 and (pk[5] & 0x40))   # RAI flag = keyframe
        pts = dts = None
        if pusi and is_es:
            pts, dts = pes_times(pk)
        if self.skip is not None and is_es:                  # HLS replay after a reconnect: skip what we already have
            if pusi:
                k = "v" if pid == self.vid else pid
                last = self.skip.get(k)
                ahead = last is None or dts is None or 0 < ((dts - last) & MASK33) < 0x100000000
                if ahead:
                    self.skip.pop(k, None); self.dropping.discard(pid)
                    if not self.skip:
                        self.skip = None
                else:
                    self.dropping.add(pid)
            if pid in self.dropping:
                self.drop_bytes += 188; self.deduped += 188
                if self.drop_bytes > 80_000_000:             # timestamps do not match: stop skipping, keep recording
                    self.skip = None; self.dropping = set()
                else:
                    return
        if self.need_key and is_es:
            if keypk:
                self.need_key = False
            elif time.time() > self.need_key_until:
                self.need_key = False
            else:
                return
        if not is_es:                                        # PAT, PMT and PCR-only packets
            key = False
            if pid == 0:
                if pusi:
                    self._pat(pk)
                    if self.vid is None and self.pmt:
                        key = True                           # audio-only stream: cut at PAT
            elif pid == self.pmt_pid:
                if pusi:
                    self._pmt(pk)
            if key and self.f is None and self.pat and self.pmt:
                self._open()
            elif key and self.f is not None and self._should_split():
                self._close(); self._open()
            if self.f is not None:
                b = bytearray(pk)
                if self.off:
                    shift_pcr(b, self.off)
                self._write(b)
            return
        # ---- elementary stream packet (video / audio) ----
        if pusi:
            if pid == self.vid and dts is not None:
                self._video_time(pts, dts, keypk)
            elif pts is not None:                            # audio: never let time run backwards after a join
                out = (pts + self.off) & MASK33
                last = self.last_out_es.get(pid)
                if last is not None:
                    dd = (out - last) & MASK33
                    if dd >= 1 << 32:
                        dd -= 1 << 33
                    if -90000 < dd <= 0:
                        self._flush(pid)
                        self.drop_pes.add(pid)               # this audio was already recorded: skip it
                        return
                self.last_out_es[pid] = out
            self.drop_pes.discard(pid)
            self._flush(pid)                                 # the previous picture/frame of this stream is complete now
            if keypk:
                if self.f is None:
                    if self.pat and self.pmt:
                        self._open()
                elif self._should_split():
                    self._close(); self._open()
                    if self.manual_flag:
                        self.manual_flag = False
                        if self.on_manual:
                            self.on_manual(self.part_no)
            b = bytearray(pk)
            if self.off:
                if pts is not None:
                    shift_pes(b, self.off)
                shift_pcr(b, self.off)
            self.held[pid] = [dts, [b]]
        elif pid in self.drop_pes:
            return
        elif pid in self.held:
            b = bytearray(pk)
            if self.off:
                shift_pcr(b, self.off)
            self.held[pid][1].append(b)
        # else: the start of this frame was never seen (after a reconnect): throw the piece away


# ---------------- messages ----------------
def status_text():
    el = time.time() - S["t0"]
    left = max(0, MINUTES * 60 - el) if MINUTES else None
    sp = SP
    saved = sum(d["size"] for d in S["done"])
    spd = sp.speed_mbps() if sp else 0
    nxt = ""
    if sp and sp.f:
        t_left = (PART_MIN * 60 - sp.media_secs()) if PART_MIN > 0 else 1e12
        if spd > 0.1:
            t_left = min(t_left, (PART_MAX - sp.cur_bytes) * 8 / (spd * 1e6))
        if t_left < 1e11:
            nxt = "\n✂️ <b>Next auto-split</b>  in ~%s  (at %s)" % (mmss(t_left), human(PART_MAX))
    lines = [
        "🔴 <b>Recording</b>  ·  %s" % esc(NAME), "",
        "⏱ <b>Elapsed</b>  %s%s" % (hms(el), ("   ·   left %s" % hms(left)) if left is not None else ""),
        "📦 <b>Current file</b>  #%02d  ·  %s  ·  %s" % (sp.part_no if sp else 0, human(sp.cur_bytes) if sp else "0 MB", mmss(sp.media_secs()) if sp else "0:00"),
        "✅ <b>Saved</b>  %d file(s)  ·  %s" % (len(S["done"]), human(saved)),
        "⚡ <b>Speed</b>  %.1f Mbps" % spd + nxt,
    ]
    if S["restarts"]:
        lines.append("📶 <b>Reconnects</b>  %s" % drop_line())
    if S["page"]:
        lines += ["", '📂 <a href="%s">Open the download page</a>' % S["page"]]
    return "\n".join(lines)


def do_action(act, cq_id=None):
    global SP
    if act == "status":
        txt = "Status sent"; say(status_text(), buttons=True)
    elif act == "split":
        if SP and SP.f:
            SP.want_split = True; txt = "Split requested"
            say("✂️ <b>Split requested</b>\nThe current file is closed at the next keyframe (a few seconds). Recording continues in a new file.", buttons=True)
        else:
            txt = "Not recording yet"; say("Recording has not started yet, nothing to split.")
    elif act == "stop":
        txt = "Stopping"
        say("⏹ <b>Stopping...</b>\nSaving the last file. This can take up to a minute.")
        halt()
    else:
        return
    if cq_id:
        tg("answerCallbackQuery", callback_query_id=cq_id, text=txt)


def halt():
    S["stop_t"] = time.time()
    stop.set()
    p = S["proc"]
    if p and p.poll() is None:
        p.send_signal(signal.SIGINT)                  # ffmpeg finishes cleanly


def poll():
    off = 0
    r = tg("getUpdates", offset=-1, timeout=0)
    if r.get("error_code") == 409:
        return                                         # a webhook (worker) is active: it handles /stop
    for u in r.get("result", []):
        off = u["update_id"] + 1
    while not stop.is_set():
        r = tg("getUpdates", offset=off, timeout=15, allowed_updates=json.dumps(["message", "callback_query"]))
        if r.get("error_code") == 409:
            return
        for u in r.get("result", []):
            off = u["update_id"] + 1
            cq = u.get("callback_query")
            if cq:
                if str(((cq.get("message") or {}).get("chat") or {}).get("id")) == str(CHAT):
                    do_action(cq.get("data", ""), cq.get("id"))
                continue
            m = u.get("message") or {}
            if str((m.get("chat") or {}).get("id")) != str(CHAT):
                continue
            t = (m.get("text") or "").strip().lower().split("@")[0]
            for key in ("status", "split", "stop"):
                if t.startswith("/" + key) or (key == "split" and t.startswith("/slipt")):
                    do_action(key); break
            else:
                if t.startswith("/start") or t.startswith("/help"):
                    say("🎬 <b>ClipByNaim recorder</b>\nUse the buttons or send /status, /split, /stop.", buttons=True)
        if not r:
            time.sleep(3)


# ---------------- upload (Gofile) ----------------
def gofile_upload(path):
    """Upload to Gofile (no account). All files of one recording go into the same folder page."""
    if DRY:
        print("[dry] would upload to gofile", path); return True, "https://gofile.io/d/DRYRUN", ""
    err = ""
    for attempt in range(6):
        cmd = ["curl", "-sS", "-m", "3600", "-F", "file=@" + path]
        if GF["folder"] and GF["token"]:
            cmd += ["-F", "folderId=" + GF["folder"], "-F", "token=" + GF["token"]]
        r = subprocess.run(cmd + [GOFILE_URL], capture_output=True, text=True)
        try:
            j = json.loads(r.stdout)
        except Exception:
            err = (r.stderr or r.stdout or "no answer from Gofile").strip()[:200]
            j = None
        if j is not None:
            if j.get("status") == "ok":
                d = j.get("data") or {}
                GF["folder"] = d.get("parentFolder") or GF["folder"]
                GF["token"] = d.get("guestToken") or GF["token"]
                return True, d.get("downloadPage") or "", ""
            err = json.dumps(j)[:200]
            GF["folder"] = GF["token"] = ""          # maybe the folder/token was the problem, start a new folder
        print("gofile upload failed (try %d): %s" % (attempt + 1, err), flush=True)
        time.sleep(RETRY_BASE * (attempt + 1))
    return False, "", err


def media_info(path):
    try:
        r = subprocess.run(["ffprobe", "-v", "error", "-select_streams", "v:0", "-show_entries", "stream=width,height:format=duration",
                            "-of", "json", path], capture_output=True, text=True, timeout=60)
        j = json.loads(r.stdout or "{}"); st = (j.get("streams") or [{}])[0]
        return float((j.get("format") or {}).get("duration") or 0), int(st.get("width") or 0), int(st.get("height") or 0)
    except Exception:
        return 0.0, 0, 0


def process(ts):
    """remux the finished .ts to .mp4 (proper duration), upload it, tell Telegram, clean up."""
    os.makedirs(MP4_DIR, exist_ok=True)
    base = os.path.basename(ts)[:-3] + ".mp4"
    mp4 = os.path.join(MP4_DIR, base)
    r = subprocess.run(["ffmpeg", "-hide_banner", "-loglevel", "error", "-y", "-i", ts, "-map", "0:v?", "-map", "0:a?", "-c", "copy", "-avoid_negative_ts", "make_zero", "-movflags", "+faststart", mp4],
                       capture_output=True, text=True)
    if r.returncode != 0 or not os.path.exists(mp4):
        mp4 = ts; base = os.path.basename(ts)
    elif not DRY:
        try: os.remove(ts)                           # free disk space right away
        except OSError: pass
    size = os.path.getsize(mp4)
    dur = media_info(mp4)[0]
    n = len(S["done"]) + 1
    ok, link, err = gofile_upload(mp4)
    head = "✅ <b>File %d saved</b>\n🎞 %s  ·  %s\n" % (n, mmss(dur), human(size))
    if ok:
        if link:
            S["page"] = link
        S["done"].append({"name": base, "size": size, "secs": dur})
        say(head + '⬇️ <a href="%s">Download page</a>  (all files of this recording are listed there)' % (link or S["page"]), buttons=True)
        if not DRY:
            for f in {ts, mp4}:
                try: os.remove(f)
                except OSError: pass
    else:
        os.makedirs(FAILED, exist_ok=True)
        try: shutil.move(mp4, os.path.join(FAILED, base))
        except OSError: pass
        S["done"].append({"name": base, "size": size, "secs": dur})
        say("⚠️ <b>Upload to Gofile failed</b> for %s (%s)\n<b>Reason:</b> <code>%s</code>\n\nThe file is still on the GitHub server until the run ends. If this keeps happening, try again later." %
            (esc(base), human(size), esc((err or "unknown")[:250])))


def uploader():
    while True:
        item = upq.get()
        if item is None:
            return
        try:
            process(item)
        except Exception as e:
            print("process error:", repr(e), flush=True)
            say("⚠️ Error while saving a file: <code>%s</code>" % esc(repr(e)[:200]))


# ---------------- link check + recording ----------------
def explain(err):
    e = (err or "").lower()
    if "403" in e or "forbidden" in e:
        return "403 Forbidden: the stream server refuses GitHub's server. Country/IP block, or the link needs a login or an expired token."
    if "401" in e or "unauthorized" in e:
        return "401 Unauthorized: the link needs a login or its token is wrong or expired."
    if "404" in e or "not found" in e:
        return "404 Not found: the link has expired or is wrong. Copy a fresh link and try again."
    if "timed out" in e or "timeout" in e:
        return "Connection timed out: the server does not answer GitHub's server. Usually an IP/country block."
    if "could not resolve" in e or "name or service not known" in e or "nodename" in e:
        return "The website name in the link could not be found. Check the link for typing mistakes."
    if "invalid data found" in e:
        return "This link is not a video playlist (.m3u8). Open it in a browser: it should give a playlist, not a web page."
    if "connection refused" in e or "reset by peer" in e or "end of file" in e:
        return "The server closed the connection. Usually it blocks GitHub's server."
    return "Unknown reason. Read the ffmpeg line above."


KIND = "hls"                                       # "hls" (.m3u8 playlist) or "ts" (live MPEG-TS over HTTP)


def kind_from_url():
    u = URL.lower()
    path = u.split("?")[0]
    if "m3u8" in u:
        return "hls"
    if path.endswith((".ts", ".mpegts", ".mts", ".m2ts")):
        return "ts"
    return "?"


def probe_kind():
    try:
        r = subprocess.run(["ffprobe", "-v", "error", "-rw_timeout", "20000000"] + HDR + ["-show_entries", "format=format_name", "-of", "csv=p=0", URL],
                           capture_output=True, text=True, timeout=60)
        names = (r.stdout or "").lower()
    except Exception:
        names = ""
    return "hls" if ("hls" in names or "applehttp" in names) else "ts"


def ff_hdr(d):
    out = []
    if d.get("User-Agent"):
        out += ["-user_agent", d["User-Agent"]]
    if d.get("Referer"):
        out += ["-referer", d["Referer"]]
    if d.get("Origin"):
        out += ["-headers", "Origin: %s\r\n" % d["Origin"]]
    return out


def header_sets():
    """Browser / player like request headers to try. Some servers refuse requests that look like a script."""
    own = _origin(URL)
    refs = []
    if REFERER:
        refs.append(("the referer you gave", {"Referer": REFERER, "Origin": _origin(REFERER)}))
    refs.append(("no referer", {}))
    if own:
        refs.append(("the stream's own site as referer", {"Referer": own + "/", "Origin": own}))
    sets = []
    for rl, rd in refs:
        sets.append(("%s, %s" % ("your User-Agent" if E("UA") else "a normal browser", rl), dict(rd, **{"User-Agent": UA})))
    if kind_from_url() != "hls":
        for lab, ua in (("a VLC player", "VLC/3.0.20 LibVLC/3.0.20"), ("ExoPlayer", "ExoPlayerLib/2.18.7"),
                        ("okhttp (many Android IPTV players)", "okhttp/4.9.3"), ("the default ffmpeg", None)):
            sets.append((lab, {"User-Agent": ua} if ua else {}))
    return sets


def precheck():
    global HDR, REQ_HDR, KIND
    last = ""
    for label, d in header_sets():
        hdr = ff_hdr(d)
        try:
            r = subprocess.run(["ffmpeg", "-hide_banner", "-loglevel", "error"] + hdr + ["-t", "6", "-i", URL, "-f", "null", "-"],
                               capture_output=True, text=True, timeout=40)
        except Exception as e:
            last = str(e); continue
        if r.returncode == 0:
            HDR = hdr
            REQ_HDR = {"Accept": "*/*", "Accept-Encoding": "identity", "Connection": "keep-alive", "User-Agent": d.get("User-Agent") or "Lavf/60.16.100"}
            for k in ("Referer", "Origin"):
                if d.get(k):
                    REQ_HDR[k] = d[k]
            KIND = kind_from_url()
            if KIND == "?":
                KIND = probe_kind()
            forced = (E("STREAM_TYPE") or "auto").lower()
            if forced in ("hls", "ts"):
                KIND = forced
            print("Link opened using: %s | stream type: %s" % (label, "MPEG-TS (live)" if KIND == "ts" else "HLS (.m3u8)"), flush=True)
            return True, ""
        last = mask((r.stderr or "").strip())[-400:]
        print("Could not open with %s: %s" % (label, last.splitlines()[-1] if last else "?"), flush=True)
    return False, last


def ask_link():
    """URL = "ask": wait for the m3u8 link in Telegram, so a public repo never shows it."""
    global URL, ASKED
    r = tg("getUpdates", timeout=0)
    if r.get("error_code") == 409:
        print("::error title=Cannot read the link::A webhook is set on the bot. Paste the link in the Run workflow form instead.", flush=True)
        sys.exit(1)
    off = 0
    for u in r.get("result", []):
        off = u["update_id"] + 1
    say("🔗 <b>Send me the stream link</b> (.m3u8 or .ts address) as a normal message.\nI wait 15 minutes. The link stays only in this chat.")
    deadline = time.time() + 15 * 60
    while time.time() < deadline:
        r = tg("getUpdates", offset=off, timeout=20)
        for u in r.get("result", []):
            off = u["update_id"] + 1
            m = u.get("message") or {}
            if str((m.get("chat") or {}).get("id")) != str(CHAT):
                continue
            f = re.search(r"https?://\S+", m.get("text") or "")
            if f:
                URL = f.group(0).strip("<>\"'"); ASKED = True
                print("::add-mask::" + URL, flush=True)      # hide it in every log line from now on
                say("✅ <b>Link received.</b> Checking it...")
                return
        if not r:
            time.sleep(3)
    say("⏰ No link came in 15 minutes, so I stopped. Run the workflow again when you are ready.")
    print("::error title=No link received::Nothing was sent in 15 minutes.", flush=True)
    sys.exit(1)


def where():
    try:
        d = json.load(urllib.request.urlopen("https://ipinfo.io/json", timeout=8))
        return "%s, %s" % (d.get("city", "?"), d.get("country", "?"))
    except Exception:
        return "unknown"


def chain(rem_minutes):
    time.sleep(LIMIT - 300)
    if stop.is_set() or not shutil.which("gh"):
        return
    say("⏳ The 6 hour job limit is near. Starting the next run to continue...")
    if ASKED:
        say("🔁 A new run starts now. <b>Send the stream link again</b> when it asks, so the link is never shown on GitHub.")
    cmd = ["gh", "workflow", "run", "record.yml", "--repo", REPO, "-f", "url=" + ("ask" if ASKED else URL), "-f", "minutes=%d" % rem_minutes,
           "-f", "name=" + NAME, "-f", "part_min=%s" % PART_MIN, "-f", "part_mb=%d" % (PART_MAX / 1e6)]
    if REFERER:
        cmd += ["-f", "referer=" + REFERER]
    subprocess.run(cmd)


def why_exit(rc, lines):
    text = [l.strip() for l in lines if l.strip()]
    key = re.compile(r"error|failed|timed out|timeout|refused|forbidden|not found|invalid data|end of file|server returned|reset", re.I)
    hit = [l for l in text if key.search(l)]
    reason = mask((hit or text or ["no message"])[-1])[:180]
    return "exit code %s: %s" % (rc, reason)


def stderr_reader(p, box):
    for line in iter(p.stderr.readline, b""):
        box.append(line.decode("utf-8", "ignore"))
        del box[:-30]


def drop_line():
    d = S["drops"]
    if not d:
        return "0"
    alive = sum(x["alive"] for x in d) / len(d)
    return "%d  ·  a connection lasts ~%s  ·  ~%d s lost in total" % (len(d), mmss(alive), S["gap_total"])


def drop_reasons():
    cnt = {}
    for x in S["drops"]:
        cnt[x["reason"]] = cnt.get(x["reason"], 0) + 1
    return ", ".join("%s ×%d" % (k, v) for k, v in sorted(cnt.items(), key=lambda kv: -kv[1])[:3])


def ts_source(q):
    """Reads a direct MPEG-TS link with plain HTTP. No ffmpeg start-up, so a dropped connection is re-opened within a second."""
    ctx = None; attempt = 0
    while not stop.is_set():
        t0 = time.time(); got = 0; reason = "server closed the connection"; r = None
        try:
            req = urllib.request.Request(URL, headers=REQ_HDR)
            try:
                r = urllib.request.urlopen(req, timeout=20, context=ctx)
            except urllib.error.URLError as e:
                if isinstance(getattr(e, "reason", None), ssl.SSLError):
                    ctx = ssl._create_unverified_context()
                    r = urllib.request.urlopen(req, timeout=20, context=ctx)
                else:
                    raise
            if getattr(r, "status", 200) != 200:
                raise IOError("HTTP %s" % r.status)
            while not stop.is_set():
                d = r.read1(65536)
                if not d:
                    break
                got += len(d)
                q.put(("data", d))
        except urllib.error.HTTPError as e:
            reason = "HTTP %d" % e.code
        except Exception as e:
            reason = "timeout (no data for 20 s)" if "timed out" in str(e).lower() else ("%s %s" % (type(e).__name__, str(e)[:60])).strip()
        try:
            if r is not None:
                r.close()
        except Exception:
            pass
        if stop.is_set():
            break
        q.put(("drop", reason, time.time() - t0, got))
        if got > 100000:
            attempt = 0
            delay = 0.2                                      # it was a good connection: try again at once
        else:
            attempt += 1
            delay = min(10.0, 0.5 * attempt)
        stop.wait(delay)
    S["src_done"].set()


def ffmpeg_source(q):
    """HLS: ffmpeg reads the playlist; every restart looks back over the whole playlist, repeated data is skipped."""
    first = True
    while not stop.is_set():
        inopts = ["-fflags", "+discardcorrupt+genpts", "-rw_timeout", "60000000", "-reconnect", "1", "-reconnect_streamed", "1",
                  "-reconnect_delay_max", "15", "-seg_max_retry", "15", "-max_reload", "1000", "-m3u8_hold_counters", "1000",
                  "-http_persistent", "0", "-live_start_index", ("-" + BACK) if first else "-10"]
        cmd = ["ffmpeg", "-hide_banner", "-loglevel", "warning", "-y"] + inopts + HDR + [
               "-i", URL, "-map", "0:v?", "-map", "0:a?", "-c", "copy", "-copyts", "-muxdelay", "0", "-muxpreload", "0",
               "-f", "mpegts", "-mpegts_flags", "+resend_headers", "pipe:1"]
        first = False
        t0 = time.time(); got = 0
        p = S["proc"] = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, bufsize=0)
        last_err = []
        threading.Thread(target=stderr_reader, args=(p, last_err), daemon=True).start()
        while True:
            data = p.stdout.read(188 * 1024)
            if not data:
                break
            got += len(data)
            q.put(("data", data))
        p.wait()
        if stop.is_set() or TEST_ONCE:
            break
        q.put(("drop", why_exit(p.returncode, last_err)[:90], time.time() - t0, got))
        stop.wait(1.0)
    q.put(("end",))
    S["src_done"].set()


def record():
    global SP
    os.makedirs(OUT, exist_ok=True)
    detect_chat()
    if URL.strip().lower() in ("", "ask", "telegram"):
        if not (TOKEN and CHAT) and not DRY:
            print("::error title=No Telegram chat::Send 'hi' to your bot first, then run again.", flush=True)
            sys.exit(1)
        ask_link()
    ok, err = precheck()
    if not ok:
        why = explain(err)
        print("PRECHECK FAILED. ffmpeg said:\n" + err, flush=True)
        print("::error title=Link could not be opened from GitHub::" + why, flush=True)
        summary("## Recording did not start\n**Reason:** " + why + "\n\n```\n" + err + "\n```")
        say("❌ <b>The link could not be opened from GitHub's server</b>\n<b>Reason:</b> %s\n\n<code>%s</code>" % (esc(why), esc(err[-300:])))
        sys.exit(1)
    plan = ("stops after %d min" % MINUTES) if MINUTES else "runs until you press Stop"
    kind_txt = "📡 <b>MPEG-TS live stream</b> (starts now, no rewind)" if KIND == "ts" else "📡 HLS stream"
    every = "every %s%s" % (human(PART_MAX), (" or %g min" % PART_MIN) if PART_MIN > 0 else "")
    say("🔴 <b>Recording started</b>\n🎬 %s\n%s\n⏱ %s\n✂️ New file %s (whichever comes first)\n📍 GitHub server: %s\nThe first download link comes after the first file is full." %
        (esc(NAME), kind_txt, plan, every, esc(where())), buttons=True)
    signal.signal(signal.SIGINT, lambda *a: halt())
    signal.signal(signal.SIGTERM, lambda *a: halt())
    total = MINUTES * 60
    if not total or total > LIMIT:
        threading.Thread(target=chain, args=(int((total - LIMIT) / 60) if total else 0,), daemon=True).start()
    if TOKEN and CHAT and not DRY:
        threading.Thread(target=poll, daemon=True).start()
    up = threading.Thread(target=uploader)
    up.start()
    SP = Splitter(upq.put)
    SP.on_manual = lambda n: say("✂️ <b>Split done</b>\nFile #%d started. Recording continues." % n, buttons=True)
    end_at = S["t0"] + (min(total, LIMIT) if total else LIMIT)

    def watchdog():
        while not stop.is_set():
            if time.time() >= end_at:
                halt(); return
            if IDLE_STOP > 0 and time.time() - SP.last_es > IDLE_STOP * 60:
                say("⏹ <b>The stream sent no data for %g minutes</b>, so the match has probably ended.\nSaving what I have and ending the job to save your GitHub minutes." % IDLE_STOP)
                halt(); return
            time.sleep(2)
    threading.Thread(target=watchdog, daemon=True).start()

    def stream_monitor():
        warned, since = False, 0
        while not stop.is_set():
            idle = time.time() - SP.last_es
            if not warned and idle > 90:
                warned, since = True, time.time() - idle
                say("⚠️ <b>The stream has not sent data for %s.</b>\nStill trying. Short breaks are repaired automatically." % mmss(idle))
            elif warned and idle < 15:
                warned = False
                say("✅ <b>Stream is back</b> after %s. Recording continues in the same file." % mmss(time.time() - since))
            time.sleep(5)
    threading.Thread(target=stream_monitor, daemon=True).start()

    q = queue.Queue(maxsize=4000)                      # a big buffer: slow disk/CPU never makes the server drop us
    threading.Thread(target=(ts_source if KIND == "ts" else ffmpeg_source), args=(q,), daemon=True).start()
    t_drop = None
    while True:
        try:
            item = q.get(timeout=1)
        except queue.Empty:
            if stop.is_set() and (S["src_done"].is_set() or time.time() - S["stop_t"] > 8):
                break
            continue
        kind = item[0]
        if kind == "data":
            if t_drop is not None:
                S["gap_total"] += time.time() - t_drop; t_drop = None
            SP.feed(item[1]); S["last_data"] = time.time()
        elif kind == "drop":
            S["restarts"] += 1
            S["drops"].append({"t": time.time(), "reason": item[1], "alive": item[2], "got": item[3]})
            SP.new_session(dedupe=(KIND != "ts"))         # same file continues, the picture is joined smoothly
            t_drop = time.time()
            print("Reconnect %d after %s (%s)" % (S["restarts"], mmss(item[2]), item[1]), flush=True)   # log only
        else:
            break
    SP.finish()
    upq.put(None)
    up.join()
    saved = sum(d["size"] for d in S["done"])
    page = S["page"]
    summary("## Recording finished\n%d file(s), %s. %s" % (len(S["done"]), human(saved), ("[Download page](%s)" % page) if page else ""))
    rows = "\n".join("%d.  %s  ·  %s" % (i + 1, human(d["size"]), mmss(d["secs"])) for i, d in enumerate(S["done"][:30]))
    rec_line = ("\n\n📶 Reconnects: %s\n<i>%s</i>" % (drop_line(), esc(drop_reasons()))) if S["drops"] else ""
    say("🏁 <b>Recording finished</b>\n🎬 %s\n📁 %d file(s)  ·  %s\n⏱ %s\n\n%s%s%s" %
        (esc(NAME), len(S["done"]), human(saved), hms(time.time() - S["t0"]), rows, rec_line,
         ('\n\n📂 <a href="%s">Download all files (one page)</a>' % page) if page else "\n\n⚠️ No file could be uploaded. See the run log."))


def finish():
    """always() step: upload leftovers if the main step was cancelled or killed."""
    leftovers = sorted(glob.glob(os.path.join(OUT, "*.ts")))
    if not leftovers:
        return
    for f in leftovers:
        process(f)
    say("⚠️ <b>Recording was interrupted.</b> Saved %d leftover file(s).%s" % (len(leftovers), ('\n📂 <a href="%s">Download page</a>' % S["page"]) if S["page"] else ""))


if __name__ == "__main__":
    finish() if len(sys.argv) > 1 and sys.argv[1] == "finish" else record()
