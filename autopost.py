"""HAADIKHAN69 - Cloud engine.
GitHub Actions isay har ~30 minute baad khud chalata hai. Yeh:
  1) TikTok accounts check karta hai aur nayi videos queue mein daalta hai
  2) schedule ka time aane par video download kar ke Facebook Page par upload karta hai
  3) sab kuch state.json mein likh deta hai (iPhone app wahi parhti hai)
Settings config.json mein hain (iPhone app se badalti hain).
"""
import os
import re
import json
import base64
import datetime
import hashlib
import random
import time
import tempfile
import traceback
from zoneinfo import ZoneInfo

import requests

ROOT = os.path.dirname(os.path.abspath(__file__))
CONFIG_PATH = os.path.join(ROOT, "config.json")
STATE_PATH = os.path.join(ROOT, "state.json")
TIMEOUT = 60
UPLOAD_TIMEOUT = 60 * 20


# ------------------------------------------------------------------ helpers
def load_json(path, default):
    try:
        with open(path, encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return default


def save_state(state):
    with open(STATE_PATH, "w", encoding="utf-8") as f:
        json.dump(state, f, ensure_ascii=False, indent=1)


class Ctx:
    def __init__(self, cfg, state):
        self.cfg = cfg
        self.state = state
        self.tz = ZoneInfo(cfg.get("timezone") or "Asia/Karachi")
        self.now = datetime.datetime.now(self.tz)
        self.tokens = {}
        self.make_hook = ""
        self.scanned = set()
        self.user_token = ""
        self.pages_refreshed = False
        self.ntfy_topic = ""
        self.push = None
        self.notes = []            # things to tell the user on the phone at the end of the run
        self.uploaded = {}         # page name -> videos uploaded this run
        self.posted = set()        # TikTok video ids already posted on any Page
        self.started = time.monotonic()
        self.manual = False
        self.fp = None
        self.fp_dirty = False

    # ---- Facebook pause ("hold") so a block is never hammered
    def hold(self):
        h = self.state.get("fb_hold")
        if not h:
            return None
        if h.get("kind") == "auth":
            return h               # only a Reconnect clears this
        try:
            until = datetime.datetime.strptime(h["until"], "%Y-%m-%d %H:%M").replace(tzinfo=self.tz)
        except (KeyError, ValueError):
            until = self.now
        if datetime.datetime.now(self.tz) >= until:
            self.state.pop("fb_hold", None)
            self.state.pop("fb_error", None)
            self.log("Facebook pause is over - uploads resume", "info")
            return None
        return h

    def set_hold(self, kind, err):
        hours = {"rate": 2, "block": 12}.get(kind, 0)
        until = (datetime.datetime.now(self.tz) + datetime.timedelta(hours=hours)).strftime("%Y-%m-%d %H:%M")
        self.state["fb_hold"] = {"kind": kind, "until": until, "reason": str(err)[:200], "since": self.ts()}
        if kind == "auth":
            self.state["fb_error"] = ("Facebook login expired - tap Reconnect Facebook in the Pages tab. "
                                      "Uploads are paused until then (no videos are lost).")
        else:
            self.state["fb_error"] = (f"Facebook paused uploads ({'too many requests' if kind == 'rate' else 'access limited'}). "
                                      f"The tool is waiting safely until {until} and will not retry before that, "
                                      "so the block does not get worse. No videos are lost.")
        self.log(f"Facebook {kind} - all uploads paused until {until if kind != 'auth' else 'Reconnect'}: {err}", "error")
        self.notes.append(("high", "⚠️ " + self.state["fb_error"]))

    def ts(self):
        return datetime.datetime.now(self.tz).strftime("%Y-%m-%d %H:%M")

    def log(self, msg, level="info", acc=None):
        print(f"[{self.ts()}] {level.upper()} {('@' + acc['username'] + ': ') if acc else ''}{msg}", flush=True)
        self.state.setdefault("log", []).insert(0, {
            "t": self.ts(), "l": level, "a": acc["id"] if acc else "", "m": msg[:400]})
        del self.state["log"][300:]

    def acc_state(self, acc):
        st = self.state.setdefault("accounts", {}).setdefault(acc["id"], {})
        st.setdefault("videos", [])
        st.setdefault("seen", [])
        st.setdefault("slots", {})
        st.setdefault("last_checked", None)
        st.setdefault("first_done", False)
        return st


def decrypt_tokens(enc, password):
    """iPhone app Page tokens ko password se lock (AES-GCM) kar ke config.json mein rakhti hai."""
    from cryptography.hazmat.primitives.ciphers.aead import AESGCM
    from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC
    from cryptography.hazmat.primitives import hashes
    raw = base64.b64decode(enc)
    salt, iv, ct = raw[:16], raw[16:28], raw[28:]
    key = PBKDF2HMAC(algorithm=hashes.SHA256(), length=32, salt=salt, iterations=200000).derive(password.encode())
    return json.loads(AESGCM(key).decrypt(iv, ct, None).decode())


def parse_times(items):
    out = []
    if isinstance(items, str):
        items = re.split(r"[,\s]+", items)
    for p in items or []:
        m = re.fullmatch(r"(\d{1,2}):(\d{2})", str(p).strip())
        if m and int(m.group(1)) < 24 and int(m.group(2)) < 60:
            out.append(f"{int(m.group(1)):02d}:{int(m.group(2)):02d}")
    return sorted(set(out))


def username_from_url(url):
    m = re.search(r"tiktok\.com/@([^/?#]+)", url or "")
    return m.group(1) if m else (url or "").lstrip("@")


def normalize_url(text):
    t = (text or "").strip()
    if t.startswith("http"):
        return t.split("?")[0].rstrip("/")
    return f"https://www.tiktok.com/@{t.lstrip('@')}"


def build_caption(original, acc):
    text = original if acc.get("use_caption", True) else ""
    if text and acc.get("remove_hashtags"):
        text = re.sub(r"(?<!\w)#\S+", "", text)
        text = re.sub(r"[ \t]{2,}", " ", text).strip()
    extra = (acc.get("extra") or "").strip()
    if extra:
        text = f"{text}\n\n{extra}" if text else extra
    return text.strip()


# ------------------------------------------------------------------ TikTok
def _ydl(opts):
    import yt_dlp
    base = {"quiet": True, "no_warnings": True, "noprogress": True}
    cookies = os.path.join(ROOT, "cookies.txt")
    if os.path.isfile(cookies):
        base["cookiefile"] = cookies
    base.update(opts)
    return yt_dlp.YoutubeDL(base)


def tiktok_list(url, limit):
    with _ydl({"extract_flat": "in_playlist", "skip_download": True, "playlistend": int(limit)}) as y:
        info = y.extract_info(url, download=False)
    entries = info.get("entries")
    if entries is None:
        entries = [info]
    user = username_from_url(url)
    out = []
    for e in entries:
        if not e or not e.get("id"):
            continue
        vid = str(e["id"])
        vurl = e.get("webpage_url") or e.get("url") or ""
        if not vurl.startswith("http"):
            vurl = f"https://www.tiktok.com/@{user}/video/{vid}"
        out.append({"id": vid, "url": vurl, "caption": e.get("description") or e.get("title") or "",
                    "dur": e.get("duration")})
    return out


def tiktok_download(url, folder):
    with _ydl({"outtmpl": os.path.join(folder, "%(id)s.%(ext)s"),
               "format": "best[ext=mp4][vcodec!=none][acodec!=none]/best[ext=mp4]/best",
               "noplaylist": True, "retries": 5}) as y:
        info = y.extract_info(url, download=True)
        req = info.get("requested_downloads") or []
        path = (req[0].get("filepath") if req else None) or y.prepare_filename(info)
    if not path or not os.path.isfile(path):
        raise RuntimeError("File not found after download")
    return path, info.get("description") or info.get("title") or ""


# ------------------------------------------------------------------ Facebook
class FBError(Exception):
    def __init__(self, msg, code=None):
        super().__init__(msg)
        self.code = code


# Facebook "stop" signals. When one of these comes back, the tool must NOT keep trying:
# repeated calls while blocked make Facebook's block longer and stricter.
BLOCK_WORDS = ("blocked", "limited access", "security reasons", "cannot call api",
               "temporarily", "restricted", "checkpoint")
RATE_CODES = {4, 17, 32, 341, 613, 80001}       # too many calls -> short pause
AUTH_CODES = {102, 190, 463, 467}                # login expired -> needs Reconnect Facebook
BLOCK_CODES = {200, 10, 368, 1609005}            # access blocked -> long pause


def fb_hold_kind(err):
    """Return 'block' / 'rate' / 'auth' if this Facebook error means we must stop, else None."""
    if not isinstance(err, FBError):
        return None
    code = err.code
    msg = str(err).lower()
    if code in AUTH_CODES:
        return "auth"
    if code in RATE_CODES:
        return "rate"
    if code in BLOCK_CODES or any(w in msg for w in BLOCK_WORDS):
        return "block"
    return None


def _fb(resp):
    try:
        data = resp.json()
    except ValueError:
        raise FBError(f"HTTP {resp.status_code}: {resp.text[:200]}")
    if isinstance(data, dict) and data.get("error"):
        e = data["error"]
        raise FBError(f"{e.get('message')} (code {e.get('code')})", e.get("code"))
    if resp.status_code >= 400:
        raise FBError(f"HTTP {resp.status_code}: {resp.text[:200]}")
    return data


def fb_list_pages(ver, user_token):
    url = f"https://graph.facebook.com/{ver}/me/accounts"
    params = {"fields": "id,name,access_token", "limit": 100, "access_token": user_token}
    pages = []
    while url:
        d = _fb(requests.get(url, params=params, timeout=TIMEOUT))
        pages.extend(d.get("data", []))
        url = (d.get("paging") or {}).get("next")
        params = None
    return pages


def fb_upload_reel(ver, page_id, token, path, desc):
    g = f"https://graph.facebook.com/{ver}"
    start = _fb(requests.post(f"{g}/{page_id}/video_reels",
                              data={"upload_phase": "start", "access_token": token}, timeout=TIMEOUT))
    vid = start["video_id"]
    up_url = start.get("upload_url") or f"https://rupload.facebook.com/video-upload/{ver}/{vid}"
    with open(path, "rb") as f:
        _fb(requests.post(up_url, headers={"Authorization": f"OAuth {token}", "offset": "0",
                                           "file_size": str(os.path.getsize(path))},
                          data=f, timeout=UPLOAD_TIMEOUT))
    _fb(requests.post(f"{g}/{page_id}/video_reels", data={
        "upload_phase": "finish", "video_id": vid, "video_state": "PUBLISHED",
        "description": desc, "access_token": token}, timeout=TIMEOUT))
    return vid


def fb_upload_video(ver, page_id, token, path, desc):
    with open(path, "rb") as f:
        data = _fb(requests.post(f"https://graph-video.facebook.com/{ver}/{page_id}/videos",
                                 data={"description": desc, "access_token": token},
                                 files={"source": (os.path.basename(path), f, "video/mp4")},
                                 timeout=UPLOAD_TIMEOUT))
    return data.get("id") or data.get("post_id")


def fb_upload(ver, page_id, token, path, desc, mode):
    if mode == "video":
        return fb_upload_video(ver, page_id, token, path, desc), "video"
    try:
        return fb_upload_reel(ver, page_id, token, path, desc), "reel"
    except FBError as e:
        if fb_hold_kind(e):   # blocked / rate limited / logged out: don't make a second call
            raise
        return fb_upload_video(ver, page_id, token, path, desc), "video (reel failed)"


# ------------------------------------------------------------------ Make.com (no developer app needed)
MAKE_LIMIT = int(4.8 * 1024 * 1024)   # Make free plan file limit is 5 MB


def gh_token():
    """GitHub Actions token: from env, or from the credential that actions/checkout saved in git config."""
    tok = os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN")
    if tok:
        return tok
    import subprocess
    try:
        out = subprocess.run(["git", "config", "--get-all", "http.https://github.com/.extraheader"],
                             cwd=ROOT, capture_output=True, text=True).stdout
        for line in out.splitlines():
            if "basic" in line.lower():
                raw = base64.b64decode(line.split()[-1]).decode()
                return raw.split(":", 1)[1]
    except Exception:
        pass
    raise RuntimeError("GitHub token not available inside the workflow")


def gh_api(method, url, **kw):
    headers = kw.pop("headers", {})
    headers.update({"Authorization": f"Bearer {gh_token()}", "Accept": "application/vnd.github+json",
                    "X-GitHub-Api-Version": "2022-11-28"})
    r = requests.request(method, url, headers=headers, timeout=kw.pop("timeout", 120), **kw)
    if r.status_code >= 400 and r.status_code != 404:
        raise RuntimeError(f"GitHub {method} failed ({r.status_code}): {r.text[:200]}")
    return r


def media_release(repo):
    r = gh_api("GET", f"https://api.github.com/repos/{repo}/releases/tags/media")
    if r.status_code == 200:
        return r.json()
    r = gh_api("POST", f"https://api.github.com/repos/{repo}/releases",
               json={"tag_name": "media", "name": "media (temporary videos)", "prerelease": True,
                     "body": "Temporary video files for HAADIKHAN69. Deleted automatically after 2 days."})
    return r.json()


def cleanup_media(ctx):
    """Delete temporary videos older than 2 days."""
    repo = os.environ.get("GITHUB_REPOSITORY")
    if not repo or not ctx.make_hook:
        return
    try:
        rel = gh_api("GET", f"https://api.github.com/repos/{repo}/releases/tags/media")
        if rel.status_code != 200:
            return
        cutoff = datetime.datetime.now(datetime.timezone.utc) - datetime.timedelta(days=2)
        for a in rel.json().get("assets", []):
            created = datetime.datetime.fromisoformat(a["created_at"].replace("Z", "+00:00"))
            if created < cutoff:
                gh_api("DELETE", f"https://api.github.com/repos/{repo}/releases/assets/{a['id']}")
    except Exception as e:
        print("cleanup skipped:", e)


def shrink_video(path):
    """Make's free plan only accepts files up to 5 MB, so bigger videos are re-encoded smaller."""
    import shutil
    import subprocess
    if os.path.getsize(path) <= MAKE_LIMIT or not shutil.which("ffmpeg"):
        return path
    try:
        dur = float(subprocess.run(["ffprobe", "-v", "error", "-show_entries", "format=duration",
                                    "-of", "default=nw=1:nk=1", path], capture_output=True, text=True).stdout.strip())
    except ValueError:
        dur = 60.0
    out = path.rsplit(".", 1)[0] + "_small.mp4"
    factor = 0.92
    for _ in range(3):
        total_kbps = (MAKE_LIMIT * 8 / 1024) / max(dur, 1) * factor
        v_kbps = max(150, int(total_kbps - 64))
        subprocess.run(["ffmpeg", "-y", "-loglevel", "error", "-i", path,
                        "-vf", "scale='if(gt(ih,1280),-2,iw)':'if(gt(ih,1280),1280,ih)'",
                        "-c:v", "libx264", "-preset", "veryfast", "-b:v", f"{v_kbps}k",
                        "-maxrate", f"{int(v_kbps * 1.2)}k", "-bufsize", f"{v_kbps * 2}k",
                        "-c:a", "aac", "-b:a", "64k", "-movflags", "+faststart", out], check=True)
        if os.path.getsize(out) <= MAKE_LIMIT:
            return out
        factor *= 0.8
    return out


def make_upload(ctx, page_id, path, caption, vid):
    repo = os.environ.get("GITHUB_REPOSITORY")
    if not repo:
        raise RuntimeError("GITHUB_REPOSITORY not set (must run inside GitHub Actions)")
    if ctx.cfg.get("make_compress", True):
        path = shrink_video(path)
    rel = media_release(repo)
    name = f"{vid}_{int(datetime.datetime.now().timestamp())}.mp4"
    with open(path, "rb") as f:
        up = gh_api("POST", f"https://uploads.github.com/repos/{repo}/releases/{rel['id']}/assets",
                    params={"name": name}, headers={"Content-Type": "video/mp4"}, data=f, timeout=600)
    if up.status_code >= 400:
        raise RuntimeError(f"temporary video upload failed ({up.status_code})")
    video_url = up.json()["browser_download_url"]
    r = requests.post(ctx.make_hook, json={"page_id": str(page_id), "video_url": video_url, "caption": caption},
                      timeout=60)
    if r.status_code >= 400:
        raise RuntimeError(f"Make webhook error ({r.status_code}): {r.text[:150]}. Is the Make scenario ON?")
    return "make", "via Make"


# ------------------------------------------------------------------ phone notifications (Web Push)
# The iPhone home-screen app itself receives the notifications - no extra app needed.
def _b64u(b):
    return base64.urlsafe_b64encode(b).rstrip(b"=").decode()


def _b64u_dec(s):
    return base64.urlsafe_b64decode(s + "=" * (-len(s) % 4))


def _hmac(key, data):
    import hmac as _h
    return _h.new(key, data, hashlib.sha256).digest()


def webpush_encrypt(p256dh, auth, payload):
    """RFC 8291 (aes128gcm) message encryption."""
    from cryptography.hazmat.primitives.asymmetric import ec
    from cryptography.hazmat.primitives import serialization
    from cryptography.hazmat.primitives.ciphers.aead import AESGCM
    ua_pub = _b64u_dec(p256dh)
    auth_secret = _b64u_dec(auth)
    ua_key = ec.EllipticCurvePublicKey.from_encoded_point(ec.SECP256R1(), ua_pub)
    as_priv = ec.generate_private_key(ec.SECP256R1())
    as_pub = as_priv.public_key().public_bytes(serialization.Encoding.X962,
                                               serialization.PublicFormat.UncompressedPoint)
    shared = as_priv.exchange(ec.ECDH(), ua_key)
    ikm = _hmac(_hmac(auth_secret, shared), b"WebPush: info\x00" + ua_pub + as_pub + b"\x01")
    salt = os.urandom(16)
    prk = _hmac(salt, ikm)
    cek = _hmac(prk, b"Content-Encoding: aes128gcm\x00\x01")[:16]
    nonce = _hmac(prk, b"Content-Encoding: nonce\x00\x01")[:12]
    ct = AESGCM(cek).encrypt(nonce, payload + b"\x02", None)
    return salt + (4096).to_bytes(4, "big") + bytes([len(as_pub)]) + as_pub + ct


def vapid_header(endpoint, d_b64, pub_b64):
    from urllib.parse import urlparse
    from cryptography.hazmat.primitives.asymmetric import ec
    from cryptography.hazmat.primitives import hashes
    from cryptography.hazmat.primitives.asymmetric.utils import decode_dss_signature
    u = urlparse(endpoint)
    head = _b64u(json.dumps({"typ": "JWT", "alg": "ES256"}, separators=(",", ":")).encode())
    body = _b64u(json.dumps({"aud": f"{u.scheme}://{u.netloc}", "exp": int(time.time()) + 12 * 3600,
                             "sub": "mailto:autoposter@users.noreply.github.com"}, separators=(",", ":")).encode())
    key = ec.derive_private_key(int.from_bytes(_b64u_dec(d_b64), "big"), ec.SECP256R1())
    r, s_ = decode_dss_signature(key.sign(f"{head}.{body}".encode(), ec.ECDSA(hashes.SHA256())))
    sig = _b64u(r.to_bytes(32, "big") + s_.to_bytes(32, "big"))
    return f"vapid t={head}.{body}.{sig}, k={pub_b64}"


def send_push(ctx, title, body):
    if not ctx.push:
        return
    payload = json.dumps({"title": title, "body": body}, ensure_ascii=False).encode()[:3000]
    dead = set(ctx.state.get("push_dead", []))
    for sub in ctx.push.get("subs", []):
        ep = sub.get("endpoint", "")
        tag = hashlib.sha256(ep.encode()).hexdigest()[:12]
        if not ep or tag in dead:
            continue
        try:
            r = requests.post(ep, data=webpush_encrypt(sub["p256dh"], sub["auth"], payload), timeout=20, headers={
                "Authorization": vapid_header(ep, ctx.push["vapid_d"], ctx.cfg.get("push_pub", "")),
                "Content-Encoding": "aes128gcm", "Content-Type": "application/octet-stream",
                "TTL": "86400", "Urgency": "high"})
            if r.status_code in (404, 410):       # phone removed / app deleted
                ctx.state.setdefault("push_dead", []).append(tag)
            elif r.status_code >= 400:
                print("push failed:", r.status_code, r.text[:200])
        except Exception as e:
            print("push failed:", e)


def notify(ctx):
    """Send one phone notification (free ntfy app) at the end of the run, only if something happened."""
    if ctx.uploaded and ctx.cfg.get("notify_success", True):
        total = sum(ctx.uploaded.values())
        parts = ", ".join(f"{n} ({c})" for n, c in ctx.uploaded.items())
        ctx.notes.insert(0, ("default", f"✅ {total} video{'s' if total != 1 else ''} uploaded: {parts}"))
    if not ctx.notes:
        return
    high = any(p == "high" for p, _ in ctx.notes)
    body = "\n".join(m for _, m in ctx.notes)[:3500]
    send_push(ctx, "HAADIKHAN69" + (" ⚠️" if high else ""), body)
    if not ctx.ntfy_topic:
        return
    try:
        requests.post(f"https://ntfy.sh/{ctx.ntfy_topic}", data=body.encode("utf-8"), timeout=20,
                      headers={"Title": "HAADIKHAN69", "Priority": "high" if high else "default",
                               "Tags": "warning" if high else "white_check_mark"})
    except Exception as e:
        print("notification failed:", e)


def refresh_pages(ctx):
    """Ask Facebook for the Page list. Called at most once per run and only when an upload needs a
    Page that has no saved token. (Before: this ran every 30 minutes = 48 calls a day for nothing.)"""
    ctx.pages_refreshed = True
    try:
        found = fb_list_pages(ctx.cfg.get("graph_version") or "v23.0", ctx.user_token)
        for p in found:
            ctx.tokens[str(p["id"])] = p["access_token"]
        ctx.state["fb_pages"] = [{"id": str(p["id"]), "name": p.get("name", "")} for p in found]
    except Exception as e:
        kind = fb_hold_kind(e)
        if kind:
            ctx.set_hold(kind, e)
        else:
            ctx.state["fb_error"] = f"Facebook connection needs a refresh (tap Reconnect Facebook in the app): {str(e)[:150]}"


# ------------------------------------------------------------------ skip videos already on the Page
# The tool LOOKS at the videos: it takes 6 small "fingerprints" (frames) from every video already on the
# Page, and from each TikTok video right after downloading it. Same pictures + same length = same video.
# Captions are NOT used (creators often reuse the same caption and length).
FP_PATH = os.path.join(ROOT, "fp.json")
FP_POINTS = (0.1, 0.25, 0.4, 0.55, 0.7, 0.85)
FP_MAX_PER_PAGE = 300


def _run(cmd, timeout=60):
    import subprocess
    return subprocess.run(cmd, capture_output=True, timeout=timeout)


def media_duration(src):
    r = _run(["ffprobe", "-v", "error", "-show_entries", "format=duration", "-of", "csv=p=0", src], 60)
    try:
        return float(r.stdout.decode().strip())
    except ValueError:
        return None


def frame_hash(src, t):
    """64-bit difference hash of the frame at t seconds (reads only that part of a remote video)."""
    r = _run(["ffmpeg", "-v", "error", "-ss", f"{max(t, 0):.2f}", "-i", src, "-frames:v", "1",
              "-vf", "scale=9:8:flags=area,format=gray", "-f", "rawvideo", "-"], 60)
    px = r.stdout
    if len(px) < 72:
        return None
    h = 0
    for row in range(8):
        for col in range(8):
            h = (h << 1) | (px[row * 9 + col] > px[row * 9 + col + 1])
    return h


AUDIO_POINTS = (0.2, 0.5, 0.8)
AUDIO_SECS = 3.0
AUDIO_STEP = 400          # samples at 8 kHz = 50 ms per value


def audio_env(src, t):
    """Loudness curve of 3 seconds of sound (voice/music) starting at t - very different between videos."""
    r = _run(["ffmpeg", "-v", "error", "-ss", f"{max(t, 0):.2f}", "-t", str(AUDIO_SECS), "-i", src,
              "-vn", "-ac", "1", "-ar", "8000", "-f", "s16le", "-"], 60)
    raw = r.stdout
    n = len(raw) // 2
    if n < AUDIO_STEP * 20:
        return None
    import array
    a = array.array("h", raw[:n * 2])
    vals = []
    for i in range(0, n - AUDIO_STEP + 1, AUDIO_STEP):
        seg = a[i:i + AUDIO_STEP]
        vals.append((sum(x * x for x in seg) / AUDIO_STEP) ** 0.5)
    top = max(vals) or 1
    return "".join(format(min(255, int(v / top * 255)), "02x") for v in vals)


def video_fp(src):
    dur = media_duration(src)
    if not dur or dur < 1:
        return None
    hs = [frame_hash(src, dur * p) for p in FP_POINTS]
    if sum(h is not None for h in hs) < 4:
        return None
    au = [audio_env(src, max(0.0, dur * p - AUDIO_SECS / 2)) for p in AUDIO_POINTS]
    return (f"{dur:.1f}|" + ",".join("-" if h is None else format(h, "016x") for h in hs) + "|" +
            ",".join(x or "-" for x in au))


def _corr(x, y):
    n = min(len(x), len(y))
    if n < 10:
        return None
    x, y = x[:n], y[:n]
    mx, my = sum(x) / n, sum(y) / n
    vx = sum((a - mx) ** 2 for a in x)
    vy = sum((b - my) ** 2 for b in y)
    if vx < 1e-9 or vy < 1e-9:
        return None
    return sum((a - mx) * (b - my) for a, b in zip(x, y)) / (vx * vy) ** 0.5


def _audio_score(ea, eb):
    """Best correlation of two loudness curves, allowing up to 0.2 s shift."""
    a = [int(ea[i:i + 2], 16) for i in range(0, len(ea), 2)]
    b = [int(eb[i:i + 2], 16) for i in range(0, len(eb), 2)]
    if max(a) - min(a) < 25 or max(b) - min(b) < 25:      # silence / flat sound: can't tell
        return None
    best = None
    for lag in range(-4, 5):
        c = _corr(a[lag:], b) if lag >= 0 else _corr(a, b[-lag:])
        if c is not None and (best is None or c > best):
            best = c
    return best


def fp_same(a, b):
    """Same video = same length AND same pictures AND (if there is sound) the same sound."""
    try:
        pa, pb = a.split("|"), b.split("|")
        if abs(float(pa[0]) - float(pb[0])) > 2.5:
            return False
        bits = []
        for x, y in zip(pa[1].split(","), pb[1].split(",")):
            if x != "-" and y != "-":
                bits.append(bin(int(x, 16) ^ int(y, 16)).count("1"))
        if len(bits) < 5 or sum(d <= 6 for d in bits) < len(bits) - 1:
            return False
        has_a = len(pa) > 2 and any(x != "-" for x in pa[2].split(","))
        has_b = len(pb) > 2 and any(x != "-" for x in pb[2].split(","))
        if has_a != has_b:             # one has sound, the other not: different videos
            return False
        scores = []
        if has_a and has_b:
            for x, y in zip(pa[2].split(","), pb[2].split(",")):
                if x != "-" and y != "-":
                    sc = _audio_score(x, y)
                    if sc is not None:
                        scores.append(sc)
        if scores:
            return sum(scores) / len(scores) >= 0.9 and min(scores) >= 0.75
        return max(bits) <= 4          # no usable sound: pictures must match very closely
    except Exception:
        return False


def load_fp(ctx):
    if getattr(ctx, "fp", None) is None:
        ctx.fp = load_json(FP_PATH, {})
    return ctx.fp


def save_fp(ctx):
    if getattr(ctx, "fp", None) is not None and getattr(ctx, "fp_dirty", False):
        with open(FP_PATH, "w", encoding="utf-8") as f:
            json.dump(ctx.fp, f, separators=(",", ":"))


def fb_page_videos(ver, page_id, token, max_items):
    out, seen = [], set()
    for edge in ("videos", "video_reels"):
        url = f"https://graph.facebook.com/{ver}/{page_id}/{edge}"
        params = {"fields": "id,source,length", "limit": 100, "access_token": token}
        while url and len(out) < max_items:
            try:
                d = _fb(requests.get(url, params=params, timeout=TIMEOUT))
            except FBError as e:
                if fb_hold_kind(e) or edge == "videos":
                    raise
                break
            for v in d.get("data", []):
                if v.get("id") not in seen and v.get("source"):
                    seen.add(v["id"])
                    out.append(v)
            url = (d.get("paging") or {}).get("next")
            params = None
    return out[:max_items]


def build_page_index(ctx, acc, force=False, budget=8 * 60):
    """Fingerprint the videos already on the Page. Full scan once, then a small top-up every 3 days."""
    if acc.get("skip_existing", True) is False or ctx.hold():
        return
    page_id = str(acc.get("page_id") or "")
    token = ctx.tokens.get(page_id)
    if not page_id or not token:
        return
    left = 12 * 60 - (time.monotonic() - ctx.started)    # at most ~12 min of looking per run, all Pages together
    if left < 30 and not force:
        return
    budget = min(budget, max(left, 30))
    idx = load_fp(ctx).setdefault(page_id, {"v": {}, "complete": False, "checked": None})
    if idx["complete"] and not force and idx.get("checked"):
        try:
            last = datetime.datetime.strptime(idx["checked"], "%Y-%m-%d %H:%M").replace(tzinfo=ctx.tz)
            if (ctx.now - last).days < 3:
                return
        except ValueError:
            pass
    try:
        listed = fb_page_videos(ctx.cfg.get("graph_version") or "v23.0", page_id, token,
                                FP_MAX_PER_PAGE if (force or not idx["complete"]) else 100)
    except Exception as e:
        kind = fb_hold_kind(e)
        if kind:
            ctx.set_hold(kind, e)
        else:
            ctx.log(f"could not read the Page's videos - {str(e)[:150]}", "error", acc)
        return
    todo = [v for v in listed if v["id"] not in idx["v"]]
    from concurrent.futures import ThreadPoolExecutor
    t0, done = time.monotonic(), 0
    with ThreadPoolExecutor(6) as pool:
        for i in range(0, len(todo), 6):
            if time.monotonic() - t0 > budget:
                break
            batch = todo[i:i + 6]
            for v, fp in zip(batch, pool.map(lambda v: video_fp(v["source"]), batch)):
                idx["v"][v["id"]] = fp or ""      # "" = could not read; don't try again
                done += 1
    complete = done >= len(todo)
    if complete:
        idx["complete"] = True
        idx["checked"] = ctx.ts()
    ctx.fp_dirty = True
    ctx.log(f"looked at {done} video(s) already on the Page" + ("" if complete else
            f" ({len(todo) - done} left, continuing next run)") +
            f" - {sum(1 for x in idx['v'].values() if x)} known", "info", acc)


def already_on_page(ctx, acc, path):
    """Return (True, fp) if the downloaded TikTok video is already on this Page."""
    if acc.get("skip_existing", True) is False:
        return False, None
    fp = video_fp(path)
    if not fp:
        return False, None
    idx = load_fp(ctx).get(str(acc.get("page_id") or ""), {}).get("v", {})
    return any(x and fp_same(fp, x) for x in idx.values()), fp


# ------------------------------------------------------------------ core
def scan(ctx, acc):
    st = ctx.acc_state(acc)
    ctx.scanned.add(acc["id"])
    first = not st["first_done"]
    limit = int(ctx.cfg.get("scan_limit") or 30)
    if first and acc.get("import_old", True):
        limit = max(limit, 200)
    try:
        items = tiktok_list(normalize_url(acc["tiktok"]), limit)
    except Exception as e:
        ctx.log(f"TikTok check failed - {e}", "error", acc)
        st["last_checked"] = ctx.ts()
        st["scan_fail"] = int(st.get("scan_fail") or 0) + 1
        if st["scan_fail"] == 3:   # tell the user once, not every hour
            ctx.notes.append(("high", f"⚠️ TikTok check for @{acc['username']} failed 3 times in a row - "
                                      f"no new videos are coming in. Is the account link right / public? ({str(e)[:100]})"))
        return 0
    if int(st.get("scan_fail") or 0) >= 3:
        ctx.notes.append(("default", f"✅ TikTok check for @{acc['username']} is working again"))
    st["scan_fail"] = 0
    seen = set(st["seen"])
    new = 0
    for it in reversed(items):  # purani pehle
        if it["id"] in seen:
            continue
        seen.add(it["id"])
        st["seen"].append(it["id"])
        status = "skipped" if (first and not acc.get("import_old", True)) else "new"
        st["videos"].append({"id": it["id"], "url": it["url"], "caption": it["caption"][:300],
                             "dur": it.get("dur"), "status": status, "attempts": 0, "found": ctx.ts()})
        new += status == "new"
    st["first_done"] = True
    st["last_checked"] = ctx.ts()
    if first and not acc.get("import_old", True):
        ctx.log(f"first check: skipped {len(items)} old videos, only new ones will be uploaded", "info", acc)
    else:
        ctx.log(f"check done: {new} new videos added to queue", "info", acc)
    return new


def process(ctx, acc, video):
    page_id = str(acc.get("page_id") or "")
    if not page_id:
        ctx.log("no Facebook Page selected for this account (Edit the account and choose a Page)", "error", acc)
        return None
    if ctx.hold():
        h = ctx.state["fb_hold"]
        ctx.log(f"skipped - Facebook is paused until {h.get('until') if h.get('kind') != 'auth' else 'you Reconnect Facebook'}",
                "info", acc)
        return None
    token = ctx.tokens.get(page_id)
    if not token and ctx.user_token and not ctx.pages_refreshed:
        refresh_pages(ctx)          # brand-new Page: look it up once (only when actually needed)
        token = ctx.tokens.get(page_id)
    if not token and not ctx.make_hook:
        ctx.log("Facebook is not connected. In the app go to Pages and connect via Make.", "error", acc)
        return None
    if video["id"] in ctx.posted and not ctx.manual:
        video.update(status="skipped", error="Already posted on another Page (duplicate protection)")
        ctx.log(f"video {video['id'][-6:]} skipped - already posted on another Page", "info", acc)
        return "dup"
    max_attempts = int(ctx.cfg.get("max_attempts") or 3)
    ver = ctx.cfg.get("graph_version") or "v23.0"
    idx = load_fp(ctx).get(page_id)
    if acc.get("skip_existing", True) is not False and token and not (idx and idx.get("complete")):
        build_page_index(ctx, acc, budget=5 * 60)   # make sure we know the Page's videos first
    with tempfile.TemporaryDirectory() as tmp:
        try:
            path, cap = tiktok_download(video["url"], tmp)
            on_page, fp = already_on_page(ctx, acc, path)
            if on_page and not ctx.manual:
                video.update(status="skipped", error="Already on the Facebook Page (same video found)")
                ctx.log(f"video {video['id'][-6:]} skipped - the same video is already on the Page", "info", acc)
                return "dup"
            cap = cap or video.get("caption") or ""
            video["caption"] = cap[:300]
            if token:
                post_id, kind = fb_upload(ver, page_id, token, path, build_caption(cap, acc), acc.get("mode", "reel"))
            else:
                post_id, kind = make_upload(ctx, page_id, path, build_caption(cap, acc), video["id"])
            video.update(status="uploaded", fb=str(post_id), uploaded=ctx.ts(), error="")
            ctx.state.pop("fb_error", None)
            page_name = next((p["name"] for p in ctx.cfg.get("pages", []) if str(p["id"]) == page_id), page_id)
            ctx.log(f"video {video['id'][-6:]} -> {page_name} uploaded ({kind})", "success", acc)
            ctx.posted.add(video["id"])
            if fp:
                load_fp(ctx).setdefault(page_id, {"v": {}, "complete": False, "checked": None})["v"][f"tt{video['id']}"] = fp
                ctx.fp_dirty = True
            ctx.state.setdefault("posted_ids", []).append(video["id"])
            del ctx.state["posted_ids"][:-20000]
            ctx.uploaded[page_name] = ctx.uploaded.get(page_name, 0) + 1
            return True
        except Exception as e:
            kind = fb_hold_kind(e)
            if kind:
                # Facebook said stop. The video is fine - keep it in the queue without using up a try.
                video["status"] = "new"
                video["error"] = ""
                ctx.set_hold(kind, e)
                return None
            video["attempts"] = int(video.get("attempts") or 0) + 1
            video["status"] = "retry" if video["attempts"] < max_attempts else "failed"
            video["error"] = str(e)[:300]
            ctx.log(f"video {video['id'][-6:]} fail ({video['attempts']}/{max_attempts}) - {e}", "error", acc)
            if video["status"] == "failed":
                ctx.notes.append(("high", f"❌ @{acc['username']}: video {video['id'][-6:]} failed - {str(e)[:120]}"))
            return False


def post_next(ctx, acc, count):
    st = ctx.acc_state(acc)
    done = tries = 0
    while done < count and tries < count + 3:
        video = next((v for v in st["videos"] if v["status"] in ("new", "retry")), None)
        if not video:
            if acc["id"] not in ctx.scanned and scan(ctx, acc) > 0:
                continue
            ctx.log("no new videos in queue", "info", acc)
            break
        if done and not ctx.manual:
            time.sleep(random.randint(40, 120))   # small human-like gap between videos on the same Page
        ok = process(ctx, acc, video)
        if ok == "dup":     # duplicate skipped, take the next video (doesn't use up a try)
            continue
        tries += 1
        if ok is None:      # setup problem / Facebook paused: don't retry this run
            break
        if ok:
            done += 1
    return done


def trim(st):
    keep_open = [v for v in st["videos"] if v["status"] in ("new", "retry")]
    others = [v for v in st["videos"] if v["status"] not in ("new", "retry")][-200:]
    order = {id(v): i for i, v in enumerate(st["videos"])}
    st["videos"] = sorted(keep_open + others, key=lambda v: order[id(v)])
    st["seen"] = st["seen"][-5000:]
    for day in sorted(st["slots"])[:-3]:
        del st["slots"][day]


def auto(ctx, acc):
    st = ctx.acc_state(acc)
    today = ctx.now.date().isoformat()
    hhmm = ctx.now.strftime("%H:%M")
    slots = parse_times(acc.get("times"))
    done = st["slots"].setdefault(today, [])
    new_account = st["last_checked"] is None

    # TikTok check (har ghante, ya settings ke mutabiq)
    every = int(ctx.cfg.get("check_minutes") or 60)
    due = True
    if st["last_checked"]:
        try:
            last = datetime.datetime.strptime(st["last_checked"], "%Y-%m-%d %H:%M").replace(tzinfo=ctx.tz)
            due = (ctx.now - last).total_seconds() >= (every - 5) * 60
        except ValueError:
            pass
    if due:
        scan(ctx, acc)
    build_page_index(ctx, acc)

    passed = [s for s in slots if s <= hhmm]
    if new_account:  # naya account: aaj ke guzre slots par ek dum upload na karo
        done.extend(s for s in passed if s not in done)
        return []
    pending = [s for s in passed if s not in done]
    if pending and ctx.cfg.get("paused"):
        done.extend(pending)
        ctx.log(f"{pending[-1]} slot skipped - all uploads are paused (Home → Resume all)", "info", acc)
        return []
    if pending and ctx.hold():
        done.extend(pending)
        ctx.log(f"{pending[-1]} slot skipped - Facebook is paused, videos stay in the queue for the next slot", "info", acc)
        return []
    return pending


RUN_BUDGET = 40 * 60   # stop starting new Pages after 40 min; the rest continue in the next run


def upload_round(ctx, due):
    """Upload Page by Page with a random 3-6 minute gap between Pages, so 30 Pages don't all post
    in the same minute (that looks like a bot to Facebook)."""
    gmin = max(1, int(ctx.cfg.get("gap_min") or 3))
    gmax = max(gmin, int(ctx.cfg.get("gap_max") or 6))
    first = True
    for i, (acc, pending) in enumerate(due):
        st = ctx.acc_state(acc)
        done = st["slots"].setdefault(ctx.now.date().isoformat(), [])
        if ctx.hold():
            done.extend(pending)
            continue
        if not first:
            gap = random.randint(gmin * 60, gmax * 60)
            if time.monotonic() - ctx.started + gap > RUN_BUDGET:
                left = len(due) - i
                ctx.log(f"{left} Page(s) left - they will upload in the next run (keeps the gaps safe)", "info")
                break
            time.sleep(gap)
        done.extend(pending)
        ctx.log(f"{pending[-1]} slot - starting upload", "info", acc)
        if post_next(ctx, acc, max(1, int(acc.get("per_slot") or 1))):
            first = False
        save_state(ctx.state)


def main():
    cfg = load_json(CONFIG_PATH, {})
    state = load_json(STATE_PATH, {})
    ctx = Ctx(cfg, state)
    action = (os.environ.get("ACTION") or "auto").strip() or "auto"
    target = (os.environ.get("ACCOUNT") or "").strip()
    video_arg = (os.environ.get("VIDEO") or "").strip()

    # "Tool stopped" alert: GitHub normally runs every ~30 min. A long gap means it was stopped / delayed.
    try:
        prev = datetime.datetime.strptime(state.get("last_run") or "", "%Y-%m-%d %H:%M").replace(tzinfo=ctx.tz)
        gap_h = (ctx.now - prev).total_seconds() / 3600
        if gap_h >= 2:
            ctx.notes.append(("high", f"⚠️ GitHub did not run the tool for {gap_h:.0f} hours (last run {state['last_run'][5:]}). "
                                      "It is running again now. If this repeats, tell Claude."))
            ctx.log(f"tool did not run for {gap_h:.1f} hours", "error")
    except ValueError:
        pass

    accounts = []
    for a in cfg.get("accounts", []):
        a = dict(a)
        a["username"] = username_from_url(normalize_url(a.get("tiktok", "")))
        accounts.append(a)

    key = os.environ.get("APP_KEY", "")
    if cfg.get("tokens_enc"):
        try:
            ctx.tokens = {str(k): v for k, v in decrypt_tokens(cfg["tokens_enc"], key).items()}
        except Exception:
            ctx.log("Could not unlock Facebook tokens: GitHub Secret 'APP_KEY' must match the app password", "error")
    if cfg.get("make_enc"):
        try:
            ctx.make_hook = (decrypt_tokens(cfg["make_enc"], key) or {}).get("webhook", "")
        except Exception:
            ctx.log("Could not unlock the Make webhook: GitHub Secret 'APP_KEY' must match the app password", "error")
    if cfg.get("fb_user_enc"):
        # The user token is kept only for finding brand-new Pages. Facebook is NOT called here any more:
        # Page tokens saved by the app (Reconnect / Refresh my Pages) never expire, so normal runs make
        # zero Facebook calls and Facebook is only contacted at upload time.
        try:
            ctx.user_token = (decrypt_tokens(cfg["fb_user_enc"], key) or {}).get("user_token", "")
        except Exception:
            ctx.log("Could not unlock the Facebook login: GitHub Secret 'APP_KEY' must match the app password", "error")

    if cfg.get("push_enc"):
        try:
            ctx.push = decrypt_tokens(cfg["push_enc"], key) or None
        except Exception:
            pass
    if cfg.get("ntfy_enc"):
        try:
            ctx.ntfy_topic = (decrypt_tokens(cfg["ntfy_enc"], key) or {}).get("topic", "").strip()
        except Exception:
            pass

    # Undo the old caption-based check (it could skip different videos that only had the same caption)
    for st_ in state.get("accounts", {}).values():
        for v in st_.get("videos", []):
            if v.get("status") == "skipped" and v.get("error") == "Already on the Facebook Page":
                v.update(status="new", error="")
        st_.pop("dedupe_done", None)

    # Duplicate protection: every TikTok video id that is already on any Page
    ctx.posted = set(state.get("posted_ids", []))
    for st in state.get("accounts", {}).values():
        ctx.posted.update(v["id"] for v in st.get("videos", []) if v.get("status") == "uploaded")

    # Reconnect / Refresh my Pages in the app = a fresh start: clear the pause and old warnings
    conn = hashlib.sha256((cfg.get("fb_user_enc", "") + cfg.get("tokens_enc", "")).encode()).hexdigest()[:16]
    if state.get("fb_conn") != conn:
        if state.get("fb_conn") is not None and (state.get("fb_hold") or state.get("fb_error")):
            ctx.log("Facebook reconnected - pause and warning cleared", "success")
        state["fb_conn"] = conn
        state.pop("fb_hold", None)
        state.pop("fb_error", None)

    # Videos that failed only because Facebook was blocking go back into the queue (when not paused)
    if not ctx.hold():
        for st in state.get("accounts", {}).values():
            for v in st.get("videos", []):
                if v.get("status") in ("failed", "retry") and fb_hold_kind(FBError(v.get("error", ""))):
                    v.update(status="new", attempts=0, error="")
    if not ctx.tokens and not ctx.make_hook:
        ctx.log("Facebook is not connected yet (see the Pages tab in the app)", "error")

    try:
        if action == "auto":
            due = []
            for acc in accounts:
                if acc.get("enabled", True):
                    pending = auto(ctx, acc)
                    if pending:
                        due.append((acc, pending))
            upload_round(ctx, due)
        elif action == "notify_test":
            ctx.notes.append(("default", "🔔 Test - notifications are working! You will get a message here when videos upload, fail, or Facebook pauses."))
        else:
            ctx.manual = action in ("upload_video",)
            sel = [a for a in accounts if a["id"] == target] if target else accounts
            if not sel:
                ctx.log(f"account '{target}' not found", "error")
            for acc in sel:
                st = ctx.acc_state(acc)
                vid = next((v for v in st["videos"] if v["id"] == video_arg), None)
                if action == "scan":
                    scan(ctx, acc)
                elif action == "dedupe":
                    build_page_index(ctx, acc, force=True)
                elif action == "upload_now":
                    if st["last_checked"] is None:
                        scan(ctx, acc)
                    post_next(ctx, acc, 1)
                elif action == "upload_video" and vid:
                    process(ctx, acc, vid)
                elif action == "retry" and vid:
                    vid.update(status="new", attempts=0, error="")
                elif action == "skip" and vid:
                    vid["status"] = "skipped"
                elif action == "add_video":
                    m = re.search(r"/video/(\d+)", video_arg)
                    if not m:
                        ctx.log("invalid TikTok video link", "error", acc)
                    elif m.group(1) in st["seen"]:
                        ctx.log("this video is already in the list", "info", acc)
                    else:
                        st["seen"].append(m.group(1))
                        st["videos"].append({"id": m.group(1), "url": video_arg.split("?")[0], "caption": "",
                                             "status": "new", "attempts": 0, "found": ctx.ts()})
                        ctx.log("video added to queue", "info", acc)
    except Exception as e:
        ctx.log(f"Engine error: {e} | {traceback.format_exc()[-300:]}", "error")

    # purane / delete kiye gaye accounts ka data saaf
    ids = {a["id"] for a in accounts}
    for aid in list(state.get("accounts", {})):
        if aid not in ids:
            del state["accounts"][aid]
    for st in state.get("accounts", {}).values():
        trim(st)
    cleanup_media(ctx)
    notify(ctx)
    save_fp(ctx)
    state["last_run"] = ctx.ts()
    state["last_action"] = action
    save_state(state)


if __name__ == "__main__":
    main()
