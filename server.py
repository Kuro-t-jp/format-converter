#!/usr/bin/env python3
"""メディア形式変換アプリ（動画・音声・画像・PDF）。ローカルで動くWebアプリ。
依存: ffmpeg / ffprobe (Homebrew), Pillow, PyMuPDF(fitz)。HEIC読み込みとダイアログは macOS 標準機能を使用。
"""
import atexit
import json
import mimetypes
import os
import re
import shutil
import socket
import subprocess
import sys
import tempfile
import threading
import time
import urllib.request
import uuid
import webbrowser
import zipfile
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, quote, unquote, urlparse

APP_DIR = Path(__file__).resolve().parent
OUT_DIR = APP_DIR / "変換済み"
TMP_DIR = Path(tempfile.gettempdir()) / "format_converter"
HISTORY_FILE = APP_DIR / "history.json"
OUT_DIR.mkdir(exist_ok=True)
TMP_DIR.mkdir(exist_ok=True)
PORT = int(os.environ.get("FC_PORT", "8765"))

FFMPEG = shutil.which("ffmpeg") or "/opt/homebrew/bin/ffmpeg"
FFPROBE = shutil.which("ffprobe") or "/opt/homebrew/bin/ffprobe"

VIDEO_IN = {"mp4", "mov", "mkv", "avi", "webm", "flv", "wmv", "m4v", "mpg", "mpeg", "ts", "3gp", "mts", "m2ts", "ogv"}
AUDIO_IN = {"mp3", "wav", "m4a", "aac", "flac", "ogg", "opus", "wma", "aiff", "aif", "caf", "amr"}
IMAGE_IN = {"jpg", "jpeg", "png", "webp", "gif", "bmp", "tif", "tiff", "heic", "heif", "avif", "ico"}
PDF_IN = {"pdf"}

VIDEO_OUT = {"mp4", "mov", "mkv", "webm", "avi", "gif"}
AUDIO_OUT = {"mp3", "m4a", "wav", "flac", "opus", "aiff"}
IMAGE_OUT = {"jpg", "png", "webp", "gif", "bmp", "tiff", "ico", "pdf"}
FRAME_OUT = {"jpg", "png", "webp"}

CRF = {"high": 18, "mid": 23, "low": 28}
JPEG_Q = {"high": 95, "mid": 85, "low": 70}
FONT_CANDIDATES = [
    "/System/Library/Fonts/ヒラギノ角ゴシック W6.ttc",
    "/System/Library/Fonts/ヒラギノ角ゴシック W3.ttc",
    "/System/Library/Fonts/Hiragino Sans GB.ttc",
    "/System/Library/Fonts/Helvetica.ttc",
]

STAGE = {}      # 読み込み済みファイル id -> {path,name,kind,orig,info}
JOBS = {}
JOBS_LOCK = threading.Lock()
SLOTS = threading.Semaphore(2)
HIST_LOCK = threading.Lock()


# ---------------------------------------------------------------- 共通ユーティリティ
def kind_of(ext):
    for k, s in (("video", VIDEO_IN), ("audio", AUDIO_IN), ("image", IMAGE_IN), ("pdf", PDF_IN)):
        if ext in s:
            return k
    return None


def safe_stem(stem):
    return re.sub(r'[\\/:*?"<>|]', "_", stem) or "output"


def unique_path(folder, stem, ext=None):
    stem = safe_stem(stem)
    suffix = f".{ext}" if ext else ""
    p = Path(folder) / f"{stem}{suffix}"
    n = 2
    while p.exists():
        p = Path(folder) / f"{stem}_{n}{suffix}"
        n += 1
    return p


def parse_t(s):
    s = (s or "").strip()
    if not s:
        return None
    try:
        v = 0.0
        for part in s.split(":"):
            v = v * 60 + float(part)
        return v
    except ValueError:
        raise RuntimeError(f"時間の形式が正しくありません: {s}")


def probe(path, kind):
    """ファイル情報（表示用）。"""
    info = {"size": Path(path).stat().st_size}
    try:
        if kind == "pdf":
            import fitz
            with fitz.open(path) as d:
                info["pages"] = d.page_count
            return info
        if kind == "image" and Path(path).suffix.lower().lstrip(".") not in ("heic", "heif", "avif"):
            from PIL import Image
            with Image.open(path) as im:
                info["width"], info["height"] = im.size
            return info
        r = subprocess.run([FFPROBE, "-v", "error", "-print_format", "json", "-show_format",
                            "-show_streams", str(path)], capture_output=True, text=True, timeout=60)
        j = json.loads(r.stdout or "{}")
        info["duration"] = float(j.get("format", {}).get("duration") or 0)
        for s in j.get("streams", []):
            if s.get("codec_type") == "video" and "vcodec" not in info and s.get("disposition", {}).get("attached_pic") != 1:
                info.update(width=s.get("width"), height=s.get("height"), vcodec=s.get("codec_name"))
            elif s.get("codec_type") == "audio" and "acodec" not in info:
                info["acodec"] = s.get("codec_name")
        info["has_audio"] = "acodec" in info
    except Exception:
        pass
    return info


def stage_file(path, name, orig):
    ext = Path(name).suffix.lower().lstrip(".")
    kind = kind_of(ext)
    sid = uuid.uuid4().hex[:12]
    info = probe(path, kind) if kind else {"size": Path(path).stat().st_size}
    STAGE[sid] = {"path": str(path), "name": name, "kind": kind, "orig": orig, "info": info}
    return {"id": sid, "name": name, "kind": kind, "orig": orig, "info": info,
            "dir": str(Path(path).parent) if orig else None}


def osa_pick(kind):
    prompt = "変換するフォルダを選んでください" if kind == "folder" else "変換するファイルを選んでください"
    if kind == "folder":
        body = f'set f to choose folder with prompt "{prompt}"\nreturn POSIX path of f'
    else:
        body = (f'set fs to choose file with prompt "{prompt}" with multiple selections allowed\n'
                'set out to ""\nrepeat with f in fs\nset out to out & POSIX path of f & linefeed\nend repeat\nreturn out')
    r = subprocess.run(["osascript", "-e", "tell current application to activate", "-e", body],
                       capture_output=True, text=True)
    if r.returncode != 0:
        return []
    return [p.strip() for p in r.stdout.splitlines() if p.strip()]


def scan_folder(folder, recursive, accept):
    out = []
    folder = Path(folder)
    it = folder.rglob("*") if recursive else folder.glob("*")
    for p in sorted(it):
        if p.is_file() and not p.name.startswith(".") and p.suffix.lower().lstrip(".") in accept:
            if OUT_DIR in p.parents:
                continue
            out.append(p)
        if len(out) >= 500:
            break
    return out


def move_to_trash(path):
    subprocess.run(["osascript", "-e", f'tell application "Finder" to delete POSIX file "{path}"'],
                   capture_output=True)


# ---------------------------------------------------------------- 履歴
def history_load():
    try:
        return json.loads(HISTORY_FILE.read_text(encoding="utf-8"))
    except Exception:
        return []


def history_add(entry):
    with HIST_LOCK:
        h = history_load()
        h.insert(0, entry)
        HISTORY_FILE.write_text(json.dumps(h[:60], ensure_ascii=False), encoding="utf-8")


# ---------------------------------------------------------------- ffmpeg 組み立て
def size_plan(o, out_dur, is_audio):
    """目標サイズ(MB)から (映像ビットレートbps, 音声kbps文字列) を決める。"""
    br = o.get("bitrate", "192")
    try:
        mb = float(o.get("size_mb") or 0)
    except ValueError:
        mb = 0
    if mb <= 0 or out_dur <= 0:
        return None, br
    total = mb * 8 * 1024 * 1024 * 0.93 / out_dur  # bit/s
    if is_audio:
        return None, str(int(max(16, min(320, total / 1000))))
    ab = int(max(32, min(int(br), 128, total * 0.2 / 1000)))
    return int(max(50_000, total - ab * 1000)), str(ab)


def venc_args(target, o, vb):
    q = o.get("quality", "mid")
    br = o.get("bitrate", "192")
    if target == "webm":
        a = ["-c:v", "libvpx-vp9", "-row-mt", "1", "-deadline", "good", "-cpu-used", "4"]
        a += ["-b:v", str(vb)] if vb else ["-crf", str(CRF[q] + 7), "-b:v", "0"]
        return a + ["-c:a", "libopus", "-b:a", f"{br}k"]
    if target == "avi":
        a = ["-c:v", "mpeg4"]
        a += ["-b:v", str(vb)] if vb else ["-q:v", {"high": "2", "mid": "4", "low": "7"}[q]]
        return a + ["-c:a", "libmp3lame", "-b:a", f"{br}k"]
    a = ["-c:v", "libx264", "-preset", "medium", "-pix_fmt", "yuv420p"]
    a += ["-b:v", str(vb), "-maxrate", str(int(vb * 1.5)), "-bufsize", str(int(vb * 3))] if vb else ["-crf", str(CRF[q])]
    a += ["-c:a", "aac", "-b:a", f"{br}k"]
    if target in ("mp4", "mov"):
        a += ["-movflags", "+faststart"]
    return a


def aenc_args(target, br):
    return {
        "mp3": ["-c:a", "libmp3lame", "-b:a", f"{br}k"],
        "m4a": ["-c:a", "aac", "-b:a", f"{br}k", "-movflags", "+faststart"],
        "wav": ["-c:a", "pcm_s16le"],
        "aiff": ["-c:a", "pcm_s16be"],
        "flac": ["-c:a", "flac"],
        "opus": ["-c:a", "libopus", "-b:a", f"{br}k"],
    }[target]


def audio_filters(o, speed, is_audio_out):
    af = []
    if is_audio_out and o.get("silence"):
        af.append("silenceremove=start_periods=1:start_threshold=-50dB:"
                  "stop_periods=-1:stop_duration=0.7:stop_threshold=-50dB")
    if speed != 1:
        af.append(f"atempo={speed}")
    if o.get("loudnorm"):
        af.append("loudnorm=I=-16:TP=-1.5:LRA=11")
    return af


def meta_args(o):
    a = []
    for k in ("title", "artist", "album"):
        if o.get(k):
            a += ["-metadata", f"{k}={o[k]}"]
    return a


def staged_path(sid):
    s = STAGE.get(sid or "")
    return s["path"] if s else None


def base_cmd():
    return [FFMPEG, "-y", "-hide_banner", "-loglevel", "error", "-progress", "pipe:1", "-nostats"]


def run_ffmpeg(job, cmd, out_dur, base=0.0, span=1.0):
    errf = tempfile.TemporaryFile()
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=errf, text=True)
    job["proc"] = p
    for line in p.stdout:
        if line.startswith(("out_time_us=", "out_time_ms=")):
            try:
                t = int(line.split("=")[1]) / 1_000_000
                if out_dur > 0:
                    job["progress"] = base + span * min(0.99, t / out_dur)
            except ValueError:
                pass
    p.wait()
    errf.seek(0)
    err = errf.read().decode("utf-8", "replace").strip()
    errf.close()
    job.pop("proc", None)
    if job.get("cancelled"):
        raise RuntimeError("キャンセルしました")
    if p.returncode != 0:
        raise RuntimeError(err[-400:] or "ffmpegでエラーが発生しました")


def parse_srt(path):
    raw = Path(path).read_bytes()
    try:
        txt = raw.decode("utf-8-sig")
    except UnicodeDecodeError:
        txt = raw.decode("cp932", "replace")
    cues = []
    for blk in re.split(r"\n\s*\n", txt.replace("\r", "").strip()):
        lines = blk.split("\n")
        for i, l in enumerate(lines):
            m = re.match(r"(\d+):(\d+):(\d+)[,.](\d+)\s*-->\s*(\d+):(\d+):(\d+)[,.](\d+)", l.strip())
            if m:
                g = m.groups()
                a = int(g[0]) * 3600 + int(g[1]) * 60 + int(g[2]) + float("0." + g[3])
                b = int(g[4]) * 3600 + int(g[5]) * 60 + int(g[6]) + float("0." + g[7])
                text = re.sub(r"<[^>]+>", "", "\n".join(lines[i + 1:])).strip()
                if text:
                    cues.append((a, b, text))
                break
    return cues


def render_cue(text, width, path):
    from PIL import Image, ImageDraw, ImageFont
    fs = max(18, int(width / 36))
    font = None
    for f in FONT_CANDIDATES:
        if Path(f).exists():
            try:
                font = ImageFont.truetype(f, fs)
                break
            except Exception:
                pass
    font = font or ImageFont.load_default()
    lines = []
    for raw in text.split("\n"):
        cur = ""
        for ch in raw:
            if cur and font.getlength(cur + ch) > width * 0.92:
                lines.append(cur)
                cur = ch
            else:
                cur += ch
        lines.append(cur)
    lh = int(fs * 1.35)
    im = Image.new("RGBA", (width, lh * len(lines) + int(fs * 0.6)), (0, 0, 0, 0))
    d = ImageDraw.Draw(im)
    for i, l in enumerate(lines):
        d.text(((width - font.getlength(l)) / 2, fs * 0.3 + i * lh), l, font=font, fill="white",
               stroke_width=max(2, fs // 12), stroke_fill="black")
    im.save(path)


def convert_media(job, src, dst, kind, target, o, info, tmp):
    start = parse_t(o.get("ss")) or 0.0
    end = parse_t(o.get("to"))
    dur = info.get("duration") or 0
    if end is not None and dur and end > dur:
        end = dur
    eff = (end if end is not None else dur) - start if (end is not None or dur) else 0
    if (start or end is not None) and eff <= 0:
        raise RuntimeError("開始位置と終了位置の指定が正しくありません")
    speed = float(o.get("speed") or 1)
    out_dur = eff / speed if eff > 0 else 0
    is_audio_out = target in AUDIO_OUT
    if is_audio_out and not info.get("has_audio", kind == "audio"):
        raise RuntimeError("このファイルには音声トラックがありません")

    vb, abr = size_plan(o, out_dur, is_audio_out)
    o = dict(o, bitrate=abr)
    cmd = base_cmd()
    if start > 0:
        cmd += ["-ss", f"{start:.3f}"]
    if end is not None:
        cmd += ["-t", f"{eff:.3f}"]
    cmd += ["-i", src]
    af = audio_filters(o, speed, is_audio_out)

    if is_audio_out:
        cover = staged_path(o.get("cover"))
        use_cover = bool(cover) and target in ("mp3", "m4a")
        if use_cover:
            cmd += ["-i", cover]
        cmd += ["-map", "0:a:0"] + (["-map", "1:0"] if use_cover else []) + ["-vn"] * (not use_cover)
        if af:
            cmd += ["-af", ",".join(af)]
        cmd += aenc_args(target, abr)
        if use_cover:
            cmd += ["-c:v", "mjpeg", "-pix_fmt", "yuvj420p", "-disposition:v:0", "attached_pic"]
            if target == "mp3":
                cmd += ["-id3v2_version", "3"]
        cmd += meta_args(o)
    else:
        h = o.get("height", "")
        h = h if h.isdigit() else ""
        scale = f"scale=-2:{h}" if h else "scale=trunc(iw/2)*2:trunc(ih/2)*2"
        vf = ([f"setpts=PTS/{speed}"] if speed != 1 else [])
        sub = staged_path(o.get("sub"))
        submode = o.get("submode", "soft")
        burn_cues = []
        if target == "gif":
            vf += ["fps=12", f"scale=-1:{h}:flags=lanczos" if h else "scale=480:-1:flags=lanczos"]
            cmd += ["-an", "-vf", ",".join(vf) + ",split[a][b];[a]palettegen[p];[b][p]paletteuse", "-loop", "0"]
        else:
            vf.append(scale)
            if sub and submode == "burn":
                cues = parse_srt(sub)
                if not cues:
                    raise RuntimeError("字幕ファイル(.srt)を読み取れませんでした")
                if len(cues) > 120:
                    raise RuntimeError(f"焼き込みは字幕120個までです（{len(cues)}個）。「埋め込み」を使ってください")
                vw, vh = info.get("width") or 1280, info.get("height") or 720
                tw = (round(vw * int(h) / vh / 2) * 2) if h else (vw // 2) * 2
                th = int(h) if h else (vh // 2) * 2
                for i, (a, b, text) in enumerate(cues):
                    png = TMP_DIR / f"{uuid.uuid4().hex}.png"
                    tmp.append(png)
                    render_cue(text, tw, png)
                    burn_cues.append(((a - start) / speed, (b - start) / speed, png))
                burn_cues = [c for c in burn_cues if c[1] > 0]
                for _, _, png in burn_cues:
                    cmd += ["-i", str(png)]
                chain = f"[0:v]{','.join(vf)}[b0]"
                for i, (a, b, _) in enumerate(burn_cues):
                    chain += (f";[b{i}][{i + 1}:v]overlay=x=0:y=H-h-{int(th * 0.06)}:"
                              f"enable='between(t,{max(a, 0):.3f},{b:.3f})'[b{i + 1}]")
                cmd += ["-filter_complex", chain, "-map", f"[b{len(burn_cues)}]", "-map", "0:a:0?"]
            else:
                if sub:
                    if target not in ("mp4", "mov", "mkv"):
                        raise RuntimeError("この形式には字幕を埋め込めません（MP4 / MOV / MKV を選ぶか、焼き込みにしてください）")
                    if start > 0:
                        cmd += ["-ss", f"{start:.3f}"]
                    cmd += ["-i", sub]  # 入力はすべて出力オプションより前に置く
                cmd += ["-vf", ",".join(vf)]
                if sub:
                    cmd += ["-map", "0:v:0", "-map", "0:a:0?", "-map", "1:0",
                            "-c:s", "srt" if target == "mkv" else "mov_text"]
            if af:
                cmd += ["-af", ",".join(af)]
            cmd += venc_args(target, o, vb)
    cmd.append(str(dst))
    run_ffmpeg(job, cmd, out_dur)


def convert_image(src, dst, target, o, tmp):
    from PIL import Image, ImageOps

    src = Path(src)
    work = src
    if src.suffix.lower() in (".heic", ".heif"):
        work = TMP_DIR / f"{uuid.uuid4().hex}.png"
        tmp.append(work)
        r = subprocess.run(["sips", "-s", "format", "png", str(src), "--out", str(work)],
                           capture_output=True, text=True)
        if r.returncode != 0:
            raise RuntimeError("HEICの読み込みに失敗しました: " + r.stderr.strip())

    def open_img(p):
        im = Image.open(p)
        im.load()
        return im

    try:
        im = open_img(work)
    except Exception:
        alt = TMP_DIR / f"{uuid.uuid4().hex}.png"
        tmp.append(alt)
        r = subprocess.run([FFMPEG, "-y", "-loglevel", "error", "-i", str(work), "-frames:v", "1", str(alt)],
                           capture_output=True, text=True)
        if r.returncode != 0:
            raise RuntimeError("画像を読み込めませんでした: " + r.stderr.strip()[-300:])
        im = open_img(alt)

    im = ImageOps.exif_transpose(im)
    exif = None
    if not o.get("strip_exif"):
        try:
            ex = im.getexif()
            if ex:
                ex.pop(274, None)
                exif = ex.tobytes()
        except Exception:
            exif = None

    mode, val = o.get("resize_mode", "width"), o.get("resize_val", "")
    try:
        v = float(val)
    except ValueError:
        v = 0
    if v > 0:
        w0, h0 = im.size
        k = {"width": v / w0, "height": v / h0, "long": v / max(w0, h0), "percent": v / 100}.get(mode, 1)
        if mode != "percent":
            k = min(k, 1)
        if abs(k - 1) > 1e-6:
            im = im.resize((max(1, round(w0 * k)), max(1, round(h0 * k))), Image.LANCZOS)

    q = JPEG_Q[o.get("quality", "mid")]
    has_alpha = im.mode in ("RGBA", "LA") or (im.mode == "P" and "transparency" in im.info)
    if target in ("jpg", "bmp", "pdf"):
        if has_alpha:
            im = im.convert("RGBA")
            bg = Image.new("RGB", im.size, (255, 255, 255))
            bg.paste(im, mask=im.getchannel("A"))
            im = bg
        else:
            im = im.convert("RGB")
    kw = {"exif": exif} if exif else {}
    if target == "jpg":
        im.save(dst, "JPEG", quality=q, optimize=True, **kw)
    elif target == "png":
        im.save(dst, "PNG", optimize=True, **kw)
    elif target == "webp":
        im.save(dst, "WEBP", quality=q, **kw)
    elif target == "gif":
        im.convert("RGBA" if has_alpha else "RGB").save(dst, "GIF")
    elif target == "bmp":
        im.save(dst, "BMP")
    elif target == "tiff":
        im.save(dst, "TIFF", compression="tiff_lzw")
    elif target == "ico":
        s = min(256, max(im.size))
        im.convert("RGBA").save(dst, "ICO", sizes=[(s, s)])
    elif target == "pdf":
        im.save(dst, "PDF", resolution=150.0)


def extract_frames(job, src, outdir, stem, target, o, info):
    outdir.mkdir(parents=True, exist_ok=True)
    mode, val = o.get("frames_mode", "interval"), o.get("frames_val", "10")
    h = o.get("height", "")
    scale = [f"scale=-2:{h}"] if h.isdigit() else []
    qual = ["-q:v", "2"] if target == "jpg" else (["-quality", "90"] if target == "webp" else [])
    if mode == "times":
        times = [parse_t(x) for x in re.split(r"[,\s、]+", val.strip()) if x]
        if not times:
            raise RuntimeError("時刻を入力してください（例: 5, 30, 1:20）")
        for i, t in enumerate(times):
            cmd = [FFMPEG, "-y", "-hide_banner", "-loglevel", "error", "-ss", f"{t:.3f}", "-i", src,
                   "-frames:v", "1"] + (["-vf", ",".join(scale)] if scale else []) + qual + \
                  [str(outdir / f"{stem}_{i + 1:03d}_{t:g}s.{target}")]
            run_ffmpeg(job, cmd, 0)
            job["progress"] = (i + 1) / len(times)
    else:
        try:
            step = float(val)
            assert step > 0
        except Exception:
            raise RuntimeError("間隔は正の数（秒）で入力してください")
        start = parse_t(o.get("ss")) or 0.0
        end = parse_t(o.get("to"))
        dur = info.get("duration") or 0
        eff = (end if end is not None else dur) - start
        cmd = base_cmd()
        if start > 0:
            cmd += ["-ss", f"{start:.3f}"]
        if end is not None:
            cmd += ["-t", f"{eff:.3f}"]
        cmd += ["-i", src, "-vf", ",".join([f"fps=1/{step}"] + scale)] + qual + \
               [str(outdir / f"{stem}_%04d.{target}")]
        run_ffmpeg(job, cmd, eff)
    if not any(outdir.iterdir()):
        raise RuntimeError("静止画を書き出せませんでした（時刻が動画の長さを超えている可能性があります）")


def pdf_to_images(job, src, outdir, stem, target, o):
    import fitz
    from PIL import Image
    outdir.mkdir(parents=True, exist_ok=True)
    dpi = int(o.get("dpi") or 150)
    q = JPEG_Q[o.get("quality", "mid")]
    with fitz.open(src) as d:
        n = d.page_count
        for i, page in enumerate(d):
            if job.get("cancelled"):
                raise RuntimeError("キャンセルしました")
            pix = page.get_pixmap(dpi=dpi, alpha=False)
            out = outdir / f"{stem}_{i + 1:03d}.{target}"
            if target == "png":
                pix.save(out)
            else:
                im = Image.frombytes("RGB", (pix.width, pix.height), pix.samples)
                im.save(out, "JPEG" if target == "jpg" else "WEBP", quality=q)
            job["progress"] = (i + 1) / n


def merge_media(job, srcs, dst, target, o):
    infos = [probe(s, "video") for s in srcs]
    total = sum(i.get("duration") or 0 for i in infos)
    is_audio_out = target in AUDIO_OUT
    vb, abr = size_plan(o, total, is_audio_out)
    o = dict(o, bitrate=abr)
    cmd = base_cmd()
    for s in srcs:
        cmd += ["-i", s]
    chain, labels = [], ""
    if is_audio_out:
        for i, inf in enumerate(infos):
            if not inf.get("has_audio"):
                raise RuntimeError("音声のないファイルが含まれています")
            chain.append(f"[{i}:a]aresample=44100,aformat=channel_layouts=stereo[a{i}]")
            labels += f"[a{i}]"
        tail = ",".join(["concat=n=%d:v=0:a=1" % len(srcs)] + audio_filters(o, 1, False))
        chain.append(f"{labels}{tail}[a]")
        cmd += ["-filter_complex", ";".join(chain), "-map", "[a]"] + aenc_args(target, abr) + meta_args(o)
    else:
        first = infos[0]
        h = o.get("height", "")
        H = int(h) if h.isdigit() else (first.get("height") or 720)
        W = round((first.get("width") or 1280) * H / (first.get("height") or 720) / 2) * 2
        H = H // 2 * 2
        extra = len(srcs)
        for i, inf in enumerate(infos):
            chain.append(f"[{i}:v]scale={W}:{H}:force_original_aspect_ratio=decrease,"
                         f"pad={W}:{H}:(ow-iw)/2:(oh-ih)/2,setsar=1,fps=30,format=yuv420p[v{i}]")
            if inf.get("has_audio"):
                chain.append(f"[{i}:a]aresample=44100,aformat=channel_layouts=stereo[a{i}]")
            else:  # 音声のない動画は無音で補う
                cmd += ["-f", "lavfi", "-t", f"{inf.get('duration') or 1:.3f}", "-i", "anullsrc=r=44100:cl=stereo"]
                chain.append(f"[{extra}:a]aformat=channel_layouts=stereo[a{i}]")
                extra += 1
            labels += f"[v{i}][a{i}]"
        chain.append(f"{labels}concat=n={len(srcs)}:v=1:a=1[v][a]")
        cmd += ["-filter_complex", ";".join(chain), "-map", "[v]", "-map", "[a]"]
        if o.get("loudnorm"):
            cmd += ["-af", "loudnorm=I=-16:TP=-1.5:LRA=11"]
        cmd += venc_args(target, o, vb)
    cmd.append(str(dst))
    run_ffmpeg(job, cmd, total)


def images_to_pdf(srcs, dst, tmp):
    from PIL import Image, ImageOps
    pages = []
    for s in srcs:
        s = Path(s)
        work = s
        if s.suffix.lower() in (".heic", ".heif"):
            work = TMP_DIR / f"{uuid.uuid4().hex}.png"
            tmp.append(work)
            subprocess.run(["sips", "-s", "format", "png", str(s), "--out", str(work)], capture_output=True)
        im = ImageOps.exif_transpose(Image.open(work))
        if im.mode in ("RGBA", "LA", "P"):
            im = im.convert("RGBA")
            bg = Image.new("RGB", im.size, (255, 255, 255))
            bg.paste(im, mask=im.getchannel("A"))
            im = bg
        pages.append(im.convert("RGB"))
    pages[0].save(dst, "PDF", save_all=True, append_images=pages[1:], resolution=150.0)


# ---------------------------------------------------------------- ジョブ実行
def run_job(job_id, req):
    job = JOBS[job_id]
    task, target, o = req["task"], req["target"], req.get("opts", {})
    ids = req.get("ids") or [req.get("id")]
    items = [STAGE[i] for i in ids]
    tmp = []
    produced = None
    with SLOTS:
        try:
            if job.get("cancelled"):
                raise RuntimeError("キャンセルしました")
            job["status"] = "running"
            first = items[0]
            beside = req.get("outdir") == "beside" and first["orig"]
            folder = Path(first["path"]).parent if beside else OUT_DIR
            stem = Path(first["name"]).stem
            if task == "convert":
                produced = unique_path(folder, stem, target)
                if first["kind"] == "image":
                    convert_image(first["path"], produced, target, o, tmp)
                else:
                    convert_media(job, first["path"], produced, first["kind"], target, o, first["info"], tmp)
            elif task == "frames":
                produced = unique_path(folder, stem + "_frames")
                extract_frames(job, first["path"], produced, safe_stem(stem), target, o, first["info"])
            elif task == "pdf2img":
                produced = unique_path(folder, stem + "_pages")
                pdf_to_images(job, first["path"], produced, safe_stem(stem), target, o)
            elif task == "merge":
                stem = stem + "_結合"
                produced = unique_path(folder, stem, target)
                if target == "pdf":
                    images_to_pdf([i["path"] for i in items], produced, tmp)
                else:
                    merge_media(job, [i["path"] for i in items], produced, target, o)
            if produced.is_dir():
                size = sum(f.stat().st_size for f in produced.iterdir())
            else:
                size = produced.stat().st_size
            job.update(status="done", progress=1.0, out_name=produced.name, out_path=str(produced), size=size)
            history_add({"time": time.strftime("%Y-%m-%d %H:%M"), "src": ", ".join(i["name"] for i in items)[:120],
                         "out_name": produced.name, "out_path": str(produced), "ui": req.get("ui", {})})
            if req.get("trash"):
                for it in items:
                    if it["orig"]:
                        move_to_trash(it["path"])
        except Exception as e:
            job.update(status="error", error=str(e) or e.__class__.__name__)
            if produced and produced.exists():
                shutil.rmtree(produced, ignore_errors=True) if produced.is_dir() else produced.unlink(missing_ok=True)
        finally:
            job.pop("proc", None)
            for f in tmp:
                Path(f).unlink(missing_ok=True)


def validate(req):
    task, target = req.get("task"), req.get("target")
    ids = req.get("ids") or [req.get("id")]
    if not ids or any(i not in STAGE for i in ids):
        return "ファイルが見つかりません。もう一度読み込んでください"
    kinds = [STAGE[i]["kind"] for i in ids]
    k = kinds[0]
    if task == "convert":
        ok = (k == "image" and target in IMAGE_OUT) or (k == "audio" and target in AUDIO_OUT) or \
             (k == "video" and (target in VIDEO_OUT or target in AUDIO_OUT))
    elif task == "frames":
        ok = k == "video" and target in FRAME_OUT
    elif task == "pdf2img":
        ok = k == "pdf" and target in FRAME_OUT
    elif task == "merge":
        if len(ids) < 2:
            return "結合するファイルを2つ以上選んでください"
        if all(x == "image" for x in kinds):
            ok = target == "pdf"
        elif all(x in ("video", "audio") for x in kinds):
            ok = target in AUDIO_OUT or (target in VIDEO_OUT and target != "gif" and all(x == "video" for x in kinds))
        else:
            ok = False
    else:
        ok = False
    return None if ok else "未対応の形式の組み合わせです"


# ---------------------------------------------------------------- HTTP
class Handler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"

    def log_message(self, *a):
        pass

    def allowed(self):
        host = (self.headers.get("Host") or "").split(":")[0]
        origin = self.headers.get("Origin")
        if host not in ("127.0.0.1", "localhost"):
            return False
        return not origin or urlparse(origin).hostname in ("127.0.0.1", "localhost")

    def send_json(self, obj, code=200):
        body = json.dumps(obj, ensure_ascii=False).encode()
        self.send_response(code)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def read_json(self):
        n = int(self.headers.get("Content-Length", 0))
        try:
            return json.loads(self.rfile.read(n) or b"{}")
        except Exception:
            return {}

    def serve_file(self, path, name=None, download=False):
        path = Path(path)
        size = path.stat().st_size
        rng = self.headers.get("Range")
        start, end, code = 0, size - 1, 200
        if rng:
            m = re.match(r"bytes=(\d*)-(\d*)", rng)
            if m:
                if m.group(1):
                    start = int(m.group(1))
                    end = int(m.group(2)) if m.group(2) else size - 1
                else:
                    start = max(0, size - int(m.group(2)))
                end = min(end, size - 1)
                code = 206
        ctype = mimetypes.guess_type(str(path))[0] or "application/octet-stream"
        self.send_response(code)
        self.send_header("Content-Type", "application/octet-stream" if download else ctype)
        self.send_header("Accept-Ranges", "bytes")
        self.send_header("Content-Length", str(end - start + 1))
        if code == 206:
            self.send_header("Content-Range", f"bytes {start}-{end}/{size}")
        if download:
            self.send_header("Content-Disposition", f"attachment; filename*=UTF-8''{quote(name or path.name)}")
        self.end_headers()
        try:
            with open(path, "rb") as f:
                f.seek(start)
                left = end - start + 1
                while left > 0:
                    chunk = f.read(min(1 << 20, left))
                    if not chunk:
                        break
                    self.wfile.write(chunk)
                    left -= len(chunk)
        except (BrokenPipeError, ConnectionResetError):
            pass

    def do_GET(self):
        if not self.allowed():
            return self.send_json({"error": "forbidden"}, 403)
        u = urlparse(self.path)
        tail = u.path.rsplit("/", 1)[-1]
        if u.path in ("/", "/index.html"):
            body = (APP_DIR / "index.html").read_bytes()
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
        elif u.path == "/api/ping":
            self.send_json({"app": "format_converter"})
        elif u.path == "/api/history":
            self.send_json(history_load()[:50])
        elif u.path.startswith("/api/job/"):
            job = JOBS.get(tail)
            if not job:
                return self.send_json({"error": "not found"}, 404)
            self.send_json({k: v for k, v in job.items() if k not in ("proc", "out_path")})
        elif u.path.startswith("/api/file/"):
            s = STAGE.get(tail)
            if not s:
                return self.send_json({"error": "not found"}, 404)
            self.serve_file(s["path"])
        elif u.path.startswith("/api/download/"):
            job = JOBS.get(tail)
            if not job or job.get("status") != "done":
                return self.send_json({"error": "not found"}, 404)
            p = Path(job["out_path"])
            if p.is_dir():
                z = TMP_DIR / f"{p.name}.zip"
                with zipfile.ZipFile(z, "w", zipfile.ZIP_STORED) as zf:
                    for f in sorted(p.iterdir()):
                        zf.write(f, f"{p.name}/{f.name}")
                self.serve_file(z, z.name, download=True)
                z.unlink(missing_ok=True)
            else:
                self.serve_file(p, p.name, download=True)
        else:
            self.send_json({"error": "not found"}, 404)

    def do_POST(self):
        if not self.allowed():
            return self.send_json({"error": "forbidden"}, 403)
        u = urlparse(self.path)
        tail = u.path.rsplit("/", 1)[-1]
        if u.path == "/api/stage":  # ブラウザからドロップされたファイルを受け取る
            q = {k: v[0] for k, v in parse_qs(u.query).items()}
            name = unquote(q.get("name", "file"))
            ext = Path(name).suffix.lower().lstrip(".")
            sid = uuid.uuid4().hex
            dst = TMP_DIR / f"{sid}.{ext or 'bin'}"
            left = int(self.headers.get("Content-Length", 0))
            with open(dst, "wb") as f:
                while left > 0:
                    chunk = self.rfile.read(min(1 << 20, left))
                    if not chunk:
                        break
                    f.write(chunk)
                    left -= len(chunk)
            self.send_json(stage_file(dst, name, False))
        elif u.path == "/api/pick":  # Finderで選択（元の場所を保持）
            req = self.read_json()
            accept = set(req.get("accept", []))
            picked = osa_pick("folder" if req.get("type") == "folder" else "file")
            paths = []
            for p in picked:
                if req.get("type") == "folder":
                    paths += scan_folder(p, bool(req.get("recursive")), accept)
                elif Path(p).suffix.lower().lstrip(".") in accept:
                    paths.append(Path(p))
            self.send_json({"items": [stage_file(p, p.name, True) for p in paths[:500]],
                            "cancelled": not picked})
        elif u.path == "/api/unstage":
            for i in self.read_json().get("ids", []):
                s = STAGE.pop(i, None)
                if s and not s["orig"]:
                    Path(s["path"]).unlink(missing_ok=True)
            self.send_json({"ok": True})
        elif u.path == "/api/convert":
            req = self.read_json()
            err = validate(req)
            if err:
                return self.send_json({"error": err}, 400)
            job_id = uuid.uuid4().hex[:12]
            JOBS[job_id] = {"status": "queued", "progress": 0.0}
            threading.Thread(target=run_job, args=(job_id, req), daemon=True).start()
            self.send_json({"job": job_id})
        elif u.path.startswith("/api/cancel/"):
            job = JOBS.get(tail)
            if job:
                job["cancelled"] = True
                if job.get("proc"):
                    job["proc"].terminate()
            self.send_json({"ok": True})
        elif u.path.startswith("/api/reveal/"):
            job = JOBS.get(tail)
            target = job.get("out_path") if job else None
            subprocess.Popen(["open", "-R", target] if target else ["open", str(OUT_DIR)])
            self.send_json({"ok": True})
        elif u.path == "/api/history_reveal":
            h = history_load()
            i = self.read_json().get("i", -1)
            if 0 <= i < len(h) and Path(h[i]["out_path"]).exists():
                subprocess.Popen(["open", "-R", h[i]["out_path"]])
            self.send_json({"ok": True})
        elif u.path == "/api/history/clear":
            HISTORY_FILE.write_text("[]")
            self.send_json({"ok": True})
        else:
            self.send_json({"error": "not found"}, 404)


def cleanup():
    for s in STAGE.values():
        if not s["orig"]:
            Path(s["path"]).unlink(missing_ok=True)


def existing_instance():
    try:
        with urllib.request.urlopen(f"http://127.0.0.1:{PORT}/api/ping", timeout=1) as r:
            return json.load(r).get("app") == "format_converter"
    except Exception:
        return False


def main():
    if not Path(FFMPEG).exists():
        sys.exit("ffmpeg が見つかりません。 `brew install ffmpeg` を実行してください。")
    url = f"http://127.0.0.1:{PORT}/"
    if existing_instance():  # すでに起動中ならブラウザを開くだけ
        if "--no-browser" not in sys.argv:
            webbrowser.open(url)
        return
    try:
        srv = ThreadingHTTPServer(("127.0.0.1", PORT), Handler)
    except OSError:
        sys.exit(f"ポート {PORT} を使用できません。")
    atexit.register(cleanup)
    print(f"形式変換アプリを起動しました: {url}\n出力先: {OUT_DIR}\n（終了するには Ctrl+C）", flush=True)
    if "--no-browser" not in sys.argv:
        threading.Timer(0.6, lambda: webbrowser.open(url)).start()
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()
