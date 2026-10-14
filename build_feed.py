"""
Rinse feeds: builds podcast RSS feeds from the rinse.fm schedule API.

One feed per channel (Kool, Rinse FM, France, SWU) plus one feed per artist
listed in config.json, matched across all channels.

Each episode's GUID is its file size, so a repost of the same recording under
a new link and a new date shows up as the same episode in the podcast app.

Run by GitHub Actions once a day. Standard library only.
"""

import collections
import json
import os
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from concurrent.futures import ThreadPoolExecutor
from zoneinfo import ZoneInfo
from datetime import datetime, timedelta, timezone
from email.utils import format_datetime
from xml.sax.saxutils import escape

ROOT = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(ROOT, "data")
DOCS = os.path.join(ROOT, "docs")
STATE_FILE = os.path.join(DATA, "episodes.json")
DATES_FILE = os.path.join(DATA, "fetched_dates.json")
REPORT_FILE = os.path.join(DATA, "channel_report.json")
META_FILE = os.path.join(DATA, "meta.json")
STATE_VERSION = 5
SAMPLE_FILE = os.path.join(DATA, "sample_entry.json")
ART = "?w=1400&h=1400&fit=crop"

API = "https://www.rinse.fm/api/query/v1/schedule/{}"
UA = ("Mozilla/5.0 (iPhone; CPU iPhone OS 17_0 like Mac OS X) AppleWebKit/605.1.15 "
      "(KHTML, like Gecko) Version/17.0 Mobile/15E148 Safari/604.1")

# Test hooks: point at local fixtures instead of the network
FIXTURE_DIR = os.environ.get("RINSE_FIXTURE")
FIXTURE_SIZES = os.environ.get("RINSE_FIXTURE_SIZES")


# ---------------------------------------------------------------- helpers

def log(*a):
    print(*a, flush=True)


def load_json(path, default):
    try:
        with open(path, encoding="utf-8") as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError):
        return default


def save_json(path, obj):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(obj, f, indent=1, ensure_ascii=False, sort_keys=True)
    os.replace(tmp, path)


def slugify(s):
    return re.sub(r"[^a-z0-9]+", "-", s.lower()).strip("-")


def norm(s):
    return " " + re.sub(r"[^a-z0-9]+", " ", (s or "").lower()).strip() + " "


def http(url, method="GET", headers=None, timeout=30):
    req = urllib.request.Request(url, method=method, headers={"User-Agent": UA, **(headers or {})})
    return urllib.request.urlopen(req, timeout=timeout)


# ---------------------------------------------------------------- schedule

def fetch_day(date_str):
    if FIXTURE_DIR:
        p = os.path.join(FIXTURE_DIR, date_str + ".json")
        return load_json(p, {}).get("entries", []) if os.path.exists(p) else []
    for attempt in range(3):
        try:
            with http(API.format(date_str)) as r:
                return (json.load(r) or {}).get("entries", []) or []
        except urllib.error.HTTPError as e:
            if e.code == 404:
                return []
            log(f"  {date_str}: HTTP {e.code}, retry {attempt + 1}")
        except Exception as e:
            log(f"  {date_str}: {e}, retry {attempt + 1}")
        time.sleep(2 * (attempt + 1))
    return None  # failed, do not mark as fetched


def walk(entry):
    """Yield the entry and every nested originalEpisode."""
    if not isinstance(entry, dict):
        return
    yield entry
    oe = entry.get("originalEpisode")
    if isinstance(oe, list):
        for o in oe:
            yield from walk(o)
    elif isinstance(oe, dict):
        yield from walk(oe)


def field_text(v):
    """Flatten a channel-ish field (str, dict, list) into searchable text."""
    if v is None:
        return ""
    if isinstance(v, str):
        return v
    if isinstance(v, dict):
        return " ".join(str(v.get(k, "")) for k in ("slug", "name", "title", "id"))
    if isinstance(v, list):
        return " ".join(field_text(x) for x in v)
    return str(v)


KNOWN = {"kool": "kool", "uk": "uk", "rinsefm": "uk", "rinse": "uk", "france": "france", "swu": "swu"}


def channel_of(entry, url):
    """Rinse tags every entry with channel[].slug. Fall back to the replay path segment."""
    ch = entry.get("channel")
    for c in (ch if isinstance(ch, list) else [ch]):
        if isinstance(c, dict) and c.get("slug"):
            slug = str(c["slug"]).lower()
            return KNOWN.get(slug, slug)
    seg = url.split("replay.rinse.fm/", 1)[-1].split("/", 1)[0].lower()
    return KNOWN.get(seg, "other")


def air_time(entry, day, channel):
    """When this slot went out: the schedule day plus the slot's clock time.

    The API time field carries the right clock time and offset but not the right
    date, and titles of rebroadcasts carry the original date, so the schedule day
    we asked for is the only reliable date.
    """
    y, mo, d = (int(x) for x in day.split("-"))
    for k in ("episodeTime", "startTime", "start", "airDate", "date", "broadcastDate"):
        v = entry.get(k)
        if isinstance(v, str) and re.match(r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}", v):
            try:
                t = datetime.fromisoformat(v.replace("Z", "+00:00"))
                tz = t.tzinfo or timezone.utc
                return datetime(y, mo, d, t.hour, t.minute, tzinfo=tz)
            except ValueError:
                pass
    tz = ZoneInfo("Europe/Paris" if channel == "france" else "Europe/London")
    m = re.search(r"(\d{1,2}):(\d{2})\s*$", entry.get("title") or "")
    if m and int(m.group(1)) < 24:
        return datetime(y, mo, d, int(m.group(1)), int(m.group(2)), tzinfo=tz)
    return datetime(y, mo, d, tzinfo=tz)


SKIP_KEYS = {"channel", "channels", "originalEpisode", "station"}
IMG_EXT = re.compile(r"\.(jpe?g|png|webp|gif)(\?|$)", re.I)


def asset_filename(v):
    """First filename in a Craft asset list like featuredImage: [{"filename": "x.jpg"}]."""
    if isinstance(v, list):
        for a in v:
            if isinstance(a, dict) and isinstance(a.get("filename"), str) and IMG_EXT.search(a["filename"]):
                return a["filename"]
    return None


def episode_image(entry):
    """Episode art, else the show's default episode art, else the show's own image."""
    f = asset_filename(entry.get("featuredImage"))
    path = ".featuredImage.filename"
    if not f:
        shows = entry.get("parentShow")
        show = shows[0] if isinstance(shows, list) and shows and isinstance(shows[0], dict) else {}
        for k in ("defaultEpisodeImage", "featuredImage"):
            f = asset_filename(show.get(k))
            if f:
                path = f".parentShow.{k}.filename"
                break
    if f:
        return "https://image.rinse.fm/_/" + urllib.parse.quote(f), path
    return find_image(entry)


def art_url(u):
    """Ask Rinse's image server for a 1400 px square. Other hosts get the link as is."""
    return u + ART if "image.rinse.fm/" in u else u


def find_image(entry, path=""):
    """First image.rinse.fm link in the entry, ignoring channel logos and nested episodes.

    Returns (base_url_without_query, json_path) or (None, None).
    """
    if isinstance(entry, dict):
        # look at keys that sound like images first
        keys = sorted(entry.keys(), key=lambda k: 0 if "image" in k.lower() or "artwork" in k.lower() else 1)
        for k in keys:
            if k in SKIP_KEYS:
                continue
            u, p = find_image(entry[k], f"{path}.{k}")
            if u:
                return u, p
    elif isinstance(entry, list):
        for i, v in enumerate(entry):
            u, p = find_image(v, f"{path}[{i}]")
            if u:
                return u, p
    elif isinstance(entry, str) and ("image.rinse.fm/" in entry or IMG_EXT.search(entry)):
        u = entry.strip()
        if u.startswith("//"):
            u = "https:" + u
        if u.startswith("http") and not u.lower().split("?")[0].endswith(".mp3"):
            return (u.split("?", 1)[0] if "image.rinse.fm/" in u else u), path
    return None, None


def is_mp3(url):
    return isinstance(url, str) and url.lower().split("?")[0].endswith(".mp3")


# ---------------------------------------------------------------- size

_fixture_sizes = None


def remote_size(url):
    global _fixture_sizes
    if FIXTURE_SIZES:
        if _fixture_sizes is None:
            _fixture_sizes = load_json(FIXTURE_SIZES, {})
        return _fixture_sizes.get(url)
    try:
        with http(url, method="HEAD", timeout=20) as r:
            n = int(r.headers.get("Content-Length") or 0)
            if n > 0:
                return n
    except urllib.error.HTTPError as e:
        if e.code in (404, 410):
            return -1  # gone
    except Exception:
        pass
    # Some servers refuse HEAD. Ask for one byte and read the total.
    try:
        with http(url, headers={"Range": "bytes=0-0"}, timeout=20) as r:
            cr = r.headers.get("Content-Range") or ""
            m = re.search(r"/(\d+)$", cr)
            if m:
                return int(m.group(1))
    except urllib.error.HTTPError as e:
        if e.code in (404, 410):
            return -1
    except Exception:
        pass
    return None


# ---------------------------------------------------------------- station covers

COVERS_FILE = os.path.join(DATA, "covers.json")
COVER_DIR = os.path.join(DOCS, "covers")
COVER_PX = 1400
COVER_REFRESH_DAYS = 7
PAGE_SLUGS = {"uk": ["uk", "rinse-fm", "rinsefm"]}   # other channels use their own key
PALETTE = {"red": "#C8102E", "steel": "#46525E", "blue": "#1F4FD1", "navy": "#1B2A4A",
           "green": "#1E8C4E", "yellow": "#F2C230", "orange": "#E8692A", "pink": "#E84D8A",
           "purple": "#6B3FA0", "black": "#111111", "white": "#F2F2F2", "grey": "#6E6E6E", "gray": "#6E6E6E"}
DEFAULT_COLOURS = {"kool": "#C8102E", "uk": "#46525E", "france": "#1F4FD1", "swu": "#E8692A"}


def fetch_bytes(url, limit=30_000_000):
    if FIXTURE_DIR:
        name = "page_" + url.rstrip("/").rsplit("/", 1)[-1] + ".html" if "/channels/" in url \
            else "img_" + url.split("?")[0].rsplit("/", 1)[-1]
        p = os.path.join(FIXTURE_DIR, name)
        if not os.path.exists(p):
            raise FileNotFoundError(url)
        with open(p, "rb") as f:
            return f.read()
    with http(url, timeout=30) as r:
        return r.read(limit)


def colour_for(key, colour_slug):
    for word, hexv in PALETTE.items():
        if colour_slug and word in colour_slug.lower():
            return hexv
    return DEFAULT_COLOURS.get(key, "#333333")


def footer_logos(keys):
    """Rinse draws each station logo inline in the site footer, right after the
    link to that channel. Returns key -> svg text for the stations it finds."""
    try:
        html = fetch_bytes("https://www.rinse.fm/channels/kool").decode("utf-8", "replace")
    except Exception as e:
        log(f"  logo page failed: {e}")
        return {}
    out = {}
    for k in keys:
        for slug in PAGE_SLUGS.get(k, [k]):
            i = html.rfind(f'href="/channels/{slug}"')
            if i < 0:
                continue
            m = re.compile(r"<svg\b.*?</svg>", re.S).search(html, i, i + 6000)
            if m and "currentColor" in m.group(0):
                out[k] = m.group(0)
                break
    return out


def make_cover_from_logo(svg, hexv, dest):
    import io
    import cairosvg
    from PIL import Image
    rgb = tuple(int(hexv[i:i + 2], 16) for i in (1, 3, 5))
    ink = "#111111" if (0.299 * rgb[0] + 0.587 * rgb[1] + 0.114 * rgb[2]) > 160 else "#FFFFFF"
    svg = re.sub(r'\sclass="[^"]*"', "", svg, count=1).replace("currentColor", ink)
    logo = Image.open(io.BytesIO(cairosvg.svg2png(bytestring=svg.encode(), output_width=int(COVER_PX * 0.7)))).convert("RGBA")
    im = Image.new("RGB", (COVER_PX, COVER_PX), rgb)
    im.paste(logo, ((COVER_PX - logo.width) // 2, (COVER_PX - logo.height) // 2), logo)
    im.save(dest, "JPEG", quality=92)


def make_cover_generated(name, hexv, dest):
    from PIL import Image, ImageDraw, ImageFont
    rgb = tuple(int(hexv[i:i + 2], 16) for i in (1, 3, 5))
    ink = (17, 17, 17) if (0.299 * rgb[0] + 0.587 * rgb[1] + 0.114 * rgb[2]) > 160 else (255, 255, 255)
    im = Image.new("RGB", (COVER_PX, COVER_PX), rgb)
    d = ImageDraw.Draw(im)
    size = 260
    while size > 60:
        font = ImageFont.load_default(size=size)
        box = d.textbbox((0, 0), name, font=font)
        if box[2] - box[0] <= COVER_PX * 0.84:
            break
        size -= 10
    box = d.textbbox((0, 0), name, font=font)
    x = (COVER_PX - (box[2] - box[0])) // 2 - box[0]
    y = (COVER_PX - (box[3] - box[1])) // 2 - box[1]
    d.text((x, y), name, font=font, fill=ink)
    im.save(dest, "JPEG", quality=92)


def station_covers(channels, colours, base_url, today, cover_colours=None):
    """One square cover per station: Rinse's own station logo from the site footer,
    white on the station colour. Falls back to a plain name cover if the logo
    cannot be found or rendered. Returns key -> absolute URL."""
    cover_colours = cover_colours or {}
    if not base_url:
        return {}
    try:
        import PIL  # noqa: F401
    except ImportError:
        log("Pillow missing, station covers skipped")
        return {}
    os.makedirs(COVER_DIR, exist_ok=True)
    state = load_json(COVERS_FILE, {})
    def stale(k):
        st = state.get(k)
        return (not st or not os.path.exists(os.path.join(COVER_DIR, f"{k}.jpg"))
                or not st["source"].startswith("logo:")      # keep trying until the logo cover exists
                or (today - datetime.fromisoformat(st["checked"]).date()).days >= COVER_REFRESH_DAYS)

    todo = [k for k in channels if stale(k)]
    logos = footer_logos(todo) if todo else {}
    import hashlib
    for k in todo:
        dest = os.path.join(COVER_DIR, f"{k}.jpg")
        colour = cover_colours.get(k) or colour_for(k, colours.get(k))
        src = None
        if k in logos:
            want = f"logo:{hashlib.sha1(logos[k].encode()).hexdigest()[:10]}:{colour}"
            try:
                if state.get(k, {}).get("source") != want or not os.path.exists(dest):
                    make_cover_from_logo(logos[k], colour, dest)
                src = want
            except Exception as e:
                log(f"  cover {k}: logo render failed ({e}), generating")
        if not src:
            want = f"generated:{channels[k]}:{colour}"
            if state.get(k, {}).get("source") != want or not os.path.exists(dest):
                make_cover_generated(channels[k], colour, dest)
            src = want
        with open(dest, "rb") as f:
            ver = hashlib.sha1(f.read()).hexdigest()[:8]
        state[k] = {"source": src, "checked": today.isoformat(), "ver": ver}
        log(f"  cover {k}: {src.split(':')[0]}")
    save_json(COVERS_FILE, state)
    # ?v= changes only when the image changes, so Apple refetches it then and only then
    return {k: f"{base_url}/covers/{k}.jpg?v={v['ver']}" for k, v in state.items() if k in channels}


# ---------------------------------------------------------------- rss

def describe(ep, dt):
    text = f"{ep['channel_name']}, broadcast {dt.strftime('%d %b %Y %H:%M')}"
    if ep.get("genres"):
        text += ". " + ", ".join(ep["genres"])
    return text


def rss(title, description, link, items, self_url="", fixed_cover=None):
    # Most used image in the feed, so the cover stays put instead of changing daily
    imgs = [ep["image"] for ep in items if ep.get("image")]
    # ties go to the newest episode (items are newest first), so the result never flips between runs
    cover = collections.Counter(imgs).most_common(1)[0][0] if imgs else None
    out = [
        '<?xml version="1.0" encoding="UTF-8"?>',
        '<rss version="2.0" xmlns:itunes="http://www.itunes.com/dtds/podcast-1.0.dtd" '
        'xmlns:atom="http://www.w3.org/2005/Atom">',
        "<channel>",
        f"<title>{escape(title)}</title>",
        f"<link>{escape(link)}</link>",
        f"<description>{escape(description)}</description>",
        "<language>en</language>",
        f"<itunes:author>{escape(title)}</itunes:author>",
        "<itunes:explicit>false</itunes:explicit>",
        "<itunes:block>Yes</itunes:block>",
    ]
    cover = fixed_cover or (art_url(cover) if cover else None)
    if cover:
        out += [f'<itunes:image href="{escape(cover)}"/>',
                f"<image><url>{escape(cover)}</url><title>{escape(title)}</title><link>{escape(link)}</link></image>"]
    if self_url:
        out.append(f'<atom:link href="{escape(self_url)}" rel="self" type="application/rss+xml"/>')
    for ep in items:
        dt = datetime.fromisoformat(ep["date"])
        out += [
            "<item>",
            f"<title>{escape(ep['title'])}</title>",
            f"<description>{escape(describe(ep, dt))}</description>",
            f'<enclosure url="{escape(ep["url"])}" length="{ep["size"]}" type="audio/mpeg"/>',
            f'<guid isPermaLink="false">rinse-size-{ep["size"]}</guid>',
            f"<pubDate>{format_datetime(dt)}</pubDate>",
            f"<itunes:author>{escape(ep['channel_name'])}</itunes:author>",
        ]
        if ep.get("minutes"):
            out.append(f"<itunes:duration>{ep['minutes'] * 60}</itunes:duration>")
        if ep.get("image"):
            out.append(f'<itunes:image href="{escape(art_url(ep["image"]))}"/>')
        out += [
            "</item>",
        ]
    out += ["</channel>", "</rss>", ""]
    return "\n".join(out)


def write_if_changed(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    try:
        with open(path, encoding="utf-8") as f:
            if f.read() == text:
                return False
    except FileNotFoundError:
        pass
    with open(path, "w", encoding="utf-8") as f:
        f.write(text)
    return True


# ---------------------------------------------------------------- main

def main():
    cfg = load_json(os.path.join(ROOT, "config.json"), {})
    channels = cfg.get("channels", {})
    artists = cfg.get("artists", [])
    backfill = int(cfg.get("backfill_days", 120))
    recent = int(cfg.get("recent_days", 7))
    max_checks = int(cfg.get("max_size_checks_per_run", 400))
    max_items = int(cfg.get("max_items_per_channel_feed", 300))
    base_url = os.environ.get("FEED_BASE_URL", "").rstrip("/")

    episodes = load_json(STATE_FILE, {})        # url -> record
    fetched = set(load_json(DATES_FILE, []))    # schedule days already read
    meta = load_json(META_FILE, {})
    if meta.get("version") != STATE_VERSION:
        # Older state: wrong dates (v1) or no images (v2). Keep sizes, reread every day.
        log(f"Upgrading state v{meta.get('version', 1)} to v{STATE_VERSION}: rereading schedule")
        for r in episodes.values():
            r["date"] = None
        fetched = set()

    # 1. Read the schedule. Recent days every run, older days once.
    today = datetime.now(timezone.utc).date()
    if os.environ.get("RINSE_TODAY"):
        today = datetime.strptime(os.environ["RINSE_TODAY"], "%Y-%m-%d").date()
    days = [(today - timedelta(days=i)).isoformat() for i in range(backfill)]
    to_read = [d for i, d in enumerate(days) if i < recent or d not in fetched]
    log(f"Reading {len(to_read)} schedule days")

    report = {}
    colours = {}
    new_links = 0
    sample = None
    for d in to_read:
        entries = fetch_day(d)
        if entries is None:
            continue
        for top in entries:
            top_img, top_path = episode_image(top)
            for e in walk(top):
                url = e.get("fileUrl")
                if not is_mp3(url):
                    continue
                img, img_path = episode_image(e)
                minutes = e.get("episodeLength") if isinstance(e.get("episodeLength"), int) else None
                genres = [g.get("title") for g in (e.get("genreTag") or [])
                          if isinstance(g, dict) and g.get("title")]
                if not img:
                    img, img_path = top_img, ("parent" + (top_path or "")) if top_img else None
                if sample is None or (img and not sample.get("image")):
                    sample = {"image_found_at": img_path, "image": img, "entry": e}
                ch = channel_of(e, url)
                when = air_time(e, d, ch)
                report.setdefault(ch, {"count": 0, "sample_url": url, "sample_fields": {}})
                report[ch]["count"] += 1
                if ch not in colours:
                    for c in (e.get("channel") or []):
                        if isinstance(c, dict):
                            cc = c.get("channelColour")
                            if isinstance(cc, list) and cc and isinstance(cc[0], dict):
                                colours[ch] = cc[0].get("slug") or cc[0].get("title")
                if not report[ch]["sample_fields"]:
                    report[ch]["sample_fields"] = {k: e.get(k) for k in ("channel", "channels", "station") if k in e}
                rec = episodes.get(url)
                if rec is None:
                    episodes[url] = {
                        "title": (e.get("title") or url.rsplit("/", 1)[-1]).strip(),
                        "channel": ch,
                        "date": when.isoformat(),
                        "size": None,
                        "image": img,
                        "minutes": minutes,
                        "genres": genres,
                    }
                    new_links += 1
                else:
                    rec["channel"] = ch
                    if img:
                        rec["image"] = img
                    if minutes:
                        rec["minutes"] = minutes
                    if genres:
                        rec["genres"] = genres
                    # keep the first time it aired
                    if not rec.get("date") or when < datetime.fromisoformat(rec["date"]):
                        rec["date"] = when.isoformat()
        fetched.add(d)
        if not FIXTURE_DIR:
            time.sleep(0.4)
    for u in [u for u, r in episodes.items() if not r.get("date")]:
        del episodes[u]
    log(f"New links found: {new_links}, total known: {len(episodes)}")

    # 2. Get sizes, newest first, capped per run so the backfill spreads over days.
    pending = sorted((u for u, r in episodes.items() if r["size"] is None),
                     key=lambda u: datetime.fromisoformat(episodes[u]["date"]), reverse=True)
    batch = pending[:max_checks]
    workers = 1 if FIXTURE_SIZES else 8
    with ThreadPoolExecutor(max_workers=workers) as pool:
        for u, s in zip(batch, pool.map(remote_size, batch)):
            if s is not None:
                episodes[u]["size"] = s
    log(f"Size checks: {len(batch)}, still pending: {len(pending) - len(batch)}")

    save_json(STATE_FILE, episodes)
    save_json(DATES_FILE, sorted(fetched))
    save_json(REPORT_FILE, report)
    save_json(META_FILE, {"version": STATE_VERSION})
    if sample:
        save_json(SAMPLE_FILE, sample)
    with_img = sum(1 for r in episodes.values() if r.get("image"))
    log(f"Episodes with artwork: {with_img} of {len(episodes)}")

    # 3. Collapse reposts: one episode per file size, keep the earliest airing.
    by_size = {}
    for u, r in episodes.items():
        if not r["size"] or r["size"] <= 0:
            continue
        cur = by_size.get(r["size"])
        if cur is None or datetime.fromisoformat(r["date"]) < datetime.fromisoformat(cur["date"]):
            by_size[r["size"]] = {**r, "url": u,
                                  "channel_name": channels.get(r["channel"], r["channel"].upper())}
    ready = sorted(by_size.values(), key=lambda r: datetime.fromisoformat(r["date"]), reverse=True)
    log(f"Publishable episodes after repost merge: {len(ready)}")

    # 4. Write feeds.
    covers = station_covers(channels, colours, base_url, today, cfg.get("cover_colours", {}))
    index = []
    keys = list(channels.keys()) + (["other"] if any(r["channel"] == "other" for r in ready) else [])
    for key in keys:
        name = channels.get(key, "Other")
        items = [r for r in ready if r["channel"] == key][:max_items]
        fn = f"{key}.xml"
        write_if_changed(os.path.join(DOCS, fn),
                         rss(name, f"{name} shows from the rinse.fm schedule.", "https://www.rinse.fm",
                             items, f"{base_url}/{fn}" if base_url else "", covers.get(key)))
        index.append((name, fn, len(items)))

    for a in artists:
        na = norm(a)
        items = [r for r in ready if na in norm(r["title"])]
        fn = f"artists/{slugify(a)}.xml"
        write_if_changed(os.path.join(DOCS, fn),
                         rss(f"{a} on Rinse", f"Every {a} set found across Rinse channels.",
                             f"https://www.rinse.fm/shows/{slugify(a)}",
                             items, f"{base_url}/{fn}" if base_url else ""))
        index.append((f"{a} (artist)", fn, len(items)))

    rows = "\n".join(
        f'<li><b>{escape(n)}</b> <span>{c} episodes</span><br>'
        f'<input readonly value="{escape((base_url + "/" if base_url else "") + fn)}" onclick="this.select()"></li>'
        for n, fn, c in index)
    stamp = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
    write_if_changed(os.path.join(DOCS, "index.html"), f"""<!doctype html>
<html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<meta name="robots" content="noindex"><title>Rinse feeds</title>
<style>body{{font:16px -apple-system,system-ui,sans-serif;margin:16px;max-width:640px}}
li{{margin:0 0 16px}}span{{color:#888;font-size:14px}}input{{width:100%;font-size:14px;padding:6px;margin-top:4px}}</style>
</head><body><h1>Rinse feeds</h1><p>Tap a link, copy it, then in Apple Podcasts: Library, the ⋯ menu, Follow a Show by URL.</p>
<ul style="list-style:none;padding:0">{rows}</ul><p><span>Updated {stamp}</span></p></body></html>
""")

    for n, fn, c in index:
        log(f"  {fn}: {c}")
    log("Channel report:", json.dumps({k: v["count"] for k, v in report.items()}))


if __name__ == "__main__":
    sys.exit(main())
