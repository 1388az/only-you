# -*- coding: utf-8 -*-
"""
«فقط برای تو ♡» — ربات تلگرام + بک‌اند Mini App در یک فایل.

یک پروسه‌ی واحد اجرا می‌کند:
  * ربات (aiogram 3، long polling)
  * سرور وب aiohttp: فایل webapp/index.html و API امن (/api/...)
  * زمان‌بند پیام صبح و شب (با قفل در دیتابیس، ضدتکرار)
"""
import asyncio
import html
import hashlib
import hmac
import io
import json
import logging
import os
import random
import re
import sqlite3
import time
import uuid
from collections import defaultdict, deque
from datetime import date, datetime, timedelta
from pathlib import Path
from urllib.parse import parse_qsl
from zoneinfo import ZoneInfo

import aiohttp
import aiosqlite
from aiohttp import web
from aiogram import BaseMiddleware, Bot, Dispatcher, F, Router
from aiogram.client.default import DefaultBotProperties
from aiogram.enums import ParseMode
from aiogram.filters import Command, CommandStart
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
from aiogram.fsm.storage.memory import MemoryStorage
from aiogram.types import (BotCommand, CallbackQuery, FSInputFile, InlineKeyboardButton,
                           ErrorEvent, InlineKeyboardMarkup, InputMediaPhoto, KeyboardButton, MenuButtonWebApp,
                           Message, ReplyKeyboardMarkup, WebAppInfo)

# ───────────────────────── پیکربندی ─────────────────────────
def env(name, default=""):
    return os.getenv(name, default).strip()


def env_int(name):
    try:
        return int(env(name, "0") or 0)
    except ValueError:
        return 0


BOT_TOKEN = env("BOT_TOKEN")
ADMIN_ID = env_int("ADMIN_ID")
ALLOWED_USER_ID = env_int("ALLOWED_USER_ID")
WEBAPP_URL = env("WEBAPP_URL").rstrip("/")
GEMINI_API_KEY = env("GEMINI_API_KEY")
GEMINI_MODEL = env("GEMINI_MODEL", "gemini-2.5-flash")
TZ = ZoneInfo(env("TIMEZONE", "Asia/Tehran"))
PORT = int(env("PORT", "8080") or 8080)

_db_url = env("DATABASE_URL")
DB_PATH = env("DB_PATH") or (_db_url[len("sqlite:///"):] if _db_url.startswith("sqlite:///") else "data/app.db")
DATA_DIR = Path(DB_PATH).resolve().parent
MEDIA_DIR = DATA_DIR / "media"
WEBAPP_FILE = Path(__file__).resolve().parent / "webapp" / "index.html"

MAX_PHOTO = 10 * 1024 * 1024
MAX_VOICE = 15 * 1024 * 1024
PAGE = 5

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(name)s: %(message)s")
log = logging.getLogger("love")

DB: aiosqlite.Connection = None
HTTP: aiohttp.ClientSession = None
STARTED_AT = time.time()
RATE = defaultdict(deque)
RATE_LIMIT, RATE_WINDOW = 240, 60  # درخواست در دقیقه برای هر کاربر

PRIVACY_TEXT = (
    "پیش از ثبت اولین خاطره، لطفاً این‌ها را بخوان:\n\n"
    "• متن، عکس و ویس‌هایی که ثبت می‌کنی روی سرور این پروژه ذخیره می‌شود.\n"
    "• مدیر پروژه می‌تواند این محتوا (متن، عکس و ویس) را ببیند.\n"
    "• هیچ محتوایی برای شخص ثالث ارسال نمی‌شود. (برای ساخت پیام‌های صبح و شب فقط یک موضوع کلی به Gemini داده می‌شود، نه خاطره‌های تو.)\n"
    "• هر زمان می‌توانی ثبت خاطرات را متوقف کنی یا حذف همه‌ی خاطراتت را بخواهی.\n\n"
    "بدون تأیید صریح تو، ذخیره‌ی خاطره فعال نمی‌شود."
)

# ───────────────────────── تقویم شمسی ─────────────────────────
J_MONTHS = ["فروردین", "اردیبهشت", "خرداد", "تیر", "مرداد", "شهریور", "مهر", "آبان", "آذر", "دی", "بهمن", "اسفند"]
WEEKDAYS = ["دوشنبه", "سه‌شنبه", "چهارشنبه", "پنجشنبه", "جمعه", "شنبه", "یکشنبه"]  # بر اساس date.weekday()
_FA = str.maketrans("0123456789", "۰۱۲۳۴۵۶۷۸۹")
_EN = str.maketrans("۰۱۲۳۴۵۶۷۸۹٠١٢٣٤٥٦٧٨٩", "01234567890123456789")


def fa(x):
    return str(x).translate(_FA)


def g2j(gy, gm, gd):
    g_d_m = [0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334]
    gy2 = gy + 1 if gm > 2 else gy
    days = 355666 + 365 * gy + (gy2 + 3) // 4 - (gy2 + 99) // 100 + (gy2 + 399) // 400 + gd + g_d_m[gm - 1]
    jy = -1595 + 33 * (days // 12053)
    days %= 12053
    jy += 4 * (days // 1461)
    days %= 1461
    if days > 365:
        jy += (days - 1) // 365
        days = (days - 1) % 365
    if days < 186:
        jm, jd = 1 + days // 31, 1 + days % 31
    else:
        jm, jd = 7 + (days - 186) // 30, 1 + (days - 186) % 30
    return jy, jm, jd


def j2g(jy, jm, jd):
    jy += 1595
    days = -355668 + 365 * jy + (jy // 33) * 8 + ((jy % 33) + 3) // 4 + jd
    days += (jm - 1) * 31 if jm < 7 else (jm - 7) * 30 + 186
    gy = 400 * (days // 146097)
    days %= 146097
    if days > 36524:
        days -= 1
        gy += 100 * (days // 36524)
        days %= 36524
        if days >= 365:
            days += 1
    gy += 4 * (days // 1461)
    days %= 1461
    if days > 365:
        gy += (days - 1) // 365
        days = (days - 1) % 365
    gd = days + 1
    leap = (gy % 4 == 0 and gy % 100 != 0) or gy % 400 == 0
    sal = [0, 31, 29 if leap else 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]
    gm = 0
    while gm < 13 and gd > sal[gm]:
        gd -= sal[gm]
        gm += 1
    return gy, gm, gd


def is_jleap(jy):
    return g2j(*j2g(jy, 12, 30)) == (jy, 12, 30)


def jdays_in_month(jy, jm):
    return 31 if jm <= 6 else 30 if jm <= 11 else (30 if is_jleap(jy) else 29)


def fmt_j(d):
    if isinstance(d, datetime):
        d = d.date()
    jy, jm, jd = g2j(d.year, d.month, d.day)
    return f"{fa(jd)} {J_MONTHS[jm - 1]} {fa(jy)}"


def valid_jdate(jy, jm, jd):
    return 1200 <= jy <= 1600 and 1 <= jm <= 12 and 1 <= jd <= jdays_in_month(jy, jm)


def parse_jparts(text):
    """'۱۴۰۳/۰۵/۱۲' → [1403,5,12]"""
    parts = [p for p in re.split(r"[/\-.\s]+", text.translate(_EN).strip()) if p]
    if not all(p.isdigit() for p in parts):
        return None
    return [int(p) for p in parts]


def now_local():
    return datetime.now(TZ)


def ts():
    return now_local().strftime("%Y-%m-%d %H:%M:%S")


def next_occurrence(jm, jd, today):
    ty = g2j(today.year, today.month, today.day)[0]
    for jy in (ty, ty + 1):
        d = min(jd, jdays_in_month(jy, jm))
        g = date(*j2g(jy, jm, d))
        if g >= today:
            return g, jy
    raise RuntimeError("unreachable")


def rel_diff(start, today):
    sy, sm, sd = g2j(start.year, start.month, start.day)
    ty, tm, td = g2j(today.year, today.month, today.day)
    y, m, d = ty - sy, tm - sm, td - sd
    if d < 0:
        pm, py = (tm - 1, ty) if tm > 1 else (12, ty - 1)
        d += jdays_in_month(py, pm)
        m -= 1
    if m < 0:
        m += 12
        y -= 1
    return max(y, 0), max(m, 0), max(d, 0)


# ───────────────────────── دیتابیس ─────────────────────────
SCHEMA = """
CREATE TABLE IF NOT EXISTS users(
  id INTEGER PRIMARY KEY, role TEXT, consent INTEGER DEFAULT 0, consent_at TEXT,
  paused INTEGER DEFAULT 0, created_at TEXT);
CREATE TABLE IF NOT EXISTS settings(key TEXT PRIMARY KEY, value TEXT);
CREATE TABLE IF NOT EXISTS memories(
  id INTEGER PRIMARY KEY AUTOINCREMENT, owner_id INTEGER NOT NULL, title TEXT NOT NULL,
  body TEXT NOT NULL DEFAULT '', mem_date TEXT NOT NULL, created_at TEXT, updated_at TEXT);
CREATE TABLE IF NOT EXISTS media(
  id INTEGER PRIMARY KEY AUTOINCREMENT, owner_id INTEGER NOT NULL,
  memory_id INTEGER REFERENCES memories(id) ON DELETE CASCADE,
  kind TEXT NOT NULL, mime TEXT, path TEXT NOT NULL, size INTEGER, title TEXT DEFAULT '',
  caption TEXT DEFAULT '', duration INTEGER DEFAULT 0, created_at TEXT);
CREATE INDEX IF NOT EXISTS idx_media_mem ON media(memory_id);
CREATE TABLE IF NOT EXISTS letters(
  id INTEGER PRIMARY KEY AUTOINCREMENT, title TEXT, body TEXT NOT NULL, created_at TEXT, read_at TEXT);
CREATE TABLE IF NOT EXISTS events(
  id INTEGER PRIMARY KEY AUTOINCREMENT, title TEXT NOT NULL, repeat INTEGER NOT NULL,
  jm INTEGER, jd INTEGER, gdate TEXT, created_at TEXT);
CREATE TABLE IF NOT EXISTS schedule_log(
  kind TEXT, day TEXT, status TEXT, attempts INTEGER DEFAULT 0, message TEXT, error TEXT,
  updated_at TEXT, PRIMARY KEY(kind, day));
CREATE TABLE IF NOT EXISTS error_log(
  id INTEGER PRIMARY KEY AUTOINCREMENT, ts TEXT, scope TEXT, message TEXT);
"""


async def init_db():
    global DB
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    MEDIA_DIR.mkdir(parents=True, exist_ok=True)
    DB = await aiosqlite.connect(DB_PATH)
    DB.row_factory = aiosqlite.Row
    await DB.execute("PRAGMA journal_mode=WAL")
    await DB.execute("PRAGMA foreign_keys=ON")
    await DB.executescript(SCHEMA)
    await DB.commit()


async def q_all(sql, args=()):
    async with DB.execute(sql, args) as c:
        return [dict(r) for r in await c.fetchall()]


async def q_one(sql, args=()):
    async with DB.execute(sql, args) as c:
        r = await c.fetchone()
        return dict(r) if r else None


async def q_exec(sql, args=()):
    cur = await DB.execute(sql, args)
    await DB.commit()
    return cur.lastrowid


async def get_setting(k, d=None):
    r = await q_one("SELECT value FROM settings WHERE key=?", (k,))
    return r["value"] if r else d


async def set_setting(k, v):
    await q_exec("INSERT INTO settings(key,value) VALUES(?,?) ON CONFLICT(key) DO UPDATE SET value=excluded.value", (k, v))


async def log_error(scope, err):
    log.error("%s: %s", scope, err)
    try:
        await q_exec("INSERT INTO error_log(ts,scope,message) VALUES(?,?,?)", (ts(), scope, str(err)[:500]))
        await q_exec("DELETE FROM error_log WHERE id NOT IN (SELECT id FROM error_log ORDER BY id DESC LIMIT 200)")
    except Exception:
        pass


def allowed_ids():
    return {i for i in (ADMIN_ID, ALLOWED_USER_ID) if i}


async def ensure_user(uid):
    role = "admin" if uid == ADMIN_ID else "user"
    await q_exec("INSERT OR IGNORE INTO users(id,role,created_at) VALUES(?,?,?)", (uid, role, ts()))
    return await q_one("SELECT * FROM users WHERE id=?", (uid,))


class ApiError(Exception):
    def __init__(self, code, status=400):
        self.code, self.status = code, status


async def check_can_write(uid):
    """کاربر مجاز بدون رضایت یا با توقف ثبت، نمی‌تواند چیزی ذخیره کند."""
    if uid == ALLOWED_USER_ID:
        u = await ensure_user(uid)
        if not u["consent"]:
            raise ApiError("consent_required", 403)
        if u["paused"]:
            raise ApiError("paused", 403)
    elif uid != ADMIN_ID:
        raise ApiError("forbidden", 403)


# ───────────────────────── فایل‌ها ─────────────────────────
def sniff(d):
    """تشخیص نوع واقعی فایل از روی محتوا → (kind, mime, ext)"""
    if d[:3] == b"\xff\xd8\xff":
        return "photo", "image/jpeg", ".jpg"
    if d[:8] == b"\x89PNG\r\n\x1a\n":
        return "photo", "image/png", ".png"
    if d[:4] == b"RIFF" and d[8:12] == b"WEBP":
        return "photo", "image/webp", ".webp"
    if d[:4] == b"OggS":
        return "voice", "audio/ogg", ".ogg"
    if d[:4] == b"\x1a\x45\xdf\xa3":
        return "voice", "audio/webm", ".webm"
    if d[4:8] == b"ftyp" and d[8:12] not in (b"heic", b"heix", b"hevc", b"heif", b"mif1", b"msf1", b"avif", b"qt  "):
        return "voice", "audio/mp4", ".m4a"
    if d[:3] == b"ID3" or d[:2] in (b"\xff\xfb", b"\xff\xf3", b"\xff\xf2"):
        return "voice", "audio/mpeg", ".mp3"
    if d[:4] == b"RIFF" and d[8:12] == b"WAVE":
        return "voice", "audio/wav", ".wav"
    return None


async def save_media(owner_id, data, kind_hint=None, memory_id=None, title="", caption="", duration=0):
    info = sniff(data)
    if not info:
        raise ApiError("invalid_file_type", 415)
    kind, mime, ext = info
    if kind_hint in ("photo", "voice") and kind_hint != kind:
        raise ApiError("kind_mismatch", 400)
    if len(data) > (MAX_PHOTO if kind == "photo" else MAX_VOICE):
        raise ApiError("file_too_large", 413)
    if memory_id is not None and not await q_one("SELECT id FROM memories WHERE id=?", (memory_id,)):
        raise ApiError("memory_not_found", 404)
    name = uuid.uuid4().hex + ext
    path = MEDIA_DIR / name
    await asyncio.to_thread(path.write_bytes, data)
    try:
        mid = await q_exec(
            "INSERT INTO media(owner_id,memory_id,kind,mime,path,size,title,caption,duration,created_at) VALUES(?,?,?,?,?,?,?,?,?,?)",
            (owner_id, memory_id, kind, mime, name, len(data), title[:120], caption[:500], max(0, min(int(duration or 0), 3600)), ts()))
    except Exception:
        path.unlink(missing_ok=True)
        raise
    return mid


def unlink_media(names):
    for n in names:
        try:
            (MEDIA_DIR / n).unlink(missing_ok=True)
        except Exception as e:
            log.warning("unlink failed %s: %s", n, e)


async def delete_memories_where(where, args=()):
    mems = await q_all(f"SELECT id FROM memories WHERE {where}", args)
    if not mems:
        return 0
    ids = [m["id"] for m in mems]
    ph = ",".join("?" * len(ids))
    files = [r["path"] for r in await q_all(f"SELECT path FROM media WHERE memory_id IN ({ph})", ids)]
    await q_exec(f"DELETE FROM memories WHERE id IN ({ph})", ids)  # media حذف آبشاری
    unlink_media(files)
    return len(ids)


# ───────────────────────── داده‌های مشترک (ربات و API) ─────────────────────────
async def get_start_date():
    s = await get_setting("start_date")
    return date.fromisoformat(s) if s else None


async def events_with_dates(today):
    out = []
    start = await get_start_date()
    if start:
        nxt, jy = next_occurrence(*g2j(start.year, start.month, start.day)[1:], today)
        n = jy - g2j(start.year, start.month, start.day)[0]
        out.append({"id": "anniv", "title": f"سالگرد رابطه" + (f" ({fa(n)} سالگی)" if n > 0 else ""), "builtin": True,
                    "date": nxt.isoformat(), "jdate": fmt_j(nxt), "days_left": (nxt - today).days, "repeat": True})
    for e in await q_all("SELECT * FROM events ORDER BY id"):
        if e["repeat"]:
            nxt, _ = next_occurrence(e["jm"], e["jd"], today)
        else:
            nxt = date.fromisoformat(e["gdate"])
            if nxt < today:
                continue
        out.append({"id": e["id"], "title": e["title"], "builtin": False, "date": nxt.isoformat(), "jdate": fmt_j(nxt),
                    "days_left": (nxt - today).days, "repeat": bool(e["repeat"])})
    out.sort(key=lambda x: x["days_left"])
    return out


async def build_home():
    now = now_local()
    today = now.date()
    start = await get_start_date()
    data = {"now_iso": now.isoformat(), "jdate": fmt_j(today), "weekday": WEEKDAYS[today.weekday()], "start": None}
    if start:
        y, m, d = rel_diff(start, today)
        data["start"] = {"jdate": fmt_j(start), "days": max((today - start).days, 0), "years": y, "months": m, "days_part": d}
    evs = await events_with_dates(today)
    data["events"] = evs[:3]
    data["anniversary"] = next((e for e in evs if e.get("builtin")), None)
    data["special_today"] = [e["title"] for e in evs if e["days_left"] == 0]
    data["counts"] = {
        "memories": (await q_one("SELECT COUNT(*) c FROM memories"))["c"],
        "voices": (await q_one("SELECT COUNT(*) c FROM media WHERE kind='voice'"))["c"],
        "photos": (await q_one("SELECT COUNT(*) c FROM media WHERE kind='photo'"))["c"],
    }
    ids = [r["id"] for r in await q_all("SELECT id FROM memories ORDER BY id")]
    mod = None
    if ids:
        pick = ids[int(hashlib.sha256(today.isoformat().encode()).hexdigest(), 16) % len(ids)]
        m = await q_one("SELECT id,title,body,mem_date FROM memories WHERE id=?", (pick,))
        mod = {"id": m["id"], "title": m["title"], "body": m["body"][:300], "jdate": fmt_j(date.fromisoformat(m["mem_date"]))}
    data["memory_of_day"] = mod
    return data


def mem_row_json(r, viewer):
    return {"id": r["id"], "title": r["title"], "body": r["body"], "mem_date": r["mem_date"],
            "jdate": fmt_j(date.fromisoformat(r["mem_date"])), "created_at": r["created_at"],
            "mine": r["owner_id"] == viewer, "from_admin": r["owner_id"] == ADMIN_ID,
            "photos": r.get("pc", 0), "voices": r.get("vc", 0), "cover": r.get("cover")}


MEM_SELECT = """SELECT m.*,
 (SELECT COUNT(*) FROM media WHERE memory_id=m.id AND kind='photo') pc,
 (SELECT COUNT(*) FROM media WHERE memory_id=m.id AND kind='voice') vc,
 (SELECT id FROM media WHERE memory_id=m.id AND kind='photo' ORDER BY id LIMIT 1) cover
 FROM memories m"""


def like(s):
    return "%" + s.replace("\\", "\\\\").replace("%", "\\%").replace("_", "\\_") + "%"


def media_json(r, viewer):
    return {"id": r["id"], "kind": r["kind"], "mime": r["mime"], "title": r["title"], "caption": r["caption"],
            "duration": r["duration"], "memory_id": r["memory_id"], "memory_title": r.get("memory_title"),
            "jdate": fmt_j(datetime.strptime(r["created_at"], "%Y-%m-%d %H:%M:%S")), "mine": r["owner_id"] == viewer,
            "size": r["size"]}


# ───────────────────────── پیام‌های خودکار + Gemini ─────────────────────────
MORNING = [
    "صبح‌بخیر عزیزم ♡ امیدوارم امروز اون‌قدر مهربون باشه که لایقش هستی. فاصله‌ها هر چقدر که باشن، فکرم همین صبح هم پیش توئه.",
    "صبح تو بخیر ☀️ هر روز با فکر تو شروع می‌شه و همین، روزم رو قشنگ می‌کنه. امروز هم مراقب خودت باش.",
    "سلام به قشنگ‌ترین شروعِ روز ♡ یادت باشه که یکی اون‌طرف دنیا (یا همین نزدیکی دل‌ها) همیشه بهت فکر می‌کنه.",
    "صبح‌بخیر نازنینم 🌷 امروز هر جا که رفتی، لبخندت رو با خودت ببر؛ من هم از دور باهات هستم.",
    "چشم‌هات رو که باز کردی، بدون که اولین فکر امروزم تو بودی. روزت پر از اتفاق‌های خوب ♡",
    "صبحت بخیر عشق من. هر روز که می‌گذره، فاصله‌ها کم‌تر می‌شن و دلتنگی‌ام بیشتر؛ ولی دلگرمم که مال همدیگه‌ایم.",
    "امروز هم یه روز دیگه نزدیک‌تر شدیم به دیدار. صبح‌بخیر، قدر خودت رو بدون ♡",
    "صبح‌بخیر. اگه امروز سخت شد، یادت باشه یکی هست که با همه‌ی دلش پشتته.",
    "سلام عزیز دلم ☀️ چای یا قهوه‌ات رو بخور و یادت باشه که حضورت توی زندگی من یه هدیه‌ست.",
    "صبح‌بخیر ♡ آسمون هر جا که باشه، یه تیکه‌ش مال ماست. روز قشنگی داشته باشی.",
]
NIGHT = [
    "شب‌بخیر عزیزم ♡ امروز هم تموم شد و من هنوز دلم پیش توئه. خوب بخوابی و خواب‌های قشنگ ببینی.",
    "شب تو بخیر 🌙 هر چقدر هم که دور باشیم، ماه یکیه و هر دومون بهش نگاه می‌کنیم. دوستت دارم.",
    "خسته نباشی نازنینم. بذار همه‌ی دغدغه‌های امروز همین‌جا تموم بشن؛ فردا یه روز تازه‌ست. شب‌بخیر ♡",
    "شب‌بخیر. امشب هم قبل از خواب بهت فکر می‌کنم و لبخند می‌زنم. آروم بخواب 🌷",
    "امروز هم گذشت و یه روز دیگه به دیدارمون نزدیک‌تر شدیم. شب‌بخیر عشق من ♡",
    "چشم‌هات رو ببند و بدون که یکی از دور بغلت کرده. شب‌بخیر و خواب شیرین 🌙",
    "شب‌بخیر زندگی‌م. ممنونم که امروز هم بودی؛ بودنت آرامش منه ♡",
    "ستاره‌ها امشب برای تو چشمک می‌زنن. شب‌بخیر، فردا دوباره با هم شروع می‌کنیم ✨",
    "دلم برات تنگ شده، ولی خوشحالم که مال منی. شبت آروم و رویاهات قشنگ ♡",
    "شب تو بخیر عزیزم. هر چی امروز سخت بود، تموم شد؛ حالا وقت استراحته 🌙",
]
SPECIAL = [
    "فقط می‌خواستم بدونی که همین الان بهت فکر می‌کنم ♡",
    "دوستت دارم؛ این رو بدون حتی اگه امروز بهت نگفته باشم.",
    "یه قلب کوچیک فرستادم از اون‌طرف فاصله‌ها: ♡ ببینش و لبخند بزن.",
    "تو بهترین اتفاق زندگی منی. همین.",
    "هر وقت دلتنگ شدی، این پیام رو دوباره بخون: من همیشه اینجام ♡",
    "قشنگ‌ترین بخش روزم لحظه‌ایه که بهت فکر می‌کنم.",
]
THEMES = ["آسمان و ستاره‌ها", "دلتنگی شیرین", "امید به دیدار", "چای و آرامش", "باران", "قدردانی", "خنده‌هات", "آینده‌ی با هم",
          "گل و بهار", "نور صبح", "ماه شب", "اعتماد", "صبوری"]
KIND_DESC = {"morning": "صبح‌بخیر گفتن در ساعت ۶ صبح", "night": "شب‌بخیر گفتن در نیمه‌شب", "special": "یک پیام عاشقانه‌ی غیرمنتظره"}


async def gemini_text(prompt):
    if not GEMINI_API_KEY:
        return None
    url = f"https://generativelanguage.googleapis.com/v1beta/models/{GEMINI_MODEL}:generateContent"
    try:
        async with HTTP.post(url, headers={"x-goog-api-key": GEMINI_API_KEY},
                             json={"contents": [{"parts": [{"text": prompt}]}],
                                   "generationConfig": {"temperature": 1.0, "maxOutputTokens": 1024}},
                             timeout=aiohttp.ClientTimeout(total=20)) as r:
            if r.status != 200:
                raise RuntimeError(f"HTTP {r.status}: {(await r.text())[:200]}")
            data = await r.json()
        parts = data["candidates"][0]["content"]["parts"]
        text = "".join(p.get("text", "") for p in parts).strip().strip('"«»')
        if 15 <= len(text) <= 700 and re.search(r"[\u0600-\u06FF]", text):
            return text
        raise RuntimeError("unusable Gemini output")
    except Exception as e:
        await log_error("gemini", e)  # خطا نباید ربات را متوقف کند
        return None


async def make_message(kind):
    recent = {r["message"] for r in await q_all("SELECT message FROM schedule_log WHERE kind=? ORDER BY day DESC LIMIT 10", (kind,)) if r["message"]}
    prompt = (f"یک پیام کوتاه (۲ تا ۳ جمله)، صمیمی و عاشقانه به فارسی برای «{KIND_DESC[kind]}» به عزیزِ یک رابطه‌ی عاشقانه‌ی "
              f"لانگ‌دیستنس بنویس. مضمون: {random.choice(THEMES)}. فقط خود پیام را بنویس؛ بدون توضیح، هشتگ، نقل‌قول و فهرست. "
              "حداکثر یک یا دو ایموجی. تکراری و کلیشه‌ای نباش.")
    text = await gemini_text(prompt)
    if text and text not in recent:
        return text
    pool = {"morning": MORNING, "night": NIGHT, "special": SPECIAL}[kind]
    fresh = [m for m in pool if m not in recent] or pool
    return random.choice(fresh)


async def claim_job(kind, day):
    """ثبت اتمیک اجرای یک کار؛ فقط یک بار برای هر (kind, day) موفق می‌شود."""
    cur = await DB.execute("INSERT OR IGNORE INTO schedule_log(kind,day,status,attempts,updated_at) VALUES(?,?,'sending',1,?)", (kind, day, ts()))
    await DB.commit()
    if cur.rowcount == 1:
        return True
    cut = (now_local() - timedelta(minutes=2)).strftime("%Y-%m-%d %H:%M:%S")
    cur = await DB.execute("UPDATE schedule_log SET status='sending',attempts=attempts+1,updated_at=? "
                           "WHERE kind=? AND day=? AND status='failed' AND attempts<3 AND updated_at<?", (ts(), kind, day, cut))
    await DB.commit()
    return cur.rowcount == 1


async def run_job(bot, kind, day):
    try:
        text = await make_message(kind)
        if kind == "morning":
            specials = [e for e in await events_with_dates(now_local().date()) if e["days_left"] == 0]
            if specials:
                text += "\n\n🎉 امروز: " + "، ".join(e["title"] for e in specials)
        await bot.send_message(ALLOWED_USER_ID, html.escape(text))
        await q_exec("UPDATE schedule_log SET status='sent',message=?,error=NULL,updated_at=? WHERE kind=? AND day=?", (text, ts(), kind, day))
    except Exception as e:
        await q_exec("UPDATE schedule_log SET status='failed',error=?,updated_at=? WHERE kind=? AND day=?", (str(e)[:300], ts(), kind, day))
        await log_error(f"job:{kind}", e)


async def scheduler_loop(bot):
    log.info("scheduler started")
    while True:
        try:
            now = now_local()
            for kind, hour, window in (("morning", 6, 180), ("night", 0, 90)):
                start = now.replace(hour=hour, minute=0, second=0, microsecond=0)
                if start <= now < start + timedelta(minutes=window):
                    if ALLOWED_USER_ID and await claim_job(kind, now.date().isoformat()):
                        await run_job(bot, kind, now.date().isoformat())
        except asyncio.CancelledError:
            raise
        except Exception as e:
            await log_error("scheduler", e)
        await asyncio.sleep(20)


# ───────────────────────── احراز هویت Mini App ─────────────────────────
def validate_init_data(init_data):
    try:
        pairs = dict(parse_qsl(init_data, keep_blank_values=True, strict_parsing=True))
    except ValueError:
        return None
    received = pairs.pop("hash", None)
    if not received:
        return None
    check = "\n".join(f"{k}={v}" for k, v in sorted(pairs.items()))
    secret = hmac.new(b"WebAppData", BOT_TOKEN.encode(), hashlib.sha256).digest()
    calc = hmac.new(secret, check.encode(), hashlib.sha256).hexdigest()
    if not hmac.compare_digest(calc, received):
        return None
    try:
        if time.time() - int(pairs.get("auth_date", "0")) > 86400:
            return None
        return json.loads(pairs["user"])
    except Exception:
        return None


def jerr(code, status=400):
    return web.json_response({"error": code}, status=status)


@web.middleware
async def error_mw(request, handler):
    try:
        resp = await handler(request)
    except ApiError as e:
        return jerr(e.code, e.status)
    except web.HTTPException:
        raise
    except Exception as e:
        await log_error(f"api:{request.method} {request.path}", e)
        return jerr("server_error", 500)
    resp.headers["X-Content-Type-Options"] = "nosniff"
    if request.path.startswith("/api/"):
        resp.headers["Cache-Control"] = "no-store"
    return resp


@web.middleware
async def auth_mw(request, handler):
    if not request.path.startswith("/api/"):
        return await handler(request)
    h = request.headers.get("Authorization", "")
    if not h.startswith("tma "):
        raise ApiError("unauthorized", 401)
    user = validate_init_data(h[4:])
    if not user:
        raise ApiError("unauthorized", 401)  # initData نامعتبر/منقضی
    uid = int(user["id"])
    if uid not in allowed_ids():
        raise ApiError("forbidden", 403)
    q, nowt = RATE[uid], time.time()
    while q and nowt - q[0] > RATE_WINDOW:
        q.popleft()
    if len(q) >= RATE_LIMIT:
        raise ApiError("rate_limited", 429)
    q.append(nowt)
    request["uid"] = uid
    request["is_admin"] = uid == ADMIN_ID
    await ensure_user(uid)
    return await handler(request)


async def jbody(request):
    try:
        d = await request.json()
        if isinstance(d, dict):
            return d
    except Exception:
        pass
    raise ApiError("bad_json", 400)


def need_admin(request):
    if not request["is_admin"]:
        raise ApiError("admin_only", 403)


def s_field(d, k, maxlen, required=False):
    v = d.get(k, "")
    v = v.strip() if isinstance(v, str) else ""
    if required and not v:
        raise ApiError(f"{k}_required", 400)
    if len(v) > maxlen:
        raise ApiError(f"{k}_too_long", 400)
    return v


def iso_date(v):
    try:
        return date.fromisoformat(v).isoformat()
    except Exception:
        raise ApiError("bad_date", 400)


# ───────────────────────── API ─────────────────────────
routes = web.RouteTableDef()


@routes.get("/")
async def index(request):
    csp = ("default-src 'self'; script-src 'self' 'unsafe-inline' https://telegram.org; "
           "style-src 'self' 'unsafe-inline' https://fonts.googleapis.com; font-src https://fonts.gstatic.com; "
           "img-src 'self' blob: data:; media-src 'self' blob:; connect-src 'self'; object-src 'none'; base-uri 'none'")
    return web.FileResponse(WEBAPP_FILE, headers={"Cache-Control": "no-cache", "Content-Security-Policy": csp, "Referrer-Policy": "no-referrer"})


@routes.get("/health")
async def health(request):
    return web.json_response({"ok": True})


@routes.get("/api/me")
async def api_me(request):
    u = await ensure_user(request["uid"])
    unread = (await q_one("SELECT COUNT(*) c FROM letters WHERE read_at IS NULL"))["c"] if request["uid"] == ALLOWED_USER_ID else 0
    return web.json_response({"unread_letters": unread, "uid": request["uid"], "is_admin": request["is_admin"],
                              "needs_consent": request["uid"] == ALLOWED_USER_ID, "consent": bool(u["consent"]),
                              "paused": bool(u["paused"]), "privacy_text": PRIVACY_TEXT, "timezone": str(TZ)})


@routes.post("/api/consent")
async def api_consent(request):
    d = await jbody(request)
    if d.get("accept") is True:
        await q_exec("UPDATE users SET consent=1,consent_at=? WHERE id=?", (ts(), request["uid"]))
    else:
        await q_exec("UPDATE users SET consent=0 WHERE id=?", (request["uid"],))
    return web.json_response({"ok": True})


@routes.post("/api/pause")
async def api_pause(request):
    d = await jbody(request)
    await q_exec("UPDATE users SET paused=? WHERE id=?", (1 if d.get("paused") else 0, request["uid"]))
    return web.json_response({"ok": True})


@routes.post("/api/delete-all")
async def api_delete_all(request):
    d = await jbody(request)
    if d.get("confirm") is not True:
        raise ApiError("confirm_required", 400)
    uid = request["uid"]
    n = await delete_memories_where("owner_id=?", (uid,))
    files = [r["path"] for r in await q_all("SELECT path FROM media WHERE owner_id=?", (uid,))]
    await q_exec("DELETE FROM media WHERE owner_id=?", (uid,))
    unlink_media(files)
    return web.json_response({"deleted_memories": n, "deleted_files": len(files)})


@routes.get("/api/home")
async def api_home(request):
    return web.json_response(await build_home())


@routes.get("/api/memories")
async def api_mem_list(request):
    qp, uid = request.query, request["uid"]
    where, args = ["1=1"], []
    q = qp.get("q", "").strip()[:100]
    if q:
        where.append("(m.title LIKE ? ESCAPE '\\' OR m.body LIKE ? ESCAPE '\\')")
        args += [like(q), like(q)]
    if qp.get("from"):
        where.append("m.mem_date>=?"); args.append(iso_date(qp["from"]))
    if qp.get("to"):
        where.append("m.mem_date<=?"); args.append(iso_date(qp["to"]))
    t = qp.get("type", "")
    having = {"photo": "pc>0", "voice": "vc>0", "text": "pc=0 AND vc=0"}.get(t)
    sql = f"SELECT * FROM ({MEM_SELECT} WHERE {' AND '.join(where)})" + (f" WHERE {having}" if having else "") + " ORDER BY mem_date DESC, id DESC LIMIT 300"
    return web.json_response({"items": [mem_row_json(r, uid) for r in await q_all(sql, args)]})


@routes.get("/api/memories/{id}")
async def api_mem_get(request):
    r = await q_one(MEM_SELECT + " WHERE m.id=?", (int(request.match_info["id"]),))
    if not r:
        raise ApiError("not_found", 404)
    media = await q_all("SELECT * FROM media WHERE memory_id=? ORDER BY id", (r["id"],))
    out = mem_row_json(r, request["uid"])
    out["media"] = [media_json(m, request["uid"]) for m in media]
    return web.json_response(out)


def mem_fields(d):
    title = s_field(d, "title", 120, required=True)
    body = s_field(d, "body", 5000)
    md = iso_date(d["mem_date"]) if d.get("mem_date") else now_local().date().isoformat()
    return title, body, md


@routes.post("/api/memories")
async def api_mem_create(request):
    uid = request["uid"]
    await check_can_write(uid)
    title, body, md = mem_fields(await jbody(request))
    mid = await q_exec("INSERT INTO memories(owner_id,title,body,mem_date,created_at,updated_at) VALUES(?,?,?,?,?,?)", (uid, title, body, md, ts(), ts()))
    asyncio.create_task(notify_admin_memory(request.app["bot"], uid, title))
    return web.json_response({"id": mid})


@routes.put("/api/memories/{id}")
async def api_mem_update(request):
    uid, mid = request["uid"], int(request.match_info["id"])
    r = await q_one("SELECT owner_id FROM memories WHERE id=?", (mid,))
    if not r:
        raise ApiError("not_found", 404)
    if r["owner_id"] != uid:
        raise ApiError("forbidden", 403)
    await check_can_write(uid)
    title, body, md = mem_fields(await jbody(request))
    await q_exec("UPDATE memories SET title=?,body=?,mem_date=?,updated_at=? WHERE id=?", (title, body, md, ts(), mid))
    return web.json_response({"ok": True})


@routes.delete("/api/memories/{id}")
async def api_mem_delete(request):
    uid, mid = request["uid"], int(request.match_info["id"])
    r = await q_one("SELECT owner_id FROM memories WHERE id=?", (mid,))
    if not r:
        raise ApiError("not_found", 404)
    if r["owner_id"] != uid:
        raise ApiError("forbidden", 403)
    await delete_memories_where("id=?", (mid,))
    return web.json_response({"ok": True})


async def read_multipart(request):
    reader = await request.multipart()
    fields, file = {}, None
    limit = max(MAX_PHOTO, MAX_VOICE)
    while True:
        part = await reader.next()
        if part is None:
            break
        if part.name == "file":
            buf = bytearray()
            while True:
                chunk = await part.read_chunk(65536)
                if not chunk:
                    break
                buf += chunk
                if len(buf) > limit:
                    raise ApiError("file_too_large", 413)
            file = bytes(buf)
        elif part.name:
            fields[part.name] = (await part.text())[:1000]
    if not file:
        raise ApiError("file_required", 400)
    return fields, file


@routes.post("/api/media")
async def api_media_upload(request):
    uid = request["uid"]
    await check_can_write(uid)
    fields, file = await read_multipart(request)
    memory_id = None
    if fields.get("memory_id", "").isdigit():
        memory_id = int(fields["memory_id"])
        m = await q_one("SELECT owner_id FROM memories WHERE id=?", (memory_id,))
        if not m or m["owner_id"] != uid:
            raise ApiError("forbidden", 403)
    dur = int(fields["duration"]) if fields.get("duration", "").isdigit() else 0
    mid = await save_media(uid, file, fields.get("kind"), memory_id, fields.get("title", "").strip(), fields.get("caption", "").strip(), dur)
    return web.json_response({"id": mid})


MEDIA_SELECT = "SELECT a.*, m.title AS memory_title FROM media a LEFT JOIN memories m ON m.id=a.memory_id"


@routes.get("/api/media")
async def api_media_list(request):
    kind = request.query.get("kind")
    if kind not in ("photo", "voice"):
        raise ApiError("bad_kind", 400)
    rows = await q_all(MEDIA_SELECT + " WHERE a.kind=? ORDER BY a.id DESC LIMIT 500", (kind,))
    return web.json_response({"items": [media_json(r, request["uid"]) for r in rows]})


async def own_media(request):
    r = await q_one("SELECT * FROM media WHERE id=?", (int(request.match_info["id"]),))
    if not r:
        raise ApiError("not_found", 404)
    return r


@routes.get("/api/media/{id}/file")
async def api_media_file(request):
    r = await own_media(request)
    path = MEDIA_DIR / r["path"]
    if not path.is_file():
        raise ApiError("file_missing", 404)
    return web.FileResponse(path, headers={"Content-Type": r["mime"], "Cache-Control": "private, max-age=3600"})


@routes.patch("/api/media/{id}")
async def api_media_patch(request):
    r = await own_media(request)
    if r["owner_id"] != request["uid"]:
        raise ApiError("forbidden", 403)
    d = await jbody(request)
    title = s_field(d, "title", 120) if "title" in d else r["title"]
    caption = s_field(d, "caption", 500) if "caption" in d else r["caption"]
    memory_id = r["memory_id"]
    if "memory_id" in d:
        memory_id = d["memory_id"]
        if memory_id is not None:
            m = await q_one("SELECT owner_id FROM memories WHERE id=?", (memory_id,)) if isinstance(memory_id, int) else None
            if not m or m["owner_id"] != request["uid"]:
                raise ApiError("forbidden", 403)
    await q_exec("UPDATE media SET title=?,caption=?,memory_id=? WHERE id=?", (title, caption, memory_id, r["id"]))
    return web.json_response({"ok": True})


@routes.delete("/api/media/{id}")
async def api_media_delete(request):
    r = await own_media(request)
    if r["owner_id"] != request["uid"]:
        raise ApiError("forbidden", 403)
    await q_exec("DELETE FROM media WHERE id=?", (r["id"],))
    unlink_media([r["path"]])
    return web.json_response({"ok": True})


@routes.get("/api/letters")
async def api_letters(request):
    rows = await q_all("SELECT * FROM letters ORDER BY id DESC LIMIT 200")
    return web.json_response({"items": [{"id": r["id"], "title": r["title"], "body": r["body"], "read": bool(r["read_at"]),
                                         "jdate": fmt_j(datetime.strptime(r["created_at"], "%Y-%m-%d %H:%M:%S"))} for r in rows]})


@routes.post("/api/letters")
async def api_letter_create(request):
    need_admin(request)
    d = await jbody(request)
    title, body = s_field(d, "title", 120, True), s_field(d, "body", 5000, True)
    lid = await q_exec("INSERT INTO letters(title,body,created_at) VALUES(?,?,?)", (title, body, ts()))
    asyncio.create_task(notify_new_letter(request.app["bot"], title))
    return web.json_response({"id": lid})


@routes.post("/api/letters/{id}/read")
async def api_letter_read(request):
    if request["uid"] != ALLOWED_USER_ID:
        return web.json_response({"ok": True})  # فقط گیرنده علامت می‌زند
    await q_exec("UPDATE letters SET read_at=COALESCE(read_at,?) WHERE id=?", (ts(), int(request.match_info["id"])))
    return web.json_response({"ok": True})


@routes.delete("/api/letters/{id}")
async def api_letter_delete(request):
    need_admin(request)
    await q_exec("DELETE FROM letters WHERE id=?", (int(request.match_info["id"]),))
    return web.json_response({"ok": True})


@routes.get("/api/events")
async def api_events(request):
    return web.json_response({"items": await events_with_dates(now_local().date())})


@routes.post("/api/events")
async def api_event_create(request):
    need_admin(request)
    d = await jbody(request)
    title = s_field(d, "title", 80, True)
    try:
        jm, jd, repeat = int(d["jm"]), int(d["jd"]), bool(d.get("repeat"))
        jy = int(d["jy"]) if d.get("jy") else None
    except (KeyError, ValueError, TypeError):
        raise ApiError("bad_date", 400)
    if not (1 <= jm <= 12) or not 1 <= jd <= (31 if jm <= 6 else 30):
        raise ApiError("bad_date", 400)
    if repeat:
        eid = await q_exec("INSERT INTO events(title,repeat,jm,jd,created_at) VALUES(?,1,?,?,?)", (title, jm, jd, ts()))
    else:
        if not jy or not valid_jdate(jy, jm, jd):
            raise ApiError("bad_date", 400)
        eid = await q_exec("INSERT INTO events(title,repeat,jm,jd,gdate,created_at) VALUES(?,0,?,?,?,?)",
                           (title, jm, jd, date(*j2g(jy, jm, jd)).isoformat(), ts()))
    return web.json_response({"id": eid})


@routes.delete("/api/events/{id}")
async def api_event_delete(request):
    need_admin(request)
    await q_exec("DELETE FROM events WHERE id=?", (int(request.match_info["id"]),))
    return web.json_response({"ok": True})


@routes.post("/api/admin/start")
async def api_admin_start(request):
    need_admin(request)
    d = await jbody(request)
    try:
        jy, jm, jd = int(d["jy"]), int(d["jm"]), int(d["jd"])
    except (KeyError, ValueError, TypeError):
        raise ApiError("bad_date", 400)
    if not valid_jdate(jy, jm, jd):
        raise ApiError("bad_date", 400)
    await set_setting("start_date", date(*j2g(jy, jm, jd)).isoformat())
    return web.json_response({"ok": True})


async def admin_stats_data():
    return {
        "memories": (await q_one("SELECT COUNT(*) c FROM memories"))["c"],
        "voices": (await q_one("SELECT COUNT(*) c FROM media WHERE kind='voice'"))["c"],
        "photos": (await q_one("SELECT COUNT(*) c FROM media WHERE kind='photo'"))["c"],
        "letters": (await q_one("SELECT COUNT(*) c FROM letters"))["c"],
        "storage_mb": round(((await q_one("SELECT COALESCE(SUM(size),0) s FROM media"))["s"]) / 1048576, 2),
        "gemini": bool(GEMINI_API_KEY),
        "uptime_min": int((time.time() - STARTED_AT) / 60),
        "schedule": await q_all("SELECT kind,day,status,attempts,error,updated_at FROM schedule_log ORDER BY day DESC, kind LIMIT 8"),
        "errors": await q_all("SELECT ts,scope,message FROM error_log ORDER BY id DESC LIMIT 8"),
    }


@routes.get("/api/admin/stats")
async def api_admin_stats(request):
    need_admin(request)
    return web.json_response(await admin_stats_data())


# ───────────────────────── ربات ─────────────────────────
router = Router()
esc = html.escape

B_COUNT, B_DIARY, B_VOICE = "💗 روزشمار رابطه", "📖 دفتر خاطرات", "🎙 صدای تو"
B_GALLERY, B_LETTERS, B_EVENTS = "🖼 گالری عکس‌ها", "💌 نامه‌های عاشقانه", "🌷 روز دختر و مناسبت‌ها"
B_SPECIAL, B_APP, B_SETTINGS = "✨ پیام‌های ویژه", "🖥 باز کردن مینی‌اپ", "⚙️ تنظیمات"
MENU_TEXTS = {B_COUNT, B_DIARY, B_VOICE, B_GALLERY, B_LETTERS, B_EVENTS, B_SPECIAL, B_APP, B_SETTINGS}


def main_menu():
    k = [[B_COUNT, B_DIARY], [B_VOICE, B_GALLERY], [B_LETTERS, B_EVENTS], [B_SPECIAL, B_APP], [B_SETTINGS]]
    return ReplyKeyboardMarkup(keyboard=[[KeyboardButton(text=t) for t in row] for row in k], resize_keyboard=True)


def ikb(rows):
    return InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text=t, callback_data=c) if not c.startswith("webapp:")
                                                  else InlineKeyboardButton(text=t, web_app=WebAppInfo(url=WEBAPP_URL)) for t, c in row] for row in rows])


class NewMem(StatesGroup):
    title = State(); body = State(); photos = State(); voices = State(); confirm = State()


class SearchS(StatesGroup):
    q = State()


class NewVoice(StatesGroup):
    wait = State()


class AdLetter(StatesGroup):
    title = State(); body = State()


class AdMsg(StatesGroup):
    text = State()


class AdEvent(StatesGroup):
    title = State(); date = State()


class AdStart(StatesGroup):
    date = State()


class AccessMW(BaseMiddleware):
    async def __call__(self, handler, event, data):
        u = getattr(event, "from_user", None)
        if not u or u.id not in allowed_ids():
            if isinstance(event, Message):
                await event.answer("این ربات اختصاصی است و برای شما فعال نیست. 🔒")
            elif isinstance(event, CallbackQuery):
                await event.answer("دسترسی ندارید", show_alert=True)
            return None
        return await handler(event, data)


router.message.middleware(AccessMW())
router.callback_query.middleware(AccessMW())


def is_admin(uid):
    return uid == ADMIN_ID


async def notify_admin_memory(bot, uid, title):
    if uid != ADMIN_ID and ADMIN_ID:
        try:
            await bot.send_message(ADMIN_ID, f"📖 خاطره‌ی جدید ثبت شد: <b>{esc(title)}</b>")
        except Exception as e:
            await log_error("notify_admin", e)


async def notify_new_letter(bot, title):
    if not ALLOWED_USER_ID:
        return
    try:
        await bot.send_message(ALLOWED_USER_ID, f"💌 نامه‌ی تازه‌ای برایت رسیده: <b>{esc(title)}</b>",
                               reply_markup=ikb([[("💌 خواندن نامه‌ها", "lt:0")], [("🖥 باز کردن مینی‌اپ", "webapp:")]]) if WEBAPP_URL else ikb([[("💌 خواندن نامه‌ها", "lt:0")]]))
    except Exception as e:
        await log_error("notify_letter", e)


@router.message(CommandStart())
async def cmd_start(m: Message, state: FSMContext):
    await state.clear()
    await ensure_user(m.from_user.id)
    await m.answer("سلام ♡ به <b>«فقط برای تو»</b> خوش اومدی.\nاینجا فضای شخصی ماست: خاطره، ویس، عکس و نامه.", reply_markup=main_menu())


@router.message(Command("cancel"))
async def cmd_cancel(m: Message, state: FSMContext):
    await state.clear()
    await m.answer("لغو شد.", reply_markup=main_menu())


@router.message(Command("new"))
async def cmd_new(m: Message, state: FSMContext):
    await begin_memory(m, state, m.from_user.id)


@router.message(Command("admin"))
async def cmd_admin(m: Message, state: FSMContext):
    await state.clear()
    if not is_admin(m.from_user.id):
        return await m.answer("این بخش فقط برای مدیر است.")
    await show_admin(m)


@router.message(Command("setstart"))
async def cmd_setstart(m: Message):
    if not is_admin(m.from_user.id):
        return await m.answer("این بخش فقط برای مدیر است.")
    if not await do_set_start(m, (m.text or "").partition(" ")[2]):
        await m.answer("فرمت: /setstart ۱۴۰۲/۰۵/۱۲")


@router.message(F.text.in_(MENU_TEXTS))
async def on_menu(m: Message, state: FSMContext):
    await state.clear()
    t, uid = m.text, m.from_user.id
    if t == B_COUNT:
        await m.answer(await count_text())
    elif t == B_DIARY:
        await m.answer("📖 <b>دفتر خاطرات</b>", reply_markup=ikb([[("➕ ثبت خاطره", "nm:start"), ("📚 فهرست", "ml:0")], [("🔎 جست‌وجو", "ms:start")]]))
    elif t == B_VOICE:
        await m.answer("🎙 <b>صدای تو</b>", reply_markup=ikb([[("➕ ضبط/ارسال ویس جدید", "nv:start")], [("📚 فهرست ویس‌ها", "vl:0")]]))
    elif t == B_GALLERY:
        await send_gallery(m, 0)
    elif t == B_LETTERS:
        await show_letters(m, 0)
    elif t == B_EVENTS:
        await m.answer(await events_text())
    elif t == B_SPECIAL:
        await m.answer(esc(await make_message("special")))
    elif t == B_APP:
        await m.answer("برای باز کردن مینی‌اپ بزن 👇" if WEBAPP_URL else "آدرس مینی‌اپ (WEBAPP_URL) هنوز تنظیم نشده.",
                       reply_markup=ikb([[("🖥 باز کردن «فقط برای تو ♡»", "webapp:")]]) if WEBAPP_URL else None)
    elif t == B_SETTINGS:
        await show_settings(m, uid)


async def count_text():
    h = await build_home()
    if not h["start"]:
        return "💗 تاریخ شروع رابطه هنوز تنظیم نشده است. (مدیر با /setstart یا از پنل مدیر می‌تواند تنظیم کند.)"
    s, a = h["start"], h["anniversary"]
    txt = (f"💗 <b>روزشمار رابطه</b>\n\n<b>{fa(s['days'])}</b> روز با هم\n"
           f"({fa(s['years'])} سال، {fa(s['months'])} ماه و {fa(s['days_part'])} روز)\nشروع: {s['jdate']}\n")
    if a:
        txt += f"\n🎉 تا سالگرد بعدی ({a['jdate']}): <b>{fa(a['days_left'])}</b> روز" if a["days_left"] else "\n🎉 امروز سالگرد شماست!"
    return txt


async def events_text():
    evs = await events_with_dates(now_local().date())
    if not evs:
        return "🌷 هنوز مناسبتی ثبت نشده. مدیر می‌تواند از پنل مدیر اضافه کند."
    lines = ["🌷 <b>مناسبت‌ها</b>\n"]
    for e in evs:
        left = "امروز است! 🎉" if e["days_left"] == 0 else f"{fa(e['days_left'])} روز مانده"
        lines.append(f"• {esc(e['title'])} — {e['jdate']} — {left}")
    return "\n".join(lines)


# ----- تنظیمات و حریم خصوصی -----
async def show_settings(m, uid):
    u = await ensure_user(uid)
    rows = [[("🔒 سیاست حریم خصوصی", "st:privacy")],
            [("▶️ ادامه‌ی ثبت خاطرات" if u["paused"] else "⏸ توقف ثبت خاطرات", "st:pause")],
            [("🗑 درخواست حذف خاطرات من", "st:delask")]]
    if is_admin(uid):
        rows.append([("🛠 پنل مدیر", "ad:home")])
    status = ""
    if uid == ALLOWED_USER_ID:
        status = f"\nرضایت حریم خصوصی: {'✅ تأیید شده' if u['consent'] else '❌ هنوز تأیید نشده'}"
    await m.answer(f"⚙️ <b>تنظیمات</b>\nثبت خاطرات: {'⏸ متوقف' if u['paused'] else '▶️ فعال'}{status}", reply_markup=ikb(rows))


@router.callback_query(F.data.startswith("st:"))
async def cb_settings(cb: CallbackQuery):
    act, uid = cb.data.split(":")[1], cb.from_user.id
    await cb.answer()
    if act == "privacy":
        await cb.message.answer("🔒 <b>حریم خصوصی</b>\n\n" + esc(PRIVACY_TEXT))
    elif act == "pause":
        u = await ensure_user(uid)
        await q_exec("UPDATE users SET paused=? WHERE id=?", (0 if u["paused"] else 1, uid))
        await cb.message.answer("ثبت خاطرات ادامه پیدا کرد ▶️" if u["paused"] else "ثبت خاطرات متوقف شد ⏸ (خاطرات قبلی سر جایشان هستند).")
    elif act == "delask":
        await cb.message.answer("⚠️ همه‌ی خاطرات، عکس‌ها و ویس‌هایی که <b>خودت</b> ثبت کرده‌ای برای همیشه حذف می‌شود. مطمئنی؟",
                                reply_markup=ikb([[("🗑 بله، حذف شود", "st:delok"), ("انصراف", "st:no")]]))
    elif act == "delok":
        n = await delete_memories_where("owner_id=?", (uid,))
        files = [r["path"] for r in await q_all("SELECT path FROM media WHERE owner_id=?", (uid,))]
        await q_exec("DELETE FROM media WHERE owner_id=?", (uid,))
        unlink_media(files)
        await cb.message.answer(f"حذف شد: {fa(n)} خاطره و {fa(len(files))} فایل.")
    elif act == "no":
        await cb.message.answer("انصراف داده شد.")


@router.callback_query(F.data.startswith("consent:"))
async def cb_consent(cb: CallbackQuery, state: FSMContext):
    await cb.answer()
    if cb.data.endswith("yes"):
        await q_exec("UPDATE users SET consent=1,consent_at=? WHERE id=?", (ts(), cb.from_user.id))
        await cb.message.answer("ممنون ♡ رضایتت ثبت شد. حالا خاطره‌ات رو شروع می‌کنیم.")
        await begin_memory(cb.message, state, cb.from_user.id)
    else:
        await cb.message.answer("باشه، چیزی ذخیره نمی‌شود. هر وقت خواستی از «ثبت خاطره» دوباره شروع کن.")


# ----- ثبت خاطره -----
CANCEL_KB = ikb([[("❌ لغو", "nm:cancel")]])
NEXT_KB = ikb([[("➡️ ادامه / رد شدن", "nm:next")], [("❌ لغو", "nm:cancel")]])


async def begin_memory(target, state, uid):
    await state.clear()
    if uid == ALLOWED_USER_ID:
        u = await ensure_user(uid)
        if not u["consent"]:
            return await target.answer("🔒 <b>حریم خصوصی</b>\n\n" + esc(PRIVACY_TEXT),
                                       reply_markup=ikb([[("✅ موافقم", "consent:yes"), ("❌ موافق نیستم", "consent:no")]]))
        if u["paused"]:
            return await target.answer("ثبت خاطرات الان متوقف است. از «⚙️ تنظیمات» می‌توانی ادامه‌اش بدهی.")
    await state.set_state(NewMem.title)
    await target.answer("📝 عنوان خاطره چیست؟", reply_markup=CANCEL_KB)


@router.callback_query(F.data == "nm:start")
async def cb_nm_start(cb: CallbackQuery, state: FSMContext):
    await cb.answer()
    await begin_memory(cb.message, state, cb.from_user.id)


@router.callback_query(F.data == "nm:cancel")
async def cb_nm_cancel(cb: CallbackQuery, state: FSMContext):
    await cb.answer()
    await state.clear()
    await cb.message.answer("لغو شد.", reply_markup=main_menu())


@router.message(NewMem.title, F.text)
async def nm_title(m: Message, state: FSMContext):
    if len(m.text) > 120:
        return await m.answer("عنوان باید حداکثر ۱۲۰ نویسه باشد.")
    await state.update_data(title=m.text.strip(), photos=[], voices=[])
    await state.set_state(NewMem.body)
    await m.answer("✍️ حالا متن خاطره را بنویس:", reply_markup=CANCEL_KB)


@router.message(NewMem.body, F.text)
async def nm_body(m: Message, state: FSMContext):
    if len(m.text) > 5000:
        return await m.answer("متن باید حداکثر ۵۰۰۰ نویسه باشد.")
    await state.update_data(body=m.text.strip())
    await state.set_state(NewMem.photos)
    await m.answer("🖼 اگر عکسی داری بفرست (می‌توانی چند عکس بفرستی). وگرنه «ادامه» را بزن.", reply_markup=NEXT_KB)


@router.message(NewMem.photos, F.photo)
async def nm_photo(m: Message, state: FSMContext):
    d = await state.get_data()
    d["photos"].append(m.photo[-1].file_id)
    await state.update_data(photos=d["photos"])
    await m.answer(f"عکس {fa(len(d['photos']))} اضافه شد. عکس دیگری بفرست یا «ادامه» را بزن.", reply_markup=NEXT_KB)


@router.message(NewMem.voices, F.voice)
async def nm_voice(m: Message, state: FSMContext):
    if (m.voice.file_size or 0) > MAX_VOICE:
        return await m.answer("حجم این ویس بیشتر از ۱۵ مگابایت است.")
    d = await state.get_data()
    d["voices"].append((m.voice.file_id, m.voice.duration or 0))
    await state.update_data(voices=d["voices"])
    await m.answer(f"ویس {fa(len(d['voices']))} اضافه شد. ویس دیگری بفرست یا «ادامه» را بزن.", reply_markup=NEXT_KB)


@router.message(NewMem.photos)
async def nm_photo_hint(m: Message):
    await m.answer("لطفاً عکس بفرست یا «ادامه» را بزن.", reply_markup=NEXT_KB)


@router.message(NewMem.voices)
async def nm_voice_hint(m: Message):
    await m.answer("لطفاً یک ویس واقعی بفرست (دکمه‌ی میکروفون تلگرام) یا «ادامه» را بزن.", reply_markup=NEXT_KB)


@router.message(NewMem.title)
@router.message(NewMem.body)
async def nm_text_hint(m: Message):
    await m.answer("لطفاً متن بفرست.", reply_markup=CANCEL_KB)


@router.callback_query(F.data == "nm:next")
async def cb_nm_next(cb: CallbackQuery, state: FSMContext):
    await cb.answer()
    st = await state.get_state()
    if st == NewMem.photos.state:
        await state.set_state(NewMem.voices)
        return await cb.message.answer("🎙 اگر ویس داری بفرست (همان ویس واقعی تلگرام). وگرنه «ادامه» را بزن.", reply_markup=NEXT_KB)
    if st == NewMem.voices.state:
        d = await state.get_data()
        await state.set_state(NewMem.confirm)
        return await cb.message.answer(
            f"📋 <b>{esc(d['title'])}</b>\n\n{esc(d['body'])}\n\n🖼 {fa(len(d['photos']))} عکس · 🎙 {fa(len(d['voices']))} ویس\n\nذخیره شود؟",
            reply_markup=ikb([[("✅ تأیید و ذخیره", "nm:save"), ("❌ لغو", "nm:cancel")]]))


@router.callback_query(F.data == "nm:save", NewMem.confirm)
async def cb_nm_save(cb: CallbackQuery, state: FSMContext, bot: Bot):
    await cb.answer()
    uid = cb.from_user.id
    d = await state.get_data()
    await state.clear()
    try:
        await check_can_write(uid)
    except ApiError:
        return await cb.message.answer("ذخیره ممکن نیست (رضایت یا توقف ثبت). از تنظیمات بررسی کن.", reply_markup=main_menu())
    mid = await q_exec("INSERT INTO memories(owner_id,title,body,mem_date,created_at,updated_at) VALUES(?,?,?,?,?,?)",
                       (uid, d["title"], d["body"], now_local().date().isoformat(), ts(), ts()))
    failed = 0
    for fid in d["photos"]:
        try:
            data = (await bot.download(fid, destination=io.BytesIO())).getvalue()
            await save_media(uid, data, "photo", mid, d["title"])
        except Exception as e:
            failed += 1
            await log_error("save_photo", e)
    for fid, dur in d["voices"]:
        try:
            data = (await bot.download(fid, destination=io.BytesIO())).getvalue()
            await save_media(uid, data, "voice", mid, d["title"], duration=dur)
        except Exception as e:
            failed += 1
            await log_error("save_voice", e)
    await cb.message.answer("✅ خاطره ذخیره شد و در مینی‌اپ هم دیده می‌شود ♡" + (f"\n⚠️ {fa(failed)} فایل ذخیره نشد." if failed else ""), reply_markup=main_menu())
    await notify_admin_memory(bot, uid, d["title"])


# ----- فهرست و نمایش خاطرات -----
async def mem_page(target, page, edit=False):
    total = (await q_one("SELECT COUNT(*) c FROM memories"))["c"]
    rows = await q_all("SELECT id,title,mem_date FROM memories ORDER BY mem_date DESC,id DESC LIMIT ? OFFSET ?", (PAGE, page * PAGE))
    if not rows:
        return await target.answer("هنوز خاطره‌ای ثبت نشده.")
    kb = [[(f"📖 {r['title'][:40]} — {fmt_j(date.fromisoformat(r['mem_date']))}", f"mv:{r['id']}")] for r in rows]
    nav = []
    if page > 0:
        nav.append(("◀️ قبلی", f"ml:{page - 1}"))
    if (page + 1) * PAGE < total:
        nav.append(("بعدی ▶️", f"ml:{page + 1}"))
    if nav:
        kb.append(nav)
    text = f"📚 <b>خاطرات</b> ({fa(total)})"
    if edit:
        try:
            return await target.edit_text(text, reply_markup=ikb(kb))
        except Exception:
            pass
    await target.answer(text, reply_markup=ikb(kb))


@router.callback_query(F.data.startswith("ml:"))
async def cb_ml(cb: CallbackQuery):
    await cb.answer()
    await mem_page(cb.message, int(cb.data.split(":")[1]), edit=True)


@router.callback_query(F.data == "ms:start")
async def cb_ms(cb: CallbackQuery, state: FSMContext):
    await cb.answer()
    await state.set_state(SearchS.q)
    await cb.message.answer("🔎 چه چیزی را جست‌وجو کنم؟ (عنوان یا متن)", reply_markup=CANCEL_KB)


@router.message(SearchS.q, F.text)
async def ms_query(m: Message, state: FSMContext):
    await state.clear()
    q = m.text.strip()[:100]
    rows = await q_all("SELECT id,title,mem_date FROM memories WHERE title LIKE ? ESCAPE '\\' OR body LIKE ? ESCAPE '\\' ORDER BY mem_date DESC LIMIT 10", (like(q), like(q)))
    if not rows:
        return await m.answer("چیزی پیدا نشد.", reply_markup=main_menu())
    await m.answer(f"نتیجه‌ها برای «{esc(q)}»:", reply_markup=ikb([[(f"📖 {r['title'][:40]} — {fmt_j(date.fromisoformat(r['mem_date']))}", f"mv:{r['id']}")] for r in rows]))


@router.callback_query(F.data.startswith("mv:"))
async def cb_mv(cb: CallbackQuery):
    await cb.answer()
    r = await q_one(MEM_SELECT + " WHERE m.id=?", (int(cb.data.split(":")[1]),))
    if not r:
        return await cb.message.answer("این خاطره پیدا نشد.")
    row = []
    if r["vc"]:
        row.append((f"🎙 ویس‌ها ({fa(r['vc'])})", f"mp:v:{r['id']}"))
    if r["pc"]:
        row.append((f"🖼 عکس‌ها ({fa(r['pc'])})", f"mp:p:{r['id']}"))
    kb = [row] if row else []
    if r["owner_id"] == cb.from_user.id:
        kb.append([("🗑 حذف خاطره", f"md:{r['id']}")])
    who = "از طرف مدیر" if r["owner_id"] == ADMIN_ID else "از طرف کاربر"
    await cb.message.answer(f"📖 <b>{esc(r['title'])}</b>\n🗓 {fmt_j(date.fromisoformat(r['mem_date']))} · {who}\n\n{esc(r['body'])}", reply_markup=ikb(kb) if kb else None)


async def send_media_row(bot, chat_id, r, caption=None):
    path = MEDIA_DIR / r["path"]
    if not path.is_file():
        return await bot.send_message(chat_id, "⚠️ فایل پیدا نشد.")
    if r["kind"] == "photo":
        return await bot.send_photo(chat_id, FSInputFile(path), caption=caption)
    try:
        if r["mime"] == "audio/ogg":
            return await bot.send_voice(chat_id, FSInputFile(path), caption=caption)
        return await bot.send_audio(chat_id, FSInputFile(path), caption=caption)
    except Exception:
        return await bot.send_document(chat_id, FSInputFile(path), caption=caption)


@router.callback_query(F.data.startswith("mp:"))
async def cb_mp(cb: CallbackQuery, bot: Bot):
    await cb.answer()
    _, kind, mid = cb.data.split(":")
    rows = await q_all("SELECT * FROM media WHERE memory_id=? AND kind=? ORDER BY id", (int(mid), "photo" if kind == "p" else "voice"))
    for r in rows:
        await send_media_row(bot, cb.message.chat.id, r, esc(r["title"]) or None)


@router.callback_query(F.data.startswith("md:"))
async def cb_md(cb: CallbackQuery):
    await cb.answer()
    await cb.message.answer("⚠️ این خاطره با همه‌ی عکس‌ها و ویس‌هایش برای همیشه حذف شود؟",
                            reply_markup=ikb([[("🗑 بله، حذف شود", f"mdok:{cb.data.split(':')[1]}"), ("انصراف", "st:no")]]))


@router.callback_query(F.data.startswith("mdok:"))
async def cb_mdok(cb: CallbackQuery):
    await cb.answer()
    mid = int(cb.data.split(":")[1])
    n = await delete_memories_where("id=? AND owner_id=?", (mid, cb.from_user.id))
    await cb.message.answer("🗑 حذف شد." if n else "امکان حذف این خاطره برای تو نیست.")


# ----- صدا -----
@router.callback_query(F.data == "nv:start")
async def cb_nv(cb: CallbackQuery, state: FSMContext):
    await cb.answer()
    try:
        await check_can_write(cb.from_user.id)
    except ApiError:
        return await cb.message.answer("ابتدا با «ثبت خاطره» رضایت حریم خصوصی را تأیید کن (یا ثبت متوقف است).")
    await state.set_state(NewVoice.wait)
    await cb.message.answer("🎙 ویس واقعی‌ات را بفرست.", reply_markup=CANCEL_KB)


@router.message(NewVoice.wait, F.voice)
async def nv_voice(m: Message, state: FSMContext, bot: Bot):
    await state.clear()
    if (m.voice.file_size or 0) > MAX_VOICE:
        return await m.answer("حجم ویس بیشتر از ۱۵ مگابایت است.")
    try:
        data = (await bot.download(m.voice.file_id, destination=io.BytesIO())).getvalue()
        await save_media(m.from_user.id, data, "voice", None, f"ویس {fmt_j(now_local())}", duration=m.voice.duration or 0)
        await m.answer("✅ ویس در «صدای تو» ذخیره شد ♡", reply_markup=main_menu())
    except Exception as e:
        await log_error("nv_voice", e)
        await m.answer("ذخیره‌ی ویس ناموفق بود. دوباره تلاش کن.")


@router.message(NewVoice.wait)
async def nv_hint(m: Message):
    await m.answer("لطفاً یک ویس بفرست.", reply_markup=CANCEL_KB)


@router.callback_query(F.data.startswith("vl:"))
async def cb_vl(cb: CallbackQuery):
    await cb.answer()
    page = int(cb.data.split(":")[1])
    rows = await q_all("SELECT * FROM media WHERE kind='voice' ORDER BY id DESC LIMIT ? OFFSET ?", (PAGE, page * PAGE))
    if not rows:
        return await cb.message.answer("هنوز ویسی ذخیره نشده.")
    total = (await q_one("SELECT COUNT(*) c FROM media WHERE kind='voice'"))["c"]
    kb = [[(f"🎙 {r['title'][:30] or 'ویس'} ({fa(r['duration'])}ث)", f"vp:{r['id']}")] for r in rows]
    if (page + 1) * PAGE < total:
        kb.append([("بعدی ▶️", f"vl:{page + 1}")])
    await cb.message.answer(f"🎙 <b>ویس‌ها</b> ({fa(total)})", reply_markup=ikb(kb))


@router.callback_query(F.data.startswith("vp:"))
async def cb_vp(cb: CallbackQuery, bot: Bot):
    await cb.answer()
    r = await q_one("SELECT * FROM media WHERE id=?", (int(cb.data.split(":")[1]),))
    if r:
        await send_media_row(bot, cb.message.chat.id, r, esc(r["title"]) or None)


# ----- گالری -----
async def send_gallery(m, page):
    rows = await q_all("SELECT * FROM media WHERE kind='photo' ORDER BY id DESC LIMIT 6 OFFSET ?", (page * 6,))
    if not rows:
        return await m.answer("هنوز عکسی ثبت نشده.")
    files = [r for r in rows if (MEDIA_DIR / r["path"]).is_file()]
    if len(files) == 1:
        await m.answer_photo(FSInputFile(MEDIA_DIR / files[0]["path"]), caption=esc(files[0]["title"]) or None)
    elif files:
        await m.answer_media_group([InputMediaPhoto(media=FSInputFile(MEDIA_DIR / r["path"]), caption=esc(r["title"]) or None) for r in files])
    total = (await q_one("SELECT COUNT(*) c FROM media WHERE kind='photo'"))["c"]
    if (page + 1) * 6 < total:
        await m.answer(f"🖼 {fa(total)} عکس ثبت شده.", reply_markup=ikb([[("عکس‌های قدیمی‌تر ▶️", f"gl:{page + 1}")]]))


@router.callback_query(F.data.startswith("gl:"))
async def cb_gl(cb: CallbackQuery):
    await cb.answer()
    await send_gallery(cb.message, int(cb.data.split(":")[1]))


# ----- نامه‌ها -----
async def show_letters(m, page):
    rows = await q_all("SELECT * FROM letters ORDER BY id DESC LIMIT ? OFFSET ?", (PAGE, page * PAGE))
    if not rows:
        return await m.answer("💌 هنوز نامه‌ای نیست.")
    total = (await q_one("SELECT COUNT(*) c FROM letters"))["c"]
    kb = [[(("💌 " if not r["read_at"] else "📭 ") + (r["title"] or "نامه")[:40], f"lv:{r['id']}")] for r in rows]
    if (page + 1) * PAGE < total:
        kb.append([("بعدی ▶️", f"lt:{page + 1}")])
    await m.answer("💌 <b>نامه‌ها</b>", reply_markup=ikb(kb))


@router.callback_query(F.data.startswith("lt:"))
async def cb_lt(cb: CallbackQuery):
    await cb.answer()
    await show_letters(cb.message, int(cb.data.split(":")[1]))


@router.callback_query(F.data.startswith("lv:"))
async def cb_lv(cb: CallbackQuery):
    await cb.answer()
    r = await q_one("SELECT * FROM letters WHERE id=?", (int(cb.data.split(":")[1]),))
    if not r:
        return await cb.message.answer("نامه پیدا نشد.")
    if cb.from_user.id == ALLOWED_USER_ID:
        await q_exec("UPDATE letters SET read_at=COALESCE(read_at,?) WHERE id=?", (ts(), r["id"]))
    await cb.message.answer(f"💌 <b>{esc(r['title'] or 'نامه')}</b>\n{fmt_j(date.fromisoformat(r['created_at'][:10]))}\n\n{esc(r['body'])}")


# ----- پشتیبان‌گیری (فقط دیتابیس؛ فایل‌های عکس/ویس روی Volume می‌مانند) -----
async def send_backup(bot, chat_id):
    out = DATA_DIR / f"backup-{now_local():%Y%m%d-%H%M%S}.db"

    def _do():
        src, dst = sqlite3.connect(DB_PATH), sqlite3.connect(out)
        try:
            src.backup(dst)
        finally:
            dst.close()
            src.close()
    try:
        await asyncio.to_thread(_do)
        await bot.send_document(chat_id, FSInputFile(out), caption="💾 پشتیبان دیتابیس (بدون عکس‌ها و ویس‌ها). آن را جای امن نگه دار.")
    finally:
        out.unlink(missing_ok=True)


@router.message(Command("backup"))
async def cmd_backup(m: Message, bot: Bot):
    if not is_admin(m.from_user.id):
        return await m.answer("این بخش فقط برای مدیر است.")
    await send_backup(bot, m.chat.id)


# ----- پنل مدیر -----
async def show_admin(m):
    await m.answer("🛠 <b>پنل مدیر</b>", reply_markup=ikb([
        [("📊 آمار", "ad:stats"), ("🗂 مشاهده خاطرات", "ml:0")],
        [("✉️ ارسال نامه", "ad:letter"), ("💬 پیام اختصاصی", "ad:msg")],
        [("📅 افزودن مناسبت", "ad:event"), ("🗓 تاریخ شروع رابطه", "ad:start")],
        [("🧾 زمان‌بندی و خطاها", "ad:sched"), ("💾 پشتیبان‌گیری", "ad:backup")]]))


@router.callback_query(F.data.startswith("ad:"))
async def cb_admin(cb: CallbackQuery, state: FSMContext, bot: Bot):
    await cb.answer()
    if not is_admin(cb.from_user.id):
        return await cb.message.answer("فقط مدیر.")
    act = cb.data.split(":")[1]
    if act == "home":
        await show_admin(cb.message)
    elif act == "stats":
        s = await admin_stats_data()
        await cb.message.answer(f"📊 <b>آمار</b>\nخاطرات: {fa(s['memories'])}\nویس‌ها: {fa(s['voices'])}\nعکس‌ها: {fa(s['photos'])}\n"
                                f"نامه‌ها: {fa(s['letters'])}\nحجم فایل‌ها: {fa(s['storage_mb'])} مگابایت")
    elif act == "backup":
        await send_backup(bot, cb.message.chat.id)
    elif act == "sched":
        s = await admin_stats_data()
        lines = [f"🧾 <b>زمان‌بندی</b> (Gemini: {'فعال' if s['gemini'] else 'غیرفعال، پیام‌های آماده'}؛ آپ‌تایم {fa(s['uptime_min'])} دقیقه)"]
        lines += [f"• {r['day']} {'صبح' if r['kind'] == 'morning' else 'شب'}: {r['status']} (تلاش {r['attempts']})" + (f" — {esc(r['error'] or '')[:80]}" if r["error"] else "") for r in s["schedule"]] or ["هنوز اجرایی ثبت نشده."]
        lines.append("\n⚠️ <b>آخرین خطاها</b>")
        lines += [f"• {r['ts']} [{esc(r['scope'])}] {esc(r['message'])[:100]}" for r in s["errors"]] or ["بدون خطا ✅"]
        await cb.message.answer("\n".join(lines))
    elif act == "letter":
        await state.set_state(AdLetter.title)
        await cb.message.answer("✉️ عنوان نامه؟", reply_markup=CANCEL_KB)
    elif act == "msg":
        await state.set_state(AdMsg.text)
        await cb.message.answer("💬 متن پیام اختصاصی را بنویس (مستقیم برای کاربر ارسال می‌شود):", reply_markup=CANCEL_KB)
    elif act == "event":
        await state.set_state(AdEvent.title)
        await cb.message.answer("📅 عنوان مناسبت؟ (مثلاً «روز دختر»)", reply_markup=CANCEL_KB)
    elif act == "start":
        await state.set_state(AdStart.date)
        await cb.message.answer("🗓 تاریخ شروع رابطه را شمسی بنویس: سال/ماه/روز\nمثال: ۱۴۰۲/۰۵/۱۲", reply_markup=CANCEL_KB)


@router.message(AdLetter.title, F.text)
async def al_title(m: Message, state: FSMContext):
    await state.update_data(title=m.text.strip()[:120])
    await state.set_state(AdLetter.body)
    await m.answer("متن نامه را بنویس:", reply_markup=CANCEL_KB)


@router.message(AdLetter.body, F.text)
async def al_body(m: Message, state: FSMContext, bot: Bot):
    d = await state.get_data()
    await state.clear()
    await q_exec("INSERT INTO letters(title,body,created_at) VALUES(?,?,?)", (d["title"], m.text.strip()[:5000], ts()))
    await m.answer("✅ نامه ثبت و برای کاربر اعلان فرستاده شد.", reply_markup=main_menu())
    await notify_new_letter(bot, d["title"])


@router.message(AdMsg.text, F.text)
async def am_text(m: Message, state: FSMContext, bot: Bot):
    await state.clear()
    try:
        await bot.send_message(ALLOWED_USER_ID, esc(m.text))
        await m.answer("✅ ارسال شد.", reply_markup=main_menu())
    except Exception as e:
        await log_error("admin_msg", e)
        await m.answer("ارسال نشد (احتمالاً کاربر هنوز /start را نزده).")


@router.message(AdEvent.title, F.text)
async def ae_title(m: Message, state: FSMContext):
    await state.update_data(title=m.text.strip()[:80])
    await state.set_state(AdEvent.date)
    await m.answer("تاریخ شمسی را بنویس:\n• هر سال تکرار شود: <b>ماه/روز</b> مثل ۰۲/۰۵\n• فقط یک بار: <b>سال/ماه/روز</b> مثل ۱۴۰۵/۰۲/۰۵\n"
                   "(تاریخ مناسبت‌های قمری مثل روز دختر را هر سال از تقویم رسمی ببین و با نوع «فقط یک بار» ثبت کن.)", reply_markup=CANCEL_KB)


@router.message(AdEvent.date, F.text)
async def ae_date(m: Message, state: FSMContext):
    p = parse_jparts(m.text)
    d = await state.get_data()
    if p and len(p) == 2 and 1 <= p[0] <= 12 and 1 <= p[1] <= (31 if p[0] <= 6 else 30):
        await q_exec("INSERT INTO events(title,repeat,jm,jd,created_at) VALUES(?,1,?,?,?)", (d["title"], p[0], p[1], ts()))
    elif p and len(p) == 3 and valid_jdate(*p):
        await q_exec("INSERT INTO events(title,repeat,jm,jd,gdate,created_at) VALUES(?,0,?,?,?,?)", (d["title"], p[1], p[2], date(*j2g(*p)).isoformat(), ts()))
    else:
        return await m.answer("تاریخ نامعتبر است. دوباره بنویس (مثل ۰۲/۰۵ یا ۱۴۰۵/۰۲/۰۵).", reply_markup=CANCEL_KB)
    await state.clear()
    await m.answer("✅ مناسبت ثبت شد.", reply_markup=main_menu())


async def do_set_start(m, text):
    p = parse_jparts(text)
    if not p or len(p) != 3 or not valid_jdate(*p):
        return False
    await set_setting("start_date", date(*j2g(*p)).isoformat())
    await m.answer(f"✅ تاریخ شروع رابطه: {fmt_j(date(*j2g(*p)))}", reply_markup=main_menu())
    return True


@router.message(AdStart.date, F.text)
async def as_date(m: Message, state: FSMContext):
    if await do_set_start(m, m.text):
        await state.clear()
    else:
        await m.answer("تاریخ نامعتبر است. مثل ۱۴۰۲/۰۵/۱۲ بنویس.", reply_markup=CANCEL_KB)


@router.error()
async def on_error(event: ErrorEvent):
    await log_error("bot_handler", repr(event.exception))
    upd = event.update
    try:
        if upd.message:
            await upd.message.answer("⚠️ مشکلی پیش آمد؛ دوباره امتحان کن. (گزارش خطا برای مدیر ثبت شد)")
        elif upd.callback_query:
            await upd.callback_query.answer("⚠️ مشکلی پیش آمد؛ دوباره امتحان کن.", show_alert=True)
    except Exception:
        pass
    return True


@router.message()
async def fallback(m: Message):
    await m.answer("از منوی پایین یکی را انتخاب کن ♡", reply_markup=main_menu())


# ───────────────────────── راه‌اندازی ─────────────────────────
async def main():
    global HTTP
    problems = [n for n, v in (("BOT_TOKEN", BOT_TOKEN), ("ADMIN_ID", ADMIN_ID), ("ALLOWED_USER_ID", ALLOWED_USER_ID), ("WEBAPP_URL", WEBAPP_URL)) if not v]
    if problems:
        raise SystemExit("متغیرهای محیطی تنظیم نشده: " + ", ".join(problems))
    if not WEBAPP_URL.startswith("https://"):
        raise SystemExit("WEBAPP_URL باید با https:// شروع شود.")
    if _db_url.startswith("postgres"):
        log.warning("DATABASE_URL از نوع PostgreSQL است ولی این نسخه فقط SQLite دارد؛ از DB_PATH روی Volume استفاده می‌شود.")
    await init_db()
    HTTP = aiohttp.ClientSession()
    bot = Bot(BOT_TOKEN, default=DefaultBotProperties(parse_mode=ParseMode.HTML))
    dp = Dispatcher(storage=MemoryStorage())
    dp.include_router(router)

    app = web.Application(middlewares=[error_mw, auth_mw])
    app["bot"] = bot
    app.add_routes(routes)
    runner = web.AppRunner(app)
    await runner.setup()
    await web.TCPSite(runner, "0.0.0.0", PORT).start()
    log.info("web server on :%s", PORT)

    await bot.delete_webhook(drop_pending_updates=False)
    await bot.set_my_commands([BotCommand(command="start", description="شروع"), BotCommand(command="new", description="ثبت خاطره"),
                               BotCommand(command="cancel", description="لغو"), BotCommand(command="admin", description="پنل مدیر"), BotCommand(command="backup", description="پشتیبان دیتابیس (مدیر)")])
    menu = MenuButtonWebApp(text="فقط برای تو ♡", web_app=WebAppInfo(url=WEBAPP_URL))
    try:
        await bot.set_chat_menu_button(menu_button=menu)
    except Exception as e:
        await log_error("menu_button", e)
    for uid in allowed_ids():
        try:
            await bot.set_chat_menu_button(chat_id=uid, menu_button=menu)
        except Exception as e:
            log.warning("menu button for %s: %s", uid, e)

    sched = asyncio.create_task(scheduler_loop(bot))
    try:
        await dp.start_polling(bot, allowed_updates=dp.resolve_used_update_types())
    finally:
        sched.cancel()
        await runner.cleanup()
        await HTTP.close()
        await bot.session.close()
        await DB.close()


if __name__ == "__main__":
    asyncio.run(main())
