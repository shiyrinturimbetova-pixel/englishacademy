"""
English Academy Tutoring Bot.

Features:
  * Roles: Creator, Teacher, Supporter, Student. Students register once with an access code and a full name.
  * Tests: 10-60 questions, one time limit for the whole test, shuffled questions/options,
    24-hour lifetime, new-test alerts, practice attempts, review after the test ends
  * Ranks (10 levels), Daily / Weekly / Overall rankings
  * Announcements (to the group or to one student) with Preview + Publish
  * Rankings as a leaderboard picture (Today / Week / Overall); group: /rankings, daily digest
  * Creator panel: settings, users, roles, all tests, statistics, rankings, security,
    backup & restore, notifications
  * Mandatory subscription: students must join the required channels (managed in Security & Access)
  * Safety: automatic backup pinned in the Creator's chat, restored by itself on a fresh server

Run locally:   python bot.py          (needs a .env file next to this file)
Environment:   BOT_TOKEN, CREATOR_ID (required), TEACHER_IDS, SUPPORTER_IDS (optional),
               DB_PATH (optional), PORT (set by Render; opens a small health-check page),
               BUTTON_COLORS=0 (optional; switches the colored buttons off)
"""

import asyncio
import logging
import os
import random
import re
import sqlite3
import shutil
import sys
import tempfile
import time
from contextlib import contextmanager
from datetime import datetime, timedelta, timezone
from html import escape

from dotenv import load_dotenv

from aiogram import BaseMiddleware, Bot, Dispatcher, F, Router
from aiogram.client.default import DefaultBotProperties
from aiogram.enums import ParseMode
from aiogram.exceptions import TelegramAPIError, TelegramBadRequest, TelegramRetryAfter, TelegramUnauthorizedError
from aiogram.filters import Command, CommandStart, Filter, StateFilter
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
from aiogram.fsm.storage.memory import MemoryStorage
from aiogram.types import (
    BotCommand,
    BotCommandScopeAllGroupChats,
    BufferedInputFile,
    CallbackQuery,
    ErrorEvent,
    FSInputFile,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    InputMediaDocument,
    InputMediaPhoto,
    Message,
    TelegramObject,
)

# ============================================================================
# Configuration
# ============================================================================

load_dotenv()


def parse_ids(raw: str) -> list[int]:
    """'123, 456 789' -> [123, 456, 789]. Invalid parts are ignored."""
    ids = []
    for part in re.split(r"[,\s;]+", raw or ""):
        if part.strip().lstrip("-").isdigit():
            ids.append(int(part))
    return ids


BOT_TOKEN = (os.getenv("BOT_TOKEN") or "").strip()
CREATOR_RAW = (os.getenv("CREATOR_ID") or "").strip()
TEACHER_IDS = parse_ids(os.getenv("TEACHER_IDS", ""))
SUPPORTER_IDS = parse_ids(os.getenv("SUPPORTER_IDS", ""))
DB_PATH = os.getenv("DB_PATH", "academy.db")
BUTTON_COLORS = os.getenv("BUTTON_COLORS", "1") != "0"  # set BUTTON_COLORS=0 to switch colored buttons off

if not BOT_TOKEN or ":" not in BOT_TOKEN:
    sys.exit("ERROR: BOT_TOKEN is missing or invalid. Open the .env file and paste the token from @BotFather.")
if not CREATOR_RAW.lstrip("-").isdigit():
    sys.exit("ERROR: CREATOR_ID is missing or is not a number. Open the .env file and check it.")
CREATOR_ID = int(CREATOR_RAW)

TZ = timezone(timedelta(hours=5))  # Uzbekistan time (UTC+5, no daylight saving)
LINE = "━━━━━━━━━━━━━━"
OPTS = ("A", "B", "C", "D")
MEDALS = {1: "🥇", 2: "🥈", 3: "🥉"}

ANY_ROLE = ("student", "teacher", "supporter", "creator")
STAFF = ("teacher", "supporter", "creator")
TS = ("teacher", "supporter")
ROLE_LABEL = {"creator": "Creator", "teacher": "Teacher", "supporter": "Supporter", "student": "Student"}

MAX_CHANNELS = 5    # required channels for the mandatory subscription
PAGE = 6            # items per page in lists
PAGE_STUDENTS = 8   # students per page
REVIEW_PAGE = 4     # questions per page in Review Answers
MIN_TEST_MIN = 1    # shortest test duration, minutes
MAX_TEST_MIN = 720  # longest test duration, minutes (12 hours)
LEGACY_Q_SECONDS = 30  # only for old tests that were created with per-question times
GRACE = 2           # seconds of tolerance for slow connections

# Default values; written to the `settings` table only if they do not exist yet.
DEFAULT_SETTINGS = {
    "teacher_url": "https://t.me/positive_b",
    "supporter_url": "https://t.me/Qanatbek_Bekmuratov",
    "creator_url": "https://t.me/lowlyskill",
    "points_per_correct": "5",
    "min_questions": "10",
    "max_questions": "60",
    "rank_thresholds": "0:Newcomer,100:Noob,200:Rookie,300:Beginner,400:Learner,"
                       "500:Intermediate,600:Advanced,700:Expert,800:Master,"
                       "900:Grandmaster,1000:Max Level",
    "group_chat_id": "",
    "post_results": "1",
    "auto_reports": "1",
    "report_hour": "21",
    "test_lifetime_hours": "24",
    "registration_open": "1",
    "notify_new_test": "1",
    "notify_registration": "1",
    "notify_test_published": "1",
    "access_code": "0010",
    "auto_backup": "1",
    "backup_msg_id": "",
    "last_digest_at": "",
    "last_daily": "",
    "last_weekly": "",
}

# Settings the Creator can edit in Bot Settings: key -> (button label, kind, min, max)
# "range" (questions per test) and "reports" (group reports) are combined settings.
SETTING_DEFS = {
    "points_per_correct": ("Points per answer", "int", 1, 100),
    "rank_thresholds": ("Rank thresholds", "ranks", None, None),
    "questions_range": ("Questions per test", "range", None, None),
    "test_lifetime_hours": ("Test lifetime", "int", 1, 168),
    "post_results": ("Group results", "bool", None, None),
    "group_reports": ("Group reports", "reports", None, None),
}

# Notification switches in the Creator panel: key -> label
NOTIFY_DEFS = {
    "notify_new_test": "New test alert to students",
    "notify_registration": "New student registered",
    "notify_test_published": "Test published by staff",
    "auto_backup": "Automatic backup to you",
}

# ============================================================================
# Database
# ============================================================================

SCHEMA = """
CREATE TABLE IF NOT EXISTS users (
    tg_id         INTEGER PRIMARY KEY,
    full_name     TEXT,
    first_name    TEXT,
    last_name     TEXT,
    username      TEXT,
    registered_at TEXT,
    blocked       INTEGER DEFAULT 0
);
CREATE TABLE IF NOT EXISTS roles (
    tg_id    INTEGER PRIMARY KEY,
    role     TEXT NOT NULL,
    name     TEXT,
    added_at TEXT
);
CREATE TABLE IF NOT EXISTS tests (
    id         INTEGER PRIMARY KEY AUTOINCREMENT,
    title      TEXT NOT NULL,
    created_by INTEGER,
    status     TEXT NOT NULL DEFAULT 'published',
    time_limit INTEGER,
    created_at TEXT,
    expires_at TEXT,
    shuffle    INTEGER DEFAULT 1
);
CREATE TABLE IF NOT EXISTS questions (
    id        INTEGER PRIMARY KEY AUTOINCREMENT,
    test_id   INTEGER NOT NULL,
    position  INTEGER,
    text      TEXT NOT NULL,
    option_a  TEXT,
    option_b  TEXT,
    option_c  TEXT,
    option_d  TEXT,
    correct   TEXT,
    time_limit INTEGER
);
CREATE TABLE IF NOT EXISTS attempts (
    id              INTEGER PRIMARY KEY AUTOINCREMENT,
    user_id         INTEGER NOT NULL,
    test_id         INTEGER NOT NULL,
    started_at      TEXT,
    finished_at     TEXT,
    correct_count   INTEGER DEFAULT 0,
    total_questions INTEGER DEFAULT 0,
    points_earned   INTEGER DEFAULT 0,
    practice        INTEGER DEFAULT 0,
    q_deadline      INTEGER,
    cur_qid         INTEGER,
    chat_id         INTEGER,
    message_id      INTEGER
);
CREATE TABLE IF NOT EXISTS answers (
    id          INTEGER PRIMARY KEY AUTOINCREMENT,
    attempt_id  INTEGER NOT NULL,
    user_id     INTEGER NOT NULL,
    question_id INTEGER NOT NULL,
    chosen      TEXT,
    is_correct  INTEGER NOT NULL DEFAULT 0,
    answered_at TEXT
);
CREATE TABLE IF NOT EXISTS points_history (
    id         INTEGER PRIMARY KEY AUTOINCREMENT,
    user_id    INTEGER NOT NULL,
    points     INTEGER NOT NULL,
    reason     TEXT,
    attempt_id INTEGER,
    created_at TEXT
);
CREATE TABLE IF NOT EXISTS announcements (
    id           INTEGER PRIMARY KEY AUTOINCREMENT,
    author_id    INTEGER,
    content_type TEXT,
    text         TEXT,
    file_id      TEXT,
    url          TEXT,
    created_at   TEXT,
    target       TEXT,
    delivered    INTEGER
);
CREATE TABLE IF NOT EXISTS settings (
    key   TEXT PRIMARY KEY,
    value TEXT
);
CREATE TABLE IF NOT EXISTS activity_logs (
    id         INTEGER PRIMARY KEY AUTOINCREMENT,
    user_id    INTEGER,
    action     TEXT,
    details    TEXT,
    created_at TEXT
);
CREATE TABLE IF NOT EXISTS required_channels (
    id         INTEGER PRIMARY KEY AUTOINCREMENT,
    chat_id    INTEGER NOT NULL,
    title      TEXT,
    username   TEXT,
    invite_url TEXT,
    added_at   TEXT
);
CREATE INDEX IF NOT EXISTS idx_points_user_date ON points_history (user_id, created_at);
CREATE INDEX IF NOT EXISTS idx_attempts_user    ON attempts (user_id);
CREATE INDEX IF NOT EXISTS idx_answers_attempt  ON answers (attempt_id);
CREATE INDEX IF NOT EXISTS idx_answers_user     ON answers (user_id);
CREATE INDEX IF NOT EXISTS idx_questions_test   ON questions (test_id);
"""

# Columns that older databases may be missing: {table: {column: type}}.
EXPECTED_COLUMNS = {
    "users": {"full_name": "TEXT", "first_name": "TEXT", "last_name": "TEXT",
              "username": "TEXT", "registered_at": "TEXT", "blocked": "INTEGER DEFAULT 0"},
    "roles": {"name": "TEXT", "added_at": "TEXT"},
    "points_history": {"reason": "TEXT", "attempt_id": "INTEGER"},
    "attempts": {"practice": "INTEGER DEFAULT 0", "q_deadline": "INTEGER", "cur_qid": "INTEGER",
                 "chat_id": "INTEGER", "message_id": "INTEGER"},
    "tests": {"expires_at": "TEXT", "shuffle": "INTEGER DEFAULT 1"},
    "questions": {"time_limit": "INTEGER"},
    "announcements": {"target": "TEXT", "delivered": "INTEGER"},
}


def now() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S")


@contextmanager
def db():
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    try:
        yield conn
        conn.commit()
    except Exception:
        conn.rollback()
        raise
    finally:
        conn.close()


def init_db() -> None:
    """Create missing tables/columns. Existing data is never deleted."""
    with db() as c:
        c.execute("PRAGMA journal_mode = WAL")
        c.executescript(SCHEMA)
        for table, columns in EXPECTED_COLUMNS.items():
            existing = {row["name"] for row in c.execute(f"PRAGMA table_info({table})")}
            for column, ctype in columns.items():
                if column not in existing:
                    c.execute(f"ALTER TABLE {table} ADD COLUMN {column} {ctype}")
        for key, value in DEFAULT_SETTINGS.items():
            c.execute("INSERT OR IGNORE INTO settings (key, value) VALUES (?, ?)", (key, value))
        # Replace the provisional ranks of version 1 (only if they were never changed).
        c.execute(
            "UPDATE settings SET value = ? WHERE key = 'rank_thresholds' AND value = ?",
            (DEFAULT_SETTINGS["rank_thresholds"],
             "0:Beginner,100:Elementary,250:Pre-Intermediate,500:Intermediate,"
             "1000:Upper-Intermediate,2000:Advanced"),
        )


def seed_roles() -> None:
    """Creator comes from .env (always authoritative). Teachers and supporters
    are added only if they do not have a role yet, so later changes made by
    the Creator are not overwritten on restart."""
    with db() as c:
        c.execute("DELETE FROM roles WHERE role = 'creator' AND tg_id != ?", (CREATOR_ID,))
        c.execute(
            "INSERT OR REPLACE INTO roles (tg_id, role, added_at) VALUES (?, 'creator', ?)",
            (CREATOR_ID, now()),
        )
        for tg_id in TEACHER_IDS:
            c.execute("INSERT OR IGNORE INTO roles (tg_id, role, added_at) VALUES (?, 'teacher', ?)", (tg_id, now()))
        for tg_id in SUPPORTER_IDS:
            c.execute("INSERT OR IGNORE INTO roles (tg_id, role, added_at) VALUES (?, 'supporter', ?)", (tg_id, now()))


def get_setting(key: str, default: str = "") -> str:
    with db() as c:
        row = c.execute("SELECT value FROM settings WHERE key = ?", (key,)).fetchone()
    if row is None or row["value"] is None:
        return default
    return row["value"]


def set_setting(key: str, value: str) -> None:
    with db() as c:
        c.execute("INSERT OR REPLACE INTO settings (key, value) VALUES (?, ?)", (key, value))


def get_int(key: str, default: int) -> int:
    try:
        return int(get_setting(key, str(default)))
    except ValueError:
        return default


def get_group_id():
    raw = get_setting("group_chat_id")
    return int(raw) if raw.lstrip("-").isdigit() else None


def get_role(tg_id: int):
    """'creator' | 'teacher' | 'supporter' | 'student' | 'blocked' | None (not registered)."""
    with db() as c:
        row = c.execute("SELECT role FROM roles WHERE tg_id = ?", (tg_id,)).fetchone()
        if row:
            return row["role"]
        user = c.execute("SELECT blocked FROM users WHERE tg_id = ?", (tg_id,)).fetchone()
        if user:
            return "blocked" if user["blocked"] else "student"
    return None


def get_channels() -> list:
    """Channels students must join (mandatory subscription). Empty list = the check is off."""
    with db() as c:
        return c.execute("SELECT * FROM required_channels ORDER BY id").fetchall()


def get_user(tg_id: int):
    with db() as c:
        return c.execute("SELECT * FROM users WHERE tg_id = ?", (tg_id,)).fetchone()


def log_activity(user_id: int, action: str, details: str = "") -> None:
    with db() as c:
        c.execute(
            "INSERT INTO activity_logs (user_id, action, details, created_at) VALUES (?, ?, ?, ?)",
            (user_id, action, details, now()),
        )


def register_user(tg_id: int, full_name: str, username) -> None:
    words = full_name.split()
    with db() as c:
        c.execute(
            "INSERT OR IGNORE INTO users (tg_id, full_name, first_name, last_name, username, registered_at) "
            "VALUES (?, ?, ?, ?, ?, ?)",
            (tg_id, full_name, words[0], " ".join(words[1:]), username, now()),
        )


def delete_user(tg_id: int) -> None:
    """Removes a student together with all of their results."""
    with db() as c:
        c.execute("DELETE FROM answers WHERE user_id = ?", (tg_id,))
        c.execute("DELETE FROM attempts WHERE user_id = ?", (tg_id,))
        c.execute("DELETE FROM points_history WHERE user_id = ?", (tg_id,))
        c.execute("DELETE FROM users WHERE tg_id = ?", (tg_id,))


# ============================================================================
# Small helpers
# ============================================================================

def clip(text, limit: int) -> str:
    text = str(text or "")
    return text if len(text) <= limit else text[: limit - 1] + "…"


def pct(value: float) -> str:
    """80.0 -> '80%', 72.5 -> '72.5%'."""
    return f"{value:.1f}".rstrip("0").rstrip(".") + "%"


def fmt_clock(ts: float) -> str:
    """Unix time -> 'HH:MM' in Uzbekistan time."""
    return datetime.fromtimestamp(ts, TZ).strftime("%H:%M")


_DUR = re.compile(r"^(\d+(?:[.,]\d+)?)\s*(h|hr|hrs|hour|hours|soat|m|min|mins|minute|minutes|daqiqa)?$")


def parse_minutes(text: str):
    """'90' -> 90, '2h' -> 120, '1.5 hours' -> 90. None if invalid or out of range."""
    m = _DUR.match((text or "").strip().lower())
    if not m:
        return None
    value = float(m.group(1).replace(",", "."))
    unit = m.group(2) or "m"
    minutes = int(round(value * 60 if unit in ("h", "hr", "hrs", "hour", "hours", "soat") else value))
    return minutes if MIN_TEST_MIN <= minutes <= MAX_TEST_MIN else None


def parse_ts(value: str) -> datetime:
    return datetime.strptime(value, "%Y-%m-%d %H:%M:%S").replace(tzinfo=timezone.utc)


def fmt_duration(seconds: float) -> str:
    seconds = max(0, int(seconds))
    h, rest = divmod(seconds, 3600)
    m = rest // 60
    if h:
        return f"{h}h {m}m"
    if m:
        return f"{m}m"
    return f"{seconds}s"


def time_left(expires_at) -> str:
    if not expires_at:
        return "no limit"
    return fmt_duration((parse_ts(expires_at) - datetime.now(timezone.utc)).total_seconds())


def local_time(ts: str) -> str:
    """UTC database timestamp -> 'YYYY-MM-DD HH:MM' in Uzbekistan time."""
    return parse_ts(ts).astimezone(TZ).strftime("%Y-%m-%d %H:%M")


_WORD = re.compile(r"^[^\W\d_]+(?:['ʻʼ’‘`\-][^\W\d_]+)*$")


def parse_full_name(text: str):
    """Returns a cleaned 'First Last' string, or None if the input is invalid."""
    words = (text or "").strip().split()
    if not 2 <= len(words) <= 4:
        return None
    if not all(len(w) >= 2 and _WORD.match(w) for w in words):
        return None
    if len(" ".join(words)) > 60:
        return None
    return " ".join(w[:1].upper() + w[1:] for w in words)


def normalize_url(value: str) -> str:
    value = (value or "").strip()
    if value.startswith("@"):
        return "https://t.me/" + value[1:]
    if value.startswith("t.me/"):
        return "https://" + value
    return value


# ============================================================================
# Ranks, points and statistics
# ============================================================================

def parse_ranks(raw: str):
    """'0:Newcomer,100:Noob' -> [(0,'Newcomer'),(100,'Noob')] or None if invalid."""
    tiers = []
    for part in (raw or "").split(","):
        if ":" not in part:
            return None
        need, name = part.split(":", 1)
        need, name = need.strip(), name.strip()
        if not need.isdigit() or not name or len(name) > 30:
            return None
        tiers.append((int(need), name))
    if not tiers:
        return None
    tiers.sort()
    if tiers[0][0] != 0:
        return None
    return tiers


def rank_for(points: int) -> str:
    tiers = parse_ranks(get_setting("rank_thresholds")) or parse_ranks(DEFAULT_SETTINGS["rank_thresholds"])
    title = tiers[0][1]
    for need, name in tiers:
        if points >= need:
            title = name
    return title


def total_points(tg_id: int) -> int:
    with db() as c:
        return c.execute(
            "SELECT COALESCE(SUM(points), 0) FROM points_history WHERE user_id = ?", (tg_id,)
        ).fetchone()[0]


def profile_stats(tg_id: int) -> dict:
    """Only completed, non-practice attempts count towards statistics."""
    points = total_points(tg_id)
    with db() as c:
        ans = c.execute(
            "SELECT COALESCE(SUM(a.is_correct), 0) AS ok, COUNT(*) AS total "
            "FROM answers a JOIN attempts t ON t.id = a.attempt_id "
            "WHERE a.user_id = ? AND t.finished_at IS NOT NULL AND COALESCE(t.practice, 0) = 0",
            (tg_id,),
        ).fetchone()
        tests = c.execute(
            "SELECT COUNT(*) FROM attempts "
            "WHERE user_id = ? AND finished_at IS NOT NULL AND COALESCE(practice, 0) = 0",
            (tg_id,),
        ).fetchone()[0]
    correct = ans["ok"]
    incorrect = ans["total"] - correct
    accuracy = (correct / ans["total"] * 100) if ans["total"] else 0.0
    return {"points": points, "rank": rank_for(points), "correct": correct,
            "incorrect": incorrect, "accuracy": accuracy, "tests": tests}


def period_start(kind: str):
    """UTC timestamp where the daily/weekly period began (Uzbekistan time)."""
    local = datetime.now(TZ)
    if kind == "daily":
        start = local.replace(hour=0, minute=0, second=0, microsecond=0)
    elif kind == "weekly":
        start = (local - timedelta(days=local.weekday())).replace(hour=0, minute=0, second=0, microsecond=0)
    else:
        return None
    return start.astimezone(timezone.utc).strftime("%Y-%m-%d %H:%M:%S")


def ranking_rows(kind: str):
    since = period_start(kind)
    where, params = ("WHERE p.created_at >= ?", (since,)) if since else ("", ())
    with db() as c:
        rows = c.execute(
            f"SELECT u.tg_id, u.full_name, SUM(p.points) AS pts FROM users u "
            f"JOIN points_history p ON p.user_id = u.tg_id {where} "
            f"GROUP BY u.tg_id HAVING pts > 0 ORDER BY pts DESC, u.full_name",
            params,
        ).fetchall()
        totals = {r["user_id"]: r["t"] for r in c.execute(
            "SELECT user_id, SUM(points) AS t FROM points_history GROUP BY user_id")}
    return rows, totals


# ============================================================================
# Tests: creation, attempts, results
# ============================================================================

def get_test(test_id: int):
    with db() as c:
        return c.execute("SELECT * FROM tests WHERE id = ?", (test_id,)).fetchone()


def count_questions(test_id: int) -> int:
    with db() as c:
        return c.execute("SELECT COUNT(*) FROM questions WHERE test_id = ?", (test_id,)).fetchone()[0]


def save_test(title: str, owner_id: int, questions: list, total_seconds: int, shuffle: bool = True) -> int:
    lifetime = get_int("test_lifetime_hours", 24)
    created = datetime.now(timezone.utc)
    expires = (created + timedelta(hours=lifetime)).strftime("%Y-%m-%d %H:%M:%S")
    with db() as c:
        cur = c.execute(
            "INSERT INTO tests (title, created_by, status, time_limit, created_at, expires_at, shuffle) "
            "VALUES (?, ?, 'published', ?, ?, ?, ?)",
            (title, owner_id, total_seconds, created.strftime("%Y-%m-%d %H:%M:%S"), expires, 1 if shuffle else 0),
        )
        test_id = cur.lastrowid
        c.executemany(
            "INSERT INTO questions (test_id, position, text, option_a, option_b, option_c, option_d, correct) "
            "VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
            [(test_id, i, q["q"], q["a"], q["b"], q["c"], q["d"], q["correct"])
             for i, q in enumerate(questions, 1)],
        )
    return test_id


def test_seconds(test_id: int) -> int:
    """Total time a student has for the whole test (seconds)."""
    with db() as c:
        row = c.execute("SELECT time_limit FROM tests WHERE id = ?", (test_id,)).fetchone()
        if row and row["time_limit"]:
            return row["time_limit"]
        # old tests (created with per-question times): add the question times up
        total = c.execute(
            "SELECT COALESCE(SUM(COALESCE(time_limit, ?)), 0) FROM questions WHERE test_id = ?",
            (LEGACY_Q_SECONDS, test_id)).fetchone()[0]
    return total or LEGACY_Q_SECONDS * 10


def next_posting_time(owner_id: int):
    """None if the person may publish a test now, otherwise the datetime (UTC)
    when they may publish again. Deleted tests do not count."""
    lifetime = get_int("test_lifetime_hours", 24)
    with db() as c:
        last = c.execute(
            "SELECT MAX(created_at) FROM tests WHERE created_by = ? AND status != 'deleted'", (owner_id,)
        ).fetchone()[0]
    if not last:
        return None
    allowed_at = parse_ts(last) + timedelta(hours=lifetime)
    return allowed_at if allowed_at > datetime.now(timezone.utc) else None


def expire_tests() -> list:
    """Marks tests whose lifetime has ended as 'expired'. Returns the tests that just expired."""
    with db() as c:
        rows = c.execute(
            "SELECT * FROM tests WHERE status IN ('published', 'closed') "
            "AND expires_at IS NOT NULL AND expires_at <= ?", (now(),)
        ).fetchall()
        for r in rows:
            c.execute("UPDATE tests SET status = 'expired' WHERE id = ?", (r["id"],))
    return rows


def test_summary(test_id: int) -> dict:
    """First (counted) attempts of a test: participants, average accuracy, and who earned points."""
    with db() as c:
        rows = c.execute(
            "SELECT u.full_name, a.correct_count, a.total_questions, a.points_earned "
            "FROM attempts a JOIN users u ON u.tg_id = a.user_id "
            "WHERE a.test_id = ? AND a.finished_at IS NOT NULL AND COALESCE(a.practice, 0) = 0 "
            "ORDER BY a.points_earned DESC, a.correct_count DESC, a.finished_at", (test_id,)
        ).fetchall()
    total_q = sum(r["total_questions"] for r in rows)
    total_ok = sum(r["correct_count"] for r in rows)
    return {
        "participants": len(rows),
        "accuracy": (total_ok / total_q * 100) if total_q else 0.0,
        "earners": [r for r in rows if r["points_earned"] > 0],
        "rows": rows,
    }


_OPT_LINE = re.compile(r"^\(?([A-Da-d])\s*[\)\.\:]\s*(.+)$")
_ANS_LINE = re.compile(r"^(?:answer|ans|javob|correct)\s*[:\-=]?\s*\(?([A-Da-d])\)?\s*$", re.I)
_TIME_LINE = re.compile(r"^(?:time|vaqt)\s*[:\-=]?\s*(\d{1,4})\s*(?:s|sec|seconds?|soniya)?$", re.I)


def looks_bulk(text: str) -> bool:
    return bool(re.search(r"(?mi)^\s*\(?[A-D]\s*[\)\.\:]\s*\S", text or ""))


def parse_questions(text: str):
    """Parses one or more complete questions (blocks separated by a blank line).
    Returns a list of question dicts, or None if any block is malformed."""
    out = []
    for block in re.split(r"\n\s*\n", (text or "").strip()):
        q_lines, opts, ans = [], {}, None
        for raw in block.splitlines():
            line = raw.strip()
            if not line:
                continue
            if _TIME_LINE.match(line):  # per-question time is no longer used; such lines are ignored
                continue
            a = _ANS_LINE.match(line)
            if a:
                ans = a.group(1).upper()
                continue
            m = _OPT_LINE.match(line)
            if m:
                opts[m.group(1).upper()] = m.group(2).strip()
                continue
            if not opts:
                q_lines.append(line)
            else:
                return None
        if not q_lines or set(opts) != set(OPTS) or ans is None:
            return None
        q = " ".join(q_lines)
        if len(q) > 500 or any(len(v) > 200 for v in opts.values()):
            return None
        out.append({"q": q, "a": opts["A"], "b": opts["B"], "c": opts["C"], "d": opts["D"], "correct": ans})
    return out or None


def get_attempt(attempt_id: int):
    with db() as c:
        return c.execute("SELECT * FROM attempts WHERE id = ?", (attempt_id,)).fetchone()


def open_attempt(user_id: int, test_id: int) -> int:
    """Resumes an unfinished attempt or starts a new one.
    A repeat attempt (after a completed one) is practice: it awards no points."""
    seconds = test_seconds(test_id)
    with db() as c:
        row = c.execute(
            "SELECT id FROM attempts WHERE user_id = ? AND test_id = ? AND finished_at IS NULL",
            (user_id, test_id),
        ).fetchone()
        if row:
            return row["id"]
        done = c.execute(
            "SELECT 1 FROM attempts WHERE user_id = ? AND test_id = ? "
            "AND finished_at IS NOT NULL AND COALESCE(practice, 0) = 0",
            (user_id, test_id),
        ).fetchone()
        total = c.execute("SELECT COUNT(*) FROM questions WHERE test_id = ?", (test_id,)).fetchone()[0]
        cur = c.execute(
            "INSERT INTO attempts (user_id, test_id, started_at, total_questions, practice, q_deadline) "
            "VALUES (?, ?, ?, ?, ?, ?)",
            (user_id, test_id, now(), total, 1 if done else 0, int(time.time()) + seconds),
        )
        return cur.lastrowid


def question_order(att) -> list:
    """Question ids in the order this student sees them (random, but fixed for the attempt)."""
    with db() as c:
        ids = [r[0] for r in c.execute(
            "SELECT id FROM questions WHERE test_id = ? ORDER BY position, id", (att["test_id"],))]
    random.Random(f"order:{att['id']}").shuffle(ids)
    return ids


def option_order(att, question_id: int) -> list:
    """Original option letters in display order: ['C', 'A', 'D', 'B'] means button A shows option C.
    Options are shuffled per student unless the teacher switched shuffling off for the test."""
    letters = list(OPTS)
    with db() as c:
        row = c.execute("SELECT COALESCE(shuffle, 1) AS s FROM tests WHERE id = ?", (att["test_id"],)).fetchone()
    if row is None or row["s"]:
        random.Random(f"options:{att['id']}:{question_id}").shuffle(letters)
    return letters


def next_question(att):
    """Returns (question_row or None, index_of_question, total_questions)."""
    order = question_order(att)
    with db() as c:
        answered = {r[0] for r in c.execute("SELECT question_id FROM answers WHERE attempt_id = ?", (att["id"],))}
        next_id = next((qid for qid in order if qid not in answered), None)
        q = c.execute("SELECT * FROM questions WHERE id = ?", (next_id,)).fetchone() if next_id else None
    return q, len(answered) + 1, len(order)


def review_wait(test) -> int:
    """Seconds until the correct answers of a test may be reviewed (0 = open now).
    Answers stay locked while the test is still available, so early finishers cannot pass them on."""
    if not test or test["status"] != "published" or not test["expires_at"]:
        return 0
    left = (parse_ts(test["expires_at"]) - datetime.now(timezone.utc)).total_seconds()
    return max(0, int(left))


def first_bad_block(text: str):
    """Number of the first malformed question in a message with several questions."""
    for i, block in enumerate(re.split(r"\n\s*\n", (text or "").strip()), 1):
        if parse_questions(block) is None:
            return i
    return None


def record_answer(att, question, chosen: str) -> None:
    with db() as c:
        c.execute(
            "INSERT INTO answers (attempt_id, user_id, question_id, chosen, is_correct, answered_at) "
            "VALUES (?, ?, ?, ?, ?, ?)",
            (att["id"], att["user_id"], question["id"], chosen,
             1 if chosen == question["correct"] else 0, now()),
        )


def set_message(attempt_id: int, chat_id: int, message_id: int) -> None:
    """Remembers the message that shows the test, so the timer can update it when time runs out."""
    with db() as c:
        c.execute("UPDATE attempts SET chat_id = ?, message_id = ? WHERE id = ?", (chat_id, message_id, attempt_id))


def clear_deadline(attempt_id: int) -> None:
    with db() as c:
        c.execute("UPDATE attempts SET q_deadline = NULL WHERE id = ?", (attempt_id,))


def due_attempts() -> list:
    """Unfinished attempts whose total test time has run out."""
    with db() as c:
        return c.execute(
            "SELECT * FROM attempts WHERE finished_at IS NULL AND q_deadline IS NOT NULL AND q_deadline <= ?",
            (int(time.time()),),
        ).fetchall()


def finish_attempt(attempt_id: int):
    """Finishes an attempt exactly once. Unanswered questions count as incorrect.
    Returns (attempt_row, newly_finished)."""
    per = get_int("points_per_correct", 5)
    with db() as c:
        att = c.execute("SELECT * FROM attempts WHERE id = ?", (attempt_id,)).fetchone()
        if att is None:
            return None, False
        cur = c.execute(
            "UPDATE attempts SET finished_at = ? WHERE id = ? AND finished_at IS NULL", (now(), attempt_id)
        )
        if cur.rowcount == 0:
            return att, False
        c.execute(
            "INSERT INTO answers (attempt_id, user_id, question_id, chosen, is_correct, answered_at) "
            "SELECT ?, ?, q.id, NULL, 0, ? FROM questions q WHERE q.test_id = ? "
            "AND q.id NOT IN (SELECT question_id FROM answers WHERE attempt_id = ?)",
            (attempt_id, att["user_id"], now(), att["test_id"], attempt_id),
        )
        s = c.execute(
            "SELECT COALESCE(SUM(is_correct), 0) AS ok, COUNT(*) AS n FROM answers WHERE attempt_id = ?",
            (attempt_id,),
        ).fetchone()
        points = 0 if att["practice"] else s["ok"] * per
        c.execute(
            "UPDATE attempts SET correct_count = ?, total_questions = ?, points_earned = ? WHERE id = ?",
            (s["ok"], s["n"], points, attempt_id),
        )
        if points:
            c.execute(
                "INSERT INTO points_history (user_id, points, reason, attempt_id, created_at) "
                "VALUES (?, ?, 'test', ?, ?)",
                (att["user_id"], points, attempt_id, now()),
            )
        att = c.execute("SELECT * FROM attempts WHERE id = ?", (attempt_id,)).fetchone()
    return att, True


def tests_page(page: int, owner=None, include_expired: bool = False):
    """Tests for staff lists. owner=None means all tests."""
    hidden = "('deleted')" if include_expired else "('deleted', 'expired')"
    where, params = (f"t.status NOT IN {hidden}", [])
    if owner is not None:
        where += " AND t.created_by = ?"
        params.append(owner)
    with db() as c:
        total = c.execute(f"SELECT COUNT(*) FROM tests t WHERE {where}", params).fetchone()[0]
        rows = c.execute(
            f"SELECT t.id, t.title, t.status, t.expires_at, "
            f"(SELECT COUNT(*) FROM questions q WHERE q.test_id = t.id) AS qn, "
            f"(SELECT COUNT(*) FROM attempts a WHERE a.test_id = t.id AND a.finished_at IS NOT NULL "
            f" AND COALESCE(a.practice, 0) = 0) AS done "
            f"FROM tests t WHERE {where} ORDER BY t.id DESC LIMIT ? OFFSET ?",
            params + [PAGE, page * PAGE],
        ).fetchall()
    return rows, total


def students_page(query, page: int):
    like = None
    if query:
        like = "%" + query.replace("%", "").replace("_", "") + "%"
    where = "WHERE u.full_name LIKE ?" if like else ""
    params = [like] if like else []
    with db() as c:
        total = c.execute(f"SELECT COUNT(*) FROM users u {where}", params).fetchone()[0]
        rows = c.execute(
            f"SELECT u.tg_id, u.full_name, COALESCE(u.blocked, 0) AS blocked, "
            f"COALESCE((SELECT SUM(points) FROM points_history p WHERE p.user_id = u.tg_id), 0) AS pts "
            f"FROM users u {where} ORDER BY u.full_name COLLATE NOCASE LIMIT ? OFFSET ?",
            params + [PAGE_STUDENTS, page * PAGE_STUDENTS],
        ).fetchall()
    return rows, total


def system_stats() -> dict:
    today = period_start("daily")
    with db() as c:
        one = lambda sql, *p: c.execute(sql, p).fetchone()[0]
        return {
            "students": one("SELECT COUNT(*) FROM users"),
            "teachers": one("SELECT COUNT(*) FROM roles WHERE role = 'teacher'"),
            "supporters": one("SELECT COUNT(*) FROM roles WHERE role = 'supporter'"),
            "published": one("SELECT COUNT(*) FROM tests WHERE status = 'published'"),
            "closed": one("SELECT COUNT(*) FROM tests WHERE status = 'closed'"),
            "attempts": one("SELECT COUNT(*) FROM attempts WHERE finished_at IS NOT NULL"),
            "answers": one("SELECT COUNT(*) FROM answers"),
            "points": one("SELECT COALESCE(SUM(points), 0) FROM points_history"),
            "active": one("SELECT COUNT(DISTINCT user_id) FROM activity_logs WHERE created_at >= ?", today),
        }


# ============================================================================
# UI helpers
# ============================================================================

# --- Button colors (Telegram: "success" = green, "danger" = red, "primary" = blue, none = standard) -------
# The color is chosen in ONE place, by what the button does. Older Telegram apps simply show no color.
AUTO = object()
_STYLE_OK = [True]
_SPECIAL_TEXT = {"📊 Results": "primary", "📋 Review Answers": "primary"}
_STYLE_EXACT = {
    "st:tests": "success", "st:profile": "primary", "st:rankings": "primary",
    "an:group": "primary", "an:student": "primary",
    "sec:block": "primary", "sec:code": "primary",
    "bk:make": "success", "bk:restore": "primary", "bk:yes": "success", "bk:no": "danger",
    "mr:adjust": "primary", "mr:reset": "danger", "mr:resetyes": "danger",
    "ct:pub": "success", "an:pub": "success", "sub:check": "success",
}
_LIST_PREFIXES = ("tv:", "mtv:", "spk:", "tl:", "mt:", "tr:", "sp:", "ta:", "rv:", "trv:")  # lists, pages, answers
_STYLE_WORDS = (
    (("unblock", "reopen", "open registration", "publish", "start test", "resume test", "practice again",
      "add teacher", "add supporter", "create backup", "add channel"), "success"),
    (("delete", "remove", "reset", "finish", "close test", "close registration", "block student"), "danger"),
    (("results", "adjust points"), "primary"),
)
_STYLE_PREFIX = (("panel:", "primary"), ("cr:", "primary"), ("bs:", "primary"), ("rk:", "primary"),
                 ("sec:", "primary"), ("ts:", "success"), ("tf:", "danger"), ("tfy:", "danger"),
                 ("usd:", "danger"), ("usx:", "danger"), ("mtd:", "danger"), ("mtx:", "danger"))


def style_for(text: str, data: str = None):
    """Green for the main and confirming actions, red for cancelling and deleting, blue for sections."""
    if not BUTTON_COLORS or not data:
        return None
    if text in _SPECIAL_TEXT:
        return _SPECIAL_TEXT[text]
    lowered = text.lower()
    if lowered.endswith("cancel"):
        return "danger"
    if data in _STYLE_EXACT:
        return _STYLE_EXACT[data]
    if data.startswith("lb:"):  # Today / Week / Overall: the open one is green
        return "success" if text.startswith("✅") else None
    if data.startswith(_LIST_PREFIXES) or "remove last" in lowered:
        return None
    for words, style in _STYLE_WORDS:
        if any(word in lowered for word in words):
            return style
    for prefix, style in _STYLE_PREFIX:
        if data.startswith(prefix):
            return style
    return None


def btn(text: str, data: str = None, url: str = None, style=AUTO) -> InlineKeyboardButton:
    if style is AUTO:
        style = style_for(text, data)
    fields = {"url": url} if url else {"callback_data": data}
    if style and _STYLE_OK[0]:
        try:
            return InlineKeyboardButton(text=text, style=style, **fields)
        except Exception:  # an aiogram version that does not know button styles: continue without colors
            _STYLE_OK[0] = False
            logging.warning("This aiogram version does not accept button styles: colored buttons are off.")
    return InlineKeyboardButton(text=text, **fields)


def kb(*rows) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[list(r) for r in rows if r])


MAIN = [btn("⬅️ Main Menu", "menu:main")]


def nav_row(prefix: str, page: int, total: int, size: int) -> list:
    row = []
    if page > 0:
        row.append(btn("◀️ Prev", f"{prefix}{page - 1}"))
    if (page + 1) * size < total:
        row.append(btn("Next ▶️", f"{prefix}{page + 1}"))
    return row


def title_block(title: str) -> str:
    return f"<b>{title}</b>\n{LINE}\n"


TXT_WELCOME = (
    f"🎓 <b>WELCOME TO THE ACADEMY</b>\n{LINE}\n"
    "Welcome to the English Academy Tutoring Bot.\n\n"
    "To begin, please enter your <b>full name</b> (first name and surname).\n\n"
    "<i>Example: Chingiz Urinbaev</i>"
)
TXT_BAD_NAME = (
    f"⚠️ <b>INVALID FORMAT</b>\n{LINE}\n"
    "Please enter your full name in the format: <b>First name Surname</b>.\n\n"
    "<i>Example: Chingiz Urinbaev</i>"
)
TXT_STALE = "This button is no longer active. Returning to the menu."
TXT_REG_CLOSED = (f"🔒 <b>REGISTRATION CLOSED</b>\n{LINE}\n"
                  "New registrations are temporarily closed. Please contact the academy administration.")
TXT_BLOCKED = (f"⛔ <b>ACCESS DENIED</b>\n{LINE}\n"
               "Your account has been blocked. Please contact the academy administration.")
TXT_CODE = (f"🔑 <b>ACCESS CODE</b>\n{LINE}\n"
            "Welcome to the English Academy Tutoring Bot.\n\n"
            "Please enter the <b>access code</b> given by your teacher.")
TXT_DUP_NAME = (f"⚠️ <b>NAME ALREADY REGISTERED</b>\n{LINE}\n"
                "Another student already has this name. Please enter your full name together with "
                "your middle name, for example: <i>Ali Valiyev Karimovich</i>.\n\n"
                "If this is exactly your name, send it again and it will be saved with a number.")

CODE_MAX_TRIES = 5          # wrong access codes allowed before a temporary lock
CODE_LOCK_SECONDS = 900     # lock time: 15 minutes
CODE_OK: set = set()        # users who entered the correct access code (until they register)
CODE_FAILS: dict = {}       # user id -> (wrong attempts, locked until)
DUP_WARNED: set = set()     # users who were told that their name is already taken


def registration_prompt(user_id: int) -> str:
    """What a user who is not registered yet sees: closed notice, access code or name request."""
    if get_setting("registration_open", "1") != "1":
        return TXT_REG_CLOSED
    if get_setting("access_code").strip() and user_id not in CODE_OK:
        return TXT_CODE
    return TXT_WELCOME

PANEL_TITLES = {
    "creator": "▫️ <b>Creator Panel</b> ▫️",
    "teacher": "👨‍🏫 <b>TEACHER PANEL</b>",
    "supporter": "👨‍💻 <b>SUPPORTER PANEL</b>",
}


def student_menu() -> InlineKeyboardMarkup:
    return kb(
        [btn("📝 Tests", "st:tests")],
        [btn("👤 My Profile", "st:profile"), btn("🏆 Rankings", "st:rankings")],
        [btn("👨‍🏫 Teacher", url=normalize_url(get_setting("teacher_url"))),
         btn("👨‍💻 Supporter", url=normalize_url(get_setting("supporter_url")))],
        [btn("▫️Creator▫️", url=normalize_url(get_setting("creator_url")))],
    )


def staff_menu(role: str) -> InlineKeyboardMarkup:
    if role == "creator":
        return kb(
            [btn("Bot Settings", "cr:settings"), btn("Manage Users", "cr:users")],
            [btn("Manage Roles", "cr:roles"), btn("System Statistics", "cr:stats")],
            [btn("Manage All Tests", "cr:tests"), btn("Manage Rankings", "cr:rankings")],
            [btn("Group Announcements", "cr:announce"), btn("Security & Access", "cr:security")],
            [btn("Backup & Restore", "cr:backup"), btn("Notifications", "cr:notify")],
        )
    return kb(
        [btn("📝 Create Test", "panel:create_test"), btn("📋 Manage Tests", "panel:manage_tests")],
        [btn("👥 Student Statistics", "panel:student_stats"), btn("📊 Test Results", "panel:test_results")],
        [btn("🏆 Rankings", "panel:rankings"), btn("📢 Announcements", "panel:announcements")],
        MAIN,
    )


# ============================================================================
# FSM states
# ============================================================================

class CreateTest(StatesGroup):
    title = State()
    question = State()


class Announce(StatesGroup):
    content = State()
    preview = State()


class Pick(StatesGroup):
    search = State()


class SettingEdit(StatesGroup):
    value = State()


class RoleAdd(StatesGroup):
    tg_id = State()


class PointsAdjust(StatesGroup):
    value = State()


class Restore(StatesGroup):
    file = State()


class CodeEdit(StatesGroup):
    value = State()


class ChannelAdd(StatesGroup):
    value = State()


# ============================================================================
# Filters and message helpers
# ============================================================================

class HasRole(Filter):
    """Passes only if the sender's role is one of the given roles.
    HasRole(None) matches users who have not registered yet."""

    def __init__(self, *roles) -> None:
        self.roles = roles

    async def __call__(self, event: TelegramObject) -> bool:
        user = getattr(event, "from_user", None)
        return user is not None and get_role(user.id) in self.roles


async def show(target, text: str, markup=None, ack: bool = True) -> None:
    """Edits the message under a pressed button, or sends a new message."""
    if isinstance(target, CallbackQuery):
        msg = target.message
        if isinstance(msg, Message):
            try:
                await msg.edit_text(text, reply_markup=markup)
            except TelegramBadRequest as exc:
                if "message is not modified" not in str(exc).lower():
                    await msg.answer(text, reply_markup=markup)
        else:
            await target.bot.send_message(target.from_user.id, text, reply_markup=markup)
        if ack:
            await target.answer()
    else:
        await target.answer(text, reply_markup=markup)


async def show_home(target, first_time: bool = False, ack: bool = True) -> None:
    """Shows the correct home screen for the sender's role."""
    user = target.from_user
    role = get_role(user.id)

    if role is None:
        await show(target, registration_prompt(user.id), None, ack)
    elif role == "blocked":
        await show(target, TXT_BLOCKED, None, ack)
    elif role == "student":
        row = get_user(user.id)
        name = escape(row["full_name"] if row and row["full_name"] else user.full_name)
        greeting = ("Please select a section below." if first_time
                    else f"Welcome back, <b>{name}</b>.\nPlease select a section below.")
        await show(target, f"🎓 <b>MAIN MENU</b>\n{LINE}\n{greeting}", student_menu(), ack)
    else:
        with db() as c:
            c.execute("UPDATE roles SET name = ? WHERE tg_id = ?", (user.full_name, user.id))
        text = (f"{PANEL_TITLES[role]}\n{LINE}\n"
                f"Welcome, <b>{escape(user.full_name)}</b>. Please select an action.")
        await show(target, text, staff_menu(role), ack)


# ============================================================================
# Routers
# ============================================================================

router = Router()
router.message.filter(F.chat.type == "private")

group_router = Router()
group_router.message.filter(F.chat.type.in_({"group", "supergroup"}))


# ============================================================================
# Mandatory subscription (students must join the required channels)
# ============================================================================

SUB_CACHE_SECONDS = 600           # a successful check is remembered for 10 minutes
SUB_WARN_SECONDS = 6 * 3600       # the Creator is warned about a broken channel at most every 6 hours
SUB_OK: dict = {}                 # user id -> time until which the last successful check counts
SUB_WARNED: dict = {}             # channel chat id -> time of the last warning
SUB_EXEMPT = ("ta:", "tf:", "tfy:", "tfn:", "sub:")  # test answers (a running test is never interrupted) + the check button
JOINED_STATUSES = ("member", "administrator", "creator")


def channel_url(channel) -> str:
    return channel["invite_url"] or (f"https://t.me/{channel['username']}" if channel["username"] else "")


def sub_text(missing: list) -> str:
    plural = "s" if len(missing) > 1 else ""
    return (f"🔒 <b>SUBSCRIPTION REQUIRED</b>\n{LINE}\n"
            f"To use the bot, please join the channel{plural} below, then press <b>I have joined</b>.")


def sub_markup(missing: list) -> InlineKeyboardMarkup:
    rows = [[btn(f"📢 {clip(ch['title'], 30)}", url=channel_url(ch))] for ch in missing]
    rows.append([btn("✅ I have joined", "sub:check")])
    return kb(*rows)


async def warn_broken_channel(bot: Bot, channel, error) -> None:
    """The check failed (the bot is not an administrator any more, or the channel is gone):
    students are NOT blocked, the Creator is told (not more often than every 6 hours)."""
    if time.time() - SUB_WARNED.get(channel["chat_id"], 0) < SUB_WARN_SECONDS:
        return
    SUB_WARNED[channel["chat_id"]] = time.time()
    logging.warning("Subscription check failed for %s: %s", channel["title"], error)
    await notify_creator(bot, f"{title_block('⚠️ SUBSCRIPTION CHECK FAILED')}"
                              f"<b>Channel:</b> {escape(channel['title'])}\n"
                              "The bot cannot check this channel, so students are <b>not</b> blocked. "
                              "Please make sure the bot is still an administrator of the channel.")


async def missing_channels(bot: Bot, user_id: int, fresh: bool = False) -> list:
    """The required channels this user has NOT joined (empty list = allowed)."""
    channels = get_channels()
    if not channels or (not fresh and SUB_OK.get(user_id, 0) > time.time()):
        return []
    missing = []
    for channel in channels:
        try:
            member = await bot.get_chat_member(channel["chat_id"], user_id)
        except TelegramAPIError as exc:
            await warn_broken_channel(bot, channel, exc)
            continue
        status = str(getattr(member.status, "value", member.status))
        if status in JOINED_STATUSES or (status == "restricted" and getattr(member, "is_member", False)):
            continue
        missing.append(channel)
    if not missing:
        SUB_OK[user_id] = time.time() + SUB_CACHE_SECONDS
    return missing


def gate_applies(event) -> bool:
    """Only students (and new users who are about to register) are checked, only in private chats."""
    user = getattr(event, "from_user", None)
    if user is None or not get_channels():
        return False
    role = get_role(user.id)
    if role not in ("student", None):
        return False
    if role is None and get_setting("registration_open", "1") != "1":
        return False
    if isinstance(event, CallbackQuery):
        if (event.data or "").startswith(SUB_EXEMPT):
            return False
        chat = getattr(event.message, "chat", None)
        return chat is None or chat.type == "private"
    return getattr(getattr(event, "chat", None), "type", "private") == "private"


class SubscriptionGate(BaseMiddleware):
    """Runs before every handler: a student who has not joined the channels sees the join screen instead."""

    async def __call__(self, handler, event, data):
        if gate_applies(event):
            bot = data.get("bot") or event.bot
            missing = await missing_channels(bot, event.from_user.id)
            if missing:
                text, markup = sub_text(missing), sub_markup(missing)
                if isinstance(event, CallbackQuery):
                    await show(event, text, markup)
                else:
                    await event.answer(text, reply_markup=markup)
                return None
        return await handler(event, data)


router.message.outer_middleware(SubscriptionGate())
router.callback_query.outer_middleware(SubscriptionGate())


@router.callback_query(F.data == "sub:check")
async def cb_sub_check(call: CallbackQuery) -> None:
    """The 'I have joined' button: check again right now (no cache)."""
    if get_role(call.from_user.id) not in ("student", None):
        await call.answer()
        await show_home(call, ack=False)
        return
    missing = await missing_channels(call.bot, call.from_user.id, fresh=True)
    if not missing:
        await call.answer("✅ Thank you!")
        await show_home(call, ack=False)
        return
    await call.answer("You have not joined yet. Please join the channel first.", show_alert=True)
    await show(call, sub_text(missing), sub_markup(missing), ack=False)


# --- Creator: manage the required channels (Security & Access -> Required Channels) -------------

def channels_screen():
    channels = get_channels()
    lines = [title_block("📢 REQUIRED CHANNELS").rstrip(), "Students must join these channels to use the bot.", ""]
    rows = []
    if not channels:
        lines.append("No channels yet: the subscription check is switched off.")
    for ch in channels:
        where = f"@{ch['username']}" if ch["username"] else "private channel"
        lines.append(f"• {escape(ch['title'])} ({escape(where)})")
        rows.append([btn(f"❌ Remove: {clip(ch['title'], 22)}", f"chan:rm:{ch['id']}")])
    if len(channels) < MAX_CHANNELS:
        rows.append([btn("➕ Add Channel", "chan:add")])
    rows += [[btn("◀️ Back", "cr:security")], MAIN]
    return "\n".join(lines), kb(*rows)


@router.callback_query(F.data.in_({"sec:chan", "chan:menu"}), HasRole("creator"))
async def cb_channels(call: CallbackQuery, state: FSMContext) -> None:
    await state.clear()
    text, markup = channels_screen()
    await show(call, text, markup)


@router.callback_query(F.data == "chan:add", HasRole("creator"))
async def cb_channel_add(call: CallbackQuery, state: FSMContext) -> None:
    await state.set_state(ChannelAdd.value)
    text = (f"{title_block('➕ ADD CHANNEL')}"
            "1. Add this bot to the channel as an <b>administrator</b>.\n"
            "2. Send the channel <code>@username</code>, or forward any post from the channel here "
            "(for a private channel).")
    await show(call, text, kb([btn("↩️ Cancel", "chan:menu")]))


@router.message(StateFilter(ChannelAdd.value), HasRole("creator"))
async def channel_add_value(message: Message, state: FSMContext) -> None:
    bot = message.bot
    ref = None
    origin = getattr(message, "forward_origin", None)
    if origin is not None and getattr(origin, "type", "") == "channel":
        ref = origin.chat.id
    elif getattr(message, "forward_from_chat", None) is not None:
        ref = message.forward_from_chat.id
    elif message.text:
        found = re.fullmatch(r"(?:https?://)?(?:t\.me/)?@?([A-Za-z][A-Za-z0-9_]{4,31})", message.text.strip())
        if found:
            ref = "@" + found.group(1)
    if ref is None:
        await message.answer("⚠️ Please send the channel <code>@username</code>, or forward a post from the channel.")
        return
    try:
        chat = await bot.get_chat(ref)
    except TelegramAPIError:
        await message.answer("⚠️ I could not find this channel. Check the username, and make sure the bot "
                             "is an administrator of the channel.")
        return
    if chat.type not in ("channel", "supergroup"):
        await message.answer("⚠️ Only channels and groups can be used here.")
        return
    try:
        me = await bot.get_me()
        member = await bot.get_chat_member(chat.id, me.id)
        is_admin = str(getattr(member.status, "value", member.status)) in ("administrator", "creator")
    except TelegramAPIError:
        is_admin = False
    if not is_admin:
        await message.answer("⚠️ The bot is not an administrator of this channel. Please add it as an "
                             "administrator, then send the channel again.")
        return
    url = f"https://t.me/{chat.username}" if chat.username else getattr(chat, "invite_link", None)
    if not url:
        try:
            url = (await bot.create_chat_invite_link(chat.id, name="English Academy")).invite_link
        except TelegramAPIError:
            await message.answer("⚠️ This channel is private and the bot cannot create an invite link. "
                                 "Please give the bot the <b>Invite users via link</b> right and try again.")
            return
    channels = get_channels()
    if len(channels) >= MAX_CHANNELS:
        await message.answer(f"⚠️ You can add at most {MAX_CHANNELS} channels. Remove one first.")
        return
    if any(ch["chat_id"] == chat.id for ch in channels):
        await message.answer("⚠️ This channel has already been added.")
        return
    with db() as c:
        c.execute("INSERT INTO required_channels (chat_id, title, username, invite_url, added_at) "
                  "VALUES (?, ?, ?, ?, ?)", (chat.id, chat.title or str(chat.id), chat.username, url, now()))
    SUB_OK.clear()
    await state.clear()
    log_activity(message.from_user.id, "channel_added", str(chat.id))
    await message.answer("✅ Channel added. Students must join it from now on.")
    text, markup = channels_screen()
    await message.answer(text, reply_markup=markup)


@router.callback_query(F.data.startswith("chan:rm:"), HasRole("creator"))
async def cb_channel_remove(call: CallbackQuery) -> None:
    with db() as c:
        c.execute("DELETE FROM required_channels WHERE id = ?", (int(call.data.split(":")[2]),))
    SUB_OK.clear()
    log_activity(call.from_user.id, "channel_removed", call.data)
    text, markup = channels_screen()
    await show(call, text, markup)


# ============================================================================
# General handlers
# ============================================================================

@router.message(CommandStart())
async def cmd_start(message: Message, state: FSMContext) -> None:
    await state.clear()
    log_activity(message.from_user.id, "start")
    await show_home(message)


@router.callback_query(F.data == "menu:main")
async def cb_main_menu(call: CallbackQuery, state: FSMContext) -> None:
    await state.clear()
    await show_home(call)


# ============================================================================
# Student: profile and rankings
# ============================================================================

def profile_card(tg_id: int, fallback_name: str = "-", title: str = "👤 MY PROFILE", extra: str = "") -> str:
    row = get_user(tg_id)
    name = escape(row["full_name"] if row and row["full_name"] else fallback_name)
    s = profile_stats(tg_id)
    return (
        f"{title_block(title)}"
        f"👤 <b>Full Name:</b> {name}\n"
        f"{extra}"
        f"🏅 <b>Current Rank:</b> {escape(s['rank'])}\n"
        f"⭐ <b>Total Points:</b> {s['points']}\n"
        f"✅ <b>Correct Answers:</b> {s['correct']}\n"
        f"❌ <b>Incorrect Answers:</b> {s['incorrect']}\n"
        f"📊 <b>Accuracy Rate:</b> {pct(s['accuracy'])}\n"
        f"📝 <b>Tests Completed:</b> {s['tests']}"
    )


@router.callback_query(F.data == "st:profile", HasRole("student"))
async def cb_profile(call: CallbackQuery) -> None:
    await show(call, profile_card(call.from_user.id, call.from_user.full_name), kb(MAIN))


# ============================================================================
# Leaderboard (the rankings as a picture)
# ============================================================================

LB_TITLES = {"daily": "DAILY", "weekly": "WEEKLY", "overall": "OVERALL"}
ASSET_DIR = os.path.dirname(os.path.abspath(__file__))  # logo.jpg and the .ttf fonts live next to bot.py
LAST_LEADERBOARD: dict = {}    # chat id -> id of the newest leaderboard message (the old one is deleted)
GROUP_COOLDOWN: dict = {}      # group chat id -> time of the last /rankings answer
_ASSETS: dict = {}


def fmt_points(value) -> str:
    """4206 -> '4.206'"""
    return f"{int(value):,}".replace(",", ".")


def load_font(name: str, size: int):
    from PIL import ImageFont
    try:
        return ImageFont.truetype(os.path.join(ASSET_DIR, name), size)
    except OSError:
        logging.warning("Font %s was not found next to bot.py: using the default font.", name)
        try:
            return ImageFont.load_default(size)
        except TypeError:
            return ImageFont.load_default()


def logo_badge(size: int):
    """The academy logo as a rounded badge (None if logo.jpg is missing)."""
    if size in _ASSETS:
        return _ASSETS[size]
    from PIL import Image, ImageDraw
    resample = getattr(Image, "Resampling", Image).LANCZOS
    try:
        logo = Image.open(os.path.join(ASSET_DIR, "logo.jpg")).convert("RGB").resize((size, size), resample)
    except OSError:
        logging.warning("logo.jpg was not found next to bot.py: the leaderboard is drawn without a logo.")
        _ASSETS[size] = None
        return None
    scale = 4
    radius = int(size * scale * 0.16)
    mask = Image.new("L", (size * scale, size * scale), 0)
    ImageDraw.Draw(mask).rounded_rectangle((0, 0, size * scale - 1, size * scale - 1), radius=radius, fill=255)
    out = Image.new("RGBA", (size, size), (0, 0, 0, 0))
    out.paste(logo, (0, 0), mask.resize((size, size), resample))
    ring = Image.new("RGBA", (size * scale, size * scale), (0, 0, 0, 0))
    ImageDraw.Draw(ring).rounded_rectangle((2, 2, size * scale - 3, size * scale - 3), radius=radius,
                                           outline=(190, 146, 52), width=max(3, size // 36) * scale)
    out.alpha_composite(ring.resize((size, size), resample))
    _ASSETS[size] = out
    return out


def render_leaderboard_png(title: str, entries: list) -> bytes:
    """Draws the leaderboard. entries: [(name, rank title, points), ...] (at most 10). Needs Pillow."""
    import io
    from PIL import Image, ImageDraw
    W, H = 1280, 720
    navy, navy_dark = (18, 48, 107), (10, 28, 68)
    gold, silver, bronze = (190, 146, 52), (176, 184, 196), (176, 112, 66)
    cream, panel_fill, sub_col = (243, 237, 224), (251, 248, 241), (110, 100, 80)

    img = Image.new("RGB", (W, H), cream)
    deco = Image.new("RGBA", (W, H), (0, 0, 0, 0))
    ring = (*gold, 40)
    ImageDraw.Draw(deco).ellipse((-140, -150, 160, 150), outline=ring, width=34)
    ImageDraw.Draw(deco).ellipse((W - 210, H - 230, W + 130, H + 110), outline=ring, width=30)
    img.paste(deco, (0, 0), deco)
    d = ImageDraw.Draw(img)

    title_font = load_font("DejaVuSerif-Bold.ttf", 54)
    d.text((W / 2, 62), title, font=title_font, fill=navy, anchor="mm")
    d.line((W / 2 - 115, 102, W / 2 + 115, 102), fill=gold, width=3)
    d.ellipse((W / 2 - 5, 97, W / 2 + 5, 107), fill=gold)

    px0, py0, px1, py1 = 40, 124, W - 40, H - 28
    d.rounded_rectangle((px0, py0, px1, py1), radius=26, fill=panel_fill, outline=gold, width=3)

    name_font = load_font("DejaVuSans-Bold.ttf", 21)
    sub_font = load_font("DejaVuSans.ttf", 13)
    num_font = load_font("DejaVuSans-Bold.ttf", 16)
    if not entries:
        d.text((W / 2, (py0 + py1) / 2), "No results yet", font=load_font("DejaVuSerif-Bold.ttf", 36),
               fill=sub_col, anchor="mm")
    x_num, x_name, x_bar = 74, 112, 372
    max_bar = (W - 70) - x_bar
    top = max((e[2] for e in entries), default=1) or 1
    y, row_h, gap = py0 + 20, 44, 7
    for i, (name, rank, pts) in enumerate(entries[:10]):
        cy = y + row_h / 2
        color = (gold, silver, bronze)[i] if i < 3 else navy
        d.ellipse((x_num - 16, cy - 16, x_num + 16, cy + 16), fill=color)
        d.text((x_num, cy), str(i + 1), font=num_font, fill=navy_dark if i < 3 else (255, 255, 255), anchor="mm")
        limit = x_bar - x_name - 18
        while name and d.textlength(name, font=name_font) > limit:
            name = name[:-1]
        shown = name if name == entries[i][0] else name.rstrip() + "…"
        d.text((x_name, cy - 11), shown, font=name_font, fill=navy_dark, anchor="lm")
        d.text((x_name, cy + 13), rank, font=sub_font, fill=sub_col, anchor="lm")
        bar_w = max(120, int(max_bar * pts / top))
        d.rounded_rectangle((x_bar, y + 2, x_bar + bar_w, y + row_h - 2), radius=(row_h - 4) // 2, fill=color)
        d.text((x_bar + bar_w / 2, cy), fmt_points(pts), font=name_font,
               fill=navy_dark if i < 3 else (255, 255, 255), anchor="mm")
        y += row_h + gap

    badge = logo_badge(158)
    if badge is not None:
        img.paste(badge, (W - 70 - 158 + 10, H - 28 - 158 - 14), badge)
    buffer = io.BytesIO()
    img.save(buffer, format="PNG", optimize=True)
    return buffer.getvalue()


def leaderboard_caption(kind: str, rows, viewer=None) -> str:
    lines = [f"📈 <b>{LB_TITLES[kind]} LEADERBOARD</b>"]
    if not rows:
        lines.append("No results have been recorded yet.")
    for i, r in enumerate(rows[:10], 1):
        mark = MEDALS.get(i, f"{i}. 👤")
        lines.append(f"{mark} {escape(clip(r['full_name'] or '-', 28))} • {fmt_points(r['pts'])}")
    if viewer:
        for i, r in enumerate(rows, 1):
            if r["tg_id"] == viewer and i > 10:
                lines += ["", f"👉 <b>Your position:</b> #{i} · {fmt_points(r['pts'])} pts"]
    lines += ["", f"⭐ <b>Total points:</b> {fmt_points(sum(r['pts'] for r in rows))}"]
    return "\n".join(lines)


def leaderboard_markup(active: str) -> InlineKeyboardMarkup:
    def label(kind: str, icon: str, text: str) -> str:
        return f"✅ {text}" if kind == active else f"{icon} {text}"
    return kb([btn(label("daily", "📅", "Today"), "lb:daily"), btn(label("weekly", "📆", "Week"), "lb:weekly")],
              [btn(label("overall", "🏆", "Overall"), "lb:overall")])


async def build_leaderboard(kind: str, viewer=None):
    """Returns (picture or None, caption). If the picture cannot be drawn, only the caption is used."""
    rows, totals = ranking_rows(kind)
    caption = leaderboard_caption(kind, rows, viewer)
    entries = [(r["full_name"] or "-", rank_for(totals.get(r["tg_id"], 0)), r["pts"]) for r in rows[:10]]
    try:
        png = await asyncio.to_thread(render_leaderboard_png, f"{LB_TITLES[kind]} LEADERBOARD", entries)
        return BufferedInputFile(png, filename="leaderboard.png"), caption
    except Exception:
        logging.exception("Could not draw the leaderboard picture: sending the text list only")
        return None, caption


async def send_leaderboard(bot: Bot, chat_id: int, kind: str, viewer=None, buttons: bool = True,
                           track: bool = True) -> None:
    """Sends the leaderboard as a new message. With track=True the previous one in that chat is deleted."""
    photo, caption = await build_leaderboard(kind, viewer)
    markup = leaderboard_markup(kind) if buttons else None
    if photo is not None:
        sent = await bot.send_photo(chat_id, photo, caption=caption, reply_markup=markup)
    else:
        sent = await bot.send_message(chat_id, caption, reply_markup=markup)
    if track:
        old = LAST_LEADERBOARD.get(chat_id)
        LAST_LEADERBOARD[chat_id] = sent.message_id
        if old:
            try:
                await bot.delete_message(chat_id, old)
            except TelegramAPIError:
                pass


@router.callback_query(F.data.in_({"st:rankings", "panel:rankings", "rk:menu"}), HasRole(*ANY_ROLE))
async def cb_rankings_open(call: CallbackQuery) -> None:
    await call.answer()
    await send_leaderboard(call.bot, call.from_user.id, "overall", call.from_user.id)


@router.callback_query(F.data.in_({"rk:daily", "rk:weekly", "rk:overall"}), HasRole(*ANY_ROLE))
async def cb_rank_open_kind(call: CallbackQuery) -> None:
    await call.answer()
    await send_leaderboard(call.bot, call.from_user.id, call.data.split(":")[1], call.from_user.id)


@router.callback_query(F.data.startswith("lb:"))
async def cb_leaderboard_switch(call: CallbackQuery) -> None:
    """Today / Week / Overall buttons under a leaderboard (in private chats and in the group)."""
    kind = call.data.split(":")[1]
    msg = call.message
    if kind not in LB_TITLES or not isinstance(msg, Message):
        await call.answer()
        return
    if msg.chat.type == "private":
        if get_role(call.from_user.id) not in ANY_ROLE:
            await call.answer("Access denied.", show_alert=True)
            return
        viewer = call.from_user.id
    else:
        if msg.chat.id != get_group_id():
            await call.answer()
            return
        viewer = None
    photo, caption = await build_leaderboard(kind, viewer)
    markup = leaderboard_markup(kind)
    try:
        if msg.photo and photo is not None:
            await call.bot.edit_message_media(
                InputMediaPhoto(media=photo, caption=caption, parse_mode="HTML"),
                chat_id=msg.chat.id, message_id=msg.message_id, reply_markup=markup)
        elif msg.photo:
            await call.bot.edit_message_caption(chat_id=msg.chat.id, message_id=msg.message_id,
                                                caption=caption, reply_markup=markup)
        else:
            await call.bot.edit_message_text(caption, chat_id=msg.chat.id, message_id=msg.message_id,
                                             reply_markup=markup)
    except TelegramBadRequest as exc:
        if "not modified" not in str(exc).lower():
            raise
    await call.answer()


# ============================================================================
# Student: tests
# ============================================================================

def is_open(test) -> bool:
    """A test can be started only while it is published and its lifetime has not ended."""
    return bool(test) and test["status"] == "published" and (not test["expires_at"] or test["expires_at"] > now())


def student_tests(user_id: int, page: int):
    t = now()
    with db() as c:
        total = c.execute(
            "SELECT COUNT(*) FROM tests WHERE status = 'published' AND (expires_at IS NULL OR expires_at > ?)", (t,)
        ).fetchone()[0]
        rows = c.execute(
            "SELECT t.id, t.title, t.expires_at, "
            "(SELECT COUNT(*) FROM questions q WHERE q.test_id = t.id) AS qn, "
            "EXISTS(SELECT 1 FROM attempts a WHERE a.user_id = ? AND a.test_id = t.id "
            " AND a.finished_at IS NOT NULL AND COALESCE(a.practice, 0) = 0) AS done "
            "FROM tests t WHERE t.status = 'published' AND (t.expires_at IS NULL OR t.expires_at > ?) "
            "ORDER BY t.id DESC LIMIT ? OFFSET ?",
            (user_id, t, PAGE, page * PAGE),
        ).fetchall()
    return rows, total


async def show_test_list(call: CallbackQuery, page: int) -> None:
    rows, total = student_tests(call.from_user.id, page)
    text = title_block("📝 AVAILABLE TESTS")
    if not rows:
        text += "No tests are available at the moment."
    else:
        text += ("Select a test to begin.\n✅ marks the tests you have completed. "
                 "Each test is available for a limited time.")
    buttons = [[btn(f"{'✅' if r['done'] else '📝'} {clip(r['title'], 22)} · {time_left(r['expires_at'])}",
                    f"tv:{r['id']}")] for r in rows]
    await show(call, text, kb(*buttons, nav_row("tl:", page, total, PAGE), MAIN))


@router.callback_query(F.data == "st:tests", HasRole("student"))
async def cb_tests(call: CallbackQuery) -> None:
    await show_test_list(call, 0)


@router.callback_query(F.data.startswith("tl:"), HasRole("student"))
async def cb_tests_page(call: CallbackQuery) -> None:
    await show_test_list(call, int(call.data.split(":")[1]))


@router.callback_query(F.data.startswith("tv:"), HasRole("student"))
async def cb_test_view(call: CallbackQuery) -> None:
    test = get_test(int(call.data.split(":")[1]))
    if not is_open(test):
        await call.answer("This test is not available.", show_alert=True)
        return
    per = get_int("points_per_correct", 5)
    qn = count_questions(test["id"])
    seconds = test_seconds(test["id"])
    with db() as c:
        open_att = c.execute(
            "SELECT 1 FROM attempts WHERE user_id = ? AND test_id = ? AND finished_at IS NULL",
            (call.from_user.id, test["id"])).fetchone()
        done = c.execute(
            "SELECT 1 FROM attempts WHERE user_id = ? AND test_id = ? AND finished_at IS NOT NULL "
            "AND COALESCE(practice, 0) = 0", (call.from_user.id, test["id"])).fetchone()
    if open_att:
        status, label = "In progress", "▶️ Resume Test"
    elif done:
        status, label = "Completed (a repeat attempt is practice only and awards no points)", "🔁 Practice Again"
    else:
        status, label = "Not started", "▶️ Start Test"
    text = (f"{title_block('📝 ' + escape(test['title']))}"
            f"<b>Questions:</b> {qn}\n"
            f"<b>Maximum points:</b> {qn * per}\n"
            f"<b>Time limit:</b> {fmt_duration(seconds)} for the whole test\n"
            f"<b>Available for:</b> {time_left(test['expires_at'])}\n"
            f"<b>Status:</b> {status}\n\n"
            "<i>The timer starts when you press Start. When the time ends, the test finishes "
            "automatically and unanswered questions count as incorrect. "
            "Correct answers are shown after you finish the test.</i>")
    await show(call, text, kb([btn(label, f"ts:{test['id']}")], [btn("◀️ Back to Tests", "tl:0")], MAIN))


def question_text(test, idx: int, total: int, q, deadline, order) -> str:
    left = fmt_duration(deadline - time.time()) if deadline else "-"
    until = fmt_clock(deadline) if deadline else "-"
    options = "\n".join(f"<b>{OPTS[i]})</b> {escape(q['option_' + letter.lower()])}" for i, letter in enumerate(order))
    return (
        f"🧪 <b>TEST: {escape(test['title'])}</b>\n{LINE}\n"
        f"<b>Question {idx} / {total}</b>   ⏱ <b>{left}</b> left (until {until})\n\n"
        f"{escape(q['text'])}\n\n{options}"
    )


async def edit_or_send(bot: Bot, chat_id: int, message_id, text: str, markup=None) -> int:
    """Edits a message, or sends a new one if it cannot be edited. Returns the message id."""
    if message_id:
        try:
            await bot.edit_message_text(text, chat_id=chat_id, message_id=message_id, reply_markup=markup)
            return message_id
        except TelegramBadRequest as exc:
            if "message is not modified" in str(exc).lower():
                return message_id
    sent = await bot.send_message(chat_id, text, reply_markup=markup)
    return sent.message_id


def message_id_of(call: CallbackQuery):
    return call.message.message_id if isinstance(call.message, Message) else None


async def present_question(bot: Bot, attempt_id: int, chat_id: int, message_id) -> None:
    """Shows the current question, or the result if none are left or the time is over."""
    att = get_attempt(attempt_id)
    test = get_test(att["test_id"]) if att else None
    if not att or not test or test["status"] == "deleted":
        await edit_or_send(bot, chat_id, message_id,
                           f"{title_block('⚠️ TEST UNAVAILABLE')}This test is no longer available.", kb(MAIN))
        return
    if att["q_deadline"] and att["q_deadline"] <= time.time():  # the test time is over
        await finalize_attempt(bot, attempt_id, chat_id, message_id)
        return
    q, idx, total = next_question(att)
    if q is None:
        await finalize_attempt(bot, attempt_id, chat_id, message_id)
        return
    order = option_order(att, q["id"])  # the button data carries the ORIGINAL letter of each option
    markup = kb(
        [btn("A", f"ta:{attempt_id}:{q['id']}:{order[0]}"), btn("B", f"ta:{attempt_id}:{q['id']}:{order[1]}")],
        [btn("C", f"ta:{attempt_id}:{q['id']}:{order[2]}"), btn("D", f"ta:{attempt_id}:{q['id']}:{order[3]}")],
        [btn("❌ Finish Test", f"tf:{attempt_id}")],
    )
    deadline = att["q_deadline"]
    if not deadline:  # attempt created before the whole-test timer existed
        deadline = int(time.time()) + test_seconds(att["test_id"])
        with db() as c:
            c.execute("UPDATE attempts SET q_deadline = ? WHERE id = ?", (deadline, attempt_id))
    message_id = await edit_or_send(bot, chat_id, message_id, question_text(test, idx, total, q, deadline, order), markup)
    set_message(attempt_id, chat_id, message_id)


@router.callback_query(F.data.startswith("ts:"), HasRole("student"))
async def cb_test_start(call: CallbackQuery) -> None:
    test = get_test(int(call.data.split(":")[1]))
    if not is_open(test):
        await call.answer("This test is not available.", show_alert=True)
        return
    attempt_id = open_attempt(call.from_user.id, test["id"])
    log_activity(call.from_user.id, "test_started", str(test["id"]))
    await call.answer()
    await present_question(call.bot, attempt_id, call.from_user.id, message_id_of(call))


@router.callback_query(F.data.startswith("ta:"), HasRole("student"))
async def cb_answer(call: CallbackQuery) -> None:
    _, aid, qid, opt = call.data.split(":")
    att = get_attempt(int(aid))
    if not att or att["user_id"] != call.from_user.id or att["finished_at"] or opt not in OPTS:
        await call.answer("This test session is no longer active.", show_alert=True)
        return
    if att["q_deadline"] and time.time() > att["q_deadline"] + GRACE:
        await call.answer("⏱ Time is up. The test has been finished.", show_alert=True)
        await finalize_attempt(call.bot, att["id"], call.from_user.id, message_id_of(call))
        return
    q, _, _ = next_question(att)
    if q is not None and q["id"] == int(qid):  # stale or double taps are ignored
        record_answer(att, q, opt)
    await call.answer()
    await present_question(call.bot, att["id"], call.from_user.id, message_id_of(call))


@router.callback_query(F.data.startswith("tf:"), HasRole("student"))
async def cb_finish_ask(call: CallbackQuery) -> None:
    aid = int(call.data.split(":")[1])
    text = (f"{title_block('⚠️ FINISH TEST')}"
            "Are you sure you want to finish now?\n"
            "Unanswered questions will be counted as incorrect.\n\n"
            "<i>The test timer keeps running.</i>")
    await show(call, text, kb([btn("✅ Yes, finish", f"tfy:{aid}")], [btn("↩️ Continue", f"tfn:{aid}")]))


@router.callback_query(F.data.startswith("tfn:"), HasRole("student"))
async def cb_finish_no(call: CallbackQuery) -> None:
    att = get_attempt(int(call.data.split(":")[1]))
    if not att or att["user_id"] != call.from_user.id or att["finished_at"]:
        await call.answer("This test session is no longer active.", show_alert=True)
        return
    await call.answer()
    await present_question(call.bot, att["id"], call.from_user.id, message_id_of(call))


@router.callback_query(F.data.startswith("tfy:"), HasRole("student"))
async def cb_finish_yes(call: CallbackQuery) -> None:
    att = get_attempt(int(call.data.split(":")[1]))
    if not att or att["user_id"] != call.from_user.id:
        await call.answer("This test session is no longer active.", show_alert=True)
        return
    await call.answer()
    await finalize_attempt(call.bot, att["id"], call.from_user.id, message_id_of(call))


async def finalize_attempt(bot: Bot, attempt_id: int, chat_id: int, message_id) -> None:
    """Finishes the attempt and shows the result. Rank-ups are recorded for the group digest."""
    att = get_attempt(attempt_id)
    user_id = att["user_id"]
    before = total_points(user_id)
    att, fresh = finish_attempt(attempt_id)
    after = total_points(user_id)
    test = get_test(att["test_id"])
    title = test["title"] if test else "Test"
    ok, n = att["correct_count"], att["total_questions"]
    acc = (ok / n * 100) if n else 0.0
    old_rank, new_rank = rank_for(before), rank_for(after)

    lines = [f"{title_block('✅ TEST COMPLETED')}<b>Test:</b> {escape(title)}",
             f"<b>Correct:</b> {ok} / {n}",
             f"<b>Accuracy:</b> {pct(acc)}"]
    if att["practice"]:
        lines.append("\n<i>Practice attempt: no points were awarded.</i>")
    else:
        lines.append(f"<b>Points earned:</b> +{att['points_earned']}")
        lines.append(f"<b>Total points:</b> {after}")
    if fresh and new_rank != old_rank:
        lines.append(f"\n🎉 <b>New rank reached: {escape(new_rank)}</b>")
    wait = review_wait(test)
    if wait > 0:
        lines.append(f"\n<i>The correct answers can be reviewed after the test ends (in {fmt_duration(wait)}).</i>")
    markup = kb([btn("📋 Review Answers", f"rv:{attempt_id}:0")], MAIN)
    try:
        await edit_or_send(bot, chat_id or user_id, message_id, "\n".join(lines), markup)
    except TelegramAPIError as exc:
        logging.warning("Could not show the result to student %s: %s", user_id, exc)

    if fresh:
        log_activity(user_id, "test_finished", f"attempt {attempt_id}: {ok}/{n}")
        if not att["practice"] and new_rank != old_rank:
            log_activity(user_id, "promotion", new_rank)


@router.callback_query(F.data.startswith("rv:"), HasRole("student"))
async def cb_review(call: CallbackQuery) -> None:
    _, aid, page = call.data.split(":")
    page = int(page)
    att = get_attempt(int(aid))
    if not att or att["user_id"] != call.from_user.id or not att["finished_at"]:
        await call.answer("This review is not available.", show_alert=True)
        return
    wait = review_wait(get_test(att["test_id"]))
    if wait > 0:
        await call.answer(f"The answers will open when the test ends, in {fmt_duration(wait)}.", show_alert=True)
        return
    with db() as c:
        rows = c.execute(
            "SELECT q.id AS qid, q.text, q.option_a, q.option_b, q.option_c, q.option_d, q.correct, "
            "a.chosen, a.is_correct FROM answers a JOIN questions q ON q.id = a.question_id "
            "WHERE a.attempt_id = ? ORDER BY a.id", (att["id"],)).fetchall()
    total = len(rows)
    chunk = rows[page * REVIEW_PAGE:(page + 1) * REVIEW_PAGE]
    pages = max(1, -(-total // REVIEW_PAGE))
    lines = [f"{title_block(f'📋 REVIEW ({page + 1}/{pages})')}"]
    for i, r in enumerate(chunk, page * REVIEW_PAGE + 1):
        order = option_order(att, r["qid"])  # letters exactly as the student saw them
        opt = {"A": r["option_a"], "B": r["option_b"], "C": r["option_c"], "D": r["option_d"]}
        shown = lambda letter: f"{OPTS[order.index(letter)]}) {escape(clip(opt[letter], 100))}"
        mine = shown(r["chosen"]) if r["chosen"] else "— (no answer)"
        lines.append(f"<b>{i}.</b> {escape(clip(r['text'], 250))}")
        lines.append(f"Your answer: <b>{mine}</b> {'✅' if r['is_correct'] else '❌'}")
        if not r["is_correct"]:
            lines.append(f"Correct answer: <b>{shown(r['correct'])}</b>")
        lines.append("")
    markup = kb(nav_row(f"rv:{att['id']}:", page, total, REVIEW_PAGE), MAIN)
    await show(call, "\n".join(lines).strip(), markup)


# ============================================================================
# Registration (users who are not registered yet)
# ============================================================================

def name_exists(full_name: str) -> bool:
    with db() as c:
        names = [r[0] or "" for r in c.execute("SELECT full_name FROM users")]
    return any(n.casefold() == full_name.casefold() for n in names)


def numbered_name(full_name: str) -> str:
    number = 2
    while name_exists(f"{full_name} ({number})"):
        number += 1
    return f"{full_name} ({number})"


@router.message(F.text, HasRole(None))
async def register_handler(message: Message) -> None:
    user = message.from_user
    if get_setting("registration_open", "1") != "1":
        await message.answer(TXT_REG_CLOSED)
        return

    # Step 1: the access code (asked once, before the name)
    code = get_setting("access_code").strip()
    if code and user.id not in CODE_OK:
        fails, locked_until = CODE_FAILS.get(user.id, (0, 0))
        if locked_until > time.time():
            await message.answer(f"⛔ Too many incorrect attempts. Please try again in "
                                 f"{fmt_duration(locked_until - time.time())}.")
            return
        if message.text.strip() == code:
            CODE_OK.add(user.id)
            CODE_FAILS.pop(user.id, None)
            await message.answer("✅ <b>Access code accepted.</b>")
            await message.answer(TXT_WELCOME)
            return
        fails += 1
        if fails >= CODE_MAX_TRIES:
            CODE_FAILS[user.id] = (0, time.time() + CODE_LOCK_SECONDS)
            await message.answer(f"⛔ Too many incorrect attempts. Please try again in "
                                 f"{fmt_duration(CODE_LOCK_SECONDS)}.")
        else:
            CODE_FAILS[user.id] = (fails, 0)
            await message.answer("⚠️ Incorrect access code. Please try again.")
        return

    # Step 2: the full name
    full_name = parse_full_name(message.text)
    if not full_name:
        await message.answer(TXT_BAD_NAME)
        return
    numbered = False
    if name_exists(full_name):
        if user.id not in DUP_WARNED:
            DUP_WARNED.add(user.id)
            await message.answer(TXT_DUP_NAME)
            return
        full_name = numbered_name(full_name)
        numbered = True
    register_user(user.id, full_name, user.username)
    CODE_OK.discard(user.id)
    DUP_WARNED.discard(user.id)
    log_activity(user.id, "registered", full_name)
    note = "\n<i>This name was already used by another student, so a number was added.</i>" if numbered else ""
    await message.answer(
        f"✅ <b>REGISTRATION COMPLETE</b>\n{LINE}\n"
        f"Welcome, <b>{escape(full_name)}</b>. Your account has been created successfully.{note}"
    )
    await show_home(message, first_time=True)
    if get_setting("notify_registration") == "1":
        with db() as c:
            total = c.execute("SELECT COUNT(*) FROM users").fetchone()[0]
        uname = f"@{user.username}" if user.username else "no username"
        await notify_creator(message.bot, f"{title_block('👤 NEW STUDENT')}"
                                          f"<b>Name:</b> {escape(full_name)}\n"
                                          f"<b>Username:</b> {escape(uname)}\n"
                                          f"<b>Total students:</b> {total}")


# ============================================================================
# Staff: create a test (Teacher / Supporter)
# ============================================================================

def duration_markup() -> InlineKeyboardMarkup:
    return kb(
        [btn("30 min", "ct:dur:30"), btn("45 min", "ct:dur:45"), btn("1 hour", "ct:dur:60")],
        [btn("1.5 hours", "ct:dur:90"), btn("2 hours", "ct:dur:120"), btn("3 hours", "ct:dur:180")],
        [btn("❌ Cancel", "ct:cancel")],
    )


def ct_markup(data=None) -> InlineKeyboardMarkup:
    rows = [[btn("✅ Publish", "ct:pub"), btn("❌ Cancel", "ct:cancel")]]
    if data is not None:
        rows.insert(0, [btn(f"🔀 Shuffle options: {'On' if data.get('shuffle', True) else 'Off'}", "ct:shuf")])
        if data.get("questions"):
            rows.insert(1, [btn("↩️ Remove last question", "ct:undo")])
    return kb(*rows)


def ct_status(data: dict) -> str:
    qs = data.get("questions", [])
    mn, mx = get_int("min_questions", 10), get_int("max_questions", 60)
    lines = [
        f"📝 <b>CREATE TEST: {escape(data['title'])}</b>", LINE,
        f"<b>Questions added:</b> {len(qs)} / {mx} (minimum {mn})",
        f"<b>Time limit:</b> {fmt_duration(data['minutes'] * 60)} for the whole test",
        f"<b>Shuffle options:</b> {'On' if data.get('shuffle', True) else 'Off'} (questions are always shuffled)", "",
    ]
    if len(qs) >= mx:
        lines.append("The maximum number of questions has been reached. Please press <b>Publish</b>.")
    else:
        lines.append(f"Send question <b>{len(qs) + 1}</b> as text, or press <b>Publish</b> when you are done.")
        if not qs:
            lines += [
                "",
                "<i>Tip: you can send one or more complete questions in a single message "
                "(separate questions with a blank line):</i>",
                "<code>She ___ to school every day.\nA) go\nB) goes\nC) going\nD) gone\nAnswer: B</code>",
                "",
                "<i>Switch shuffling off if your options refer to each other (for example “A and B”).</i>",
            ]
    return "\n".join(lines)


@router.callback_query(F.data.in_({"panel:create_test", "cr:create_test"}), HasRole(*STAFF))
async def cb_create_test(call: CallbackQuery, state: FSMContext) -> None:
    allowed_at = None if get_role(call.from_user.id) == "creator" else next_posting_time(call.from_user.id)
    if allowed_at:
        left = (allowed_at - datetime.now(timezone.utc)).total_seconds()
        text = (f"{title_block('⏳ POSTING LIMIT')}"
                f"Only one test can be published every {get_int('test_lifetime_hours', 24)} hours.\n"
                f"You can publish your next test in <b>{fmt_duration(left)}</b>.")
        await show(call, text, kb(MAIN))
        return
    await state.clear()
    await state.set_state(CreateTest.title)
    text = (f"{title_block('📝 CREATE TEST')}"
            "Step 1. Please send the <b>title</b> of the test.\n\n"
            f"<i>The test will be available to students for {get_int('test_lifetime_hours', 24)} hours "
            "and will then be removed automatically.</i>")
    await show(call, text, kb([btn("❌ Cancel", "ct:cancel")]))


@router.message(StateFilter(CreateTest.title), F.text, HasRole(*STAFF))
async def ct_title(message: Message, state: FSMContext) -> None:
    title = message.text.strip()
    if not 3 <= len(title) <= 80:
        await message.answer("The title must be between 3 and 80 characters. Please try again.")
        return
    await state.update_data(title=title, questions=[], draft={}, step="duration", minutes=60, shuffle=True)
    await state.set_state(CreateTest.question)
    text = (f"{title_block('⏱ TIME LIMIT')}"
            "Step 2. How much time will a student have to complete the <b>whole test</b>?\n"
            "Choose below, or send the time yourself, for example <code>90</code> (minutes) "
            "or <code>2h</code>.\n\n"
            "<i>The timer starts when the student presses Start. Allowed: 1 minute to 12 hours.</i>")
    await message.answer(text, reply_markup=duration_markup())


async def apply_duration(target, state: FSMContext, minutes: int) -> None:
    await state.update_data(minutes=minutes, step="q")
    data = await state.get_data()
    await show(target, ct_status(data), ct_markup(data))


@router.callback_query(StateFilter(CreateTest.question), F.data.startswith("ct:dur:"), HasRole(*STAFF))
async def ct_duration_button(call: CallbackQuery, state: FSMContext) -> None:
    data = await state.get_data()
    minutes = parse_minutes(call.data.split(":")[2])
    if data.get("step") != "duration" or minutes is None:
        await call.answer()
        return
    await apply_duration(call, state, minutes)


@router.callback_query(StateFilter(CreateTest.question), F.data.startswith("ct:ans:"), HasRole(*STAFF))
async def ct_answer_button(call: CallbackQuery, state: FSMContext) -> None:
    data = await state.get_data()
    letter = call.data.split(":")[2]
    if data.get("step") != "correct" or letter not in OPTS:
        await call.answer()
        return
    d = data["draft"]
    qs = data["questions"]
    qs.append({"q": d["q"], "a": d["a"], "b": d["b"], "c": d["c"], "d": d["d"], "correct": letter})
    await state.update_data(questions=qs, step="q", draft={})
    data["questions"] = qs
    await show(call, "✅ Question saved.\n\n" + ct_status(data), ct_markup(data))


@router.message(StateFilter(CreateTest.question), F.text, HasRole(*STAFF))
async def ct_question(message: Message, state: FSMContext) -> None:
    data = await state.get_data()
    step = data.get("step", "q")
    text = message.text.strip()

    if step == "duration":
        minutes = parse_minutes(text)
        if minutes is None:
            await message.answer("Please send the time as a number of minutes (for example <code>90</code>) "
                                 "or in hours (for example <code>2h</code>), from 1 minute to 12 hours. "
                                 "You can also use the buttons above.")
            return
        await apply_duration(message, state, minutes)
        return
    if step == "correct":
        await message.answer("Please choose the correct answer using the buttons above.")
        return

    qs = data["questions"]
    mx = get_int("max_questions", 60)
    if len(qs) >= mx:
        await message.answer("The maximum number of questions has been reached. Please press Publish.",
                             reply_markup=ct_markup(data))
        return

    # Complete question(s) in one message
    if looks_bulk(text):
        parsed = parse_questions(text)
        if parsed is None:
            bad = first_bad_block(text)
            bad_note = f"Question {bad} of your message has a problem.\n\n" if bad else ""
            await message.answer(
                f"{title_block('⚠️ INVALID FORMAT')}{bad_note}"
                "Each question needs a question line, options A, B, C, D and an answer line.\n\n"
                "<code>Question text\nA) ...\nB) ...\nC) ...\nD) ...\nAnswer: B</code>\n\n"
                "<i>Separate several questions with a blank line.</i>")
            return
        room = mx - len(qs)
        added = parsed[:room]
        qs.extend(added)
        await state.update_data(questions=qs, step="q", draft={})
        data["questions"] = qs
        note = f"✅ {len(added)} question(s) added."
        if len(parsed) > len(added):
            note += f" {len(parsed) - len(added)} skipped (maximum reached)."
        await message.answer(note + "\n\n" + ct_status(data), reply_markup=ct_markup(data))
        return

    # One question, step by step: question -> A -> B -> C -> D -> correct answer
    limit = 500 if step == "q" else 200
    if len(text) > limit:
        await message.answer(f"This is too long (maximum {limit} characters). Please shorten it.")
        return
    draft = data.get("draft", {})
    draft[step] = text
    order = ["q", "a", "b", "c", "d"]
    nxt = "correct" if step == "d" else order[order.index(step) + 1]
    await state.update_data(draft=draft, step=nxt)
    if nxt == "correct":
        recap = (f"{escape(draft['q'])}\n\n<b>A)</b> {escape(draft['a'])}\n<b>B)</b> {escape(draft['b'])}\n"
                 f"<b>C)</b> {escape(draft['c'])}\n<b>D)</b> {escape(draft['d'])}")
        await message.answer(
            f"{title_block('✔️ CORRECT ANSWER')}{recap}\n\nWhich option is correct?",
            reply_markup=kb([btn("A", "ct:ans:A"), btn("B", "ct:ans:B")],
                            [btn("C", "ct:ans:C"), btn("D", "ct:ans:D")],
                            [btn("❌ Cancel", "ct:cancel")]))
    else:
        await message.answer(f"Send option <b>{nxt.upper()}</b>.")


@router.message(StateFilter(CreateTest.title, CreateTest.question), HasRole(*STAFF))
async def ct_not_text(message: Message) -> None:
    await message.answer("Please send text only (no photos, files or stickers).")


@router.callback_query(StateFilter(CreateTest.question), F.data == "ct:shuf", HasRole(*STAFF))
async def ct_shuffle(call: CallbackQuery, state: FSMContext) -> None:
    data = await state.get_data()
    data["shuffle"] = not data.get("shuffle", True)
    await state.update_data(shuffle=data["shuffle"])
    await show(call, ct_status(data), ct_markup(data))


@router.callback_query(StateFilter(CreateTest.question), F.data == "ct:undo", HasRole(*STAFF))
async def ct_undo(call: CallbackQuery, state: FSMContext) -> None:
    data = await state.get_data()
    qs = data.get("questions", [])
    if data.get("step") != "q" or not qs:
        await call.answer("There is no question to remove.", show_alert=True)
        return
    qs.pop()
    await state.update_data(questions=qs)
    data["questions"] = qs
    await show(call, "↩️ The last question was removed.\n\n" + ct_status(data), ct_markup(data))


@router.callback_query(StateFilter(CreateTest.question), F.data == "ct:pub", HasRole(*STAFF))
async def ct_publish(call: CallbackQuery, state: FSMContext) -> None:
    data = await state.get_data()
    qs = data.get("questions", [])
    mn = get_int("min_questions", 10)
    if data.get("step") != "q":
        await call.answer("Please finish the current step first.", show_alert=True)
        return
    if len(qs) < mn:
        await call.answer(f"A test must contain at least {mn} questions.", show_alert=True)
        return
    allowed_at = None if get_role(call.from_user.id) == "creator" else next_posting_time(call.from_user.id)
    if allowed_at:
        await call.answer("You have already published a test within the posting limit.", show_alert=True)
        return
    total_seconds = data["minutes"] * 60
    test_id = save_test(data["title"], call.from_user.id, qs, total_seconds, bool(data.get("shuffle", True)))
    await state.clear()
    log_activity(call.from_user.id, "test_published", f"{test_id}: {data['title']}")
    test = get_test(test_id)
    per = get_int("points_per_correct", 5)
    text = (f"{title_block('✅ TEST PUBLISHED')}"
            f"<b>Title:</b> {escape(test['title'])}\n"
            f"<b>Questions:</b> {len(qs)}\n"
            f"<b>Time limit:</b> {fmt_duration(total_seconds)} per student\n"
            f"<b>Maximum points:</b> {len(qs) * per}\n"
            f"<b>Available until:</b> {local_time(test['expires_at'])} "
            f"({time_left(test['expires_at'])} from now)\n\n"
            "The test is now visible to all students.")
    await show(call, text, kb(MAIN))
    spawn(notify_new_test(call.bot, test_id, call.from_user.id))


@router.callback_query(F.data == "ct:cancel", HasRole(*STAFF))
async def ct_cancel(call: CallbackQuery, state: FSMContext) -> None:
    await state.clear()
    await show_home(call)


# ============================================================================
# Staff: manage tests (Teacher/Supporter: own tests, Creator: all tests)
# ============================================================================

def can_manage(role: str, user_id: int, test) -> bool:
    return bool(test) and test["status"] != "deleted" and (role == "creator" or test["created_by"] == user_id)


STATUS_ICON = {"published": "🟢", "closed": "🔴", "expired": "🔴"}
STATUS_NAME = {"published": "Published", "closed": "Closed", "expired": "Closed (time ended)"}


async def show_manage_list(call: CallbackQuery, page: int) -> None:
    role = get_role(call.from_user.id)
    owner = None if role == "creator" else call.from_user.id
    rows, total = tests_page(page, owner, include_expired=True)
    title = "📋 MANAGE ALL TESTS" if role == "creator" else "📋 MANAGE TESTS"
    text = title_block(title)
    text += ("Select a test to manage." if rows else
             "No tests yet." + ("" if role == "creator" else " Tests you publish will appear here."))
    buttons = [[btn(f"{STATUS_ICON.get(r['status'], '•')} {clip(r['title'], 22)} · {r['qn']}Q · "
                    f"{'ended' if r['status'] == 'expired' else time_left(r['expires_at'])}", f"mtv:{r['id']}")]
               for r in rows]
    top = [[btn("➕ Create Test", "cr:create_test")]] if role == "creator" else []
    await show(call, text, kb(*top, *buttons, nav_row("mt:", page, total, PAGE), MAIN))


@router.callback_query(F.data.in_({"panel:manage_tests", "cr:tests"}), HasRole(*STAFF))
async def cb_manage_tests(call: CallbackQuery) -> None:
    await show_manage_list(call, 0)


@router.callback_query(F.data.startswith("mt:"), HasRole(*STAFF))
async def cb_manage_page(call: CallbackQuery) -> None:
    await show_manage_list(call, int(call.data.split(":")[1]))


async def show_test_details(call: CallbackQuery, test_id: int) -> None:
    role = get_role(call.from_user.id)
    test = get_test(test_id)
    if not can_manage(role, call.from_user.id, test):
        await call.answer("Access denied. You can manage only your own tests.", show_alert=True)
        return
    with db() as c:
        attempts = c.execute(
            "SELECT COUNT(*) FROM attempts WHERE test_id = ? AND finished_at IS NOT NULL "
            "AND COALESCE(practice, 0) = 0", (test_id,)).fetchone()[0]
        owner = c.execute("SELECT name FROM roles WHERE tg_id = ?", (test["created_by"],)).fetchone()
    lines = [f"{title_block('📋 TEST DETAILS')}<b>Title:</b> {escape(test['title'])}",
             f"<b>Status:</b> {STATUS_NAME.get(test['status'], test['status'])}",
             f"<b>Questions:</b> {count_questions(test_id)}",
             f"<b>Time limit:</b> {fmt_duration(test_seconds(test_id))}",
             f"<b>Completed attempts:</b> {attempts}",
             f"<b>Available for:</b> {'ended' if test['status'] == 'expired' else time_left(test['expires_at'])}",
             f"<b>Created:</b> {local_time(test['created_at'])}"]
    if role == "creator":
        who = owner["name"] if owner and owner["name"] else str(test["created_by"])
        lines.append(f"<b>Created by:</b> {escape(who)}")
    toggle = (btn("🔒 Close Test", f"mtc:{test_id}") if test["status"] == "published"
              else btn("🔓 Reopen Test", f"mtc:{test_id}"))
    first_row = ([btn("🗑 Delete Test", f"mtd:{test_id}")] if test["status"] == "expired"
                 else [toggle, btn("🗑 Delete Test", f"mtd:{test_id}")])  # a test whose time ended cannot reopen
    markup = kb(first_row, [btn("📊 Results", f"trv:{test_id}")], [btn("◀️ Back", "mt:0")], MAIN)
    await show(call, "\n".join(lines), markup)


@router.callback_query(F.data.startswith("mtv:"), HasRole(*STAFF))
async def cb_test_details(call: CallbackQuery) -> None:
    await show_test_details(call, int(call.data.split(":")[1]))


@router.callback_query(F.data.startswith("mtc:"), HasRole(*STAFF))
async def cb_test_toggle(call: CallbackQuery) -> None:
    test_id = int(call.data.split(":")[1])
    test = get_test(test_id)
    if not can_manage(get_role(call.from_user.id), call.from_user.id, test):
        await call.answer("Access denied. You can manage only your own tests.", show_alert=True)
        return
    if test["status"] not in ("published", "closed"):
        await call.answer("The time of this test has ended, so it cannot be reopened.", show_alert=True)
        return
    new_status = "closed" if test["status"] == "published" else "published"
    with db() as c:
        c.execute("UPDATE tests SET status = ? WHERE id = ?", (new_status, test_id))
    log_activity(call.from_user.id, "test_" + new_status, str(test_id))
    if new_status == "closed":
        spawn(notify_review_open(call.bot, get_test(test_id)))
    await show_test_details(call, test_id)


@router.callback_query(F.data.startswith("mtd:"), HasRole(*STAFF))
async def cb_test_delete_ask(call: CallbackQuery) -> None:
    test_id = int(call.data.split(":")[1])
    if not can_manage(get_role(call.from_user.id), call.from_user.id, get_test(test_id)):
        await call.answer("Access denied. You can manage only your own tests.", show_alert=True)
        return
    text = (f"{title_block('🗑 DELETE TEST')}"
            "Are you sure you want to delete this test?\n"
            "It will no longer be available to students. Points already earned are kept.")
    await show(call, text, kb([btn("🗑 Yes, delete", f"mtx:{test_id}")], [btn("↩️ Cancel", f"mtv:{test_id}")]))


@router.callback_query(F.data.startswith("mtx:"), HasRole(*STAFF))
async def cb_test_delete(call: CallbackQuery) -> None:
    test_id = int(call.data.split(":")[1])
    if not can_manage(get_role(call.from_user.id), call.from_user.id, get_test(test_id)):
        await call.answer("Access denied. You can manage only your own tests.", show_alert=True)
        return
    with db() as c:
        c.execute("UPDATE tests SET status = 'deleted' WHERE id = ?", (test_id,))
    log_activity(call.from_user.id, "test_deleted", str(test_id))
    await call.answer("Test deleted.")
    await show_manage_list(call, 0)


# ============================================================================
# Staff: test results (read-only, visible for all tests)
# ============================================================================

async def show_results_list(call: CallbackQuery, page: int) -> None:
    rows, total = tests_page(page, None, include_expired=True)
    text = title_block("📊 TEST RESULTS")
    text += "Select a test to see the results." if rows else "No tests have been published yet."
    buttons = [[btn(f"{STATUS_ICON.get(r['status'], '•')} {clip(r['title'], 24)} · {r['done']} done", f"trv:{r['id']}")]
               for r in rows]
    await show(call, text, kb(*buttons, nav_row("tr:", page, total, PAGE), MAIN))


@router.callback_query(F.data == "panel:test_results", HasRole(*TS))
async def cb_results(call: CallbackQuery) -> None:
    await show_results_list(call, 0)


@router.callback_query(F.data.startswith("tr:"), HasRole(*TS))
async def cb_results_page(call: CallbackQuery) -> None:
    await show_results_list(call, int(call.data.split(":")[1]))


@router.callback_query(F.data.startswith("trv:"), HasRole(*STAFF))
async def cb_results_view(call: CallbackQuery) -> None:
    test_id = int(call.data.split(":")[1])
    test = get_test(test_id)
    if not test or test["status"] == "deleted":
        await call.answer("This test is not available.", show_alert=True)
        return
    summary = test_summary(test_id)
    lines = [f"{title_block('📊 TEST RESULTS')}<b>Test:</b> {escape(test['title'])}",
             f"<b>Participants:</b> {summary['participants']}",
             f"<b>Average accuracy:</b> {pct(summary['accuracy'])}",
             f"<b>Students who earned points:</b> {len(summary['earners'])}", ""]
    if not summary["rows"]:
        lines.append("No student has completed this test yet.")
    for i, r in enumerate(summary["rows"][:30], 1):
        acc = (r["correct_count"] / r["total_questions"] * 100) if r["total_questions"] else 0
        lines.append(f"{MEDALS.get(i, f'{i}.')} <b>{escape(r['full_name'])}</b> · "
                     f"{r['correct_count']}/{r['total_questions']} ({pct(acc)}) · +{r['points_earned']}")
    if len(summary["rows"]) > 30:
        lines.append(f"…and {len(summary['rows']) - 30} more.")
    back = btn("◀️ Back", "tr:0" if get_role(call.from_user.id) in TS else f"mtv:{test_id}")
    await show(call, "\n".join(lines), kb([back], MAIN))


# ============================================================================
# Staff: student picker (Student Statistics, Manage Users, Send to Student)
# ============================================================================

CTX_TITLES = {"stat": "👥 STUDENT STATISTICS", "usr": "👤 MANAGE USERS", "ann": "📢 SELECT A STUDENT",
              "pts": "➕ ADJUST POINTS", "blk": "🚫 BLOCK / UNBLOCK"}
CTX_ROLES = {"stat": TS, "usr": ("creator",), "ann": STAFF, "pts": ("creator",), "blk": ("creator",)}


def ctx_ok(ctx: str, role) -> bool:
    return ctx in CTX_ROLES and role in CTX_ROLES[ctx]


async def show_students(target, state: FSMContext, ctx: str, page: int) -> None:
    data = await state.get_data()
    query = data.get("sp_query")
    rows, total = students_page(query, page)
    text = f"{title_block(CTX_TITLES[ctx])}<b>Students:</b> {total}"
    if query:
        text += f"\n<b>Search:</b> <i>{escape(query)}</i>"
    if not rows:
        text += "\n\nNo students found."
    buttons = [[btn(f"{'🚫 ' if r['blocked'] else ''}{clip(r['full_name'], 24)} · {r['pts']}",
                    f"spk:{ctx}:{r['tg_id']}")] for r in rows]
    tools = [btn("🔎 Search", f"sps:{ctx}")]
    if query:
        tools.append(btn("✖️ Clear", f"spc:{ctx}"))
    back = [btn("◀️ Back", "an:menu")] if ctx == "ann" else None
    await show(target, text, kb(*buttons, nav_row(f"sp:{ctx}:", page, total, PAGE_STUDENTS), tools, back, MAIN))


@router.callback_query(F.data == "panel:student_stats", HasRole(*TS))
async def cb_student_stats(call: CallbackQuery, state: FSMContext) -> None:
    await state.clear()
    await show_students(call, state, "stat", 0)


@router.callback_query(F.data == "cr:users", HasRole("creator"))
async def cb_manage_users(call: CallbackQuery, state: FSMContext) -> None:
    await state.clear()
    await show_students(call, state, "usr", 0)


@router.callback_query(F.data.startswith("sp:"), HasRole(*STAFF))
async def cb_students_page(call: CallbackQuery, state: FSMContext) -> None:
    _, ctx, page = call.data.split(":")
    if not ctx_ok(ctx, get_role(call.from_user.id)):
        await call.answer("Access denied.", show_alert=True)
        return
    await state.set_state(None)
    await show_students(call, state, ctx, int(page))


@router.callback_query(F.data.startswith("sps:"), HasRole(*STAFF))
async def cb_students_search(call: CallbackQuery, state: FSMContext) -> None:
    ctx = call.data.split(":")[1]
    if not ctx_ok(ctx, get_role(call.from_user.id)):
        await call.answer("Access denied.", show_alert=True)
        return
    await state.update_data(sp_ctx=ctx)
    await state.set_state(Pick.search)
    text = f"{title_block('🔎 SEARCH')}Send a name, or part of a name, to search for."
    await show(call, text, kb([btn("↩️ Cancel", f"sp:{ctx}:0")]))


@router.message(StateFilter(Pick.search), F.text, HasRole(*STAFF))
async def pick_search_text(message: Message, state: FSMContext) -> None:
    data = await state.get_data()
    ctx = data.get("sp_ctx")
    if not ctx_ok(ctx, get_role(message.from_user.id)):
        await state.clear()
        await show_home(message)
        return
    await state.set_state(None)
    await state.update_data(sp_query=message.text.strip()[:40])
    await show_students(message, state, ctx, 0)


@router.callback_query(F.data.startswith("spc:"), HasRole(*STAFF))
async def cb_students_clear(call: CallbackQuery, state: FSMContext) -> None:
    ctx = call.data.split(":")[1]
    if not ctx_ok(ctx, get_role(call.from_user.id)):
        await call.answer("Access denied.", show_alert=True)
        return
    await state.update_data(sp_query=None)
    await show_students(call, state, ctx, 0)


@router.callback_query(F.data.startswith("spk:"), HasRole(*STAFF))
async def cb_student_picked(call: CallbackQuery, state: FSMContext) -> None:
    _, ctx, sid = call.data.split(":")
    sid = int(sid)
    if not ctx_ok(ctx, get_role(call.from_user.id)):
        await call.answer("Access denied.", show_alert=True)
        return
    user = get_user(sid)
    if not user:
        await call.answer("This student no longer exists.", show_alert=True)
        return
    if ctx == "ann":
        await start_announce_compose(call, state, sid)
        return
    if ctx == "pts":
        await state.update_data(target=sid)
        await state.set_state(PointsAdjust.value)
        text = (f"{title_block('➕ ADJUST POINTS')}"
                f"<b>Student:</b> {escape(user['full_name'])}\n"
                f"<b>Current points:</b> {total_points(sid)}\n\n"
                "Send the change as a number: <code>20</code> adds 20 points, <code>-20</code> subtracts 20. "
                "You may add a short reason after the number.")
        await show(call, text, kb([btn("↩️ Cancel", "cr:rankings")]))
        return
    uname = f"@{user['username']}" if user["username"] else "—"
    extra = f"🔗 <b>Username:</b> {escape(uname)}\n🆔 <b>ID:</b> {sid}\n"
    card = profile_card(sid, title="👥 STUDENT PROFILE", extra=extra)
    card += f"\n📅 <b>Registered:</b> {local_time(user['registered_at']) if user['registered_at'] else '—'}"
    rows = []
    if ctx == "usr":
        rows = [[btn("🗑 Remove User", f"usd:{sid}")]]
    elif ctx == "blk":
        blocked = bool(user["blocked"])
        card += "\n" + ("🚫 <b>Status:</b> Blocked" if blocked else "✅ <b>Status:</b> Active")
        rows = [[btn("✅ Unblock Student" if blocked else "🚫 Block Student", f"bl:{sid}")]]
    await show(call, card, kb(*rows, [btn("◀️ Back to list", f"sp:{ctx}:0")], MAIN))


@router.callback_query(F.data.startswith("usd:"), HasRole("creator"))
async def cb_user_delete_ask(call: CallbackQuery) -> None:
    sid = int(call.data.split(":")[1])
    user = get_user(sid)
    if not user:
        await call.answer("This student no longer exists.", show_alert=True)
        return
    text = (f"{title_block('🗑 REMOVE USER')}"
            f"Remove <b>{escape(user['full_name'])}</b>?\n"
            "The profile, all results and all points will be permanently deleted. "
            "The student will have to register again.")
    await show(call, text, kb([btn("🗑 Yes, remove", f"usx:{sid}")], [btn("↩️ Cancel", f"spk:usr:{sid}")]))


@router.callback_query(F.data.startswith("usx:"), HasRole("creator"))
async def cb_user_delete(call: CallbackQuery, state: FSMContext) -> None:
    sid = int(call.data.split(":")[1])
    delete_user(sid)
    log_activity(call.from_user.id, "user_removed", str(sid))
    await call.answer("User removed.")
    await show_students(call, state, "usr", 0)


# ============================================================================
# Creator: Bot Settings (6 buttons)
# ============================================================================

def reports_text() -> str:
    if get_setting("auto_reports") == "1":
        return f"On, daily at {get_int('report_hour', 21):02d}:00"
    return "Off"


def current_value(key: str) -> str:
    kind = SETTING_DEFS[key][1]
    if key == "questions_range":
        return f"{get_int('min_questions', 10)} {get_int('max_questions', 60)}"
    if kind == "reports":
        return reports_text()
    if kind == "ranks":
        return get_setting("rank_thresholds")
    return get_setting(key)


def settings_text() -> str:
    tiers = parse_ranks(get_setting("rank_thresholds")) or []
    group = "connected" if get_group_id() else "not connected (send /setgroup inside your group)"
    return "\n".join([
        title_block("⚙️ BOT SETTINGS").rstrip(),
        f"<b>Points per answer:</b> {get_int('points_per_correct', 5)}",
        f"<b>Rank thresholds:</b> {len(tiers)} ranks",
        f"<b>Questions per test:</b> {get_int('min_questions', 10)} – {get_int('max_questions', 60)}",
        f"<b>Test lifetime:</b> {get_int('test_lifetime_hours', 24)} hours",
        f"<b>Group results:</b> {'On' if get_setting('post_results') == '1' else 'Off'}",
        f"<b>Group reports:</b> {reports_text()}",
        f"<b>Group:</b> {group}",
    ])


def settings_markup() -> InlineKeyboardMarkup:
    items = [btn(f"{'🔁' if kind == 'bool' else '✏️'} {label}", f"bs:{key}")
             for key, (label, kind, lo, hi) in SETTING_DEFS.items()]
    rows = [items[i:i + 2] for i in range(0, len(items), 2)]
    return kb(*rows, MAIN)


def setting_hint(key: str) -> str:
    label, kind, lo, hi = SETTING_DEFS[key]
    if kind == "int":
        return f"Send a whole number from {lo} to {hi}."
    if kind == "range":
        return "Send the minimum and maximum number of questions, for example <code>10 60</code>."
    if kind == "reports":
        return ("Send the hour (0-23) when the daily report is posted, for example <code>21</code>, "
                "or <code>off</code> to switch the reports off.")
    return ("Send the ranks as <code>points:Name</code> pairs separated by commas, starting from 0.\n"
            "Example: <code>0:Newcomer,100:Noob,200:Rookie</code>")


def validate_setting(key: str, text: str):
    """Returns the cleaned value, or None if the input is invalid."""
    label, kind, lo, hi = SETTING_DEFS[key]
    text = (text or "").strip()
    if kind == "int":
        return str(int(text)) if text.isdigit() and lo <= int(text) <= hi else None
    if kind == "ranks":
        return text if parse_ranks(text) else None
    if kind == "range":
        m = re.fullmatch(r"(\d{1,3})\s*[\s,;\-–]\s*(\d{1,3})", text)
        if m and 1 <= int(m.group(1)) <= int(m.group(2)) <= 100:
            return f"{int(m.group(1))} {int(m.group(2))}"
        return None
    if kind == "reports":
        low = text.lower()
        if low in ("off", "no"):
            return "off"
        if low.isdigit() and 0 <= int(low) <= 23:
            return str(int(low))
    return None


def apply_setting(key: str, value: str) -> None:
    kind = SETTING_DEFS[key][1]
    if kind == "range":
        low, high = value.split()
        set_setting("min_questions", low)
        set_setting("max_questions", high)
    elif kind == "reports":
        if value == "off":
            set_setting("auto_reports", "0")
        else:
            set_setting("auto_reports", "1")
            set_setting("report_hour", value)
    else:
        set_setting(key, value)


@router.callback_query(F.data == "cr:settings", HasRole("creator"))
async def cb_settings(call: CallbackQuery, state: FSMContext) -> None:
    await state.clear()
    await show(call, settings_text(), settings_markup())


@router.callback_query(F.data.startswith("bs:"), HasRole("creator"))
async def cb_setting_pick(call: CallbackQuery, state: FSMContext) -> None:
    key = call.data.split(":", 1)[1]
    if key not in SETTING_DEFS:
        await call.answer("Unknown setting.", show_alert=True)
        return
    label, kind, lo, hi = SETTING_DEFS[key]
    if kind == "bool":
        set_setting(key, "0" if get_setting(key) == "1" else "1")
        await show(call, settings_text(), settings_markup())
        return
    await state.update_data(setting_key=key)
    await state.set_state(SettingEdit.value)
    text = (f"{title_block('✏️ ' + label.upper())}"
            f"<b>Current value:</b> {escape(current_value(key))}\n\n{setting_hint(key)}")
    await show(call, text, kb([btn("↩️ Cancel", "cr:settings")]))


@router.message(StateFilter(SettingEdit.value), F.text, HasRole("creator"))
async def setting_value(message: Message, state: FSMContext) -> None:
    key = (await state.get_data()).get("setting_key")
    if key not in SETTING_DEFS:
        await state.clear()
        await show_home(message)
        return
    value = validate_setting(key, message.text)
    if value is None:
        await message.answer("⚠️ This value is not valid.\n\n" + setting_hint(key))
        return
    apply_setting(key, value)
    await state.clear()
    log_activity(message.from_user.id, "setting_changed", key)
    await message.answer("✅ Saved.")
    await message.answer(settings_text(), reply_markup=settings_markup())


# ============================================================================
# Creator: Manage Roles
# ============================================================================

async def show_roles(target) -> None:
    with db() as c:
        staff = c.execute("SELECT tg_id, role, name FROM roles WHERE role != 'creator' ORDER BY role, name").fetchall()
    lines = [title_block("👥 MANAGE ROLES").rstrip(), "<b>Creator:</b> you", ""]
    if not staff:
        lines.append("No teachers or supporters have been added yet.")
    rows = []
    for r in staff:
        label = escape(r["name"] or str(r["tg_id"]))
        lines.append(f"• <b>{ROLE_LABEL[r['role']]}:</b> {label} (<code>{r['tg_id']}</code>)")
        rows.append([btn(f"❌ Remove {ROLE_LABEL[r['role']]}: {clip(r['name'] or r['tg_id'], 18)}", f"rl:rm:{r['tg_id']}")])
    rows.append([btn("➕ Add Teacher", "rl:add:teacher"), btn("➕ Add Supporter", "rl:add:supporter")])
    await show(target, "\n".join(lines), kb(*rows, MAIN))


@router.callback_query(F.data == "cr:roles", HasRole("creator"))
async def cb_roles(call: CallbackQuery, state: FSMContext) -> None:
    await state.clear()
    await show_roles(call)


@router.callback_query(F.data.startswith("rl:add:"), HasRole("creator"))
async def cb_role_add(call: CallbackQuery, state: FSMContext) -> None:
    role = call.data.split(":")[2]
    if role not in ("teacher", "supporter"):
        await call.answer()
        return
    await state.update_data(new_role=role)
    await state.set_state(RoleAdd.tg_id)
    text = (f"{title_block('➕ ADD ' + ROLE_LABEL[role].upper())}"
            "Send the Telegram ID (numbers only) of the new person.\n"
            "They can find it with @userinfobot, and must press /start in this bot once.")
    await show(call, text, kb([btn("↩️ Cancel", "cr:roles")]))


@router.message(StateFilter(RoleAdd.tg_id), F.text, HasRole("creator"))
async def role_add_value(message: Message, state: FSMContext) -> None:
    role = (await state.get_data()).get("new_role", "teacher")
    raw = message.text.strip()
    if not raw.isdigit() or not 5 <= len(raw) <= 15:
        await message.answer("⚠️ Please send a valid Telegram ID (numbers only).")
        return
    tg_id = int(raw)
    if tg_id == CREATOR_ID:
        await message.answer("The Creator already has full access.")
        return
    with db() as c:
        c.execute(
            "INSERT INTO roles (tg_id, role, added_at) VALUES (?, ?, ?) "
            "ON CONFLICT(tg_id) DO UPDATE SET role = excluded.role", (tg_id, role, now()))
    await state.clear()
    log_activity(message.from_user.id, "role_added", f"{tg_id}: {role}")
    try:
        await message.bot.send_message(
            tg_id, f"You have been assigned the role: <b>{ROLE_LABEL[role]}</b>.\nPress /start to open your panel.")
    except TelegramAPIError:
        pass
    await message.answer(f"✅ {ROLE_LABEL[role]} added: <code>{tg_id}</code>")
    await show_roles(message)


@router.callback_query(F.data.startswith("rl:rm:"), HasRole("creator"))
async def cb_role_remove(call: CallbackQuery) -> None:
    tg_id = int(call.data.split(":")[2])
    with db() as c:
        c.execute("DELETE FROM roles WHERE tg_id = ? AND role != 'creator'", (tg_id,))
    log_activity(call.from_user.id, "role_removed", str(tg_id))
    await call.answer("Role removed.")
    await show_roles(call)


# ============================================================================
# Creator: System Statistics
# ============================================================================

@router.callback_query(F.data == "cr:stats", HasRole("creator"))
async def cb_stats(call: CallbackQuery) -> None:
    s = system_stats()
    text = (f"{title_block('📈 SYSTEM STATISTICS')}"
            f"<b>Students:</b> {s['students']}\n"
            f"<b>Teachers:</b> {s['teachers']}   <b>Supporters:</b> {s['supporters']}\n"
            f"<b>Active tests:</b> {s['published']}   <b>Closed:</b> {s['closed']}\n"
            f"<b>Completed attempts:</b> {s['attempts']}\n"
            f"<b>Answers recorded:</b> {s['answers']}\n"
            f"<b>Points awarded:</b> {s['points']}\n"
            f"<b>Active today:</b> {s['active']} students\n"
            f"<b>Group:</b> {'connected' if get_group_id() else 'not connected'}")
    await show(call, text, kb(MAIN))


# ============================================================================
# Creator: Manage Rankings
# ============================================================================

@router.callback_query(F.data == "cr:rankings", HasRole("creator"))
async def cb_manage_rankings(call: CallbackQuery, state: FSMContext) -> None:
    await state.clear()
    text = (f"{title_block('🏆 MANAGE RANKINGS')}"
            "View the rankings, correct the points of a student, or reset all points.")
    await show(call, text, kb(
        [btn("📅 Daily", "rk:daily"), btn("📆 Weekly", "rk:weekly")],
        [btn("🏆 Overall", "rk:overall")],
        [btn("➕ Adjust Points", "mr:adjust"), btn("🧹 Reset Rankings", "mr:reset")],
        MAIN))


@router.callback_query(F.data == "mr:adjust", HasRole("creator"))
async def cb_adjust_points(call: CallbackQuery, state: FSMContext) -> None:
    await state.clear()
    await show_students(call, state, "pts", 0)


@router.message(StateFilter(PointsAdjust.value), F.text, HasRole("creator"))
async def points_adjust_value(message: Message, state: FSMContext) -> None:
    data = await state.get_data()
    target = int(data["target"])
    m = re.fullmatch(r"([+-]?\d{1,5})(?:\s+(.{1,60}))?", message.text.strip())
    if not m or int(m.group(1)) == 0:
        await message.answer("⚠️ Please send a number such as <code>20</code> or <code>-20</code>.")
        return
    delta = int(m.group(1))
    current = total_points(target)
    if current + delta < 0:
        await message.answer(f"⚠️ The student has only {current} points, so {-delta} cannot be subtracted.")
        return
    reason_text = (m.group(2) or "").strip()
    with db() as c:
        c.execute("INSERT INTO points_history (user_id, points, reason, created_at) VALUES (?, ?, ?, ?)",
                  (target, delta, "manual: " + (reason_text or "adjustment"), now()))
    log_activity(message.from_user.id, "points_adjusted", f"{target}: {delta:+d}")
    await state.clear()
    user = get_user(target)
    after = total_points(target)
    old_rank, new_rank = rank_for(current), rank_for(after)
    ranked_up = delta > 0 and new_rank != old_rank
    if ranked_up:
        log_activity(target, "promotion", new_rank)  # appears in the group's daily digest
    notified = await notify_points_change(message.bot, target, delta, reason_text, after, new_rank, ranked_up)
    status = ("✅ Student notified." if notified
              else "⚠️ The student could not be notified (the bot is blocked or the chat is closed).")
    await message.answer(
        f"{title_block('✅ POINTS UPDATED')}"
        f"<b>Student:</b> {escape(user['full_name'])}\n"
        f"<b>Change:</b> {delta:+d}\n"
        f"<b>Total points:</b> {after}\n"
        f"<b>Rank:</b> {escape(new_rank)}\n\n{status}",
        reply_markup=kb([btn("◀️ Back", "cr:rankings")], MAIN))


@router.callback_query(F.data == "mr:reset", HasRole("creator"))
async def cb_reset_ask(call: CallbackQuery) -> None:
    text = (f"{title_block('🧹 RESET RANKINGS')}"
            "All points of all students will be deleted, so the Daily, Weekly and Overall rankings "
            "start from zero. Answers and completed tests stay in the statistics.\n\n"
            "<i>Tip: create a backup first (Backup & Restore).</i>")
    await show(call, text, kb([btn("🧹 Yes, reset all points", "mr:resetyes")], [btn("↩️ Cancel", "cr:rankings")]))


@router.callback_query(F.data == "mr:resetyes", HasRole("creator"))
async def cb_reset_yes(call: CallbackQuery) -> None:
    with db() as c:
        c.execute("DELETE FROM points_history")
    log_activity(call.from_user.id, "rankings_reset")
    await show(call, f"{title_block('✅ RANKINGS RESET')}All points have been deleted.",
               kb([btn("◀️ Back", "cr:rankings")], MAIN))


# ============================================================================
# Creator: Security & Access
# ============================================================================

def security_screen():
    registration_open = get_setting("registration_open", "1") == "1"
    with db() as c:
        blocked = c.execute("SELECT COUNT(*) FROM users WHERE COALESCE(blocked, 0) = 1").fetchone()[0]
    code = get_setting("access_code").strip()
    text = (f"{title_block('🔐 SECURITY & ACCESS')}"
            f"<b>Registration:</b> {'Open' if registration_open else 'Closed'}\n"
            f"<b>Access code:</b> {escape(code) if code else 'off'}\n"
            f"<b>Required channels:</b> {len(get_channels()) or 'off'}\n"
            f"<b>Blocked students:</b> {blocked}")
    markup = kb(
        [btn("🔒 Close Registration" if registration_open else "🔓 Open Registration", "sec:reg")],
        [btn("🔑 Change Access Code", "sec:code")],
        [btn("📢 Required Channels", "sec:chan")],
        [btn("🚫 Block / Unblock Student", "sec:block")],
        MAIN)
    return text, markup


@router.callback_query(F.data == "cr:security", HasRole("creator"))
async def cb_security(call: CallbackQuery, state: FSMContext) -> None:
    await state.clear()
    text, markup = security_screen()
    await show(call, text, markup)


@router.callback_query(F.data == "sec:reg", HasRole("creator"))
async def cb_security_registration(call: CallbackQuery) -> None:
    set_setting("registration_open", "0" if get_setting("registration_open", "1") == "1" else "1")
    log_activity(call.from_user.id, "registration_toggled", get_setting("registration_open"))
    text, markup = security_screen()
    await show(call, text, markup)


@router.callback_query(F.data == "sec:code", HasRole("creator"))
async def cb_security_code(call: CallbackQuery, state: FSMContext) -> None:
    await state.set_state(CodeEdit.value)
    code = get_setting("access_code").strip()
    text = (f"{title_block('🔑 ACCESS CODE')}"
            f"<b>Current code:</b> {escape(code) if code else 'off'}\n\n"
            "New students must enter this code once when they register.\n"
            "Send the new code (3-20 letters or digits), or <code>off</code> to switch it off.")
    await show(call, text, kb([btn("↩️ Cancel", "cr:security")]))


@router.message(StateFilter(CodeEdit.value), F.text, HasRole("creator"))
async def security_code_value(message: Message, state: FSMContext) -> None:
    text = message.text.strip()
    if text.lower() == "off":
        new_code = ""
    elif re.fullmatch(r"[A-Za-z0-9]{3,20}", text):
        new_code = text
    else:
        await message.answer("⚠️ The code must be 3-20 letters or digits, or <code>off</code>.")
        return
    set_setting("access_code", new_code)
    await state.clear()
    log_activity(message.from_user.id, "access_code_changed")
    await message.answer("✅ Saved.")
    text, markup = security_screen()
    await message.answer(text, reply_markup=markup)


@router.callback_query(F.data == "sec:block", HasRole("creator"))
async def cb_security_block(call: CallbackQuery, state: FSMContext) -> None:
    await state.clear()
    await show_students(call, state, "blk", 0)


@router.callback_query(F.data.startswith("bl:"), HasRole("creator"))
async def cb_block_toggle(call: CallbackQuery, state: FSMContext) -> None:
    sid = int(call.data.split(":")[1])
    user = get_user(sid)
    if not user:
        await call.answer("This student no longer exists.", show_alert=True)
        return
    with db() as c:
        c.execute("UPDATE users SET blocked = ? WHERE tg_id = ?", (0 if user["blocked"] else 1, sid))
    log_activity(call.from_user.id, "student_unblocked" if user["blocked"] else "student_blocked", str(sid))
    await call.answer("Student unblocked." if user["blocked"] else "Student blocked.")
    await show_students(call, state, "blk", 0)


# ============================================================================
# Creator: Backup & Restore
# ============================================================================

def make_backup_file(name: str = None) -> str:
    """Writes a consistent copy of the database to a temporary file and returns its path."""
    name = name or datetime.now(TZ).strftime("academy_backup_%Y-%m-%d_%H-%M.db")
    path = os.path.join(tempfile.gettempdir(), name)
    src = sqlite3.connect(DB_PATH)
    dst = sqlite3.connect(path)
    try:
        src.backup(dst)
    finally:
        dst.close()
        src.close()
    return path


def inspect_backup(path: str):
    """Checks that a file is a healthy academy database. Returns a summary or None."""
    try:
        conn = sqlite3.connect(path)
        try:
            if conn.execute("PRAGMA integrity_check").fetchone()[0] != "ok":
                return None
            tables = {r[0] for r in conn.execute("SELECT name FROM sqlite_master WHERE type = 'table'")}
            if not {"users", "roles", "tests", "settings"} <= tables:
                return None
            return {"students": conn.execute("SELECT COUNT(*) FROM users").fetchone()[0],
                    "tests": conn.execute("SELECT COUNT(*) FROM tests").fetchone()[0]}
        finally:
            conn.close()
    except sqlite3.Error:
        return None


@router.callback_query(F.data == "cr:backup", HasRole("creator"))
async def cb_backup_menu(call: CallbackQuery, state: FSMContext) -> None:
    await state.clear()
    text = (f"{title_block('💾 BACKUP & RESTORE')}"
            "<b>Create Backup</b> sends you a copy of the whole database as a file.\n"
            "<b>Restore from File</b> replaces ALL current data with the data from a backup file.")
    await show(call, text, kb([btn("📤 Create Backup", "bk:make")], [btn("📥 Restore from File", "bk:restore")], MAIN))


@router.callback_query(F.data == "bk:make", HasRole("creator"))
async def cb_backup_make(call: CallbackQuery) -> None:
    await call.answer("Preparing the backup…")
    path = make_backup_file()
    try:
        await call.bot.send_document(
            call.from_user.id, FSInputFile(path),
            caption=f"💾 Database backup\n{datetime.now(TZ).strftime('%Y-%m-%d %H:%M')}\n"
                    "Keep this file safe. It can be restored in Backup & Restore.")
    finally:
        os.remove(path)
    log_activity(call.from_user.id, "backup_created")


@router.callback_query(F.data == "bk:restore", HasRole("creator"))
async def cb_backup_restore(call: CallbackQuery, state: FSMContext) -> None:
    await state.clear()
    await state.set_state(Restore.file)
    text = (f"{title_block('📥 RESTORE FROM FILE')}"
            "Send the backup file (it ends with <code>.db</code>).\n\n"
            "⚠️ Restoring replaces ALL current data. A safety copy of the current data is saved first.")
    await show(call, text, kb([btn("↩️ Cancel", "cr:backup")]))


@router.message(StateFilter(Restore.file), F.document, HasRole("creator"))
async def restore_file(message: Message, state: FSMContext) -> None:
    doc = message.document
    if not (doc.file_name or "").lower().endswith(".db") or (doc.file_size or 0) > 19 * 1024 * 1024:
        await message.answer("⚠️ Please send a backup file that ends with <code>.db</code> (up to 19 MB).")
        return
    path = os.path.join(tempfile.gettempdir(), f"restore_{message.from_user.id}.db")
    await message.bot.download(doc, destination=path)
    info = inspect_backup(path)
    if info is None:
        os.remove(path)
        await message.answer("⚠️ This file is not a valid academy database. Nothing was changed.")
        return
    await state.set_state(None)
    await state.update_data(restore_path=path)
    text = (f"{title_block('📥 CONFIRM RESTORE')}"
            f"<b>File:</b> {escape(doc.file_name)}\n"
            f"<b>Students in file:</b> {info['students']}\n"
            f"<b>Tests in file:</b> {info['tests']}\n\n"
            "All current data will be replaced. Continue?")
    await message.answer(text, reply_markup=kb([btn("✅ Restore", "bk:yes")], [btn("❌ Cancel", "bk:no")]))


@router.message(StateFilter(Restore.file), HasRole("creator"))
async def restore_wrong_content(message: Message) -> None:
    await message.answer("Please send the backup file as a document, or press Cancel.")


@router.callback_query(F.data == "bk:no", HasRole("creator"))
async def cb_restore_no(call: CallbackQuery, state: FSMContext) -> None:
    path = (await state.get_data()).get("restore_path")
    if path and os.path.exists(path):
        os.remove(path)
    await state.clear()
    await show_home(call)


@router.callback_query(F.data == "bk:yes", HasRole("creator"))
async def cb_restore_yes(call: CallbackQuery, state: FSMContext) -> None:
    path = (await state.get_data()).get("restore_path")
    if not path or not os.path.exists(path):
        await call.answer("The file is no longer available. Please start again.", show_alert=True)
        return
    safety = os.path.join(os.path.dirname(os.path.abspath(DB_PATH)), "academy_before_restore.db")
    cur = sqlite3.connect(DB_PATH)
    old = sqlite3.connect(safety)
    try:
        cur.backup(old)
    finally:
        old.close()
        cur.close()
    src = sqlite3.connect(path)
    dst = sqlite3.connect(DB_PATH)
    try:
        src.backup(dst)
    finally:
        dst.close()
        src.close()
    os.remove(path)
    init_db()
    seed_roles()
    await state.clear()
    log_activity(call.from_user.id, "backup_restored")
    await show(call, f"{title_block('✅ RESTORE COMPLETE')}The data has been restored.\n"
                     "<i>The previous data was saved as academy_before_restore.db.</i>", kb(MAIN))


# ============================================================================
# Creator: Notifications
# ============================================================================

def notify_screen():
    lines = [title_block("🔔 NOTIFICATIONS").rstrip(), "Press a line to switch it on or off.", ""]
    rows = []
    for key, label in NOTIFY_DEFS.items():
        on = get_setting(key) == "1"
        lines.append(f"{'🔔' if on else '🔕'} {label}: <b>{'On' if on else 'Off'}</b>")
        rows.append([btn(f"{'🔔' if on else '🔕'} {label}", f"nt:{key}", style="success" if on else None)])
    lines += ["", "<i>Student alerts go to all registered students. The other alerts are sent to you.</i>"]
    return "\n".join(lines), kb(*rows, MAIN)


@router.callback_query(F.data == "cr:notify", HasRole("creator"))
async def cb_notify_menu(call: CallbackQuery, state: FSMContext) -> None:
    await state.clear()
    text, markup = notify_screen()
    await show(call, text, markup)


@router.callback_query(F.data.startswith("nt:"), HasRole("creator"))
async def cb_notify_toggle(call: CallbackQuery) -> None:
    key = call.data.split(":", 1)[1]
    if key not in NOTIFY_DEFS:
        await call.answer()
        return
    set_setting(key, "0" if get_setting(key) == "1" else "1")
    text, markup = notify_screen()
    await show(call, text, markup)


# ============================================================================
# Announcements (Creator, Teacher, Supporter)
# ============================================================================

def announcement_body(text: str, role: str = "") -> str:
    """The announcement is delivered exactly as written: no title and no sender line."""
    return escape((text or "").strip())


async def send_announcement(bot: Bot, chat_id: int, ctype: str, body: str, file_id, markup=None):
    if ctype == "photo":
        return await bot.send_photo(chat_id, file_id, caption=body, reply_markup=markup)
    if ctype == "video":
        return await bot.send_video(chat_id, file_id, caption=body, reply_markup=markup)
    if ctype == "document":
        return await bot.send_document(chat_id, file_id, caption=body, reply_markup=markup)
    return await bot.send_message(chat_id, body, reply_markup=markup)


@router.callback_query(F.data.in_({"panel:announcements", "cr:announce", "an:menu"}), HasRole(*STAFF))
async def cb_ann_menu(call: CallbackQuery, state: FSMContext) -> None:
    await state.clear()
    text = f"{title_block('📢 ANNOUNCEMENTS')}Choose where to send the announcement."
    await show(call, text, kb([btn("📣 Send to Group", "an:group")], [btn("👤 Send to Student", "an:student")], MAIN))


async def start_announce_compose(call: CallbackQuery, state: FSMContext, target) -> None:
    await state.clear()
    await state.update_data(target=str(target))
    await state.set_state(Announce.content)
    if target == "group":
        dest = "the group"
    else:
        user = get_user(int(target))
        dest = escape(user["full_name"]) if user else str(target)
    text = (f"{title_block('📢 NEW ANNOUNCEMENT')}"
            f"<b>Recipient:</b> {dest}\n\n"
            "Send the announcement now: text, a photo, a video, a document or a link.\n"
            "<i>For media, you may add a caption.</i>")
    await show(call, text, kb([btn("❌ Cancel", "an:cancel")]))


@router.callback_query(F.data == "an:group", HasRole(*STAFF))
async def cb_ann_group(call: CallbackQuery, state: FSMContext) -> None:
    if not get_group_id():
        await call.answer("No group is connected. Add the bot to your group and ask the Creator "
                          "to send /setgroup there.", show_alert=True)
        return
    await start_announce_compose(call, state, "group")


@router.callback_query(F.data == "an:student", HasRole(*STAFF))
async def cb_ann_student(call: CallbackQuery, state: FSMContext) -> None:
    await state.clear()
    await show_students(call, state, "ann", 0)


@router.message(StateFilter(Announce.content), HasRole(*STAFF))
async def an_content(message: Message, state: FSMContext) -> None:
    ctype, file_id, text = None, None, ""
    if message.photo:
        ctype, file_id, text = "photo", message.photo[-1].file_id, message.caption or ""
    elif message.video:
        ctype, file_id, text = "video", message.video.file_id, message.caption or ""
    elif message.document:
        ctype, file_id, text = "document", message.document.file_id, message.caption or ""
    elif message.text:
        ctype, text = "text", message.text
    else:
        await message.answer("This type of content is not supported. Please send text, a photo, "
                             "a video, a document or a link.")
        return
    role = get_role(message.from_user.id)
    body = announcement_body(text, role)
    limit = 4096 if ctype == "text" else 1024
    if len(body) > limit:
        await message.answer(f"⚠️ This announcement is too long ({len(body)} / {limit} characters). "
                             "Please shorten it and send it again.")
        return
    await state.update_data(ctype=ctype, text=text, file_id=file_id)
    await state.set_state(Announce.preview)
    await message.answer("👁 <b>PREVIEW</b>: this is how the announcement will look. "
                         "Press Publish to send it.")
    await send_announcement(message.bot, message.chat.id, ctype, body, file_id,
                            kb([btn("✅ Publish", "an:pub"), btn("❌ Cancel", "an:cancel")]))


@router.message(StateFilter(Announce.preview), HasRole(*STAFF))
async def an_preview_text(message: Message) -> None:
    await message.answer("Please press <b>Publish</b> or <b>Cancel</b> under the preview.")


@router.callback_query(StateFilter(Announce.preview), F.data == "an:pub", HasRole(*STAFF))
async def an_publish(call: CallbackQuery, state: FSMContext) -> None:
    data = await state.get_data()
    role = get_role(call.from_user.id)
    target = data.get("target", "group")
    chat_id = get_group_id() if target == "group" else int(target)
    if chat_id is None:
        await call.answer("No group is connected.", show_alert=True)
        return
    body = announcement_body(data.get("text", ""), role)
    delivered = 1
    try:
        await send_announcement(call.bot, chat_id, data["ctype"], body, data.get("file_id"))
    except TelegramAPIError as exc:
        delivered = 0
        logging.warning("Announcement delivery failed: %s", exc)
    with db() as c:
        c.execute(
            "INSERT INTO announcements (author_id, content_type, text, file_id, created_at, target, delivered) "
            "VALUES (?, ?, ?, ?, ?, ?, ?)",
            (call.from_user.id, data["ctype"], data.get("text", ""), data.get("file_id"), now(), target, delivered))
    await state.clear()
    log_activity(call.from_user.id, "announcement", f"{target}: {'sent' if delivered else 'failed'}")
    try:
        await call.message.edit_reply_markup(reply_markup=None)
    except (TelegramAPIError, AttributeError):
        pass
    if delivered:
        text = f"{title_block('✅ ANNOUNCEMENT PUBLISHED')}The announcement has been delivered."
    else:
        text = (f"{title_block('❌ DELIVERY FAILED')}The announcement could not be delivered.\n"
                "A student must have started the bot and not blocked it; for the group, "
                "the bot must still be a member.")
    await call.answer()
    await call.bot.send_message(call.from_user.id, text, reply_markup=kb(MAIN))


@router.callback_query(F.data == "an:cancel", HasRole(*STAFF))
async def an_cancel(call: CallbackQuery, state: FSMContext) -> None:
    await state.clear()
    try:
        await call.message.edit_reply_markup(reply_markup=None)
    except (TelegramAPIError, AttributeError):
        pass
    await show_home(call)


# ============================================================================
# Group features
# ============================================================================

def is_connected_group(message: Message) -> bool:
    gid = get_group_id()
    return gid is not None and message.chat.id == gid


@group_router.message(Command("setgroup"))
async def g_setgroup(message: Message) -> None:
    if not message.from_user or get_role(message.from_user.id) != "creator":
        await message.reply("Access denied. Only the Creator can connect this group.")
        return
    set_setting("group_chat_id", str(message.chat.id))
    log_activity(message.from_user.id, "group_connected", str(message.chat.id))
    await message.answer(
        f"{title_block('✅ GROUP CONNECTED')}"
        "This group is now connected. Every day the bot posts the leaderboard, the tests that ended "
        "and the new ranks here.\n\n"
        "Commands: /rankings, /daily, /weekly")


async def group_leaderboard(message: Message, kind: str) -> None:
    """/rankings /daily /weekly in the connected group: one leaderboard picture, 30 s cooldown."""
    if not is_connected_group(message):
        return
    if time.time() - GROUP_COOLDOWN.get(message.chat.id, 0) < 30:
        return
    GROUP_COOLDOWN[message.chat.id] = time.time()
    await send_leaderboard(message.bot, message.chat.id, kind)


@group_router.message(Command("rankings", "rank"))
async def g_rankings(message: Message) -> None:
    await group_leaderboard(message, "overall")


@group_router.message(Command("daily"))
async def g_daily(message: Message) -> None:
    await group_leaderboard(message, "daily")


@group_router.message(Command("weekly"))
async def g_weekly(message: Message) -> None:
    await group_leaderboard(message, "weekly")


@router.message(Command("setgroup"))
async def private_setgroup(message: Message) -> None:
    await message.answer("Please send /setgroup inside your group chat (the bot must be a member), "
                         "and only the Creator can use it.")


def render_digest(ended, promos, per_test: int, max_tests: int) -> str:
    lines = ["<b>📊 DAILY DIGEST</b>", LINE, f"📅 {datetime.now(TZ).strftime('%Y-%m-%d')}"]
    if ended:
        lines += ["", "<b>📝 TESTS ENDED</b>"]
        for test, summary in ended[:max_tests]:
            lines.append(f"• <b>{escape(test['title'])}</b> — {summary['participants']} participants · "
                         f"average {pct(summary['accuracy'])}")
            for i, r in enumerate(summary["earners"][:per_test], 1):
                lines.append(f"   {MEDALS.get(i, f'{i}.')} {escape(r['full_name'])} · "
                             f"{r['correct_count']}/{r['total_questions']} · +{r['points_earned']}")
            if len(summary["earners"]) > per_test:
                lines.append(f"   …and {len(summary['earners']) - per_test} more")
        if len(ended) > max_tests:
            lines.append(f"…and {len(ended) - max_tests} more tests")
    if promos:
        lines += ["", "<b>🎉 NEW RANKS</b>"]
        lines += [f"• {escape(name)} → <b>{escape(rank)}</b>" for name, rank in promos[:12]]
        if len(promos) > 12:
            lines.append(f"…and {len(promos) - 12} more")
    return "\n".join(lines)


def build_digest(since: str):
    """The text part of the daily digest: tests that ended and new ranks since the last digest.
    Returns None when there is nothing to report (or 'Group results' is switched off)."""
    if get_setting("post_results") != "1":
        return None
    ended, latest = [], {}
    with db() as c:
        test_ids = [int(r["details"].split(":")[0]) for r in c.execute(
            "SELECT details FROM activity_logs WHERE action = 'test_expired' AND created_at >= ? ORDER BY id",
            (since,))]
        for r in c.execute(
                "SELECT u.full_name AS name, l.details AS rank FROM activity_logs l "
                "JOIN users u ON u.tg_id = l.user_id "
                "WHERE l.action = 'promotion' AND l.created_at >= ? ORDER BY l.id", (since,)):
            latest[r["name"]] = r["rank"]
    for test_id in test_ids:
        test = get_test(test_id)
        summary = test_summary(test_id) if test else None
        if summary and summary["participants"]:
            ended.append((test, summary))
    promos = list(latest.items())
    if not (ended or promos):
        return None
    text = ""
    for per_test, max_tests in ((5, 5), (3, 3), (1, 2)):  # shrink until it fits one Telegram message
        text = render_digest(ended, promos, per_test, max_tests)
        if len(text) <= 3900:
            return text
    return text[:3900].rsplit("\n", 1)[0] + "\n…"


async def send_digest(bot: Bot, gid: int, include_weekly: bool) -> None:
    """Daily group report: today's leaderboard picture (and the weekly one on Sundays),
    then one text message with the tests that ended and the new ranks."""
    since = get_setting("last_digest_at") or (
        datetime.now(timezone.utc) - timedelta(hours=24)).strftime("%Y-%m-%d %H:%M:%S")
    try:
        if ranking_rows("daily")[0]:
            await send_leaderboard(bot, gid, "daily", buttons=False, track=False)
        if include_weekly and ranking_rows("weekly")[0]:
            await send_leaderboard(bot, gid, "weekly", buttons=False, track=False)
        text = build_digest(since)
        if text:
            await bot.send_message(gid, text)
    except TelegramAPIError as exc:
        logging.warning("Could not post the digest to the group: %s", exc)
        return  # keep the events for the next try
    set_setting("last_digest_at", now())


async def notify_review_open(bot: Bot, test) -> None:
    """A test has ended: tell the students who completed it that the answers can now be reviewed."""
    if not test:
        return
    with db() as c:
        rows = c.execute(
            "SELECT id, user_id FROM attempts WHERE test_id = ? AND finished_at IS NOT NULL "
            "AND COALESCE(practice, 0) = 0", (test["id"],)).fetchall()
    text = (f"{title_block('📋 TEST ENDED')}<b>{escape(test['title'])}</b> has ended.\n"
            "You can now review the correct answers.")
    for r in rows:
        for _ in range(2):
            try:
                await bot.send_message(r["user_id"], text, reply_markup=kb([btn("📋 Review Answers", f"rv:{r['id']}:0")]))
                break
            except TelegramRetryAfter as exc:
                await asyncio.sleep(exc.retry_after)
            except TelegramAPIError:
                break
        await asyncio.sleep(0.05)


# ----------------------------------------------------------------------------
# Automatic backup (sent to the Creator, pinned) and automatic restore on a fresh server
# ----------------------------------------------------------------------------

LAST_BACKUP = {"time": 0.0, "stamp": 0.0}
BACKUP_EVERY = 1800  # seconds; a backup is sent only if the data changed


def db_stamp() -> float:
    stamps = [os.path.getmtime(p) for p in (DB_PATH, DB_PATH + "-wal") if os.path.exists(p)]
    return max(stamps) if stamps else 0.0


async def send_auto_backup(bot: Bot, force: bool = False) -> None:
    """Keeps ONE pinned backup message in the Creator's chat up to date (the file is replaced in place)."""
    if not force and get_setting("auto_backup") != "1":
        return
    stamp = db_stamp()
    if not force and (time.time() - LAST_BACKUP["time"] < BACKUP_EVERY or stamp <= LAST_BACKUP["stamp"]):
        return
    path = make_backup_file()
    caption = f"💾 Automatic backup · {datetime.now(TZ).strftime('%Y-%m-%d %H:%M')}"
    try:
        done = False
        message_id = get_setting("backup_msg_id")
        if message_id.isdigit():
            try:
                await bot.edit_message_media(InputMediaDocument(media=FSInputFile(path), caption=caption),
                                             chat_id=CREATOR_ID, message_id=int(message_id))
                done = True
            except TelegramAPIError:
                done = False  # the old message was deleted: send a new one
        if not done:
            sent = await bot.send_document(CREATOR_ID, FSInputFile(path), caption=caption,
                                           disable_notification=True)
            set_setting("backup_msg_id", str(sent.message_id))
            try:
                await bot.pin_chat_message(CREATOR_ID, sent.message_id, disable_notification=True)
            except TelegramAPIError as exc:
                logging.warning("Could not pin the backup message: %s", exc)
    except TelegramAPIError as exc:
        logging.warning("Automatic backup failed: %s", exc)
        return
    finally:
        os.remove(path)
    LAST_BACKUP.update(time=time.time(), stamp=db_stamp())


async def restore_from_pinned_backup(bot: Bot):
    """On a fresh server (no database file yet) restore the newest backup pinned in the Creator's chat.
    Returns the id of the backup message, or None if nothing was restored."""
    if os.path.exists(DB_PATH):
        return None
    try:
        chat = await bot.get_chat(CREATOR_ID)
        pinned = getattr(chat, "pinned_message", None)
        doc = getattr(pinned, "document", None)
        if not doc or not (doc.file_name or "").lower().endswith(".db"):
            return None
        path = os.path.join(tempfile.gettempdir(), "auto_restore.db")
        await bot.download(doc, destination=path)
    except TelegramAPIError as exc:
        logging.warning("Automatic restore is not possible: %s", exc)
        return None
    if inspect_backup(path) is None:
        os.remove(path)
        return None
    src = sqlite3.connect(path)
    dst = sqlite3.connect(DB_PATH)
    try:
        src.backup(dst)
    finally:
        dst.close()
        src.close()
    os.remove(path)
    return pinned.message_id


async def start_health_server():
    """Render (and similar hosts) need an open HTTP port; an uptime monitor can ping it to keep the bot awake."""
    port = os.getenv("PORT", "")
    if not port.isdigit():
        logging.info("PORT is not set: the health-check web server is off (normal when running locally).")
        return None
    from aiohttp import web

    async def ok(_request):
        return web.Response(text="OK")

    app = web.Application()
    app.router.add_get("/", ok)
    app.router.add_get("/health", ok)
    runner = web.AppRunner(app)
    await runner.setup()
    try:
        await web.TCPSite(runner, "0.0.0.0", int(port)).start()
    except OSError as exc:  # a busy port must never stop the bot itself
        logging.error("The health-check server could not start on port %s: %s (the bot keeps running)", port, exc)
        await runner.cleanup()
        return None
    logging.info("Health server is listening on port %s", port)
    return runner


BACKGROUND_TASKS: set = set()


def spawn(coro) -> None:
    """Runs a coroutine in the background (and keeps a reference so it is not cancelled)."""
    task = asyncio.create_task(coro)
    BACKGROUND_TASKS.add(task)
    task.add_done_callback(BACKGROUND_TASKS.discard)


async def notify_points_change(bot: Bot, target: int, delta: int, reason: str, total: int,
                               rank: str, ranked_up: bool) -> bool:
    """Tells a student that the Creator added or removed points. Returns False if the message did not arrive."""
    title = "🎁 POINTS ADDED" if delta > 0 else "📉 POINTS DEDUCTED"
    lines = [title_block(title).rstrip(), f"<b>Change:</b> {delta:+d}"]
    if reason:
        lines.append(f"<b>Reason:</b> {escape(reason)}")
    lines += [f"<b>Total points:</b> {total}", f"<b>Rank:</b> {escape(rank)}"]
    if ranked_up:
        lines += ["", f"🎉 <b>New rank reached: {escape(rank)}</b>"]
    try:
        await bot.send_message(target, "\n".join(lines))
        return True
    except TelegramAPIError:
        return False


async def notify_creator(bot: Bot, text: str) -> None:
    try:
        await bot.send_message(CREATOR_ID, text)
    except TelegramAPIError as exc:
        logging.warning("Could not notify the Creator: %s", exc)


async def notify_new_test(bot: Bot, test_id: int, publisher_id: int) -> None:
    """After a test is published: tell the Creator and send an alert to every student."""
    test = get_test(test_id)
    if not test:
        return
    if publisher_id != CREATOR_ID and get_setting("notify_test_published") == "1":
        with db() as c:
            row = c.execute("SELECT role, name FROM roles WHERE tg_id = ?", (publisher_id,)).fetchone()
        who = f"{ROLE_LABEL.get(row['role'], 'Staff')} {row['name'] or publisher_id}" if row else str(publisher_id)
        await notify_creator(bot, f"{title_block('📝 TEST PUBLISHED')}"
                                  f"<b>Test:</b> {escape(test['title'])}\n"
                                  f"<b>By:</b> {escape(who)}\n"
                                  f"<b>Questions:</b> {count_questions(test_id)}")
    if get_setting("notify_new_test") != "1":
        return
    with db() as c:
        ids = [r[0] for r in c.execute("SELECT tg_id FROM users WHERE COALESCE(blocked, 0) = 0")]
    text = (f"{title_block('🆕 NEW TEST AVAILABLE')}"
            f"<b>Test:</b> {escape(test['title'])}\n"
            f"<b>Questions:</b> {count_questions(test_id)}\n"
            f"<b>Time limit:</b> {fmt_duration(test_seconds(test_id))}\n"
            f"<b>Available for:</b> {time_left(test['expires_at'])}")
    markup = kb([btn("📝 Open Test", f"tv:{test_id}", style="success")])
    sent = 0
    for uid in ids:
        for attempt in range(2):
            try:
                await bot.send_message(uid, text, reply_markup=markup)
                sent += 1
                break
            except TelegramRetryAfter as exc:
                await asyncio.sleep(exc.retry_after)
            except TelegramAPIError:
                break  # the student blocked the bot or deleted the chat
        await asyncio.sleep(0.05)  # stay below Telegram's sending limit
    try:
        await bot.send_message(publisher_id, f"📣 <b>Students notified:</b> {sent} / {len(ids)}")
    except TelegramAPIError:
        pass


# ============================================================================
# Background jobs
# ============================================================================

async def handle_timeout(bot: Bot, attempt_id: int) -> None:
    """The time for the whole test is over: finish it and show the result."""
    att = get_attempt(attempt_id)
    if not att or att["finished_at"] or not att["q_deadline"] or att["q_deadline"] > time.time():
        return
    await finalize_attempt(bot, attempt_id, att["chat_id"] or att["user_id"], att["message_id"])


async def timer_loop(bot: Bot) -> None:
    """Every 2 seconds: finish the tests whose time is over."""
    while True:
        try:
            await asyncio.sleep(2)
            for att in due_attempts():
                await handle_timeout(bot, att["id"])
        except asyncio.CancelledError:
            raise
        except Exception:
            logging.exception("timer loop error")


async def scheduler(bot: Bot) -> None:
    """Every 30 seconds: expire old tests, post the daily digest, keep the backup fresh."""
    while True:
        try:
            await asyncio.sleep(30)
            for test in expire_tests():
                log_activity(0, "test_expired", f"{test['id']}: {test['title']}")
                spawn(notify_review_open(bot, test))

            gid = get_group_id()
            if gid and get_setting("auto_reports") == "1":
                local = datetime.now(TZ)
                if local.hour >= get_int("report_hour", 21):
                    today = local.strftime("%Y-%m-%d")
                    if get_setting("last_daily") != today:
                        set_setting("last_daily", today)
                        week = local.strftime("%G-W%V")
                        weekly = local.weekday() == 6 and get_setting("last_weekly") != week
                        if weekly:
                            set_setting("last_weekly", week)
                        await send_digest(bot, gid, weekly)
            await send_auto_backup(bot)
        except asyncio.CancelledError:
            raise
        except Exception:
            logging.exception("scheduler error")


@router.message(Command("my"), HasRole("student"))
async def cmd_my(message: Message) -> None:
    await message.answer(profile_card(message.from_user.id, message.from_user.full_name), reply_markup=kb(MAIN))


@router.message(Command("rank", "rankings"), HasRole(*ANY_ROLE))
async def cmd_rank(message: Message) -> None:
    await send_leaderboard(message.bot, message.chat.id, "overall", message.from_user.id)


# ============================================================================
# Fallbacks (must stay last) and error handling
# ============================================================================

@router.callback_query()
async def cb_fallback(call: CallbackQuery) -> None:
    """Old, expired or foreign buttons (for example a student button pressed by staff)."""
    blocked = get_role(call.from_user.id) == "blocked"
    await call.answer("Access denied. Your account is blocked." if blocked else TXT_STALE, show_alert=True)
    await show_home(call, ack=False)


@router.message()
async def msg_fallback(message: Message) -> None:
    await show_home(message)


async def on_error(event: ErrorEvent) -> bool:
    logging.error("Unhandled error: %r", event.exception, exc_info=event.exception)
    update = event.update
    try:
        if update.callback_query:
            await update.callback_query.answer("Something went wrong. Please try again.", show_alert=True)
        elif update.message:
            await update.message.answer("Something went wrong. Please try again.")
    except Exception:
        pass
    return True


# ============================================================================
# Entry point
# ============================================================================

async def main() -> None:
    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")

    health = await start_health_server()
    bot = Bot(
        token=BOT_TOKEN,
        default=DefaultBotProperties(parse_mode=ParseMode.HTML, link_preview_is_disabled=True),
    )
    try:
        me = await bot.get_me()
    except TelegramUnauthorizedError:
        await bot.session.close()
        sys.exit("ERROR: BOT_TOKEN was rejected by Telegram. Get a fresh token from @BotFather and update .env.")

    restored_id = await restore_from_pinned_backup(bot)  # only when there is no database file yet
    init_db()
    seed_roles()
    logging.info("Database ready: %s", DB_PATH)
    if restored_id:
        set_setting("backup_msg_id", str(restored_id))
        logging.info("The data was restored from the pinned backup.")
        await notify_creator(bot, f"{title_block('♻️ DATA RESTORED')}"
                                  "This server had no database, so the latest automatic backup "
                                  "was restored. Changes made after that backup are lost.")
    logging.info("Bot started as @%s", me.username)

    dp = Dispatcher(storage=MemoryStorage())
    dp.include_router(group_router)
    dp.include_router(router)
    dp.errors.register(on_error)

    await bot.set_my_commands([BotCommand(command="start", description="Open the main menu"),
                               BotCommand(command="my", description="My profile"),
                               BotCommand(command="rankings", description="Leaderboard")])
    await bot.set_my_commands(
        [BotCommand(command="rankings", description="Leaderboard"),
         BotCommand(command="daily", description="Today's leaderboard"),
         BotCommand(command="weekly", description="Weekly leaderboard"),
         BotCommand(command="setgroup", description="Connect this group (Creator only)")],
        scope=BotCommandScopeAllGroupChats(),
    )
    await bot.delete_webhook(drop_pending_updates=False)

    jobs = [asyncio.create_task(timer_loop(bot)), asyncio.create_task(scheduler(bot))]
    try:
        await dp.start_polling(bot)
    finally:
        for job in jobs:
            job.cancel()
        if health:
            await health.cleanup()
        await bot.session.close()


if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        pass
