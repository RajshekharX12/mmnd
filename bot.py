#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
import re
import csv
import time
import zipfile
import difflib
from io import BytesIO
from pathlib import Path
from datetime import datetime, timedelta
from typing import Optional, List, Tuple

from zoneinfo import ZoneInfo
from dotenv import load_dotenv
import sqlite3

from aiogram import Bot, Dispatcher, Router, F
from aiogram.enums import ParseMode
from aiogram.filters import CommandStart
from aiogram.types import (
    Message, CallbackQuery, FSInputFile, BufferedInputFile, Document
)
from aiogram.utils.keyboard import InlineKeyboardBuilder
from aiogram.fsm.state import State, StatesGroup
from aiogram.fsm.context import FSMContext
from aiogram.exceptions import TelegramBadRequest

# Optional chart rendering
try:
    import matplotlib
    matplotlib.use("Agg")  # headless
    import matplotlib.pyplot as plt
    HAS_MPL = True
except Exception:
    HAS_MPL = False

# Optional AI helper
try:
    from SafoneAPI import SafoneAPI
    HAS_SAFONE = True
except Exception:
    HAS_SAFONE = False

# Optional dataframes
try:
    import pandas as pd
    HAS_PANDAS = True
except Exception:
    HAS_PANDAS = False

# ---------- Config ----------
load_dotenv()

BOT_TOKEN = os.getenv("BOT_TOKEN") or ""
OWNER_ID = int(os.getenv("OWNER_ID") or "0")
DB_PATH = Path(os.getenv("DB_PATH") or "data/bot.db")
DATA_DIR = Path(os.getenv("DATA_DIR") or "exports")
BOT_PIN = os.getenv("BOT_PIN")  # optional

# Reminders (defaults)
DAILY_REMINDERS = int(os.getenv("DAILY_REMINDERS") or "1")
WEEKLY_REMINDERS = int(os.getenv("WEEKLY_REMINDERS") or "1")
DAILY_HOUR = int(os.getenv("DAILY_HOUR") or "9")       # 9am IST
WEEKLY_DOW = int(os.getenv("WEEKLY_DOW") or "1")       # 1 = Tuesday

TZ = ZoneInfo("Asia/Kolkata")
CURRENCY = "₹"

assert BOT_TOKEN, "BOT_TOKEN env is required"
assert OWNER_ID, "OWNER_ID env is required"

DATA_DIR.mkdir(parents=True, exist_ok=True)
DB_PATH.parent.mkdir(parents=True, exist_ok=True)

# ---------- DB ----------
def db():
    con = sqlite3.connect(DB_PATH)
    con.row_factory = sqlite3.Row
    return con

def init_db():
    con = db(); cur = con.cursor()
    # expenses
    cur.execute("""
    CREATE TABLE IF NOT EXISTS expenses (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id INTEGER NOT NULL,
        ts INTEGER NOT NULL,
        yyyymm TEXT NOT NULL,
        amount REAL NOT NULL,
        note TEXT,
        category TEXT
    )""")
    # people
    cur.execute("""
    CREATE TABLE IF NOT EXISTS people (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id INTEGER NOT NULL,
        display_name TEXT NOT NULL,
        canonical_name TEXT NOT NULL,
        credit_limit REAL,
        monthly_interest_rate REAL,
        last_interest_yyyymm TEXT,
        UNIQUE(user_id, canonical_name)
    )""")
    # ledger
    cur.execute("""
    CREATE TABLE IF NOT EXISTS ledger (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id INTEGER NOT NULL,
        person_id INTEGER NOT NULL,
        ts INTEGER NOT NULL,
        type TEXT NOT NULL CHECK(type IN ('lend','repay','interest')),
        amount REAL NOT NULL,
        note TEXT,
        due_ts INTEGER
    )""")
    # actions for undo
    cur.execute("""
    CREATE TABLE IF NOT EXISTS actions (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id INTEGER NOT NULL,
        ts INTEGER NOT NULL,
        kind TEXT NOT NULL,
        ref_table TEXT NOT NULL,
        ref_id INTEGER NOT NULL
    )""")
    # settings (reminders)
    cur.execute("""
    CREATE TABLE IF NOT EXISTS settings (
        user_id INTEGER PRIMARY KEY,
        daily_reminders INTEGER DEFAULT 1,
        weekly_reminders INTEGER DEFAULT 1,
        daily_hour INTEGER DEFAULT 9,
        weekly_dow INTEGER DEFAULT 1,
        last_daily_date TEXT,
        last_weekly_date TEXT
    )""")
    # bot messages (for auto-cleanup)
    cur.execute("""
    CREATE TABLE IF NOT EXISTS bot_msgs (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id INTEGER NOT NULL,
        chat_id INTEGER NOT NULL,
        msg_id INTEGER NOT NULL,
        ts INTEGER NOT NULL
    )""")
    con.commit(); con.close()

def migrate_defaults():
    con = db(); cur = con.cursor()
    cur.execute("SELECT 1 FROM settings WHERE user_id=?", (OWNER_ID,))
    if not cur.fetchone():
        cur.execute("""INSERT INTO settings (user_id, daily_reminders, weekly_reminders, daily_hour, weekly_dow)
                       VALUES (?,?,?,?,?)""",
                    (OWNER_ID, DAILY_REMINDERS, WEEKLY_REMINDERS, DAILY_HOUR, WEEKLY_DOW))
        con.commit()
    con.close()

# ---------- Helpers ----------
def now_ts() -> int:
    return int(datetime.now(TZ).timestamp())

def cur_yyyymm() -> str:
    d = datetime.now(TZ)
    return f"{d.year:04d}-{d.month:02d}"

def parse_date_fuzzy(s: str) -> Optional[datetime]:
    s = (s or "").strip()
    if not s:
        return None
    for fmt in ("%Y-%m-%d", "%d-%m-%Y", "%d/%m/%Y", "%Y/%m/%d", "%d %b %Y", "%b %d %Y"):
        try:
            dt = datetime.strptime(s, fmt)
            return datetime(dt.year, dt.month, dt.day, tzinfo=TZ)
        except Exception:
            continue
    try:
        return datetime.fromisoformat(s).replace(tzinfo=TZ)
    except Exception:
        pass
    if HAS_PANDAS:
        try:
            dt = pd.to_datetime(s, dayfirst=True, errors="coerce")
            if pd.notna(dt):
                return datetime(dt.year, dt.month, dt.day, tzinfo=TZ)
        except Exception:
            pass
    return None

def canonical(s: str) -> str:
    return re.sub(r"\s+", " ", re.sub(r"[^a-z0-9 ]+", " ", s.lower())).strip()

# ---------- Data ops ----------
def add_expense(user_id: int, amount: float, note: Optional[str], category: Optional[str]) -> int:
    con = db(); cur = con.cursor()
    cur.execute("""INSERT INTO expenses (user_id, ts, yyyymm, amount, note, category)
                   VALUES (?,?,?,?,?,?)""",
                (user_id, now_ts(), cur_yyyymm(), float(amount), note, category))
    con.commit(); new_id = cur.lastrowid; con.close()
    return new_id

def monthly_total(user_id: int, yyyymm: Optional[str]=None) -> float:
    if not yyyymm:
        yyyymm = cur_yyyymm()
    con = db(); cur = con.cursor()
    cur.execute("SELECT COALESCE(SUM(amount),0) AS total FROM expenses WHERE user_id=? AND yyyymm=?",
                (user_id, yyyymm))
    total = float(cur.fetchone()["total"]); con.close()
    return total

def monthly_by_category(user_id: int, yyyymm: str) -> List[sqlite3.Row]:
    con = db(); cur = con.cursor()
    cur.execute("""SELECT COALESCE(category,'Other') AS cat, COALESCE(SUM(amount),0) AS s
                   FROM expenses WHERE user_id=? AND yyyymm=? GROUP BY COALESCE(category,'Other')""",
                (user_id, yyyymm))
    rows = cur.fetchall(); con.close(); return rows

def add_person(user_id: int, display_name: str) -> Tuple[Optional[int], Optional[str]]:
    name = display_name.strip()
    if not name:
        return None, "Name cannot be empty."
    canon = name.lower()
    con = db(); cur = con.cursor()
    try:
        cur.execute("""INSERT INTO people (user_id, display_name, canonical_name)
                       VALUES (?,?,?)""", (user_id, name, canon))
        con.commit(); pid = cur.lastrowid; con.close()
        return pid, None
    except sqlite3.IntegrityError:
        con.close(); return None, "This person already exists."

def get_people(user_id: int) -> List[sqlite3.Row]:
    con = db(); cur = con.cursor()
    cur.execute("""SELECT id, display_name, canonical_name, credit_limit, monthly_interest_rate, last_interest_yyyymm
                   FROM people WHERE user_id=? ORDER BY display_name COLLATE NOCASE""", (user_id,))
    rows = cur.fetchall(); con.close(); return rows

def find_person_id_exact(user_id: int, name: str) -> Optional[int]:
    canon = name.strip().lower()
    con = db(); cur = con.cursor()
    cur.execute("SELECT id FROM people WHERE user_id=? AND canonical_name=?", (user_id, canon))
    row = cur.fetchone(); con.close()
    return row["id"] if row else None

def resolve_person_id(user_id: int, raw_name: str) -> Tuple[Optional[int], Optional[str]]:
    """Best-effort resolution: exact → substring → fuzzy (difflib)."""
    if not raw_name:
        return None, None
    people = get_people(user_id)
    if not people:
        return None, None
    # exact
    pid = find_person_id_exact(user_id, raw_name)
    if pid:
        name = next(p["display_name"] for p in people if p["id"] == pid)
        return pid, name
    # substring / startswith
    c = canonical(raw_name)
    candidates = [p for p in people if c in canonical(p["display_name"])]
    if not candidates:
        candidates = [p for p in people if canonical(p["display_name"]).startswith(c)]
    if candidates:
        return candidates[0]["id"], candidates[0]["display_name"]
    # fuzzy
    names = [p["display_name"] for p in people]
    match = difflib.get_close_matches(raw_name, names, n=1, cutoff=0.6)
    if match:
        for p in people:
            if p["display_name"] == match[0]:
                return p["id"], p["display_name"]
    return None, None

def add_ledger(user_id: int, person_id: int, entry_type: str, amount: float,
               note: Optional[str], due_ts: Optional[int]=None) -> int:
    con = db(); cur = con.cursor()
    cur.execute("""INSERT INTO ledger (user_id, person_id, ts, type, amount, note, due_ts)
                   VALUES (?,?,?,?,?,?,?)""",
                (user_id, person_id, now_ts(), entry_type, float(amount), note, due_ts))
    con.commit(); new_id = cur.lastrowid; con.close(); return new_id

def get_ledger(user_id: int, person_id: int) -> List[sqlite3.Row]:
    con = db(); cur = con.cursor()
    cur.execute("""SELECT id, ts, type, amount, COALESCE(note,'') AS note, due_ts
                   FROM ledger WHERE user_id=? AND person_id=? ORDER BY ts ASC""",
                (user_id, person_id))
    rows = cur.fetchall(); con.close(); return rows

def person_balance(user_id: int, person_id: int) -> float:
    con = db(); cur = con.cursor()
    cur.execute("""
    SELECT
      COALESCE(SUM(CASE WHEN type IN ('lend','interest') THEN amount ELSE 0 END),0) -
      COALESCE(SUM(CASE WHEN type='repay' THEN amount ELSE 0 END),0) AS balance
    FROM ledger WHERE user_id=? AND person_id=?
    """, (user_id, person_id))
    row = cur.fetchone(); con.close()
    return float(row["balance"] or 0.0)

def delete_person(user_id: int, person_id: int):
    con = db(); cur = con.cursor()
    cur.execute("DELETE FROM ledger WHERE user_id=? AND person_id=?", (user_id, person_id))
    cur.execute("DELETE FROM people WHERE user_id=? AND id=?", (user_id, person_id))
    con.commit(); con.close()

def set_credit_limit(user_id: int, person_id: int, limit: Optional[float]):
    con = db(); cur = con.cursor()
    cur.execute("UPDATE people SET credit_limit=? WHERE user_id=? AND id=?",
                (limit, user_id, person_id))
    con.commit(); con.close()

def get_credit_limit(user_id: int, person_id: int) -> Optional[float]:
    con = db(); cur = con.cursor()
    cur.execute("SELECT credit_limit FROM people WHERE user_id=? AND id=?", (user_id, person_id))
    row = cur.fetchone(); con.close()
    return None if row is None else row["credit_limit"]

def set_interest_rate(user_id: int, person_id: int, rate_percent: Optional[float]):
    con = db(); cur = con.cursor()
    cur.execute("UPDATE people SET monthly_interest_rate=? WHERE user_id=? AND id=?",
                (rate_percent, user_id, person_id))
    con.commit(); con.close()

def get_person_interest_info(user_id: int, person_id: int) -> Tuple[Optional[float], Optional[str]]:
    con = db(); cur = con.cursor()
    cur.execute("SELECT monthly_interest_rate, last_interest_yyyymm FROM people WHERE user_id=? AND id=?",
                (user_id, person_id))
    row = cur.fetchone(); con.close()
    if not row: return None, None
    return (row["monthly_interest_rate"], row["last_interest_yyyymm"])

def update_last_interest_applied(user_id: int, person_id: int, yyyymm: str):
    con = db(); cur = con.cursor()
    cur.execute("UPDATE people SET last_interest_yyyymm=? WHERE user_id=? AND id=?",
                (yyyymm, user_id, person_id))
    con.commit(); con.close()

def top_balances(user_id: int, limit: int = 5) -> List[sqlite3.Row]:
    con = db(); cur = con.cursor()
    cur.execute("""
    SELECT p.id, p.display_name,
      COALESCE(SUM(CASE WHEN l.type IN ('lend','interest') THEN l.amount ELSE 0 END),0) -
      COALESCE(SUM(CASE WHEN l.type='repay' THEN l.amount ELSE 0 END),0) AS balance
    FROM people p
    LEFT JOIN ledger l ON l.user_id=p.user_id AND l.person_id=p.id
    WHERE p.user_id=?
    GROUP BY p.id, p.display_name
    HAVING balance != 0
    ORDER BY balance DESC
    LIMIT ?
    """, (user_id, limit))
    rows = cur.fetchall(); con.close(); return rows

def due_items(user_id: int, days: int = 7) -> List[sqlite3.Row]:
    now = now_ts(); soon = now + days*24*3600
    con = db(); cur = con.cursor()
    cur.execute("""
    SELECT p.display_name AS name, l.amount, l.due_ts
    FROM ledger l
    JOIN people p ON p.id=l.person_id AND p.user_id=l.user_id
    WHERE l.user_id=? AND l.type='lend' AND l.due_ts IS NOT NULL AND l.due_ts <= ?
    ORDER BY l.due_ts ASC
    """, (user_id, soon))
    rows = cur.fetchall(); con.close(); return rows

# Actions log (undo)
def log_action(user_id: int, kind: str, ref_table: str, ref_id: int):
    con = db(); cur = con.cursor()
    cur.execute("""INSERT INTO actions (user_id, ts, kind, ref_table, ref_id)
                   VALUES (?,?,?,?,?)""", (user_id, now_ts(), kind, ref_table, ref_id))
    con.commit(); con.close()

def undo_last(user_id: int) -> str:
    con = db(); cur = con.cursor()
    cur.execute("""SELECT id, kind, ref_table, ref_id FROM actions
                   WHERE user_id=? ORDER BY id DESC LIMIT 1""", (user_id,))
    row = cur.fetchone()
    if not row:
        con.close(); return "Nothing to undo."
    act_id, kind, table, ref_id = row["id"], row["kind"], row["ref_table"], row["ref_id"]
    cur.execute(f"DELETE FROM {table} WHERE id=?", (ref_id,))
    cur.execute("DELETE FROM actions WHERE id=?", (act_id,))
    con.commit(); con.close()
    return f"Undid last {kind}."

# Settings
def get_settings(user_id: int) -> sqlite3.Row:
    con = db(); cur = con.cursor()
    cur.execute("SELECT * FROM settings WHERE user_id=?", (user_id,))
    row = cur.fetchone(); con.close(); return row

def set_setting(user_id: int, field: str, value):
    con = db(); cur = con.cursor()
    cur.execute(f"UPDATE settings SET {field}=? WHERE user_id=?", (value, user_id))
    con.commit(); con.close()

# Bot message log (auto-clean)
def record_bot_message(user_id: int, chat_id: int, msg_id: int):
    con = db(); cur = con.cursor()
    cur.execute("INSERT INTO bot_msgs (user_id, chat_id, msg_id, ts) VALUES (?,?,?,?)",
                (user_id, chat_id, msg_id, now_ts()))
    # keep at most last 200
    cur.execute("DELETE FROM bot_msgs WHERE id NOT IN (SELECT id FROM bot_msgs WHERE user_id=? ORDER BY id DESC LIMIT 200)", (user_id,))
    con.commit(); con.close()

async def delete_old_bot_messages(chat_id: int, keep_last: int = 0):
    con = db(); cur = con.cursor()
    cur.execute("SELECT id, msg_id FROM bot_msgs WHERE user_id=? AND chat_id=? ORDER BY id DESC", (OWNER_ID, chat_id))
    rows = cur.fetchall(); con.close()
    # skip latest N
    for i, r in enumerate(rows):
        if i < keep_last:
            continue
        try:
            await bot.delete_message(chat_id, r["msg_id"])
        except Exception:
            pass
    # clear log (fresh start)
    con = db(); cur = con.cursor()
    cur.execute("DELETE FROM bot_msgs WHERE user_id=? AND chat_id=?", (OWNER_ID, chat_id))
    con.commit(); con.close()

# ---------- Exports ----------
def export_person_csv(user_id: int, person_id: int, display_name: str) -> Path:
    rows = get_ledger(user_id, person_id)
    out_dir = DATA_DIR / f"user_{user_id}"
    out_dir.mkdir(parents=True, exist_ok=True)
    ts_str = datetime.now(TZ).strftime("%Y-%m-%d_%H-%M")
    safe_name = re.sub(r"[^A-Za-z0-9._-]+", "_", display_name.strip()) or f"person_{person_id}"
    fpath = out_dir / f"{safe_name}_ledger_{ts_str}.csv"
    running = 0.0
    with open(fpath, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["DateTime(IST)", "Type", "Amount", "Note", "DueDate", "Running Balance"])
        for r in rows:
            dt = datetime.fromtimestamp(r["ts"], TZ).strftime("%Y-%m-%d %H:%M")
            amt = float(r["amount"])
            if r["type"] in ("lend","interest"):
                running += amt
            else:
                running -= amt
            due_str = datetime.fromtimestamp(r["due_ts"], TZ).strftime("%Y-%m-%d") if r["due_ts"] else ""
            w.writerow([dt, r["type"], amt, r["note"], due_str, running])
        w.writerow([])
        w.writerow(["TOTAL OWED (+ means they owe you)", "", "", "", "", running])
    return fpath

def export_expenses_csv(user_id: int) -> Path:
    con = db(); cur = con.cursor()
    cur.execute("""SELECT ts, yyyymm, amount, COALESCE(note,''), COALESCE(category,'Other')
                   FROM expenses WHERE user_id=? ORDER BY ts ASC""", (user_id,))
    rows = cur.fetchall(); con.close()

    out_dir = DATA_DIR / f"user_{user_id}"
    out_dir.mkdir(parents=True, exist_ok=True)
    ts_str = datetime.now(TZ).strftime("%Y-%m-%d_%H-%M")
    fpath = out_dir / f"expenses_{ts_str}.csv"
    with open(fpath, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["DateTime(IST)", "Month", "Amount", "Note", "Category"])
        for r in rows:
            dt = datetime.fromtimestamp(r["ts"], TZ).strftime("%Y-%m-%d %H:%M")
            w.writerow([dt, r["yyyymm"], float(r[2]), r[3], r[4]])
        w.writerow([])
        this_month = cur_yyyymm()
        w.writerow([f"THIS MONTH ({this_month})", "", monthly_total(user_id, this_month), "", ""])
    return fpath

def export_all_zip(user_id: int) -> Path:
    out_dir = DATA_DIR / f"user_{user_id}"
    out_dir.mkdir(parents=True, exist_ok=True)
    ts_str = datetime.now(TZ).strftime("%Y-%m-%d_%H-%M")
    zip_path = out_dir / f"all_ledgers_{ts_str}.zip"

    to_zip = [export_expenses_csv(user_id)]
    for p in get_people(user_id):
        to_zip.append(export_person_csv(user_id, p["id"], p["display_name"]))

    summary_txt = out_dir / f"summary_{ts_str}.txt"
    with open(summary_txt, "w", encoding="utf-8") as f:
        f.write("Summary (IST)\n")
        f.write(f"Generated: {datetime.now(TZ).strftime('%Y-%m-%d %H:%M')}\n\n")
        month = cur_yyyymm()
        f.write(f"Monthly Expense {month}: {monthly_total(user_id, month)}\n\n")
        f.write("Top balances (who owes you most):\n")
        for r in top_balances(user_id, 20):
            f.write(f"- {r['display_name']}: {r['balance']}\n")
    to_zip.append(summary_txt)

    with zipfile.ZipFile(zip_path, "w", compression=zipfile.ZIP_DEFLATED) as z:
        for p in to_zip:
            z.write(p, arcname=p.name)
    return zip_path

# ---------- Charts ----------
def render_category_chart_png(user_id: int, yyyymm: Optional[str]=None) -> Optional[bytes]:
    if not HAS_MPL:
        return None
    if not yyyymm:
        yyyymm = cur_yyyymm()
    rows = monthly_by_category(user_id, yyyymm)
    if not rows:
        return None
    labels = [r["cat"] for r in rows]
    values = [float(r["s"]) for r in rows]
    fig = plt.figure()
    plt.bar(labels, values)
    plt.title(f"Expenses by Category — {yyyymm}")
    plt.xlabel("Category"); plt.ylabel("Amount")
    buf = BytesIO()
    fig.tight_layout()
    fig.savefig(buf, format="png")
    plt.close(fig)
    return buf.getvalue()

# ---------- Bot setup (aiogram ≥3.7 compatible) ----------
try:
    from aiogram.client.default import DefaultBotProperties
    bot = Bot(token=BOT_TOKEN, default=DefaultBotProperties(parse_mode=ParseMode.HTML))
except Exception:
    bot = Bot(token=BOT_TOKEN, parse_mode=ParseMode.HTML)

dp = Dispatcher()
router = Router()
dp.include_router(router)

UNLOCKED = set()  # PIN gate
SCHED_TASK = None

def only_owner(message_or_query) -> bool:
    return message_or_query.from_user.id == OWNER_ID

def deny_text() -> str:
    return "⛔️ This bot is private."

# ---------- Safe send/edit wrappers (independent replies + logging) ----------
async def send_text(chat_id: int, text: str, kb=None):
    msg = await bot.send_message(chat_id, text, reply_markup=kb)
    record_bot_message(OWNER_ID, chat_id, msg.message_id)
    return msg

async def send_photo(chat_id: int, photo_bytes: bytes, filename: str, caption: str, kb=None):
    msg = await bot.send_photo(chat_id, BufferedInputFile(photo_bytes, filename=filename), caption=caption, reply_markup=kb)
    record_bot_message(OWNER_ID, chat_id, msg.message_id)
    return msg

async def safe_edit(message, text: str, kb=None):
    """Use edit_text, but fallback to sending a new message if 'not modified'."""
    try:
        await message.edit_text(text, reply_markup=kb)
    except TelegramBadRequest as e:
        if "message is not modified" in str(e).lower():
            await send_text(message.chat.id, text, kb)
        else:
            raise

# ---------- Keyboards ----------
def main_kb():
    kb = InlineKeyboardBuilder()
    kb.button(text="➕ Add Expense", callback_data="add_expense")
    kb.button(text="👥 People", callback_data="people")
    kb.button(text="📊 Monthly", callback_data="monthly")
    kb.button(text="📉 Category Chart", callback_data="cat_chart")
    kb.button(text="📥 Import Sheet", callback_data="import_sheet")
    kb.button(text="🧑‍🤝‍🧑 Support (AI)", callback_data="support_ai")
    kb.button(text="⏰ Due Soon", callback_data="due_soon")
    kb.button(text="🔔 Reminders", callback_data="reminders")
    kb.button(text="↩️ Undo", callback_data="undo")
    kb.button(text="📁 Export All (ZIP)", callback_data="export_all")
    kb.button(text="🧼 Reset All", callback_data="reset_all_confirm")
    kb.button(text="ℹ️ Quick Add Help", callback_data="help_quick")
    kb.adjust(2,2,2,3,2)
    return kb.as_markup()

def people_kb(user_id: int):
    kb = InlineKeyboardBuilder()
    kb.button(text="➕ Add Person", callback_data="person_add")
    people = get_people(user_id)
    for p in people:
        bal = person_balance(user_id, p["id"])
        limit = p["credit_limit"]
        warn = " ⚠️" if (limit is not None and bal > float(limit)) else ""
        label = f"{p['display_name']} ({CURRENCY}{bal:,.2f}){warn}"
        kb.button(text=label, callback_data=f"person_menu:{p['id']}")
    kb.button(text="⬅️ Back", callback_data="back_main")
    kb.adjust(1)
    return kb.as_markup()

def person_menu_kb(pid: int):
    kb = InlineKeyboardBuilder()
    kb.button(text="➕ Lend", callback_data=f"lend:{pid}")
    kb.button(text="💸 Repay", callback_data=f"repay:{pid}")
    kb.button(text="🧮 Settle", callback_data=f"settle:{pid}")
    kb.button(text="🎯 Set Limit", callback_data=f"setlimit:{pid}")
    kb.button(text="💠 Set Interest %", callback_data=f"setinterest:{pid}")
    kb.button(text="🗒 Ledger", callback_data=f"ledger:{pid}")
    kb.button(text="📄 Export", callback_data=f"export_person:{pid}")
    kb.button(text="🗑 Remove", callback_data=f"person_delete:{pid}")
    kb.button(text="⬅️ Back", callback_data="people")
    kb.adjust(2,2,2,2)
    return kb.as_markup()

def reminders_kb():
    s = get_settings(OWNER_ID)
    kb = InlineKeyboardBuilder()
    kb.button(text=f"Daily: {'ON' if s['daily_reminders'] else 'OFF'}", callback_data="toggle_daily")
    kb.button(text=f"Weekly: {'ON' if s['weekly_reminders'] else 'OFF'}", callback_data="toggle_weekly")
    kb.button(text=f"Daily Hour: {s['daily_hour']:02d}:00", callback_data="set_daily_hour")
    days = ["Mon","Tue","Wed","Thu","Fri","Sat","Sun"]
    kb.button(text=f"Weekly DOW: {days[s['weekly_dow']]}", callback_data="set_weekly_dow")
    kb.button(text="⬅️ Back", callback_data="back_main")
    kb.adjust(2,2,1)
    return kb.as_markup()

def skip_kb():
    kb = InlineKeyboardBuilder()
    kb.button(text="➡️ Skip", callback_data="skip_note")
    return kb.as_markup()

def reset_confirm_kb():
    kb = InlineKeyboardBuilder()
    kb.button(text="🧼 Yes, reset everything", callback_data="reset_all_do")
    kb.button(text="❌ Cancel", callback_data="back_main")
    kb.adjust(1)
    return kb.as_markup()

# ---------- States ----------
class AddExpenseStates(StatesGroup):
    waiting_amount = State()
    waiting_category = State()
    waiting_note = State()
    waiting_custom_cat = State()

class AddPersonStates(StatesGroup):
    waiting_name = State()

class LendStates(StatesGroup):
    waiting_amount = State()
    waiting_note = State()
    waiting_due = State()

class RepayStates(StatesGroup):
    waiting_amount = State()
    waiting_note = State()

class LimitState(StatesGroup):
    waiting_amount = State()

class InterestState(StatesGroup):
    waiting_rate = State()

class PinState(StatesGroup):
    waiting_pin = State()

class DailyHourState(StatesGroup):
    waiting_hour = State()

class WeeklyDowState(StatesGroup):
    waiting_dow = State()

class ImportState(StatesGroup):
    waiting_file = State()

class SupportAIState(StatesGroup):
    waiting_query = State()

# ---------- Handlers ----------
@router.message(CommandStart())
async def start_cmd(m: Message):
    try:
        if not only_owner(m):
            return await m.answer(deny_text())
        if BOT_PIN and m.from_user.id not in UNLOCKED:
            return await m.answer("🔒 Enter PIN to unlock:")
        init_db(); migrate_defaults()
        # auto-delete old bot messages
        await delete_old_bot_messages(m.chat.id, keep_last=0)
        msg = await send_text(
            m.chat.id,
            "👋 <b>Expense & Lending Assistant</b>\n"
            "• <b>Legend</b>: + means they owe you; – means you owe them.\n"
            f"• Currency: <b>{CURRENCY}</b>\n"
            "• Quick-add: <code>Ajay +500 cab</code> or <code>500 &gt; add to &gt; Ajay</code>",
            main_kb()
        )
    except Exception as e:
        await m.answer(f"❌ start error: {e}")

@router.message(F.text.regexp(r"^\d{4,8}$"))
async def pin_try(m: Message):
    try:
        if BOT_PIN and (m.text.strip() == BOT_PIN) and only_owner(m):
            UNLOCKED.add(m.from_user.id)
            return await start_cmd(m)
    except Exception as e:
        await m.answer(f"❌ pin error: {e}")

@router.callback_query(F.data == "back_main")
async def back_main(c: CallbackQuery):
    try:
        if not only_owner(c): return await c.message.answer(deny_text())
        await send_text(c.message.chat.id, "🏠 <b>Main Menu</b>", main_kb()); await c.answer()
    except Exception as e:
        await c.message.answer(f"❌ back error: {e}")

# Add Expense
EXP_CATS = ["Food","Travel","Bills","Other","✍️ Custom"]

@router.callback_query(F.data == "add_expense")
async def cb_add_expense(c: CallbackQuery, state: FSMContext):
    try:
        if not only_owner(c): return await c.message.answer(deny_text())
        await state.set_state(AddExpenseStates.waiting_amount)
        await safe_edit(c.message, "➕ Enter expense amount (number):", None); await c.answer()
    except Exception as e:
        await c.message.answer(f"❌ expense error: {e}")

@router.message(AddExpenseStates.waiting_amount)
async def get_exp_amount(m: Message, state: FSMContext):
    try:
        if not only_owner(m): return await m.answer(deny_text())
        try:
            amt = float(m.text.strip()); assert amt > 0
        except Exception:
            return await m.answer("⚠️ Send a valid positive number for amount.")
        await state.update_data(amount=amt)
        kb = InlineKeyboardBuilder()
        for cat in EXP_CATS: kb.button(text=cat, callback_data=f"exp_cat:{cat}")
        kb.adjust(2,2,1)
        await state.set_state(AddExpenseStates.waiting_category)
        await m.answer("🏷️ Pick a category:", reply_markup=kb.as_markup())
    except Exception as e:
        await m.answer(f"❌ exp amount error: {e}")

@router.callback_query(F.data.startswith("exp_cat:"))
async def pick_cat(c: CallbackQuery, state: FSMContext):
    try:
        if not only_owner(c): return await c.message.answer(deny_text())
        cat = c.data.split(":")[1]
        if cat == "✍️ Custom":
            await state.set_state(AddExpenseStates.waiting_custom_cat)
            await c.message.answer("✍️ Send custom category name:")
        else:
            await state.update_data(category=cat)
            await state.set_state(AddExpenseStates.waiting_note)
            await c.message.answer("📝 Optional note? (or tap Skip)", reply_markup=skip_kb())
        await c.answer()
    except Exception as e:
        await c.message.answer(f"❌ exp cat error: {e}")

@router.message(AddExpenseStates.waiting_custom_cat)
async def exp_custom_cat(m: Message, state: FSMContext):
    try:
        if not only_owner(m): return await m.answer(deny_text())
        cat = m.text.strip()[:30] or "Other"
        await state.update_data(category=cat)
        await state.set_state(AddExpenseStates.waiting_note)
        await m.answer("📝 Optional note? (or tap Skip)", reply_markup=skip_kb())
    except Exception as e:
        await m.answer(f"❌ custom cat error: {e}")

@router.callback_query(F.data == "skip_note")
async def skip_note_cb(c: CallbackQuery, state: FSMContext):
    try:
        if not only_owner(c): return await c.message.answer(deny_text())
        cur = await state.get_state()
        # emulate "skip" for any waiting_note state
        if cur in {AddExpenseStates.waiting_note.state,
                   LendStates.waiting_note.state,
                   RepayStates.waiting_note.state}:
            # forward a fake "skip" message into the same handler path
            fake = Message(message_id=c.message.message_id, date=c.message.date, chat=c.message.chat, from_user=c.from_user)
            fake.text = "skip"
            if cur == AddExpenseStates.waiting_note.state:
                await get_exp_note(fake, state)
            elif cur == LendStates.waiting_note.state:
                await lend_note(fake, state)
            else:
                await repay_note(fake, state)
        await c.answer()
    except Exception as e:
        await c.message.answer(f"❌ skip error: {e}")

@router.message(AddExpenseStates.waiting_note)
async def get_exp_note(m: Message, state: FSMContext):
    try:
        if not only_owner(m): return await m.answer(deny_text())
        data = await state.get_data()
        note = None if (m.text or "").strip().lower() == "skip" else (m.text or "").strip()
        eid = add_expense(OWNER_ID, data["amount"], note, data.get("category"))
        log_action(OWNER_ID, "expense", "expenses", eid)
        await state.clear()
        total = monthly_total(OWNER_ID)
        await send_text(m.chat.id,
            f"✅ Expense saved: {CURRENCY}{data['amount']:,.2f} [{data.get('category','Other')}]\n"
            f"🧮 This month: {CURRENCY}{total:,.2f}",
            main_kb()
        )
    except Exception as e:
        await m.answer(f"❌ exp save error: {e}")

# People
@router.callback_query(F.data == "people")
async def cb_people(c: CallbackQuery):
    try:
        if not only_owner(c): return await c.message.answer(deny_text())
        await safe_edit(c.message, "👥 <b>People</b>\n(+ means they owe you)", people_kb(OWNER_ID)); await c.answer()
    except Exception as e:
        await c.message.answer(f"❌ people error: {e}")

@router.callback_query(F.data == "person_add")
async def cb_person_add(c: CallbackQuery, state: FSMContext):
    try:
        if not only_owner(c): return await c.message.answer(deny_text())
        await state.set_state(AddPersonStates.waiting_name)
        await safe_edit(c.message, "👤 Send the person’s name to add:", None); await c.answer()
    except Exception as e:
        await c.message.answer(f"❌ person add error: {e}")

@router.message(AddPersonStates.waiting_name)
async def person_add_name(m: Message, state: FSMContext):
    try:
        if not only_owner(m): return await m.answer(deny_text())
        pid, err = add_person(OWNER_ID, m.text)
        await state.clear()
        if err: return await send_text(m.chat.id, f"⚠️ {err}", people_kb(OWNER_ID))
        await send_text(m.chat.id, f"✅ Added <b>{m.text.strip()}</b>.", people_kb(OWNER_ID))
    except Exception as e:
        await m.answer(f"❌ person save error: {e}")

@router.callback_query(F.data.startswith("person_menu:"))
async def cb_person_menu(c: CallbackQuery):
    try:
        if not only_owner(c): return await c.message.answer(deny_text())
        pid = int(c.data.split(":")[1])
        con = db(); cur = con.cursor()
        cur.execute("SELECT display_name, credit_limit, monthly_interest_rate FROM people WHERE user_id=? AND id=?",
                    (OWNER_ID, pid))
        row = cur.fetchone(); con.close()
        if not row: return await c.answer("Not found")
        name = row["display_name"]
        bal = person_balance(OWNER_ID, pid)
        rate = row["monthly_interest_rate"]
        limit = row["credit_limit"]
        text = (f"👤 <b>{name}</b>\n"
                f"💼 Balance: <b>{CURRENCY}{bal:,.2f}</b>\n"
                f"🎯 Limit: {'' if limit is not None else '(not set) '}{CURRENCY}{(limit or 0):,.2f}\n"
                f"💠 Interest: {rate if rate is not None else 0:.2f}% / month")
        await safe_edit(c.message, text, person_menu_kb(pid)); await c.answer()
    except Exception as e:
        await c.message.answer(f"❌ person menu error: {e}")

# Lend with due date
@router.callback_query(F.data.startswith("lend:"))
async def cb_lend(c: CallbackQuery, state: FSMContext):
    try:
        if not only_owner(c): return await c.message.answer(deny_text())
        pid = int(c.data.split(":")[1])
        await state.set_state(LendStates.waiting_amount); await state.update_data(person_id=pid)
        await safe_edit(c.message, "➕ Enter LEND amount (they owe you):", None); await c.answer()
    except Exception as e:
        await c.message.answer(f"❌ lend error: {e}")

@router.message(LendStates.waiting_amount)
async def lend_amount(m: Message, state: FSMContext):
    try:
        if not only_owner(m): return await m.answer(deny_text())
        try:
            amt = float(m.text.strip()); assert amt > 0
        except Exception:
            return await m.answer("⚠️ Send a valid positive number.")
        await state.update_data(amount=amt)
        await state.set_state(LendStates.waiting_note)
        await m.answer("📝 Optional note? (or tap Skip)", reply_markup=skip_kb())
    except Exception as e:
        await m.answer(f"❌ lend amount error: {e}")

@router.message(LendStates.waiting_note)
async def lend_note(m: Message, state: FSMContext):
    try:
        if not only_owner(m): return await m.answer(deny_text())
        await state.update_data(note=None if (m.text or "").strip().lower()=="skip" else (m.text or "").strip())
        await state.set_state(LendStates.waiting_due)
        await m.answer("📅 Optional due date (YYYY-MM-DD) or type <code>skip</code>")
    except Exception as e:
        await m.answer(f"❌ lend note error: {e}")

@router.message(LendStates.waiting_due)
async def lend_due(m: Message, state: FSMContext):
    try:
        if not only_owner(m): return await m.answer(deny_text())
        data = await state.get_data()
        due_ts = None
        t = (m.text or "").strip().lower()
        if t != "skip":
            d = parse_date_fuzzy(t)
            if not d: return await m.answer("⚠️ Use YYYY-MM-DD (or common formats) or 'skip'")
            due_ts = int(d.replace(hour=23, minute=59).timestamp())
        lid = add_ledger(OWNER_ID, data["person_id"], "lend", data["amount"], data.get("note"), due_ts)
        log_action(OWNER_ID, "ledger", "ledger", lid)
        await state.clear()
        bal = person_balance(OWNER_ID, data["person_id"])
        limit = get_credit_limit(OWNER_ID, data["person_id"])
        warn = f"\n⚠️ <b>Over limit</b> (limit {CURRENCY}{limit:,.2f})" if (limit is not None and bal>float(limit)) else ""
        dd = "" if not due_ts else "\n⏰ Due " + datetime.fromtimestamp(due_ts, TZ).strftime("%d %b")
        await send_text(m.chat.id,
                        f"✅ Lend saved: {CURRENCY}{data['amount']:,.2f}{dd}\n"
                        f"💼 New balance: {CURRENCY}{bal:,.2f}{warn}",
                        people_kb(OWNER_ID))
    except Exception as e:
        await m.answer(f"❌ lend save error: {e}")

# Repay
@router.callback_query(F.data.startswith("repay:"))
async def cb_repay(c: CallbackQuery, state: FSMContext):
    try:
        if not only_owner(c): return await c.message.answer(deny_text())
        pid = int(c.data.split(":")[1])
        await state.set_state(RepayStates.waiting_amount); await state.update_data(person_id=pid)
        await safe_edit(c.message, "💸 Enter REPAY amount (they returned to you):", None); await c.answer()
    except Exception as e:
        await c.message.answer(f"❌ repay error: {e}")

@router.message(RepayStates.waiting_amount)
async def repay_amount(m: Message, state: FSMContext):
    try:
        if not only_owner(m): return await m.answer(deny_text())
        try:
            amt = float(m.text.strip()); assert amt > 0
        except Exception:
            return await m.answer("⚠️ Send a valid positive number.")
        await state.update_data(amount=amt)
        await state.set_state(RepayStates.waiting_note)
        await m.answer("📝 Optional note? (or tap Skip)", reply_markup=skip_kb())
    except Exception as e:
        await m.answer(f"❌ repay amount error: {e}")

@router.message(RepayStates.waiting_note)
async def repay_note(m: Message, state: FSMContext):
    try:
        if not only_owner(m): return await m.answer(deny_text())
        data = await state.get_data()
        note = None if (m.text or "").strip().lower()=="skip" else (m.text or "").strip()
        lid = add_ledger(OWNER_ID, data["person_id"], "repay", data["amount"], note)
        log_action(OWNER_ID, "ledger", "ledger", lid)
        await state.clear()
        bal = person_balance(OWNER_ID, data["person_id"])
        await send_text(m.chat.id,
                        f"✅ Repay saved: {CURRENCY}{data['amount']:,.2f}\n"
                        f"💼 New balance: {CURRENCY}{bal:,.2f}",
                        people_kb(OWNER_ID))
    except Exception as e:
        await m.answer(f"❌ repay save error: {e}")

# Settle
@router.callback_query(F.data.startswith("settle:"))
async def cb_settle(c: CallbackQuery):
    try:
        if not only_owner(c): return await c.message.answer(deny_text())
        pid = int(c.data.split(":")[1])
        bal = person_balance(OWNER_ID, pid)
        if abs(bal) < 1e-9:
            await c.answer("Already settled"); return
        if bal > 0:
            lid = add_ledger(OWNER_ID, pid, "repay", bal, "auto-settle")
        else:
            lid = add_ledger(OWNER_ID, pid, "lend", abs(bal), "auto-settle")
        log_action(OWNER_ID, "ledger", "ledger", lid)
        new_bal = person_balance(OWNER_ID, pid)
        await send_text(c.message.chat.id, f"🤝 Settled. Balance now {CURRENCY}{new_bal:,.2f}.", people_kb(OWNER_ID))
        await c.answer()
    except Exception as e:
        await c.message.answer(f"❌ settle error: {e}")

# Limits & Interest
@router.callback_query(F.data.startswith("setlimit:"))
async def cb_setlimit(c: CallbackQuery, state: FSMContext):
    try:
        if not only_owner(c): return await c.message.answer(deny_text())
        pid = int(c.data.split(":")[1])
        await state.set_state(LimitState.waiting_amount); await state.update_data(person_id=pid)
        await safe_edit(c.message, "🎯 Send limit amount (number) or <code>0</code> to clear.", None); await c.answer()
    except Exception as e:
        await c.message.answer(f"❌ setlimit error: {e}")

@router.message(LimitState.waiting_amount)
async def setlimit_amount(m: Message, state: FSMContext):
    try:
        if not only_owner(m): return await m.answer(deny_text())
        try:
            amt = float(m.text.strip())
        except Exception:
            return await m.answer("⚠️ Send a valid number.")
        data = await state.get_data(); pid = data["person_id"]
        set_credit_limit(OWNER_ID, pid, None if amt <= 0 else amt)
        await state.clear()
        await send_text(m.chat.id, "✅ Limit updated.", people_kb(OWNER_ID))
    except Exception as e:
        await m.answer(f"❌ setlimit save error: {e}")

@router.callback_query(F.data.startswith("setinterest:"))
async def cb_setinterest(c: CallbackQuery, state: FSMContext):
    try:
        if not only_owner(c): return await c.message.answer(deny_text())
        pid = int(c.data.split(":")[1])
        await state.set_state(InterestState.waiting_rate); await state.update_data(person_id=pid)
        await safe_edit(c.message, "💠 Send monthly interest rate in % (e.g., 2 for 2%). Use 0 to clear.", None); await c.answer()
    except Exception as e:
        await c.message.answer(f"❌ setinterest error: {e}")

@router.message(InterestState.waiting_rate)
async def setinterest_rate(m: Message, state: FSMContext):
    try:
        if not only_owner(m): return await m.answer(deny_text())
        try:
            rate = float(m.text.strip()); assert rate >= 0
        except Exception:
            return await m.answer("⚠️ Send a non-negative number.")
        data = await state.get_data(); pid = data["person_id"]
        set_interest_rate(OWNER_ID, pid, None if rate == 0 else rate)
        await state.clear()
        await send_text(m.chat.id, "✅ Interest updated.", people_kb(OWNER_ID))
    except Exception as e:
        await m.answer(f"❌ setinterest save error: {e}")

# Ledger & Export
@router.callback_query(F.data.startswith("ledger:"))
async def cb_ledger(c: CallbackQuery):
    try:
        if not only_owner(c): return await c.message.answer(deny_text())
        pid = int(c.data.split(":")[1])
        con = db(); cur = con.cursor()
        cur.execute("SELECT display_name FROM people WHERE user_id=? AND id=?", (OWNER_ID, pid))
        row = cur.fetchone(); con.close()
        if not row: return await c.answer("Not found")
        name = row["display_name"]
        rows = get_ledger(OWNER_ID, pid)
        if not rows:
            text = f"🗒 Ledger for <b>{name}</b> is empty."
        else:
            last = rows[-10:]
            lines = []
            for r in last:
                dt = datetime.fromtimestamp(r["ts"], TZ).strftime("%d %b %H:%M")
                sym = {"lend":"➕","repay":"➖","interest":"➕"}[r["type"]]
                due = f" ⏰{datetime.fromtimestamp(r['due_ts'], TZ).strftime('%d %b')}" if r["due_ts"] else ""
                lines.append(f"{dt} {sym} {CURRENCY}{float(r['amount']):,.2f}{due} — {r['note']}")
            bal = person_balance(OWNER_ID, pid)
            text = (f"🗒 <b>{name}</b> (last {len(last)} of {len(rows)})\n" +
                    "\n".join(lines) +
                    f"\n\n💼 Balance: <b>{CURRENCY}{bal:,.2f}</b>")
        await safe_edit(c.message, text, person_menu_kb(pid)); await c.answer()
    except Exception as e:
        await c.message.answer(f"❌ ledger error: {e}")

@router.callback_query(F.data.startswith("export_person:"))
async def cb_export_person(c: CallbackQuery):
    try:
        if not only_owner(c): return await c.message.answer(deny_text())
        pid = int(c.data.split(":")[1])
        con = db(); cur = con.cursor()
        cur.execute("SELECT display_name FROM people WHERE user_id=? AND id=?", (OWNER_ID, pid))
        row = cur.fetchone(); con.close()
        if not row: return await c.answer("Not found")
        name = row["display_name"]
        fpath = export_person_csv(OWNER_ID, pid, name)
        msg = await c.message.answer_document(FSInputFile(fpath), caption=f"📄 Ledger: {name}")
        record_bot_message(OWNER_ID, c.message.chat.id, msg.message_id)
        await c.answer("Exported")
    except Exception as e:
        await c.message.answer(f"❌ export person error: {e}")

@router.callback_query(F.data == "export_all")
async def cb_export_all(c: CallbackQuery):
    try:
        if not only_owner(c): return await c.message.answer(deny_text())
        zpath = export_all_zip(OWNER_ID)
        msg = await c.message.answer_document(FSInputFile(zpath), caption="📦 All ledgers + expenses")
        record_bot_message(OWNER_ID, c.message.chat.id, msg.message_id)
        await c.answer("Exported")
    except Exception as e:
        await c.message.answer(f"❌ export all error: {e}")

# Monthly + Category chart (independent replies to avoid 'not modified')
@router.callback_query(F.data == "monthly")
async def cb_monthly(c: CallbackQuery):
    try:
        if not only_owner(c): return await c.message.answer(deny_text())
        month = cur_yyyymm(); total = monthly_total(OWNER_ID, month)
        tb = top_balances(OWNER_ID, 5)
        lines = [f"📊 <b>{month} Summary</b>",
                 f"🧾 Personal Spend: <b>{CURRENCY}{total:,.2f}</b>"]
        cats = monthly_by_category(OWNER_ID, month)
        if cats:
            lines.append("\n🏷️ By category:")
            for r in cats:
                lines.append(f"• {r['cat']}: {CURRENCY}{float(r['s']):,.2f}")
        if tb:
            lines.append("\n👥 Top balances:")
            for r in tb:
                lines.append(f"• {r['display_name']}: {CURRENCY}{float(r['balance']):,.2f}")
        await send_text(c.message.chat.id, "\n".join(lines), main_kb()); await c.answer()
    except Exception as e:
        await c.message.answer(f"❌ monthly error: {e}")

@router.callback_query(F.data == "cat_chart")
async def cb_cat_chart(c: CallbackQuery):
    try:
        if not only_owner(c): return await c.message.answer(deny_text())
        png = render_category_chart_png(OWNER_ID, cur_yyyymm())
        if not png:
            return await send_text(c.message.chat.id, "ℹ️ No data or chart engine unavailable.", main_kb())
        await send_photo(c.message.chat.id, png, "category_chart.png", "📉 Category chart (current month)", main_kb())
        await c.answer()
    except Exception as e:
        await c.message.answer(f"❌ chart error: {e}")

# Due Soon (independent)
@router.callback_query(F.data == "due_soon")
async def cb_due_soon(c: CallbackQuery):
    try:
        if not only_owner(c): return await c.message.answer(deny_text())
        rows = due_items(OWNER_ID, 7)
        if not rows:
            txt = "✅ Nothing due in the next 7 days."
        else:
            parts = ["⏰ <b>Due Soon / Overdue</b>"]
            for r in rows:
                when = datetime.fromtimestamp(r["due_ts"], TZ).strftime("%d %b")
                parts.append(f"• {r['name']}: {CURRENCY}{float(r['amount']):,.2f} — due {when}")
            txt = "\n".join(parts)
        await send_text(c.message.chat.id, txt, main_kb()); await c.answer()
    except Exception as e:
        await c.message.answer(f"❌ due soon error: {e}")

# Reminders UI
@router.callback_query(F.data == "reminders")
async def cb_reminders(c: CallbackQuery):
    try:
        if not only_owner(c): return await c.message.answer(deny_text())
        s = get_settings(OWNER_ID)
        days = ["Mon","Tue","Wed","Thu","Fri","Sat","Sun"]
        text = (f"🔔 <b>Reminders</b>\n"
                f"Daily: {'ON' if s['daily_reminders'] else 'OFF'} at {s['daily_hour']:02d}:00 IST\n"
                f"Weekly: {'ON' if s['weekly_reminders'] else 'OFF'} on {days[s['weekly_dow']]} (10:00 IST)")
        await send_text(c.message.chat.id, text, reminders_kb()); await c.answer()
    except Exception as e:
        await c.message.answer(f"❌ reminders error: {e}")

@router.callback_query(F.data == "toggle_daily")
async def toggle_daily(c: CallbackQuery):
    try:
        if not only_owner(c): return await c.message.answer(deny_text())
        s = get_settings(OWNER_ID); newv = 0 if s["daily_reminders"] else 1
        set_setting(OWNER_ID, "daily_reminders", newv)
        await cb_reminders(c)
    except Exception as e:
        await c.message.answer(f"❌ toggle daily error: {e}")

@router.callback_query(F.data == "toggle_weekly")
async def toggle_weekly(c: CallbackQuery):
    try:
        if not only_owner(c): return await c.message.answer(deny_text())
        s = get_settings(OWNER_ID); newv = 0 if s["weekly_reminders"] else 1
        set_setting(OWNER_ID, "weekly_reminders", newv)
        await cb_reminders(c)
    except Exception as e:
        await c.message.answer(f"❌ toggle weekly error: {e}")

@router.callback_query(F.data == "set_daily_hour")
async def ask_daily_hour(c: CallbackQuery, state: FSMContext):
    try:
        if not only_owner(c): return await c.message.answer(deny_text())
        await state.set_state(DailyHourState.waiting_hour)
        await safe_edit(c.message, "🕘 Send daily reminder hour (0-23 IST):", None); await c.answer()
    except Exception as e:
        await c.message.answer(f"❌ set hour error: {e}")

@router.message(DailyHourState.waiting_hour)
async def set_daily_hour(m: Message, state: FSMContext):
    try:
        if not only_owner(m): return await m.answer(deny_text())
        try:
            h = int(m.text.strip()); assert 0 <= h <= 23
        except Exception:
            return await m.answer("⚠️ Send an integer from 0 to 23.")
        set_setting(OWNER_ID, "daily_hour", h); await state.clear()
        await send_text(m.chat.id, "✅ Daily hour updated.", reminders_kb())
    except Exception as e:
        await m.answer(f"❌ set hour save error: {e}")

@router.callback_query(F.data == "set_weekly_dow")
async def ask_weekly_dow(c: CallbackQuery, state: FSMContext):
    try:
        if not only_owner(c): return await c.message.answer(deny_text())
        await state.set_state(WeeklyDowState.waiting_dow)
        await safe_edit(c.message, "📅 Send weekly day number (0=Mon .. 6=Sun):", None); await c.answer()
    except Exception as e:
        await c.message.answer(f"❌ set dow error: {e}")

@router.message(WeeklyDowState.waiting_dow)
async def set_weekly_dow(m: Message, state: FSMContext):
    try:
        if not only_owner(m): return await m.answer(deny_text())
        try:
            d = int(m.text.strip()); assert 0 <= d <= 6
        except Exception:
            return await m.answer("⚠️ Send an integer from 0 to 6.")
        set_setting(OWNER_ID, "weekly_dow", d); await state.clear()
        await send_text(m.chat.id, "✅ Weekly day updated.", reminders_kb())
    except Exception as e:
        await m.answer(f"❌ set dow save error: {e}")

# Undo & Reset All
@router.callback_query(F.data == "undo")
async def cb_undo(c: CallbackQuery):
    try:
        if not only_owner(c): return await c.message.answer(deny_text())
        msg = undo_last(OWNER_ID)
        await send_text(c.message.chat.id, f"🧹 {msg}", main_kb()); await c.answer("Done")
    except Exception as e:
        await c.message.answer(f"❌ undo error: {e}")

@router.callback_query(F.data == "reset_all_confirm")
async def reset_all_confirm(c: CallbackQuery):
    try:
        if not only_owner(c): return await c.message.answer(deny_text())
        txt = ("⚠️ <b>Reset Everything?</b>\nThis will delete ALL people, ledger, expenses and settings. "
               "This cannot be undone.")
        await send_text(c.message.chat.id, txt, reset_confirm_kb()); await c.answer()
    except Exception as e:
        await c.message.answer(f"❌ reset ui error: {e}")

@router.callback_query(F.data == "reset_all_do")
async def reset_all_do(c: CallbackQuery):
    try:
        if not only_owner(c): return await c.message.answer(deny_text())
        con = db(); cur = con.cursor()
        cur.execute("DELETE FROM ledger WHERE user_id=?", (OWNER_ID,))
        cur.execute("DELETE FROM expenses WHERE user_id=?", (OWNER_ID,))
        cur.execute("DELETE FROM people WHERE user_id=?", (OWNER_ID,))
        cur.execute("DELETE FROM actions WHERE user_id=?", (OWNER_ID,))
        cur.execute("DELETE FROM settings WHERE user_id=?", (OWNER_ID,))
        con.commit(); con.close()
        migrate_defaults()
        await send_text(c.message.chat.id, "🧼 All data reset. Fresh start!", main_kb()); await c.answer("Reset")
    except Exception as e:
        await c.message.answer(f"❌ reset error: {e}")

# ---------- IMPORT SHEET ----------
@router.callback_query(F.data == "import_sheet")
async def cb_import_sheet(c: CallbackQuery, state: FSMContext):
    try:
        if not only_owner(c): return await c.message.answer(deny_text())
        await state.set_state(ImportState.waiting_file)
        await send_text(c.message.chat.id,
            "📥 <b>Import Sheet</b>\n"
            "Upload a CSV or XLSX (export from Google Sheets).\n"
            "Supported columns:\n"
            "• Expenses: date, amount, note, category\n"
            "• Ledger: person, type(lend|repay), amount, note, duedate\n"
            "If type is missing: positive=lend, negative=repay."
        )
        await c.answer()
    except Exception as e:
        await c.message.answer(f"❌ import ui error: {e}")

async def _download_document(doc: Document, dest: Path):
    file = await bot.get_file(doc.file_id)
    await bot.download(file, destination=dest)

def _colexists(cols, *names):
    s = {c.strip().lower() for c in cols}
    for n in names:
        if n.lower() in s: return n.lower()
    return None

def _to_float_safe(v) -> Optional[float]:
    try:
        if v is None: return None
        if isinstance(v, str): v = v.strip().replace(",", "")
        f = float(v); return f
    except Exception:
        return None

async def _ingest_dataframe(df, results):
    cols = [str(c).strip() for c in df.columns]
    lower = [c.lower() for c in cols]
    has_person = any(c in lower for c in ["person","name"])
    has_amount = any(c in lower for c in ["amount","amt","value"])
    has_type = any(c in lower for c in ["type","tx_type","kind"])
    if not has_amount:
        results["skipped"] += len(df); return

    if not has_person:
        c_amount = lower.index(_colexists(lower,"amount","amt","value"))
        c_note = lower.index(_colexists(lower,"note","description","desc","remarks")) if _colexists(lower,"note","description","desc","remarks") else None
        c_cat = lower.index(_colexists(lower,"category","cat","type")) if _colexists(lower,"category","cat","type") else None
        for _, row in df.iterrows():
            amt = _to_float_safe(row.iloc[c_amount]); 
            if (amt is None) or (amt == 0): 
                results["skipped"] += 1; continue
            note = (str(row.iloc[c_note]).strip() if (c_note is not None and (not HAS_PANDAS or pd.notna(row.iloc[c_note]))) else None)
            cat = (str(row.iloc[c_cat]).strip() if (c_cat is not None and (not HAS_PANDAS or pd.notna(row.iloc[c_cat]))) else None)
            eid = add_expense(OWNER_ID, amt, note, cat)
            log_action(OWNER_ID, "expense", "expenses", eid)
            results["expenses"] += 1
    else:
        c_person = lower.index(_colexists(lower,"person","name"))
        c_amount = lower.index(_colexists(lower,"amount","amt","value"))
        c_type = lower.index(_colexists(lower,"type","tx_type","kind")) if has_type else None
        c_note = lower.index(_colexists(lower,"note","description","desc","remarks")) if _colexists(lower,"note","description","desc","remarks") else None
        c_due = lower.index(_colexists(lower,"duedate","due","deadline","due_date")) if _colexists(lower,"duedate","due","deadline","due_date") else None
        for _, row in df.iterrows():
            name = str(row.iloc[c_person]).strip()
            if not name:
                results["skipped"] += 1; continue
            pid, _disp = resolve_person_id(OWNER_ID, name)
            if not pid:
                pid, _ = add_person(OWNER_ID, name)
            amt = _to_float_safe(row.iloc[c_amount])
            if (amt is None) or (amt == 0):
                results["skipped"] += 1; continue
            tx_type = None
            if c_type is not None:
                tx_type = str(row.iloc[c_type]).strip().lower()
                if tx_type not in ("lend","repay"):
                    tx_type = None
            if tx_type is None:
                tx_type = "lend" if amt > 0 else "repay"
                amt = abs(amt)
            note = (str(row.iloc[c_note]).strip() if (c_note is not None and (not HAS_PANDAS or pd.notna(row.iloc[c_note]))) else None)
            due_ts = None
            if c_due is not None:
                dts = str(row.iloc[c_due]).strip()
                if dts:
                    d = parse_date_fuzzy(dts)
                    if d: due_ts = int(d.replace(hour=23, minute=59).timestamp())
            lid = add_ledger(OWNER_ID, pid, tx_type, amt, note, due_ts)
            log_action(OWNER_ID, "ledger", "ledger", lid)
            results["ledger"] += 1

@router.message(ImportState.waiting_file, F.document)
async def handle_import_file(m: Message, state: FSMContext):
    try:
        if not only_owner(m): return await m.answer(deny_text())
        doc = m.document
        suffix = (doc.file_name or "").lower()
        tmp_dir = Path("imports"); tmp_dir.mkdir(exist_ok=True)
        dest = tmp_dir / f"{int(time.time())}_{doc.file_name}"
        await _download_document(doc, dest)

        results = {"expenses":0, "ledger":0, "skipped":0, "sheets":0}
        try:
            if suffix.endswith(".csv"):
                if not HAS_PANDAS:
                    return await m.answer("⚠️ Install pandas to import CSV/XLSX.")
                df = pd.read_csv(dest)
                await _ingest_dataframe(df, results); results["sheets"] = 1
            elif suffix.endswith(".xlsx") or suffix.endswith(".xls"):
                if not HAS_PANDAS:
                    return await m.answer("⚠️ Install pandas/openpyxl to import XLSX.")
                x = pd.ExcelFile(dest)
                for s in x.sheet_names:
                    df = x.parse(s)
                    await _ingest_dataframe(df, results)
                    results["sheets"] += 1
            else:
                return await m.answer("⚠️ Please upload a CSV or XLSX file.")
        except Exception as e:
            return await m.answer(f"❌ Import failed: {e}")

        await state.clear()
        month = cur_yyyymm()
        total = monthly_total(OWNER_ID, month)
        await send_text(m.chat.id,
            f"✅ <b>Import complete</b>\n"
            f"Sheets: {results['sheets']}\n"
            f"Expenses added: {results['expenses']}\n"
            f"Ledger rows added: {results['ledger']}\n"
            f"Skipped rows: {results['skipped']}\n\n"
            f"🧾 {month} spend: <b>{CURRENCY}{total:,.2f}</b>",
            main_kb()
        )
    except Exception as e:
        await m.answer(f"❌ import handler error: {e}")

# ---------- SUPPORT (AI) ----------
@router.callback_query(F.data == "support_ai")
async def cb_support_ai(c: CallbackQuery, state: FSMContext):
    try:
        if not only_owner(c): return await c.message.answer(deny_text())
        await state.set_state(SupportAIState.waiting_query)
        await send_text(c.message.chat.id,
            "🧑‍🤝‍🧑 <b>Support Assistant</b>\n"
            "Ask me: ‘how much do I owe Ajay?’, ‘Ajay balance’, ‘monthly spend’, ‘due soon’, ‘ledger Ajay’, etc."
        )
        await c.answer()
    except Exception as e:
        await c.message.answer(f"❌ support ui error: {e}")

def _nl_intent(q: str):
    s = canonical(q)
    # direct keywords
    if "monthly" in s and ("spend" in s or "expense" in s):
        return ("monthly_spend", None)
    if "due" in s or "overdue" in s or "due soon" in s:
        return ("due_soon", None)
    # patterns for balance / owe
    # capture trailing name after 'owe', 'owe to', 'balance', 'with'
    m = re.search(r"(?:owe to|owe|balance(?: with| of| for)?|how much .* owe to?)\s+([a-z0-9 ._-]{2,})", s)
    if not m:
        # "ajay balance", "ajay owes me", "i owe ajay"
        m = re.search(r"^([a-z0-9 ._-]{2,})\s+(?:balance|owes me|i owe)$", s)
    person = m.group(1).strip() if m else None
    if person:
        return ("balance_person", person)
    # ledger
    m2 = re.search(r"(?:ledger|history|statement)\s+(?:of|for)?\s*([a-z0-9 ._-]{2,})", s)
    if m2:
        return ("ledger_person", m2.group(1).strip())
    return ("unknown", None)

async def ai_explain(prompt: str, base_reply: str, context: str) -> Optional[str]:
    if not HAS_SAFONE:
        return None
    try:
        api = SafoneAPI()
        if hasattr(api, "chat"):
            msg = f"Context:\n{context}\n\nUser question: {prompt}\nAnswer briefly."
            resp = await api.chat(msg)
            text = getattr(resp, "results", None)
            if not text: text = str(resp)
            return f"{base_reply}\n\n🤖 {text}"
        return None
    except Exception:
        return None

@router.message(SupportAIState.waiting_query)
async def handle_support_query(m: Message, state: FSMContext):
    try:
        if not only_owner(m): return await m.answer(deny_text())
        q = (m.text or "").strip()
        intent, arg = _nl_intent(q)

        if intent == "monthly_spend":
            month = cur_yyyymm()
            total = monthly_total(OWNER_ID, month)
            base = f"🧾 {month} spend: <b>{CURRENCY}{total:,.2f}</b>"
            extra = await ai_explain(q, base, f"Monthly spend {month} is {total}")
            await state.clear()
            return await send_text(m.chat.id, extra or base, main_kb())

        if intent == "due_soon":
            rows = due_items(OWNER_ID, 7)
            if not rows:
                base = "✅ Nothing due in the next 7 days."
            else:
                parts = ["⏰ <b>Due Soon / Overdue</b>"]
                for r in rows:
                    when = datetime.fromtimestamp(r["due_ts"], TZ).strftime("%d %b")
                    parts.append(f"• {r['name']}: {CURRENCY}{float(r['amount']):,.2f} — due {when}")
                base = "\n".join(parts)
            extra = await ai_explain(q, base, "Due soon list above.")
            await state.clear()
            return await send_text(m.chat.id, extra or base, main_kb())

        if intent in ("balance_person","ledger_person") and arg:
            pid, disp = resolve_person_id(OWNER_ID, arg)
            if not pid:
                await state.clear()
                return await send_text(m.chat.id, f"⚠️ Person “{arg}” not found. (Add via 👥 People)", main_kb())
            if intent == "balance_person":
                bal = person_balance(OWNER_ID, pid)
                if bal > 0:
                    base = f"📌 {disp} owes you <b>{CURRENCY}{bal:,.2f}</b>."
                elif bal < 0:
                    base = f"📌 You owe {disp} <b>{CURRENCY}{abs(bal):,.2f}</b>."
                else:
                    base = f"📌 You and {disp} are settled (₹0)."
                extra = await ai_explain(q, base, f"Balance with {disp} is {bal}")
                await state.clear()
                return await send_text(m.chat.id, extra or base, main_kb())
            else:
                rows = get_ledger(OWNER_ID, pid)
                if not rows:
                    base = f"🗒 Ledger for <b>{disp}</b> is empty."
                else:
                    last = rows[-10:]
                    lines = []
                    for r in last:
                        dt = datetime.fromtimestamp(r["ts"], TZ).strftime("%d %b %H:%M")
                        sym = {"lend":"➕","repay":"➖","interest":"➕"}[r["type"]]
                        due = f" ⏰{datetime.fromtimestamp(r['due_ts'], TZ).strftime('%d %b')}" if r["due_ts"] else ""
                        lines.append(f"{dt} {sym} {CURRENCY}{float(r['amount']):,.2f}{due} — {r['note']}")
                    bal = person_balance(OWNER_ID, pid)
                    base = (f"🗒 <b>{disp}</b> (last {len(last)} of {len(rows)})\n" +
                            "\n".join(lines) +
                            f"\n\n💼 Balance: <b>{CURRENCY}{bal:,.2f}</b>")
                extra = await ai_explain(q, base, f"Ledger shown for {disp}.")
                await state.clear()
                return await send_text(m.chat.id, extra or base, main_kb())

        base = "🤖 I can answer: ‘monthly spend’, ‘due soon’, ‘Ajay balance’, ‘how much do I owe Ajay’, or ‘ledger Ajay’."
        extra = await ai_explain(q, base, "Help user with supported intents.")
        await state.clear()
        return await send_text(m.chat.id, extra or base, main_kb())
    except Exception as e:
        await state.clear()
        await m.answer(f"❌ support error: {e}")

# Quick-add parsers (extended NLP)
NAME_SIGN_RE = re.compile(r"^\s*(?P<name>[A-Za-z0-9 ._-]{2,})\s+(?P<sign>[+-])\s*(?P<amt>\d+(?:\.\d{1,2})?)\s*(?P<note>.+)?$")
QUICK_RE = re.compile(r"^\s*(\d+(?:\.\d{1,2})?)\s*>\s*(add\s*to|lend\s*to|repay|repay\s*from|repay\s*to)\s*>\s*(.+)$", re.IGNORECASE)
VERBAL_RE_1 = re.compile(r"lend\s+(?P<amt>\d+(?:\.\d{1,2})?)\s+(?:to\s+)?(?P<name>[A-Za-z0-9 ._-]{2,})(?:\s+(?P<note>.+))?", re.IGNORECASE)
VERBAL_RE_2 = re.compile(r"(?:repay|returned?)\s+(?P<amt>\d+(?:\.\d{1,2})?)\s+(?:from|by)?\s*(?P<name>[A-Za-z0-9 ._-]{2,})(?:\s+(?P<note>.+))?", re.IGNORECASE)

@router.message()
async def catch_all(m: Message):
    try:
        if not only_owner(m): return await m.answer(deny_text())
        txt = (m.text or "").strip()
        if not txt: return

        mm2 = NAME_SIGN_RE.match(txt)
        if mm2:
            name = mm2.group("name").strip()
            sign = mm2.group("sign")
            amt = float(mm2.group("amt"))
            note = (mm2.group("note") or "").strip() or "quick-add"
            pid, disp = resolve_person_id(OWNER_ID, name)
            if not pid:
                return await m.answer("⚠️ Person not found. Add them first via 👥 People → ➕ Add Person.")
            if sign == "+":
                lid = add_ledger(OWNER_ID, pid, "lend", amt, note)
                log_action(OWNER_ID, "ledger", "ledger", lid)
                bal = person_balance(OWNER_ID, pid)
                return await send_text(m.chat.id, f"✅ Lend {CURRENCY}{amt:,.2f} to <b>{disp}</b>\n💼 New balance: {CURRENCY}{bal:,.2f}", people_kb(OWNER_ID))
            else:
                lid = add_ledger(OWNER_ID, pid, "repay", amt, note)
                log_action(OWNER_ID, "ledger", "ledger", lid)
                bal = person_balance(OWNER_ID, pid)
                return await send_text(m.chat.id, f"✅ Repay {CURRENCY}{amt:,.2f} from <b>{disp}</b>\n💼 New balance: {CURRENCY}{bal:,.2f}", people_kb(OWNER_ID))

        mm = QUICK_RE.match(txt)
        if mm:
            amount = float(mm.group(1))
            action = mm.group(2).lower().replace(" ", "")
            name = mm.group(3).strip()
            pid, disp = resolve_person_id(OWNER_ID, name)
            if not pid:
                return await m.answer("⚠️ Person not found. Add them first via 👥 People → ➕ Add Person.")
            if "addto" in action or "lendto" in action:
                lid = add_ledger(OWNER_ID, pid, "lend", amount, "quick-add")
            else:
                lid = add_ledger(OWNER_ID, pid, "repay", amount, "quick-add")
            log_action(OWNER_ID, "ledger", "ledger", lid)
            bal = person_balance(OWNER_ID, pid)
            return await send_text(m.chat.id, f"✅ {'Lend' if 'addto' in action or 'lendto' in action else 'Repay'} {CURRENCY}{amount:,.2f} {'to' if 'lend' in action else 'from'} <b>{disp}</b>\n💼 New balance: {CURRENCY}{bal:,.2f}", people_kb(OWNER_ID))

        mm3 = VERBAL_RE_1.match(txt)  # lend X to Name
        mm4 = VERBAL_RE_2.match(txt)  # repay X from Name
        if mm3 or mm4:
            lend_mode = bool(mm3)
            g = mm3 if mm3 else mm4
            amount = float(g.group("amt"))
            name = g.group("name").strip()
            note = (g.group("note") or "quick-add").strip()
            pid, disp = resolve_person_id(OWNER_ID, name)
            if not pid:
                return await m.answer("⚠️ Person not found. Add them first via 👥 People → ➕ Add Person.")
            if lend_mode:
                lid = add_ledger(OWNER_ID, pid, "lend", amount, note)
            else:
                lid = add_ledger(OWNER_ID, pid, "repay", amount, note)
            log_action(OWNER_ID, "ledger", "ledger", lid)
            bal = person_balance(OWNER_ID, pid)
            return await send_text(m.chat.id, f"✅ {'Lend' if lend_mode else 'Repay'} {CURRENCY}{amount:,.2f} {'to' if lend_mode else 'from'} <b>{disp}</b>\n💼 New balance: {CURRENCY}{bal:,.2f}", people_kb(OWNER_ID))

        await send_text(m.chat.id, "Use the buttons below 👇", main_kb())
    except Exception as e:
        await m.answer(f"❌ handler error: {e}", reply_markup=main_kb())

# ---------- Background tasks: reminders + monthly interest ----------
async def send_daily_summary():
    month = cur_yyyymm()
    total = monthly_total(OWNER_ID, month)
    tb = top_balances(OWNER_ID, 10)
    lines = [f"📬 <b>Daily Summary</b> ({datetime.now(TZ).strftime('%Y-%m-%d')})",
             f"🧾 {month} spend: <b>{CURRENCY}{total:,.2f}</b>"]
    due = due_items(OWNER_ID, 7)
    if due:
        lines.append("\n⏰ Due Soon / Overdue (7d):")
        for r in due[:10]:
            when = datetime.fromtimestamp(r["due_ts"], TZ).strftime("%d %b")
            lines.append(f"• {r['name']}: {CURRENCY}{float(r['amount']):,.2f} — due {when}")
    if tb:
        lines.append("\n👥 Top balances:")
        for r in tb[:10]:
            lines.append(f"• {r['display_name']}: {CURRENCY}{float(r['balance']):,.2f}")
    try:
        msg = await bot.send_message(OWNER_ID, "\n".join(lines))
        record_bot_message(OWNER_ID, OWNER_ID, msg.message_id)
    except Exception:
        pass

async def send_weekly_digest():
    month = cur_yyyymm()
    total = monthly_total(OWNER_ID, month)
    tb = top_balances(OWNER_ID, 20)
    lines = [f"🗞️ <b>Weekly Digest</b> (week of {datetime.now(TZ).strftime('%Y-%m-%d')})",
             f"🧾 {month} spend so far: <b>{CURRENCY}{total:,.2f}</b>",
             "👥 Balances (top 20):"]
    for r in tb:
        lines.append(f"• {r['display_name']}: {CURRENCY}{float(r['balance']):,.2f}")
    try:
        msg = await bot.send_message(OWNER_ID, "\n".join(lines))
        record_bot_message(OWNER_ID, OWNER_ID, msg.message_id)
    except Exception:
        pass

async def apply_monthly_interest():
    yyyymm = cur_yyyymm()
    for p in get_people(OWNER_ID):
        rate = p["monthly_interest_rate"]
        if rate is None or rate <= 0:
            continue
        if p["last_interest_yyyymm"] == yyyymm:
            continue
        bal = person_balance(OWNER_ID, p["id"])
        if bal > 0:
            interest_amt = round(bal * (rate/100.0), 2)
            if interest_amt > 0:
                lid = add_ledger(OWNER_ID, p["id"], "interest", interest_amt, f"monthly interest {rate:.2f}%")
                log_action(OWNER_ID, "ledger", "ledger", lid)
        update_last_interest_applied(OWNER_ID, p["id"], yyyymm)

async def scheduler_loop():
    import asyncio
    while True:
        try:
            await apply_monthly_interest()
            s = get_settings(OWNER_ID)
            now = datetime.now(TZ)
            # Daily
            if s["daily_reminders"]:
                today = now.strftime("%Y-%m-%d")
                if s["last_daily_date"] != today and now.hour >= int(s["daily_hour"]):
                    await send_daily_summary()
                    set_setting(OWNER_ID, "last_daily_date", today)
            # Weekly
            if s["weekly_reminders"]:
                week_key = f"{now.year}-W{now.isocalendar().week}"
                if now.weekday() == int(s["weekly_dow"]) and now.hour >= 10 and s["last_weekly_date"] != week_key:
                    await send_weekly_digest()
                    set_setting(OWNER_ID, "last_weekly_date", week_key)
        except Exception:
            pass
        await asyncio.sleep(60)

# Proper startup/shutdown registration
@dp.startup.register
async def on_startup():
    import asyncio
    init_db(); migrate_defaults()
    global SCHED_TASK
    try:
        SCHED_TASK = asyncio.create_task(scheduler_loop())
    except Exception:
        SCHED_TASK = None

@dp.shutdown.register
async def on_shutdown():
    import asyncio
    global SCHED_TASK
    if SCHED_TASK:
        SCHED_TASK.cancel()
        try:
            await SCHED_TASK
        except asyncio.CancelledError:
            pass

# ---------- Main ----------
if __name__ == "__main__":
    import asyncio
    try:
        asyncio.run(dp.start_polling(bot))
    except (KeyboardInterrupt, SystemExit):
        pass
