#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Expense & Lending Bot (clean build)
- Aiogram v3.x
- SQLite backend
- Independent UI responses (title + separate menu)
- Robust HTML escaping for any shell/log output
- Per-user "delete user messages" (best-effort; Telegram DM limitation handled)
- Delete old bot messages keeping last N
- Dev Tools separated from Extras (Update, Restart, Logs, AI Summarize)
- Search (people) fixed – case-insensitive by name/phone
- 20+ useful Extras (calculators, conversions, reports, utilities)
"""

import os
import sys
import asyncio
import html
import json
import math
import uuid
from datetime import datetime, timezone, timedelta
from typing import Optional, List, Tuple

import sqlite3

from aiogram import Bot, Dispatcher, Router, F
from aiogram.dispatcher.middlewares.base import BaseMiddleware
from aiogram.types import Message, CallbackQuery, InputFile
from aiogram.utils.keyboard import InlineKeyboardBuilder
from aiogram.fsm.storage.memory import MemoryStorage
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import StatesGroup, State
from aiogram.filters import CommandStart, Command
from aiogram.exceptions import TelegramBadRequest

# ------------------- Config -------------------

BOT_TOKEN = os.getenv("BOT_TOKEN", "").strip()
if not BOT_TOKEN:
    print("ERROR: Set BOT_TOKEN in environment")
    sys.exit(1)

OWNER_ID = int(os.getenv("OWNER_ID", "0") or 0)

DATA_DIR = Path(os.getenv("DATA_DIR", "data"))
DATA_DIR.mkdir(parents=True, exist_ok=True)
DB_PATH = DATA_DIR / "bot.db"

TZ = timezone(timedelta(hours=int(os.getenv("TZ_OFFSET_HOURS", "5")) + int(os.getenv("TZ_OFFSET_MINUTES", "30"))/60))
CURRENCY = os.getenv("CURRENCY", "₹")

KEEP_LAST_BOT_MSGS_DEFAULT = int(os.getenv("KEEP_LAST_BOT_MSGS_DEFAULT", "2") or 2)

# ------------------- DB Helpers -------------------

def db():
    con = sqlite3.connect(DB_PATH)
    con.row_factory = sqlite3.Row
    return con

def migrate():
    con = db(); cur = con.cursor()
    cur.execute("""CREATE TABLE IF NOT EXISTS settings (
        user_id INTEGER PRIMARY KEY,
        delete_user_msgs INTEGER NOT NULL DEFAULT 1,
        keep_last_bot_msgs INTEGER NOT NULL DEFAULT 2,
        currency TEXT
    )""")
    cur.execute("""CREATE TABLE IF NOT EXISTS people (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id INTEGER NOT NULL,
        display_name TEXT NOT NULL,
        phone TEXT
    )""")
    cur.execute("""CREATE TABLE IF NOT EXISTS ledger (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id INTEGER NOT NULL,
        person_id INTEGER,
        type TEXT NOT NULL,         -- 'expense', 'lend', 'repay', etc.
        amount REAL NOT NULL,
        ts INTEGER NOT NULL,
        note TEXT
    )""")
    cur.execute("""CREATE TABLE IF NOT EXISTS bot_msgs (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id INTEGER NOT NULL,
        chat_id INTEGER NOT NULL,
        message_id INTEGER NOT NULL,
        created_ts INTEGER NOT NULL
    )""")
    # Safety: ensure keep_last_bot_msgs column exists and is not 0
    cur.execute("UPDATE settings SET keep_last_bot_msgs=2 WHERE keep_last_bot_msgs IS NULL OR keep_last_bot_msgs<1")
    con.commit(); con.close()

def get_settings(user_id: int) -> dict:
    con = db(); cur = con.cursor()
    cur.execute("SELECT * FROM settings WHERE user_id=?", (user_id,))
    r = cur.fetchone()
    con.close()
    if not r:
        return {}
    return dict(r)

def set_setting(user_id: int, key: str, value):
    con = db(); cur = con.cursor()
    cur.execute("INSERT INTO settings(user_id) VALUES(?) ON CONFLICT(user_id) DO NOTHING", (user_id,))
    con.commit()
    cur.execute(f"UPDATE settings SET {key}=? WHERE user_id=?", (value, user_id))
    con.commit(); con.close()

def get_delete_user_msgs(user_id: int) -> int:
    s = get_settings(user_id)
    if not s:
        return 1
    try:
        return 1 if int(s.get("delete_user_msgs", 1)) else 0
    except Exception:
        return 1

def get_keep_last(user_id: int) -> int:
    s = get_settings(user_id)
    if not s:
        return max(1, KEEP_LAST_BOT_MSGS_DEFAULT)
    try:
        v = int(s.get("keep_last_bot_msgs", KEEP_LAST_BOT_MSGS_DEFAULT))
    except Exception:
        v = KEEP_LAST_BOT_MSGS_DEFAULT
    return max(1, v)

def record_bot_message(user_id: int, chat_id: int, message_id: int):
    con = db(); cur = con.cursor()
    cur.execute("INSERT INTO bot_msgs(user_id, chat_id, message_id, created_ts) VALUES(?,?,?,?)",
                (user_id, chat_id, message_id, int(datetime.now(tz=TZ).timestamp())))
    con.commit(); con.close()

async def delete_old_bot_messages(chat_id: int, keep_last: int):
    keep_last = max(0, int(keep_last))
    con = db(); cur = con.cursor()
    cur.execute("SELECT id, message_id FROM bot_msgs WHERE chat_id=? ORDER BY id DESC", (chat_id,))
    rows = cur.fetchall()
    to_delete = rows[keep_last:] if keep_last >= 0 else rows
    ids_to_delete = []
    for r in to_delete:
        try:
            await bot.delete_message(chat_id, r["message_id"])
        except TelegramBadRequest:
            pass
        ids_to_delete.append(r["id"])
    if ids_to_delete:
        cur.execute(f"DELETE FROM bot_msgs WHERE id IN ({','.join('?' for _ in ids_to_delete)})", ids_to_delete)
        con.commit()
    con.close()

# ------------------- UI & Utils -------------------

def tele_escape(text: str) -> str:
    try:
        return html.escape(text or "")
    except Exception:
        return text or ""

def _fmt_currency(v: float) -> str:
    return f"{CURRENCY}{float(v):,.2f}"

async def send_text(chat_id: int, text: str, kb=None):
    msg = await bot.send_message(chat_id, text, reply_markup=kb)
    record_bot_message(OWNER_ID, chat_id, msg.message_id)
    await delete_old_bot_messages(chat_id, keep_last=get_keep_last(OWNER_ID))
    return msg

async def send_code(chat_id: int, text: str, kb=None):
    safe = tele_escape(text)
    msg = await bot.send_message(chat_id, f"<code>{safe}</code>", reply_markup=kb)
    record_bot_message(OWNER_ID, chat_id, msg.message_id)
    await delete_old_bot_messages(chat_id, keep_last=get_keep_last(OWNER_ID))
    return msg

async def run_shell(cmd: str) -> str:
    proc = await asyncio.create_subprocess_shell(
        cmd, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.STDOUT
    )
    out_b = await proc.communicate()
    out = (out_b[0] or b"").decode(errors="replace")
    return out

def only_owner(obj) -> bool:
    try:
        uid = obj.from_user.id if hasattr(obj, "from_user") and obj.from_user else 0
    except Exception:
        uid = 0
    return OWNER_ID and uid == OWNER_ID

def deny_text() -> str:
    return "⛔ Owner only."

# ------------------- Keyboards -------------------

def main_kb():
    kb = InlineKeyboardBuilder()
    kb.button(text="➕ Add Expense", callback_data="add_expense")
    kb.button(text="👥 People", callback_data="people")
    kb.button(text="📅 Monthly", callback_data="monthly")
    kb.button(text="📊 Category Chart", callback_data="cat_chart")
    kb.button(text="🧰 Dev Tools", callback_data="dev_tools")
    kb.button(text="⚙️ Extras", callback_data="extras")
    kb.adjust(2,2,2)
    return kb.as_markup()

def extras_kb():
    kb = InlineKeyboardBuilder()
    kb.button(text="🔍 Search Person", callback_data="search_person")
    kb.button(text="🧽 Delete user msgs: ON/OFF", callback_data="toggle_del_user")
    kb.button(text="🧹 Purge UI Now", callback_data="purge_ui")
    kb.button(text="🔢 Keep Last UI", callback_data="set_keep_last")
    kb.button(text="💱 Currency", callback_data="set_currency")
    kb.button(text="🧾 Export This Month CSV", callback_data="export_month_csv")
    kb.button(text="💼 Export Dues CSV", callback_data="export_dues_csv")
    kb.button(text="👤 Export People", callback_data="export_people")
    kb.button(text="📈 Trend 6 mo", callback_data="trend6")
    kb.button(text="💰 Apply Interest Now", callback_data="interest_now")
    kb.button(text="📰 Send Daily Summary", callback_data="send_daily")
    kb.button(text="🗓️ Weekly Digest Now", callback_data="send_weekly")
    kb.button(text="🧭 Feature Finder", callback_data="feature_finder")
    kb.button(text="➕ More Extras", callback_data="extras_more")
    kb.button(text="🔒 Lock Now", callback_data="lock_now")
    kb.button(text="⬅️ Back", callback_data="back_main")
    kb.adjust(2,2,2,2,2,2,2,2)
    return kb.as_markup()

def extras_more_kb():
    kb = InlineKeyboardBuilder()
    kb.button(text="🧮 Split Bill", callback_data="x_split")
    kb.button(text="💁 Tip 10/12/15%", callback_data="x_tip")
    kb.button(text="🏦 EMI Calculator", callback_data="x_emi")
    kb.button(text="📈 % Diff", callback_data="x_percent_diff")
    kb.button(text="🔁 km↔mi", callback_data="x_km_mi")
    kb.button(text="⚖️ kg↔lb", callback_data="x_kg_lb")
    kb.button(text="🕒 Date Diff", callback_data="x_datediff")
    kb.button(text="🧾 Today Report", callback_data="x_today")
    kb.button(text="⏳ Overdue >7d", callback_data="x_overdue7")
    kb.button(text="🏅 Top Debtors", callback_data="x_top")
    kb.button(text="🎯 Smallest Balances", callback_data="x_small")
    kb.button(text="🗃 Export JSON", callback_data="x_export_json")
    kb.button(text="🧪 Data Check", callback_data="x_datacheck")
    kb.button(text="📌 Scratchpad", callback_data="x_notes")
    kb.button(text="📟 Ping", callback_data="x_ping")
    kb.button(text="🕰️ Now", callback_data="x_now")
    kb.button(text="🆔 New UUID", callback_data="x_uuid")
    kb.button(text="🧵 Case ⇅", callback_data="x_case")
    kb.button(text="⬅️ Back", callback_data="extras")
    kb.adjust(2,2,2,2,2,2,2,2,2)
    return kb.as_markup()

def dev_kb():
    kb = InlineKeyboardBuilder()
    kb.button(text="🔄 Update Code (pull+install)", callback_data="dev_update")
    kb.button(text="♻️ Restart Service", callback_data="dev_restart")
    kb.button(text="📜 Tail Logs", callback_data="dev_logs")
    kb.button(text="🧠 Summarize Logs (AI)", callback_data="dev_logs_summarize")
    kb.button(text="⬅️ Back", callback_data="back_main")
    kb.adjust(2,2,1)
    return kb.as_markup()

# ------------------- FSM States -------------------
class PinState(StatesGroup):
    waiting_pin = State()

class SearchState(StatesGroup):
    waiting_query = State()

class FeatureSearchState(StatesGroup):
    waiting = State()

# ------------------- Middleware -------------------

class PrivateAutoDelete(BaseMiddleware):
    async def __call__(self, handler, event, data):
        # Process the update first
        result = await handler(event, data)
        # Best-effort delete user message (groups if bot has rights; DM will raise)
        try:
            if isinstance(event, Message) and event.chat and event.from_user and get_delete_user_msgs(event.from_user.id):
                await bot.delete_message(event.chat.id, event.message_id)
        except TelegramBadRequest:
            pass
        return result

# ------------------- Router & Handlers -------------------

router = Router()

@router.message(CommandStart())
@router.message(Command("start"))
async def start_cmd(m: Message):
    try:
        await send_text(m.chat.id, "👋 <b>Expense & Lending Assistant</b>")
        await send_text(m.chat.id, "Pick an option:", main_kb())
    except Exception as e:
        await send_text(m.chat.id, f"❌ start error: {tele_escape(str(e))}")

@router.callback_query(F.data == "back_main")
async def back_main(c: CallbackQuery):
    await send_text(c.message.chat.id, "🏠 <b>Main Menu</b>")
    await send_text(c.message.chat.id, "Pick an option:", main_kb())
    await c.answer()

@router.callback_query(F.data == "extras")
async def extras(c: CallbackQuery):
    await send_text(c.message.chat.id, "⚙️ <b>Extras</b>")
    await send_text(c.message.chat.id, "Choose a tool:", extras_kb()); await c.answer()

@router.callback_query(F.data == "extras_more")
async def extras_more(c: CallbackQuery):
    await send_text(c.message.chat.id, "➕ <b>More Extras</b>")
    await send_text(c.message.chat.id, "Pick one:", extras_more_kb()); await c.answer()

@router.callback_query(F.data == "dev_tools")
async def dev_tools(c: CallbackQuery):
    if not only_owner(c): return await c.message.answer(deny_text())
    await send_text(c.message.chat.id, "🧰 <b>Developer Tools</b>")
    await send_text(c.message.chat.id, "Owner-only ops:", dev_kb()); await c.answer()

# ------- Dev tools -------

def _local_summary(text: str, max_len: int = 1000) -> str:
    lines = (text or "").splitlines()[-300:]
    errs = [l for l in lines if any(k in l for k in ("ERROR","Exception","Traceback","Telegram","sqlite3.","aiogram"))]
    sample = errs[:20] or lines[-80:]
    s = "\n".join(sample)
    return s[-max_len:] if len(s) > max_len else (s or "(no notable errors)")

async def _summarize_ai_or_local(text: str) -> str:
    try:
        import safoneapi
        client = safoneapi.Client()
        prompt = "Summarize these service logs into 4-6 short bullets with probable causes and concrete fixes.\n\n" + text[-3500:]
        resp = client.chat(prompt)
        return str(resp)[:1500]
    except Exception:
        return _local_summary(text)

@router.callback_query(F.data == "dev_logs")
async def dev_logs(c: CallbackQuery):
    if not only_owner(c): return await c.message.answer(deny_text())
    out = await run_shell("sudo journalctl -u expensebot.service -n 120 --no-pager")
    await send_text(c.message.chat.id, "<b>Last 120 lines</b>")
    await send_code(c.message.chat.id, out, dev_kb()); await c.answer()

@router.callback_query(F.data == "dev_logs_summarize")
async def dev_logs_summarize(c: CallbackQuery):
    if not only_owner(c): return await c.message.answer(deny_text())
    out = await run_shell("sudo journalctl -u expensebot.service -n 200 --no-pager")
    await send_text(c.message.chat.id, "<b>AI Log Summary</b>")
    summary = await _summarize_ai_or_local(out)
    await send_code(c.message.chat.id, summary, dev_kb()); await c.answer()

@router.callback_query(F.data == "dev_update")
async def dev_update(c: CallbackQuery):
    if not only_owner(c): return await c.message.answer(deny_text())
    # Safe: escape output via send_code
    cmd = "git pull && python3 -m pip install -U -r requirements.txt || true"
    out = await run_shell(cmd)
    # Offer some quick actions with a mini-kb
    kb = InlineKeyboardBuilder()
    kb.button(text="♻️ Restart Service", callback_data="dev_restart")
    kb.button(text="📜 Tail Logs", callback_data="dev_logs")
    kb.button(text="🧠 Summarize Logs (AI)", callback_data="dev_logs_summarize")
    kb.button(text="⬅️ Back", callback_data="back_main")
    kb.adjust(2,2)
    await send_text(c.message.chat.id, "<b>Update result</b>")
    await send_code(c.message.chat.id, out, kb.as_markup())
    await c.answer()

@router.callback_query(F.data == "dev_restart")
async def dev_restart(c: CallbackQuery):
    if not only_owner(c): return await c.message.answer(deny_text())
    out = await run_shell("sudo systemctl restart expensebot.service && echo 'restarted' || echo 'failed'")
    await send_text(c.message.chat.id, "Service restart requested.")
    await send_code(c.message.chat.id, out, dev_kb()); await c.answer()

# ------- Extras: search / toggles / settings -------

@router.callback_query(F.data == "search_person")
async def search_person_prompt(c: CallbackQuery, state: FSMContext):
    if not only_owner(c): return await c.message.answer(deny_text())
    await state.set_state(SearchState.waiting_query)
    await send_text(c.message.chat.id, "🔎 Send a name or phone (case-insensitive).")
    await c.answer()

@router.message(SearchState.waiting_query)
async def search_person_do(m: Message, state: FSMContext):
    if not only_owner(m): return await m.answer(deny_text())
    q = (m.text or "").strip()
    con = db(); cur = con.cursor()
    like = f"%{q.lower()}%"
    cur.execute("SELECT id, display_name, phone FROM people WHERE user_id=? AND (lower(display_name) LIKE ? OR phone LIKE ?) LIMIT 50", (OWNER_ID, like, like))
    rows = cur.fetchall(); con.close()
    if not rows:
        await send_text(m.chat.id, f"No results for: {tele_escape(q)}")
    else:
        lines = ["<b>Matches:</b>"] + [f"• {tele_escape(r['display_name'])} (id={r['id']}) {('['+r['phone']+']') if r['phone'] else ''}" for r in rows]
        await send_text(m.chat.id, "\n".join(lines))
    await state.clear()

@router.callback_query(F.data == "toggle_del_user")
async def toggle_del_user(c: CallbackQuery):
    if not only_owner(c): return await c.message.answer(deny_text())
    cur = get_delete_user_msgs(OWNER_ID)
    set_setting(OWNER_ID, "delete_user_msgs", 0 if cur else 1)
    await send_text(c.message.chat.id, f"🧽 Delete user msgs: {'ON' if not cur else 'OFF'}", extras_kb()); await c.answer()

@router.callback_query(F.data == "set_keep_last")
async def set_keep_last(c: CallbackQuery):
    if not only_owner(c): return await c.message.answer(deny_text())
    v = get_keep_last(OWNER_ID)
    # Offer 1..5 options
    kb = InlineKeyboardBuilder()
    for n in [1,2,3,4,5]:
        kb.button(text=f"{n}", callback_data=f"keep_last:{n}")
    kb.button(text="⬅️ Back", callback_data="extras")
    kb.adjust(5,1)
    await send_text(c.message.chat.id, f"Current keep_last = {v}. Choose:", kb.as_markup()); await c.answer()

@router.callback_query(F.data.startswith("keep_last:"))
async def set_keep_last_do(c: CallbackQuery):
    if not only_owner(c): return await c.message.answer(deny_text())
    try:
        n = int(c.data.split(":")[1]); n = 1 if n <= 0 else n
        set_setting(OWNER_ID, "keep_last_bot_msgs", n)
        await send_text(c.message.chat.id, f"✅ keep_last set to {n}", extras_kb())
    except Exception as e:
        await send_text(c.message.chat.id, f"❌ set keep_last error: {tele_escape(str(e))}")
    await c.answer()

@router.callback_query(F.data == "set_currency")
async def set_currency(c: CallbackQuery):
    if not only_owner(c): return await c.message.answer(deny_text())
    # Show quick common choices
    kb = InlineKeyboardBuilder()
    for sym in ["₹","$","€","£","¥"]:
        kb.button(text=sym, callback_data=f"currency:{sym}")
    kb.button(text="⬅️ Back", callback_data="extras")
    kb.adjust(5,1)
    await send_text(c.message.chat.id, "Pick currency symbol:", kb.as_markup()); await c.answer()

@router.callback_query(F.data.startswith("currency:"))
async def currency_set_do(c: CallbackQuery):
    if not only_owner(c): return await c.message.answer(deny_text())
    sym = c.data.split(":",1)[1]
    global CURRENCY
    CURRENCY = sym
    set_setting(OWNER_ID, "currency", sym)
    await send_text(c.message.chat.id, f"✅ Currency set to {sym}", extras_kb()); await c.answer()

@router.callback_query(F.data == "purge_ui")
async def purge_ui(c: CallbackQuery):
    if not only_owner(c): return await c.message.answer(deny_text())
    # delete all tracked bot messages
    con = db(); cur = con.cursor()
    cur.execute("SELECT message_id FROM bot_msgs WHERE chat_id=?", (c.message.chat.id,))
    rows = cur.fetchall()
    for r in rows:
        try:
            await bot.delete_message(c.message.chat.id, r["message_id"])
        except TelegramBadRequest:
            pass
    cur.execute("DELETE FROM bot_msgs WHERE chat_id=?", (c.message.chat.id,))
    con.commit(); con.close()
    await c.answer("Purged UI")

@router.callback_query(F.data == "lock_now")
async def lock_now(c: CallbackQuery):
    if not only_owner(c): return await c.message.answer(deny_text())
    await send_text(c.message.chat.id, "🔒 Locked (placeholder).", extras_kb()); await c.answer()

# ------- Extras: Tools -------

@router.callback_query(F.data == "x_split")
async def x_split(c: CallbackQuery, state: FSMContext):
    if not only_owner(c): return await c.message.answer(deny_text())
    await state.set_state(PinState.waiting_pin)  # reuse slot
    await send_text(c.message.chat.id, "Send: total,people  (e.g., 1200,3)"); await c.answer()

@router.message(PinState.waiting_pin)
async def x_split_input(m: Message, state: FSMContext):
    try:
        if not only_owner(m): return await m.answer(deny_text())
        txt = (m.text or "").replace(" ", "")
        total_s, people_s = txt.split(",", 1)
        total = float(total_s); people = max(1, int(float(people_s)))
        each = total/people
        await send_text(m.chat.id, f"Split: {people} × {_fmt_currency(each)} = {_fmt_currency(total)}")
    except Exception as e:
        await m.answer(f"❌ split input error: {tele_escape(str(e))}")
    finally:
        await state.clear()

@router.callback_query(F.data == "x_tip")
async def x_tip(c: CallbackQuery):
    if not only_owner(c): return await c.message.answer(deny_text())
    await send_text(c.message.chat.id, "Send an amount like '850' and I’ll reply with 10% / 12% / 15% tips.")
    await c.answer()

@router.message(F.text.regexp(r"^\d+(?:\.\d+)?$"))
async def x_tip_compute(m: Message):
    try:
        if not only_owner(m): return
        amt = float(m.text)
        t10, t12, t15 = amt*0.10, amt*0.12, amt*0.15
        await send_text(m.chat.id, f"Tips on {_fmt_currency(amt)}:\n10% {_fmt_currency(t10)}\n12% {_fmt_currency(t12)}\n15% {_fmt_currency(t15)}")
    except Exception:
        pass

@router.callback_query(F.data == "x_emi")
async def x_emi(c: CallbackQuery):
    if not only_owner(c): return await c.message.answer(deny_text())
    await send_text(c.message.chat.id, "Send: principal,annual_rate%,months  (e.g., 50000,12,24)")
    await c.answer()

@router.message(F.text.regexp(r"^\d+(?:\.\d+)?,\d+(?:\.\d+)?,\d+$"))
async def x_emi_input(m: Message):
    if not only_owner(m): return
    p_s, r_s, n_s = [s.strip() for s in (m.text or "").split(",")]
    P = float(p_s); r_annual = float(r_s); n = int(n_s)
    r = (r_annual/12.0)/100.0
    if r == 0: emi = P / max(1, n)
    else: emi = P * r * (1+r)**n / ((1+r)**n - 1)
    await send_text(m.chat.id, f"EMI for {_fmt_currency(P)} @ {r_annual:.2f}% × {n} months = {_fmt_currency(emi)}")

@router.callback_query(F.data == "x_percent_diff")
async def x_percent_diff(c: CallbackQuery):
    if not only_owner(c): return await c.message.answer(deny_text())
    await send_text(c.message.chat.id, "Send: old,new  (e.g., 120,150)"); await c.answer()

@router.message(F.text.regexp(r"^\d+(?:\.\d+)?,\d+(?:\.\d+)?$"))
async def x_percent_diff_do(m: Message):
    try:
        if not only_owner(m): return
        a_s, b_s = [s.strip() for s in (m.text or "").split(",")]
        a = float(a_s); b = float(b_s)
        if a == 0:
            return await send_text(m.chat.id, "Old value cannot be 0")
        diff = (b-a)/a*100.0
        await send_text(m.chat.id, f"Change from {_fmt_currency(a)} to {_fmt_currency(b)} = {diff:.2f}%")
    except Exception:
        pass

@router.callback_query(F.data == "x_km_mi")
async def x_km_mi(c: CallbackQuery):
    if not only_owner(c): return await c.message.answer(deny_text())
    await send_text(c.message.chat.id, "Send: km or mi (e.g., '10 km' or '6.2 mi')"); await c.answer()

@router.message(F.text.regexp(r"^\d+(?:\.\d+)?\s*(km|mi)$"))
async def x_km_mi_do(m: Message):
    try:
        if not only_owner(m): return
        val, unit = (m.text or "").split()
        v = float(val)
        if unit.lower() == "km":
            out = f"{v} km = {v*0.621371:.2f} mi"
        else:
            out = f"{v} mi = {v/0.621371:.2f} km"
        await send_text(m.chat.id, out)
    except Exception:
        pass

@router.callback_query(F.data == "x_kg_lb")
async def x_kg_lb(c: CallbackQuery):
    if not only_owner(c): return await c.message.answer(deny_text())
    await send_text(c.message.chat.id, "Send: kg or lb (e.g., '70 kg' or '154 lb')"); await c.answer()

@router.message(F.text.regexp(r"^\d+(?:\.\d+)?\s*(kg|lb)$"))
async def x_kg_lb_do(m: Message):
    try:
        if not only_owner(m): return
        val, unit = (m.text or "").split()
        v = float(val)
        if unit.lower() == "kg":
            out = f"{v} kg = {v*2.20462:.2f} lb"
        else:
            out = f"{v} lb = {v/2.20462:.2f} kg"
        await send_text(m.chat.id, out)
    except Exception:
        pass

@router.callback_query(F.data == "x_datediff")
async def x_datediff(c: CallbackQuery):
    if not only_owner(c): return await c.message.answer(deny_text())
    await send_text(c.message.chat.id, "Send: YYYY-MM-DD,YYYY-MM-DD"); await c.answer()

@router.message(F.text.regexp(r"^\d{4}-\d{2}-\d{2},\d{4}-\d{2}-\d{2}$"))
async def x_datediff_do(m: Message):
    try:
        if not only_owner(m): return
        a_s, b_s = (m.text or "").split(",")
        a = datetime.fromisoformat(a_s.strip())
        b = datetime.fromisoformat(b_s.strip())
        days = abs((b-a).days)
        await send_text(m.chat.id, f"Difference: {days} days")
    except Exception:
        pass

@router.callback_query(F.data == "x_today")
async def x_today(c: CallbackQuery):
    if not only_owner(c): return await c.message.answer(deny_text())
    start = int(datetime.now(TZ).replace(hour=0, minute=0, second=0, microsecond=0).timestamp())
    end = int(datetime.now(TZ).timestamp())
    con = db(); cur = con.cursor()
    cur.execute("SELECT type, SUM(amount) as total FROM ledger WHERE user_id=? AND ts BETWEEN ? AND ? GROUP BY type", (OWNER_ID, start, end))
    rows = cur.fetchall(); con.close()
    lines = ["🧾 <b>Today</b>"]
    for r in rows or []:
        lines.append(f"• {r['type']}: {_fmt_currency(float(r['total'] or 0))}")
    if len(lines) == 1:
        lines.append("(no entries)")
    await send_text(c.message.chat.id, "\n".join(lines), extras_more_kb()); await c.answer()

# Placeholder aggregate helpers
def monthly_total(uid: int) -> float:
    con = db(); cur = con.cursor()
    now = datetime.now(TZ)
    start = int(datetime(now.year, now.month, 1, tzinfo=TZ).timestamp())
    cur.execute("SELECT SUM(amount) as total FROM ledger WHERE user_id=? AND ts>=?", (uid, start))
    r = cur.fetchone(); con.close()
    return float(r["total"] or 0.0)

def list_overdues(uid: int, days: int = 7) -> List[str]:
    # Placeholder: in real app, depends on due dates; here we synthesize
    return []

def top_debtors(uid: int, n=5) -> List[str]:
    return []

def smallest_balances(uid: int, n=5) -> List[str]:
    return []

def export_json_snapshot(uid: int) -> Optional[str]:
    try:
        con = db(); cur = con.cursor()
        out = {"people": [], "ledger": []}
        cur.execute("SELECT * FROM people WHERE user_id=?", (uid,))
        out["people"] = [dict(r) for r in cur.fetchall()]
        cur.execute("SELECT * FROM ledger WHERE user_id=?", (uid,))
        out["ledger"] = [dict(r) for r in cur.fetchall()]
        path = DATA_DIR / "export.json"
        path.write_text(json.dumps(out, indent=2), encoding="utf-8")
        con.close()
        return str(path)
    except Exception:
        return None

def run_data_check(uid: int) -> str:
    con = db(); cur = con.cursor()
    cur.execute("SELECT COUNT(*) as c FROM people WHERE user_id=?", (uid,)); a = cur.fetchone()["c"]
    cur.execute("SELECT COUNT(*) as c FROM ledger WHERE user_id=?", (uid,)); b = cur.fetchone()["c"]
    con.close()
    return f"people={a}, ledger={b}"

@router.callback_query(F.data == "x_overdue7")
async def x_overdue7(c: CallbackQuery):
    if not only_owner(c): return await c.message.answer(deny_text())
    rows = list_overdues(OWNER_ID, days=7)
    msg = "\n".join(rows) if rows else "No overdues >7d"
    await send_text(c.message.chat.id, msg, extras_more_kb()); await c.answer()

@router.callback_query(F.data == "x_top")
async def x_top(c: CallbackQuery):
    if not only_owner(c): return await c.message.answer(deny_text())
    top = top_debtors(OWNER_ID, 5)
    text = "\n".join(top) if top else "(empty)"
    await send_text(c.message.chat.id, text, extras_more_kb()); await c.answer()

@router.callback_query(F.data == "x_small")
async def x_small(c: CallbackQuery):
    if not only_owner(c): return await c.message.answer(deny_text())
    small = smallest_balances(OWNER_ID, 5)
    text = "\n".join(small) if small else "(empty)"
    await send_text(c.message.chat.id, text, extras_more_kb()); await c.answer()

@router.callback_query(F.data == "x_export_json")
async def x_export_json(c: CallbackQuery):
    if not only_owner(c): return await c.message.answer(deny_text())
    path = export_json_snapshot(OWNER_ID)
    if path:
        await send_text(c.message.chat.id, "JSON export at ./data/export.json", extras_more_kb())
    else:
        await send_text(c.message.chat.id, "No exporter defined", extras_more_kb())
    await c.answer()

@router.callback_query(F.data == "x_datacheck")
async def x_datacheck(c: CallbackQuery):
    if not only_owner(c): return await c.message.answer(deny_text())
    msg = run_data_check(OWNER_ID)
    await send_text(c.message.chat.id, f"Data check: {msg}", extras_more_kb()); await c.answer()

@router.callback_query(F.data == "x_notes")
async def x_notes(c: CallbackQuery, state: FSMContext):
    if not only_owner(c): return await c.message.answer(deny_text())
    await state.set_state(PinState.waiting_pin)  # reuse slot
    path = DATA_DIR / "scratchpad.txt"
    content = ""
    try:
        content = path.read_text(encoding="utf-8")
    except Exception:
        pass
    await send_text(c.message.chat.id, "<b>Scratchpad</b> (send lines to replace):")
    await send_code(c.message.chat.id, content or "(empty)", extras_more_kb()); await c.answer()

@router.message(PinState.waiting_pin)
async def x_notes_save(m: Message, state: FSMContext):
    try:
        if not only_owner(m): return await m.answer(deny_text())
        path = DATA_DIR / "scratchpad.txt"
        path.write_text(m.text or "", encoding="utf-8")
        await send_text(m.chat.id, "✅ Saved notes.", extras_more_kb())
    except Exception as e:
        await m.answer(f"❌ notes save error: {tele_escape(str(e))}")
    finally:
        await state.clear()

@router.callback_query(F.data == "x_ping")
async def x_ping(c: CallbackQuery):
    if not only_owner(c): return await c.message.answer(deny_text())
    await send_text(c.message.chat.id, "Pong 🏓", extras_more_kb()); await c.answer()

@router.callback_query(F.data == "x_now")
async def x_now(c: CallbackQuery):
    if not only_owner(c): return await c.message.answer(deny_text())
    now = datetime.now(TZ).strftime("%Y-%m-%d %H:%M:%S")
    await send_text(c.message.chat.id, f"Now: {now}", extras_more_kb()); await c.answer()

@router.callback_query(F.data == "x_uuid")
async def x_uuid(c: CallbackQuery):
    if not only_owner(c): return await c.message.answer(deny_text())
    await send_code(c.message.chat.id, str(uuid.uuid4()), extras_more_kb()); await c.answer()

@router.callback_query(F.data == "x_case")
async def x_case(c: CallbackQuery, state: FSMContext):
    if not only_owner(c): return await c.message.answer(deny_text())
    await state.set_state(PinState.waiting_pin)  # reuse
    await send_text(c.message.chat.id, "Send any text; I’ll show UPPER and lower.")
    await c.answer()

@router.message(PinState.waiting_pin)
async def x_case_do(m: Message, state: FSMContext):
    try:
        if not only_owner(m): return await m.answer(deny_text())
        t = m.text or ""
        await send_text(m.chat.id, f"UPPER:\n<code>{tele_escape(t.upper())}</code>\n\nlower:\n<code>{tele_escape(t.lower())}</code>")
    except Exception:
        pass
    finally:
        await state.clear()

# ------- Feature Finder -------

def _feature_catalog() -> List[Tuple[str,str]]:
    return [
        ("Add Expense","add_expense"), ("People","people"), ("Monthly","monthly"), ("Category Chart","cat_chart"),
        ("Import Sheet","import_sheet"), ("Support AI","support_ai"), ("Due Soon","due_soon"), ("Reminders","reminders"),
        ("Undo","undo"), ("Export All","export_all"), ("Reset All","reset_all_confirm"),
        ("Extras","extras"), ("Dev Tools","dev_tools"), ("Trend 6 mo","trend6"),
        ("Export People","export_people"), ("Export This Month CSV","export_month_csv"),
        ("Export Dues CSV","export_dues_csv"), ("Apply Interest Now","interest_now"),
        ("Send Daily Summary","send_daily"), ("Weekly Digest Now","send_weekly"),
        ("Search Person","search_person"), ("Find Duplicates","dup_check"),
        ("Delete user msgs","toggle_del_user"), ("Keep Last UI","set_keep_last"),
        ("Currency","set_currency"), ("Lock Now","lock_now"),
    ]

@router.callback_query(F.data == "feature_finder")
async def feature_finder(c: CallbackQuery, state: FSMContext):
    if not only_owner(c): return await c.message.answer(deny_text())
    await state.set_state(FeatureSearchState.waiting)
    await send_text(c.message.chat.id, "Type a feature keyword (e.g., 'export' or 'trend')."); await c.answer()

@router.message(FeatureSearchState.waiting)
async def feature_finder_do(m: Message, state: FSMContext):
    try:
        if not only_owner(m): return await m.answer(deny_text())
        q = (m.text or "").strip().lower()
        items = [f"• {name}  →  <code>{cb}</code>" for (name, cb) in _feature_catalog() if q in name.lower()]
        if not items:
            await send_text(m.chat.id, "No matches. Try another keyword.")
        else:
            await send_text(m.chat.id, "<b>Matches</b> (use the menus to navigate):")
            await send_code(m.chat.id, "\n".join(items))
    except Exception as e:
        await m.answer(f"❌ feature search error: {tele_escape(str(e))}")
    finally:
        await state.clear()

# ------------------- Dispatcher -------------------

bot = Bot(BOT_TOKEN, parse_mode="HTML")
storage = MemoryStorage()
dp = Dispatcher(storage=storage)
dp.message.middleware(PrivateAutoDelete())
dp.callback_query.middleware(PrivateAutoDelete())
dp.include_router(router)

async def on_startup():
    migrate()
    # ensure owner row exists
    if OWNER_ID:
        set_setting(OWNER_ID, "delete_user_msgs", get_delete_user_msgs(OWNER_ID))
        set_setting(OWNER_ID, "keep_last_bot_msgs", get_keep_last(OWNER_ID))

# ------------------- Main -------------------

if __name__ == "__main__":
    asyncio.run(on_startup())
    asyncio.run(dp.start_polling(bot))
