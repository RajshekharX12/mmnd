# Telegram Expense & Lending Bot (IST)

Owner-only inline bot that tracks expenses, lending, due dates, interest, reminders, imports CSV/XLSX (Google Sheets export), and exports CSV/ZIP. Category charts included.

## Setup
```bash
sudo apt update && sudo apt install -y python3-pip python3-venv
git clone <your-repo-url> /opt/tg-expense-bot
cd /opt/tg-expense-bot
python3 -m venv .venv && . .venv/bin/activate
pip install -r requirements.txt
cp .env.example .env   # edit with BOT_TOKEN, OWNER_ID
python3 expense_bot.py
