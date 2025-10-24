import os
import asyncio
import logging
from fastapi import FastAPI, Request
from telegram import Update
from telegram.ext import Application

import bot_core  # deine große Datei

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger("webhook")

WEBHOOK_SECRET = os.getenv("WEBHOOK_SECRET", "changeme")
TELEGRAM_BOT_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN")
if not TELEGRAM_BOT_TOKEN:
    raise ValueError("TELEGRAM_BOT_TOKEN fehlt – bitte in Render → Environment setzen.")

app = FastAPI()
tg_app: Application | None = None
_auto_task: asyncio.Task | None = None

@app.on_event("startup")
async def on_startup():
    global tg_app, _auto_task
    # 1) PTB Application bauen
    tg_app = await bot_core.build_app()
    bot_core.APP = tg_app  # Referenz für tg_post etc.

    # 2) Initialisieren & internen Worker starten
    await tg_app.initialize()
    try:
        # alten Webhook löschen (wir nutzen FastAPI + eigenes Secret)
        await tg_app.bot.delete_webhook(drop_pending_updates=True)
    except Exception:
        pass
    await tg_app.start()  # wichtig: verarbeitet Updates aus update_queue

    # 3) Optional: Strategieloop automatisch starten
    if os.getenv("AUTOLOOP", "0").lower() in ("1", "true", "yes", "on"):
        _auto_task = asyncio.create_task(bot_core.auto_loop(tg_app))
        logger.info("AUTOLOOP gestartet.")

@app.on_event("shutdown")
async def on_shutdown():
    global _auto_task
    try:
        if _auto_task and not _auto_task.done():
            _auto_task.cancel()
            try:
                await _auto_task
            except asyncio.CancelledError:
                pass
    finally:
        if tg_app:
            await tg_app.stop()
            await tg_app.shutdown()

@app.get("/health")
async def health():
    return {"ok": True}

@app.post("/webhook/{secret}")
async def webhook(request: Request, secret: str):
    if secret != WEBHOOK_SECRET:
        logger.warning("Webhook mit falschem Secret.")
        return {"ok": False}
    data = await request.json()
    update = Update.de_json(data, tg_app.bot)
    await tg_app.update_queue.put(update)
    return {"ok": True}
