import os
import asyncio
import logging
from fastapi import FastAPI, Request
from telegram import Update
from telegram.ext import Application

import bot_core  # deine Bot-Logik (build_app, auto_loop, aw_loop, auto_liq_loop, AW_CFG, LIQ_CFG)

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger("webhook")

WEBHOOK_SECRET = os.getenv("WEBHOOK_SECRET", "changeme")
TELEGRAM_BOT_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN")
PUBLIC_URL = os.getenv("PUBLIC_URL")  # z.B. https://dein-service.onrender.com
DROP_PENDING = os.getenv("WEBHOOK_DROP_PENDING", "1").lower() in ("1", "true", "yes", "on")

# Autostarts (optional): 1 = beim Start automatisch loslaufen lassen
AUTOLOOP   = os.getenv("AUTOLOOP", "0").lower()   in ("1", "true", "yes", "on")
AUTOWATCH  = os.getenv("AUTOWATCH", "0").lower()  in ("1", "true", "yes", "on")
AUTOLIQ    = os.getenv("AUTOLIQ", "0").lower()    in ("1", "true", "yes", "on")

if not TELEGRAM_BOT_TOKEN:
    raise ValueError("TELEGRAM_BOT_TOKEN fehlt – bitte in Render → Environment setzen.")

app = FastAPI()
tg_app: Application | None = None
_auto_task: asyncio.Task | None = None
_aw_task: asyncio.Task | None = None
_liq_task: asyncio.Task | None = None


@app.on_event("startup")
async def on_startup():
    """
    Baut die PTB-Application, setzt (robust) den Webhook und startet optional
    die Background-Loops für Trading (AUTOLOOP), Auto-Watch (AUTOWATCH) und
    Auto-Liquidity (AUTOLIQ).
    """
    global tg_app, _auto_task, _aw_task, _liq_task

    # 1) PTB Application bauen
    tg_app = await bot_core.build_app()
    bot_core.APP = tg_app  # Referenz für tg_post etc.

    # 2) Initialisieren
    await tg_app.initialize()

    # 3) Webhook setzen (robust zusammenbauen, egal wie PUBLIC_URL konfiguriert ist)
    if PUBLIC_URL:
        base = PUBLIC_URL.rstrip("/")
        want = f"/webhook/{WEBHOOK_SECRET}"
        webhook_url = base if base.endswith(want) or "/webhook/" in base else base + want
        try:
            await tg_app.bot.set_webhook(url=webhook_url, drop_pending_updates=DROP_PENDING)
            logger.info("Webhook gesetzt: %s (drop_pending=%s)", webhook_url, DROP_PENDING)
        except Exception as exc:
            logger.exception("Webhook-Setzen fehlgeschlagen: %s", exc)
    else:
        logger.warning("PUBLIC_URL nicht gesetzt – Webhook wird NICHT automatisch gesetzt.")

    # 4) PTB-Worker starten (bearbeitet tg_app.update_queue)
    await tg_app.start()

    # 5) Optional: Background-Loops automatisch starten
    if AUTOLOOP:
        _auto_task = asyncio.create_task(bot_core.auto_loop(tg_app))
        logger.info("AUTOLOOP gestartet (Trading-Loop).")

    if AUTOWATCH:
        try:
            # Autowatch einschalten und Loop starten
            if hasattr(bot_core, "AW_CFG"):
                bot_core.AW_CFG["enabled"] = True
            _aw_task = asyncio.create_task(bot_core.aw_loop())
            logger.info("AUTOWATCH gestartet (Auto-Watchlist).")
        except Exception as exc:
            logger.exception("AUTOWATCH konnte nicht gestartet werden: %s", exc)

    if AUTOLIQ:
        try:
            if hasattr(bot_core, "LIQ_CFG"):
                bot_core.LIQ_CFG["enabled"] = True
            _liq_task = asyncio.create_task(bot_core.auto_liq_loop())
            logger.info("AUTOLIQ gestartet (Auto-Liquidity).")
        except Exception as exc:
            logger.exception("AUTOLIQ konnte nicht gestartet werden: %s", exc)


@app.on_event("shutdown")
async def on_shutdown():
    """Sauberes Beenden aller Background-Tasks und der PTB-Application."""
    global _auto_task, _aw_task, _liq_task
    for name, task in (("AUTOLOOP", _auto_task), ("AUTOWATCH", _aw_task), ("AUTOLIQ", _liq_task)):
        try:
            if task and not task.done():
                task.cancel()
                try:
                    await task
                except asyncio.CancelledError:
                    pass
                logger.info("%s gestoppt.", name)
        except Exception:
            pass

    if tg_app:
        await tg_app.stop()
        await tg_app.shutdown()
        logger.info("PTB Application gestoppt.")


@app.get("/")
async def index():
    return {
        "ok": True,
        "service": "telegram-bot",
        "health": "/health",
        "webhook": f"/webhook/{WEBHOOK_SECRET[:6]}…",
        "autostart": {"AUTOLOOP": AUTOLOOP, "AUTOWATCH": AUTOWATCH, "AUTOLIQ": AUTOLIQ},
    }


@app.get("/health")
async def health():
    return {"ok": True}


@app.post("/webhook/{secret}")
async def webhook(request: Request, secret: str):
    if secret != WEBHOOK_SECRET:
        logger.warning("Webhook mit falschem Secret: %s", secret)
        return {"ok": False}
    if tg_app is None:
        logger.warning("PTB Application noch nicht bereit.")
        return {"ok": False, "error": "app-not-ready"}

    data = await request.json()
    update = Update.de_json(data, tg_app.bot)
    await tg_app.update_queue.put(update)
    return {"ok": True}
