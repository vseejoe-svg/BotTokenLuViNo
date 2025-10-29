# bot_core.py
# -----------------------------------------------------------
# Telegram-Trading-Bot für Solana:
# - Integrierte Strategie SwingBot v1.6.3 (5s)
# - Birdeye-Preis + GMGN-Route-Preis-Fallback (robust)
# - Volumen (saubere Quelle): DexScreener (1h/24h -> 1m/5s approx)
# - Multi-Mint-Rolling + eigene 5s-Candles + Debug-Visualisierung
# - Integriertes Modul "INDICATORS & IO" (IndiState + Debug-Formatter)
# -----------------------------------------------------------
from __future__ import annotations
import os, json, time, base64, asyncio, logging, csv, random, io
from dataclasses import dataclass, field
from collections import deque
from typing import Dict, List, Tuple, Optional, Deque
import math
import datetime as dt
UTC = getattr(dt, "UTC", dt.timezone.utc)
import requests
from urllib.parse import urlparse, parse_qs
import re  # neu: für Solana-Adressprüfung
from telegram.ext import Application, CommandHandler, ContextTypes, CallbackQueryHandler

# Matplotlib (headless) für Debug-Charts
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

from telegram import Update
from telegram.request import HTTPXRequest
from telegram.error import TimedOut, NetworkError, Conflict

from solana.rpc.api import Client
from solders.keypair import Keypair
from solders.pubkey import Pubkey
from solders.signature import Signature as Sig

from telegram import InlineKeyboardMarkup, InlineKeyboardButton
from telegram.constants import ParseMode
# ===============================================================================
import asyncio, os  # <-- falls oben noch nicht vorhanden
import contextlib

# Minimaler HTTP-Server für Render-Healthcheck (hält die Instanz wach)
async def start_keepalive_server():
    port = int(os.environ.get("PORT", "10000"))
    async def _handle(reader, writer):
        try:
            await reader.readuntil(b"\r\n\r\n")
        except Exception:
            pass
        resp = (b"HTTP/1.1 200 OK\r\nContent-Type: text/plain; charset=utf-8\r\n"
                b"Content-Length: 2\r\nConnection: close\r\n\r\nOK")
        try:
            writer.write(resp); await writer.drain()
        finally:
            with contextlib.suppress(Exception):
                writer.close()

    try:
        server = await asyncio.start_server(_handle, host="0.0.0.0", port=port)
    except OSError as e:
        # Port bereits von uvicorn belegt? Leise aussteigen.
        if getattr(e, "errno", None) == 98:  # EADDRINUSE
            logger.info("KeepAlive nicht gestartet: Port %s bereits belegt (uvicorn).", port)
            return
        raise
    addrs = ", ".join(str(s.getsockname()) for s in (server.sockets or []))
    logger.info("KeepAlive listening on %s (GET /healthz → 200)", addrs)
    async with server:
        await server.serve_forever()

# ===============================================================================
# ENV / Konfiguration
# =========================
def _need(name: str) -> str:
    v = os.getenv(name, "").strip()
    if not v:
        raise RuntimeError(f"ENV {name} fehlt – bitte setzen (Deployment/Container).")
    return v

TELEGRAM_BOT_TOKEN = _need("TELEGRAM_BOT_TOKEN")
# Chat-ID robust (0 => blockiert alles):
ALLOWED_CHAT_ID    = int((os.getenv("TELEGRAM_ALLOWED_CHAT_ID") or "0").strip() or "0")
RPC_URL            = _need("RPC_URL")
BIRDEYE_API_KEY    = os.getenv("BIRDEYE_API_KEY", "").strip()  # darf leer sein (funktioniert mit Fallbacks)

# Optionaler Helius API-Key für TX-Fallback (aus RPC_URL extrahierbar)
HELIUS_API_KEY = os.environ.get("HELIUS_API_KEY", "")
if not HELIUS_API_KEY:
    try:
        q = parse_qs(urlparse(RPC_URL).query)
        if "api-key" in q and q["api-key"]:
            HELIUS_API_KEY = q["api-key"][0]
    except Exception:
        pass
# ===============================================================================
# Globale Task-Handles (nur Background-Loops; KEIN Polling!)
APP = None
AUTO_TASK: asyncio.Task | None = None          # z.B. dein auto_loop
AUTOWATCH_TASK: asyncio.Task | None = None     # z.B. dein autowatch_loop
AUTO_LIQ_TASK: asyncio.Task | None = None      # z.B. dein auto_liquidity_loop
# ===============================================================================
# ===== PAPER MODE (aus ENV, mit Defaults) =====
PAPER_MODE    = os.environ.get("PAPER_MODE", "0").strip().lower() in ("1", "true", "yes", "on")
PAPER_FEE_BPS = float(os.environ.get("PAPER_FEE_BPS", "10"))  # 20 bps = 0.20 %
#--------------------------------------------------
# Bot App-Pointer (wird via /boot gebaut)
APP: Application | None = None
AUTO_TASK: Optional[asyncio.Task] = None

# Handel / Routing
DEFAULT_NOTIONAL_SOL  = float(os.environ.get("DEFAULT_NOTIONAL_SOL","0.10"))
GMGN_SLIPPAGE_PCT     = float(os.environ.get("GMGN_SLIPPAGE_PCT","0.5"))
GMGN_FEE_SOL          = float(os.environ.get("GMGN_FEE_SOL","0.003"))
WATCHLIST             = [s.strip() for s in os.environ.get("WATCHLIST","").split(",") if s.strip()]
ATR_PC_MIN            = float(os.environ.get("ATR_PC_MIN", "0.35"))

WSOL_MINT = "So11111111111111111111111111111111111111112"
USDC_MINT = "EPjFWdd5AufqSSqeM2qN1xzybapC8G4wEGGkZwyTDt1v"

# P&L / Logs
PNL_CSV = "trades_log.csv"
REALIZED_PNL_USD = 0.0

# Robustheit HTTP
HTTP_MAX_RETRY   = 3
HTTP_BASE_DELAY  = 0.25
CB_FAILS         = 0
CB_OPEN_UNTIL    = 0.0
CB_THRESHOLD     = 5
CB_COOLDOWN_SEC  = 120.0

# Debug/Visualisierung
DEBUG_SCAN = False
DEBUG_EVERY_N_BARS = int(os.environ.get("DEBUG_EVERY_N_BARS","6"))
DEBUG_SCAN_SEC = int(os.environ.get("DEBUG_SCAN_SEC", "30"))

_last_debug_ts: Dict[str, float] = {}
RUNNING = True
POLLING_STARTED = False

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger("autobot")

# Für echte OHLCV: je Mint den zuletzt verarbeiteten Candle-Zeitstempel merken
LAST_OHLCV_TS: Dict[str, int] = {}  # mint -> last_processed_time_ms

# --- Liquidity-Gate für ADD (mind. X on-chain Refs) ---
AW_ADD_REQUIRE_REFS = int(os.environ.get("AW_ADD_REQUIRE_REFS", "1"))

# --- AutoWatch Timing ---
AW_ENABLED_DEFAULT = int(os.environ.get("AW_ENABLED_DEFAULT", "1"))
AW_INTERVAL_SEC    = int(os.environ.get("AW_INTERVAL_SEC", "60"))
AW_RUN_TIMEOUT_SEC = int(os.environ.get("AW_RUN_TIMEOUT_SEC", "180"))

# --- Trading-Zeitfenster (lokale Stunden)
ALLOWED_HOURS_TZ_OFFSET_MIN = int(os.environ.get("ALLOWED_HOURS_TZ_OFFSET_MIN", "0"))
# Begrenze die Historie pro Mint (Default 3000 Bars; via ENV SERIES_MAXLEN anpassbar)
SERIES_MAXLEN = int(os.getenv("SERIES_MAXLEN", "3000"))

# ==== SANITY PERF KNOBS (per ENV steuerbar) ==============================
SANITY_ENABLE_MORALIS = os.getenv("SANITY_ENABLE_MORALIS", "0").lower() in ("1","true","on","yes")
SANITY_SKIP_USDC_ROUTE = os.getenv("SANITY_SKIP_USDC_ROUTE", "1").lower() in ("1","true","on","yes")
SANITY_RPC_TIMEOUT     = int(os.getenv("SANITY_RPC_TIMEOUT",   "8"))  # vorher 15
SANITY_MAX_TX_SAMPLES  = int(os.getenv("SANITY_MAX_TX_SAMPLES", "6")) # vorher 25
GMGN_HTTP_TIMEOUT = int(os.getenv("GMGN_HTTP_TIMEOUT", "20"))
SANITY_GMGN_TIMEOUT = GMGN_HTTP_TIMEOUT

KEEPALIVE_ENABLE = os.getenv("KEEPALIVE_ENABLE", "0").lower() in ("1","true","on")

# Nur in Notebook/Colab sinnvoll. In Produktion mit uvicorn/uvloop NICHT patchen.
try:
    import asyncio, nest_asyncio
    loop = None
    try:
        # patch nur, wenn bereits eine RUNNING loop existiert
        loop = asyncio.get_running_loop()
    except RuntimeError:
        loop = None  # noch keine laufende Loop -> nicht patchen

    if loop and ("uvloop" not in loop.__class__.__module__):
        nest_asyncio.apply()
except Exception:
    pass

# ==== Memory settings & helpers =============================================
def _mkdq():
    # Einheitlicher Deque-Factory mit begrenzter Länge
    from collections import deque
    return deque(maxlen=SERIES_MAXLEN)

def _drop_mint_state(m: str):
    for d in (ENGINES, BUILDERS, BAR_COUNTER, INDI_STATES, _last_debug_ts, LAST_OHLCV_TS):
        try:
            d.pop(m, None)
        except Exception:
            pass
    # NEU: auch Caches räumen
    try: _DEX_CACHE.pop(m, None)
    except Exception: pass
    try: _DECIMALS_CACHE.pop(m, None)
    except Exception: pass


def _rss_mb() -> float:
    """Optionales Monitoring: Resident Set Size in MB (psutil optional)."""
    try:
        import psutil, os as _os
        return psutil.Process(_os.getpid()).memory_info().rss / (1024 * 1024)
    except Exception:
        return -1.0
# =========================
# Telegram Hilfsfunktionen
# =========================
async def _error_handler(update: object, context: ContextTypes.DEFAULT_TYPE):
    logger.exception("Telegram handler exception", exc_info=context.error)
    try:
        if update and getattr(update, "effective_chat", None):
            await update.effective_chat.send_message("⚠️ Interner Fehler – siehe Logs.")
    except Exception:
        pass
def is_helius_url(u: str) -> bool:
    """Erkennt, ob eine RPC-URL zu Helius gehört."""
    return "helius" in (u or "").lower()

async def tg_post(text: str):
    if APP:
        try:
            await APP.bot.send_message(ALLOWED_CHAT_ID, text)
        except Exception:
            pass

def guard(update: Update)->bool:
    cid=update.effective_chat.id if update.effective_chat else None
    return cid==ALLOWED_CHAT_ID

async def send(update: Update, text:str):
    if update.effective_chat:
        await update.effective_chat.send_message(text)

def _ema_series(values: List[float], length: int) -> List[float]:
    if not values: return []
    if length <= 1: return list(values)
    k = 2.0 / (length + 1.0)
    out=[]; e=None
    for v in values:
        e = v if e is None else e + k*(v-e)
        out.append(e)
    return out

# ======= GRAFIK-RENDERER mit Entry-Markern =======
import io
from datetime import datetime

def render_mint_card(
    mint: str,
    bars: List[Dict[str, float]],
    diag: Optional[Dict[str, float]] = None,
    entries: Optional[List[Dict[str, float]]] = None,
    *,
    ema_len: int = 20,
    adx_len: int = 14,
    adx_smooth: int = 14,
) -> bytes:
    """
    PNG-Chart:
      - Close (Linie), EMA Pullback (strichliert)
      - Volumen (Balken)
      - ADX (Wilder mit SMA-Init), horizontale 20-Linie
      - Entry-Pins (grüne Dreiecke) aus 'entries' [{'time':ms,'price':...,'type':'entry'}]
    Rückgabe: PNG-Bytes.
    """
    if not bars:
        raise RuntimeError("render_mint_card: keine Bars übergeben")

    ts = [datetime.fromtimestamp(int(b["time"])/1000, dt.UTC) for b in bars]
    close = [float(b["close"]) for b in bars]
    high  = [float(b["high"])  for b in bars]
    low   = [float(b["low"])   for b in bars]
    vol   = [float(b["volume"]) for b in bars]

    # EMA
    ema = []
    prev = None; k = 2.0/(ema_len+1.0)
    for c in close:
        prev = c if prev is None else prev + k*(c - prev)
        ema.append(prev)

    # ADX (Wilder, SMA-Priming)
    def _tr(h,l,pc): return max(h-l, abs(h-pc), abs(l-pc))
    dm_pos_ema = dm_neg_ema = tr_ema = None
    init = 0
    dx_series = []
    pc = ph = pl = None
    for i in range(len(bars)):
        c,h,l = close[i], high[i], low[i]
        if pc is None:
            pc,ph,pl = c,h,l
            dx_series.append(0.0); continue
        up = h - ph
        dn = pl - l
        dm_pos = up if (up>dn and up>0) else 0.0
        dm_neg = dn if (dn>up and dn>0) else 0.0
        tr = _tr(h,l,pc)
        if dm_pos_ema is None:
            dm_pos_ema = dm_pos; dm_neg_ema = dm_neg; tr_ema = tr; init = 1
        elif init < adx_len:
            dm_pos_ema = (dm_pos_ema*init + dm_pos)/(init+1)
            dm_neg_ema = (dm_neg_ema*init + dm_neg)/(init+1)
            tr_ema     = (tr_ema*init     + tr    )/(init+1)
            init += 1
        else:
            dm_pos_ema = dm_pos_ema + (dm_pos - dm_pos_ema)/float(adx_len)
            dm_neg_ema = dm_neg_ema + (dm_neg - dm_neg_ema)/float(adx_len)
            tr_ema     = tr_ema     + (tr     - tr_ema    )/float(adx_len)
        denom = tr_ema if tr_ema else 1e-12
        di_p = 100.0*(dm_pos_ema/denom)
        di_m = 100.0*(dm_neg_ema/denom)
        dx = 0.0
        if (di_p+di_m)>0:
            dx = 100.0*abs(di_p-di_m)/(di_p+di_m)
        dx_series.append(dx)
        pc,ph,pl = c,h,l

    adx = []
    prev_adx = None; init_adx = 0
    for d in dx_series:
        if prev_adx is None:
            prev_adx = d; init_adx = 1
        elif init_adx < adx_smooth:
            prev_adx = (prev_adx*init_adx + d)/(init_adx+1); init_adx += 1
        else:
            prev_adx = prev_adx + (d - prev_adx)/float(adx_smooth)
        adx.append(prev_adx)

    # Plot
    fig = plt.figure(figsize=(9,6), dpi=140)
    gs = fig.add_gridspec(3,1, height_ratios=[3.0,1.2,1.2], hspace=0.08)
    ax_p = fig.add_subplot(gs[0,0])
    ax_v = fig.add_subplot(gs[1,0], sharex=ax_p)
    ax_a = fig.add_subplot(gs[2,0], sharex=ax_p)

    ax_p.plot(ts, close, linewidth=1.3, label="Close")
    ax_p.plot(ts, ema,   linewidth=1.0, linestyle="--", label=f"EMA{ema_len}")
    ax_p.set_ylabel("Price (USD)")
    ax_p.grid(True, alpha=0.2)
    ax_p.legend(loc="upper left", fontsize=8)

    # Entry-Marker
    if entries:
        ex = []; ey = []
        for e in entries:
            if (e.get("type") or "").lower() == "entry":
                ex.append(datetime.fromtimestamp(int(e["time"]) / 1000, dt.UTC))
                ey.append(float(e["price"]))
        if ex:
            ax_p.scatter(ex, ey, marker="^", s=40, color="tab:green", zorder=6, label="Entry")
            ax_p.legend(loc="upper left", fontsize=8)

    # Vol
    ax_v.bar(ts, vol, width=0.003*(ts[-1]-ts[0]).total_seconds() if len(ts)>1 else 5, alpha=0.6)
    ax_v.set_ylabel("Vol")
    ax_v.grid(True, alpha=0.2)

    # ADX
    ax_a.plot(ts, adx, linewidth=1.0, label=f"ADX {adx_len}/{adx_smooth}")
    ax_a.axhline(20, color="grey", alpha=0.35, linewidth=0.8)
    ax_a.set_ylabel("ADX")
    ax_a.grid(True, alpha=0.2)
    ax_a.set_xlabel(f"{mint[:6]} — UTC")

    buf = io.BytesIO()
    fig.tight_layout()
    fig.savefig(buf, format="png", bbox_inches="tight")
    plt.close(fig)
    buf.seek(0)
    return buf.getvalue()

# =========================
# Wallet/Client
# =========================
def _load_keypair_from_env() -> Keypair:
    raw = (os.environ.get("SOLANA_PRIVATE_KEY") or "").strip()
    if not raw:
        raise RuntimeError("ENV SOLANA_PRIVATE_KEY fehlt – bitte setzen oder PAPER_MODE=1 verwenden.")
    try:
        b = base64.b64decode(raw)
        if len(b) == 64: return Keypair.from_bytes(b)
        if len(b) == 32: return Keypair.from_seed(b)
    except Exception:
        pass
    try:
        arr = json.loads(raw)
        if isinstance(arr, list):
            b = bytes(arr)
            if len(b) == 64: return Keypair.from_bytes(b)
            if len(b) == 32: return Keypair.from_seed(b)
    except Exception as e:
        raise RuntimeError("SOLANA_PRIVATE_KEY ist weder Base64 noch JSON-Array") from e
    raise RuntimeError("Konnte SOLANA_PRIVATE_KEY nicht laden (erwarte 32- oder 64-Byte Key).")


# --- NEU: in Paper-Mode keinen ENV-Key erzwingen ---
if PAPER_MODE:
    KP = Keypair()  # Ephemeral Key (kein echter On-Chain Key)
else:
    KP = _load_keypair_from_env()

WALLET_PUBKEY = str(KP.pubkey())
client = Client(RPC_URL)

# =========================
# HTTP Helpers w/ Backoff
# =========================
# ===== HTTP Helpers + Circuit Breaker (tunable, DS schonend) ================
import time, random

# Tuning via ENV möglich
CB_THRESHOLD     = int(os.environ.get("CB_THRESHOLD", "5"))         # Default-Schwelle
CB_COOLDOWN_SEC  = float(os.environ.get("CB_COOLDOWN_SEC", "60"))    # Default-Cooldown (s)

# globaler, einfacher CB-Zustand (nur für "sensitive" Hosts genutzt)
CB_FAILS = 0
CB_OPEN_UNTIL = 0.0

def _retry_policy_for(url: str, method: str = "GET") -> tuple[int, float, float, bool]:
    """
    Rückgabe: (max_retry, base_delay, jitter_max, cb_sensitive)
    cb_sensitive=False => Fehlversuche lösen KEINEN globalen CB aus.
    """
    u = (url or "").lower()
    # GMGN TX: sehr vorsichtig, CB-sensitiv
    if "gmgn.ai/txproxy" in u or "send_transaction" in u:
        return 1, 0.50, 0.20, True
    # GMGN route/quote: moderat, CB-sensitiv
    if "gmgn.ai" in u and "/defi/router" in u:
        return 2, 0.50, 0.20, True
    # Birdeye: sparsam, CB-sensitiv (um Rate-Limits zu respektieren)
    if "public-api.birdeye.so" in u:
        return 2, 0.25, 0.15, True
    # DexScreener: NICHT CB-sensitiv (häufiger 403/HTML → nicht global blockieren)
    if "api.dexscreener.com" in u:
        return 3, 0.25, 0.15, False
    # Default: CB-sensitiv
    return CB_THRESHOLD, 0.25, 0.15, True

def http_get(url: str, params=None, headers=None, timeout=15):
    global CB_FAILS, CB_OPEN_UNTIL
    max_retry, base_delay, jitter_max, cb_sensitive = _retry_policy_for(url, "GET") if False else _retry_policy_for(url, "GET")  # guard for copy/paste
    # CircuitBreaker nur anwenden, wenn sensitives Ziel
    if cb_sensitive and time.time() < CB_OPEN_UNTIL:
        raise RuntimeError("CircuitBreaker aktiv")
    for i in range(max_retry):
        try:
            r = requests.get(url, params=params, headers=headers, timeout=timeout)
            # nur "harte" HTTP-Fehler als Fehler werten
            if r.status_code in (429, 500, 502, 503, 504):
                raise RuntimeError(f"HTTP {r.status_code}")
            return r
        except Exception as e:
            time.sleep(base_delay * (2 ** i) + random.uniform(0, jitter_max))
            if i == max_retry - 1:
                if cb_sensitive:
                    CB_FAILS += 1
                    if CB_FAILS >= CB_THRESHOLD:
                        CB_FAILS = 0
                        CB_OPEN_UNTIL = time.time() + CB_COOLDOWN_SEC
                raise RuntimeError(f"GET Fehlversuche erschöpft: {e}")

def http_post(url: str, json_body=None, headers=None, timeout=15):
    global CB_FAILS, CB_OPEN_UNTIL
    max_retry, base_delay, jitter_max, cb_sensitive = _retry_policy_for(url, "POST")
    if cb_sensitive and time.time() < CB_OPEN_UNTIL:
        raise RuntimeError("CircuitBreaker aktiv")
    for i in range(max_retry):
        try:
            r = requests.post(url, json=json_body, headers=headers, timeout=timeout)
            if r.status_code in (429, 500, 502, 503, 504):
                raise RuntimeError(f"HTTP {r.status_code}")
            return r
        except Exception as e:
            time.sleep(base_delay * (2 ** i) + random.uniform(0, jitter_max))
            if i == max_retry - 1:
                if cb_sensitive:
                    CB_FAILS += 1
                    if CB_FAILS >= CB_THRESHOLD:
                        CB_FAILS = 0
                        CB_OPEN_UNTIL = time.time() + CB_COOLDOWN_SEC
                raise RuntimeError(f"POST Fehlversuche erschöpft: {e}")

# =========================
# Datenquellen: Preis + Volumen
# =========================
def _have_be_key() -> bool:
    k = (os.getenv("BIRDEYE_API_KEY") or "").strip()
    return bool(k)
    
# -- Birdeye robust (Param UND Header) --
def _be_headers(chain_hint: str|None=None) -> Dict[str,str]:
    h={"X-API-KEY": BIRDEYE_API_KEY, "accept":"application/json"}
    if chain_hint: h["x-chain"] = "solana" if chain_hint.lower() in ("sol","solana") else chain_hint
    return h

def birdeye_price_detailed(mint: str) -> Tuple[float, str]:
    if not _have_be_key():
        return 0.0, "missing_api_key"
    last="unknown"
    for ch in ("sol","solana"):
        try:
            r = http_get("https://public-api.birdeye.so/defi/price",
                         params={"address": mint, "chain": ch},
                         headers=_be_headers(), timeout=10)
            if r.status_code != 200:
                last=f"http {r.status_code} (param {ch})"; continue
            j = r.json() if r.headers.get("content-type","").lower().startswith("application/json") else {}
            data = j.get("data")
            if isinstance(data, dict) and "value" in data:
                try:
                    v=float(data.get("value") or 0.0)
                except Exception:
                    last=f"parse error (param {ch})"; continue
                if v>0: return v, f"ok:param:{ch}"
                last=f"data.value=0 (param {ch})"; continue
            last=f"no data (param {ch})"
        except Exception as e:
            last=str(e)
    try:
        r = http_get("https://public-api.birdeye.so/defi/price",
                     params={"address": mint}, headers=_be_headers("solana"), timeout=10)
        if r.status_code == 200:
            j=r.json(); data=j.get("data")
            if isinstance(data, dict) and "value" in data:
                v=float(data.get("value") or 0.0)
                if v>0: return v, "ok:xhdr:solana"
                last="data.value=0 (xhdr)"
            else:
                last="no data (xhdr)"
        else:
            last=f"http {r.status_code} (xhdr)"
    except Exception as e:
        last=str(e)
    return 0.0, last


def birdeye_price(mint: str, chain="sol") -> float:
    px, _ = birdeye_price_detailed(mint); return px

def birdeye_price_multi(mints: List[str], chain="sol") -> Dict[str, float]:
    if not mints:
        return {}
    if not _have_be_key():  # Key erforderlich
        return {}
    # 1) Param chain
    headers = _be_headers()
    try:
        r = http_get(
            "https://public-api.birdeye.so/defi/multi_price",
            params={"addresses": ",".join(mints), "chain": chain},
            headers=headers,
            timeout=10
        )
        j = r.json()
        out = {}
        if j.get("success") and isinstance(j.get("data"), dict):
            for m, p in j["data"].items():
                val = (p or {}).get("value")
                if val is not None:
                    try:
                        out[m] = float(val)
                    except:
                        pass
        if out:
            return out
    except Exception:
        pass
    # 2) Header x-chain (Fallback)
    try:
        r = http_get(
            "https://public-api.birdeye.so/defi/multi_price",
            params={"addresses": ",".join(mints)},
            headers=_be_headers("solana"),
            timeout=10
        )
        j = r.json()
        out = {}
        if j.get("success") and isinstance(j.get("data"), dict):
            for m, p in j["data"].items():
                val = (p or {}).get("value")
                if val is not None:
                    try:
                        out[m] = float(val)
                    except:
                        pass
        return out
    except Exception:
        return {}

# DexScreener: Volumen/Preis
def _ds_get_json(url: str, timeout: int = 10) -> dict:
    """
    Robust: Erst via Proxy (falls gültig), sonst direkt.
    Akzeptiert nur echte JSON-Antworten; bei HTML/Fehlern -> {}.
    """
    urls = []
    p = _get_ds_proxy()
    if p:
        urls.append(_wrap(url))
    urls.append(url)  # immer auch direkt versuchen

    for u in urls:
        try:
            r = http_get(u, headers=_ds_headers(), timeout=timeout)
            ct = (r.headers.get("content-type") or "").lower()
            txt = r.text if hasattr(r, "text") else ""
            # echte JSON?
            if "application/json" in ct:
                j = r.json()
                return j if isinstance(j, (dict, list)) else {}
            # fallback: manche proxy geben falschen CT zurück
            if txt and txt.lstrip().startswith(("{", "[")):
                try:
                    import json
                    j = json.loads(txt)
                    if isinstance(j, (dict, list)):
                        return j
                except Exception:
                    pass
        except Exception as e:
            # stillschweigend weiter zur nächsten URL
            continue
    return {}




async def _get_json(url: str, timeout: int = 10) -> Optional[dict]:
    """
    Async-Wrapper um _ds_get_json (Thread-Offload).
    """
    try:
        return await asyncio.to_thread(_ds_get_json, url, timeout)
    except Exception:
        return None

def _ds_pick_best_sol_pair(pairs: list[dict]) -> dict | None:
    """Wähle das liquideste Solana-Paar; wenn keines markiert, nimm bestes nach USD-Liq."""
    if not pairs:
        return None
    sol_pairs = [p for p in pairs if (p.get("chainId") or "").lower() == "solana"]
    cand = sol_pairs if sol_pairs else pairs
    def _liq(p): 
        try: 
            return float(((p.get("liquidity") or {}).get("usd")) or 0.0)
        except Exception:
            return 0.0
    cand.sort(key=_liq, reverse=True)
    return cand[0] if cand else None

_DEX_CACHE: Dict[str, Tuple[float, float]] = {}
def dexscreener_usd_1m_approx(mint: str, ttl_sec: int = 45) -> float:
    """
    Liefert eine grobe Schätzung des USD-Volumens pro Minute (≈1m) für ein Mint.
    Quelle: DexScreener (volume.h1 bzw. fallback auf volume.h24).
    Nutzt Proxy-aware Fetch (_ds_get_json), wählt das liquideste Solana-Pair
    (_ds_pick_best_sol_pair) und cached Ergebnisse kurzzeitig in _DEX_CACHE.
    """
    now = time.time()

    # Cache-Hit?
    try:
        cached_val, cached_ts = _DEX_CACHE.get(mint, (None, 0.0))
        if cached_val is not None and (now - float(cached_ts)) < float(ttl_sec):
            return float(cached_val)
    except Exception:
        pass

    vpm = 0.0
    try:
        js = _ds_get_json(f"https://api.dexscreener.com/token-pairs/v1/solana/{mint}", timeout=10)
        pairs = js if isinstance(js, list) else (js.get("pairs") or js.get("data") or [])
        best = _ds_pick_best_sol_pair(pairs) if pairs else None

        if best:
            vol = best.get("volume") or {}
            h1  = float(vol.get("h1")  or 0.0)
            h24 = float(vol.get("h24") or 0.0)

            if h1 > 0:
                vpm = h1 / 60.0
            elif h24 > 0:
                vpm = h24 / 1440.0
    except Exception:
        vpm = 0.0

    # Immer cachen (auch 0.0), damit wir kurzfristig nicht spammen
    vpm = max(0.0, float(vpm))
    _DEX_CACHE[mint] = (vpm, now)
    return vpm


def dexscreener_price_usd(mint: str) -> float:
    """Preis in USD (bestes Solana-Paar). DS proxy-aware + headers."""
    try:
        js = _ds_get_json(f"https://api.dexscreener.com/token-pairs/v1/solana/{mint}")
        pairs = js if isinstance(js, list) else (js.get("pairs") or [])
        best = _ds_pick_best_sol_pair(pairs)
        if not best:
            return 0.0
        px = float(best.get("priceUsd") or best.get("price") or 0.0)
        return px if px > 0 else 0.0
    except Exception:
        return 0.0
                
def _fmt_age_from_ms(created_ms: Optional[int]) -> str:
    if not created_ms or created_ms <= 0:
        return "n/a"
    now_ms = int(time.time() * 1000)
    diff_s = max(0, (now_ms - created_ms) // 1000)
    days  = diff_s // 86400
    hrs   = (diff_s % 86400) // 3600
    mins  = (diff_s % 3600) // 60
    if days > 0:
        return f"{days}d {hrs}h"
    if hrs > 0:
        return f"{hrs}h {mins}m"
    return f"{mins}m"

def dexscreener_token_meta(mint: str) -> Tuple[str, str]:
    """
    Liefert (anzeige_name, alter_text) über DexScreener – robust, proxy-aware.
    Quelle: https://api.dexscreener.com/tokens/v1/solana/{mint}
    """
    try:
        js = _ds_get_json(f"https://api.dexscreener.com/tokens/v1/solana/{mint}")
        # tokens/v1 liefert i. d. R. {"pairs":[...]}
        pairs = js.get("pairs") if isinstance(js, dict) else []
        if not pairs:
            return (mint[:6] + "…", "n/a")

        # Name vom liquidesten Paar
        best = _ds_pick_best_sol_pair(pairs) or pairs[0]
        base = (best.get("baseToken") or {})
        symbol = (base.get("symbol") or "").strip()
        name   = (base.get("name") or "").strip()
        display = symbol or name or (mint[:6] + "…")

        # Alter: kleinstes pairCreatedAt
        oldest_ms = None
        for p in pairs:
            try:
                c_ms = int(p.get("pairCreatedAt") or p.get("createdAt") or p.get("poolCreatedAt") or 0)
                if c_ms > 0:
                    oldest_ms = c_ms if oldest_ms is None else min(oldest_ms, c_ms)
            except Exception:
                pass

        age_txt = _fmt_age_from_ms(oldest_ms)
        return (display, age_txt)
    except Exception:
        return (mint[:6] + "…", "n/a")
  
# ------------------------------------------------------------------------------    
# ------------------------------------------------------------------------------    
# ---- DexScreener Discovery (bereinigt) + Sanity Checks -----------------------
# discovery_ds_clean.py (inline)
# ------------------------------------------------------------------------------

from dataclasses import dataclass
from typing import Optional, List, Tuple, Dict, Any
from urllib.parse import quote_plus, urlparse
import os, time, re

# ---------- Datenmodell ----------
@dataclass
class Candidate:
    mint: str
    symbol: str
    name: str
    url: str
    lp_sol: float
    mcap_usd: float
    vol24_usd: float
    tx24: int
    m5_buys: int
    m5_sells: int
    score: float
    reasons: List[str]

# ---------- Konstanten & Helpers ----------
DS_BASE = "https://api.dexscreener.com/latest/dex"

# Live-Proxy (ENV) – erlaubt Umschalten ohne Neustart
def _get_ds_proxy() -> str:
    """Gültige Proxy-URL (http/https) oder ''."""
    v = (os.environ.get("DS_PROXY_URL") or "").strip()
    if not v:
        return ""
    try:
        u = urlparse(v)
        if u.scheme in ("http", "https") and u.netloc:
            return v.rstrip("/")
    except Exception:
        pass
    # ungültig -> ignorieren
    return ""

def _wrap(url: str) -> str:
    """
    Wenn ein gültiger Proxy gesetzt ist, leite Anfragen über:
      <proxy>/?url=<encoded_target>
    Sonst Original-URL zurückgeben.
    """
    p = _get_ds_proxy()
    if not p:
        return url
    return f"{p}/?url={quote_plus(url)}"

def _ds_headers() -> dict:
    # etwas "echterer" UA + JSON bevorzugen
    return {
        "Accept": "application/json, */*;q=0.5",
        "User-Agent": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
                      "(KHTML, like Gecko) Chrome/122.0 Safari/537.36",
        "Referer": "https://dexscreener.com/",
        "Origin":  "https://dexscreener.com",
        "Cache-Control": "no-cache",
        "Pragma": "no-cache",
    }

def _safe_float(x, d: float = 0.0) -> float:
    try:
        return float(x or 0)
    except Exception:
        return float(d)

def _safe_int(x, d: int = 0) -> int:
    try:
        return int(x or 0)
    except Exception:
        return int(d)

# Solana-Adress-Heuristik (Base58, 32–44 Zeichen, ohne 0OIl)
_SOLANA_ADDR_RE = re.compile(r"^[1-9A-HJ-NP-Za-km-z]{32,44}$")
def _looks_like_solana_addr(addr: str | None) -> bool:
    return bool(_SOLANA_ADDR_RE.fullmatch((addr or "").strip()))

# Alters-Schätzung (Minuten) aus Pair-Feldern
def _pair_age_min(p: dict) -> Optional[int]:
    ts = None
    for k in ("pairCreatedAt", "createdAt", "poolCreatedAt"):
        v = p.get(k)
        if v:
            try:
                ts = int(v); break
            except Exception:
                pass
    if ts is None:
        return None
    now_ms = int(time.time() * 1000)
    if ts > now_ms:
        return 0
    return int((now_ms - ts) // 60000)

# ========= DexScreener JSON-Grund-Fetch (nutzt dein http_get) =========
def _as_list_from_json(j: object, *keys: str) -> list:
    if isinstance(j, list):
        return j
    if isinstance(j, dict):
        for k in keys:
            v = j.get(k)
            if isinstance(v, list):
                return v
    return []

# ========= Quellen (Boosts / Profiles / Trending / Search) =========
def ds_token_boosts_latest() -> list[dict]:
    try:
        j = _ds_get_json("https://api.dexscreener.com/token-boosts/latest/v1", timeout=10)
        return _as_list_from_json(j, "data", "boosts")
    except Exception:
        return []

def ds_token_boosts_top() -> list[dict]:
    try:
        r = http_get(
            _wrap("https://api.dexscreener.com/token-boosts/top/v1"),
            headers=_ds_headers(),
            timeout=10
        )
        ct = (r.headers.get("content-type") or "").lower()
        if "application/json" not in ct:
            return []
        j = r.json() or {}
        return (j.get("data") or j.get("boosts") or (j if isinstance(j, list) else [])) or []
    except Exception:
        return []


def ds_token_profiles_latest() -> list[dict]:
    """
    DexScreener: /token-profiles/latest/v1 – robustes Parsing.
    (Nur diese Version behalten; die spätere doppelte bitte entfernen.)
    """
    try:
        j = _ds_get_json("https://api.dexscreener.com/token-profiles/latest/v1", timeout=10)
        return _as_list_from_json(j, "data", "profiles")
    except Exception:
        return []

def _fetch_pairs_by_token(mint: str) -> list[dict]:
    try:
        r = http_get(
            _wrap(f"https://api.dexscreener.com/token-pairs/v1/solana/{mint}"),
            headers=_ds_headers(), timeout=10
        )
        js = r.json() or {}
        return js if isinstance(js, list) else (js.get("pairs") or [])
    except Exception:
        return []


def _fetch_pairs_by_pair(pair_id: str) -> list[dict]:
    try:
        r = http_get(_wrap(f"https://api.dexscreener.com/latest/dex/pairs/solana/{pair_id}"),
                     headers=_ds_headers(), timeout=10)
        js = r.json() or {}
        return (js.get("pairs") or [])
    except Exception:
        return []

def _solana_id_from_url(u: str) -> tuple[str, str] | None:
    """
    ('token', <mint>) oder ('pair', <pairAddress>) aus einer DS-URL ziehen.
    """
    try:
        p = urlparse(u)
        parts = [x for x in p.path.strip("/").split("/") if x]
        i = parts.index("solana")
        tail = parts[i+1:]
        if not tail:
            return None
        if tail[0].lower()=="pair" and len(tail)>=2:
            pid = tail[1]
            return ("pair", pid) if _looks_like_solana_addr(pid) else None
        mint = tail[0]
        return ("token", mint) if _looks_like_solana_addr(mint) else None
    except Exception:
        return None

async def _fetch_pairs_trending() -> List[dict]:
    js = await _get_json(_wrap(f"{DS_BASE}/trending?include=solana"))
    return [p for p in ((js or {}).get("pairs") or []) if (p.get("chainId") or "").lower()=="solana"]

async def _fetch_pairs_search_multi() -> List[dict]:
    """
    Mehrere Search-Queries (ohne 'chain:solana' wegen 403).
    Nach dem Fetch hart auf Solana filtern + nach baseToken.address deduplizieren.
    Queries sind per ENV DSR_SEARCH_QUERIES konfigurierbar (comma-separated).
    """
    env_q = (os.environ.get("DSR_SEARCH_QUERIES") or "").strip()
    if env_q:
        queries = [q.strip() for q in env_q.split(",") if q.strip()]
    else:
        # Default-Set (breit & praktikabel)
        queries = [
            "raydium", "orca", "meteora",
            "pumpfun",
            "sol usdc", "wsol", "raydium amm",
        ]

    async def _get(q: str) -> List[dict]:
        js = await _get_json(_wrap(f"{DS_BASE}/search?q={quote_plus(q)}"))
        return (js or {}).get("pairs") or []

    seen: set[str] = set()
    out: List[dict] = []
    for q in queries:
        try:
            for p in await _get(q):
                if (p.get("chainId") or "").lower() != "solana":
                    continue
                addr = ((p.get("baseToken") or {}).get("address")) or ""
                if addr and addr not in seen:
                    out.append(p); seen.add(addr)
        except Exception:
            continue
    return out

async def _fetch_pairs_new_sol() -> List[dict]:
    js = await _get_json(_wrap(f"{DS_BASE}/new-pairs?include=solana"))
    return (js or {}).get("pairs") or []

# ========= Pair-Scoring & Hilfen =========
def _lp_sol_of_pair(p: dict) -> float:
    """LP in SOL approximieren (quote=SOL → quote; sonst USD→SOL grob)."""
    liq = p.get("liquidity") or {}
    quote_sym = ((p.get("quoteToken") or {}).get("symbol") or "").upper()
    if quote_sym == "SOL":
        return _safe_float(liq.get("quote"))
    px_usd  = _safe_float((p.get("priceUsd") or p.get("price")))
    px_nat  = _safe_float(p.get("priceNative") or 1.0) or 1.0
    sol_usd = px_usd / px_nat if px_nat else 200.0
    lp_usd  = _safe_float(liq.get("usd"))
    return lp_usd / max(1e-9, (2.0 * sol_usd))

def _is_pumpfun_pair(p: dict) -> bool:
    try:
        parts = [str(p.get("url") or ""), str(p.get("dexId") or ""), str(p.get("pairAddress") or "")]
        info = (p.get("info") or {})
        webs = info.get("websites") or []
        socs = info.get("socials") or []
        def _blob(arr):
            out=[]
            for it in arr:
                if isinstance(it, dict):
                    out.append(str(it.get("url") or "")); out.append(str(it.get("label") or ""))
                else:
                    out.append(str(it))
            return " ".join(out)
        parts.append(_blob(webs)); parts.append(_blob(socs))
        blob = " ".join(parts).lower()
        return ("pumpfun" in blob) or ("pump.fun" in blob)
    except Exception:
        return False

def _score_pair(p: dict) -> Tuple[int, List[str]]:
    """
    Kompakter Qualitäts-Score (0..100), rein DS-basiert – robust und schnell.
    """
    reasons: List[str] = []

    lp_sol   = _lp_sol_of_pair(p)
    vol24    = _safe_float((p.get("volume") or {}).get("h24"))
    tx_h24   = (p.get("txns") or {}).get("h24") or {}
    tx24     = _safe_int(tx_h24.get("buys")) + _safe_int(tx_h24.get("sells"))
    m5       = (p.get("txns") or {}).get("m5") or {}
    m5_buys  = _safe_int(m5.get("buys"))
    m5_sells = _safe_int(m5.get("sells"))
    age_min  = _pair_age_min(p)
    sol_quote= 1 if ((p.get("quoteToken") or {}).get("symbol") or "").upper()=="SOL" else 0

    sc_lp   = min(30, int(lp_sol*2))
    sc_vol  = min(25, int(vol24/1000))
    sc_tx   = min(20, int(tx24/25))
    sc_m5   = min(15, max(0, (m5_buys - m5_sells)))
    sc_age  = 0 if age_min is None else max(0, 10 - int(age_min/9))
    sc_sol  = 5 if sol_quote else 0

    total = min(100, sc_lp + sc_vol + sc_tx + sc_m5 + sc_age + sc_sol)

    if lp_sol < 1: reasons.append("LP<1SOL")
    if vol24 < 2000: reasons.append("VOL24<2k")
    if tx24 < 50: reasons.append("TX24<50")
    if m5_buys <= m5_sells: reasons.append("M5!")
    if not sol_quote: reasons.append("no SOL-quote")
    if _is_pumpfun_pair(p): reasons.insert(0, "PF")
    if not reasons: reasons = ["OK"]

    return total, reasons

def _to_candidate(p: dict, score: int, reasons: List[str]) -> Candidate:
    base = p.get("baseToken") or {}
    vol  = p.get("volume") or {}
    tx   = p.get("txns") or {}
    tx_h = tx.get("h24") or {}
    tx_m = tx.get("m5")  or {}

    return Candidate(
        mint       = base.get("address") or "",
        symbol     = base.get("symbol") or "?",
        name       = base.get("name") or "?",
        url        = p.get("url") or f"https://dexscreener.com/solana/{base.get('address') or ''}",
        lp_sol     = _lp_sol_of_pair(p),
        mcap_usd   = _safe_float(p.get("fdv")),
        vol24_usd  = _safe_float(vol.get("h24")),
        tx24       = _safe_int(tx_h.get("buys")) + _safe_int(tx_h.get("sells")),
        m5_buys    = _safe_int(tx_m.get("buys")),
        m5_sells   = _safe_int(tx_m.get("sells")),
        score      = float(score),
        reasons    = list(reasons),
    )

# ========= Boosts → Paare (bereinigt; kein toter Code) =========
async def _fetch_pairs_from_boosts(max_items: int = 200) -> list[dict]:
    boosts = ds_token_boosts_latest() or ds_token_boosts_top()
    if not boosts:
        return []
    out: list[dict] = []
    seen_pairs: set[str] = set()
    for b in boosts:
        chain = str(b.get("chainId") or "").lower()
        url   = str(b.get("url") or "")
        mint  = (b.get("tokenAddress") or "").strip()

        if chain != "solana" and "/solana/" not in url:
            continue

        if _looks_like_solana_addr(mint):
            for p in _fetch_pairs_by_token(mint):
                pid = str(p.get("pairAddress") or "")
                if pid and pid not in seen_pairs:
                    out.append(p); seen_pairs.add(pid)
            if len(seen_pairs) >= max_items:
                break
            continue

        kind_id = _solana_id_from_url(url) if url else None
        if not kind_id:
            continue
        kind, ident = kind_id
        lst = _fetch_pairs_by_token(ident) if kind == "token" else _fetch_pairs_by_pair(ident)
        for p in lst:
            pid = str(p.get("pairAddress") or "")
            if pid and pid not in seen_pairs:
                out.append(p); seen_pairs.add(pid)
        if len(seen_pairs) >= max_items:
            break
    return out

async def _fetch_pairs_from_profiles(max_items: int = 300) -> list[dict]:
    """
    Lädt Profile und dann zu jeder Mint die Pair-Details via:
    https://api.dexscreener.com/tokens/v1/solana/{mint}
    """
    prof = ds_token_profiles_latest()
    if not prof:
        return []
    mints: list[str] = []
    for it in prof:
        chain = str(it.get("chainId") or "").lower()
        mint  = (it.get("tokenAddress") or "").strip()
        if chain == "solana" and _looks_like_solana_addr(mint):
            mints.append(mint)
        if len(mints) >= max_items:
            break
    mints = list(dict.fromkeys(mints))  # de-dupe

    out: list[dict] = []
    seen_pairs: set[str] = set()
    for mint in mints:
        try:
            js = _ds_get_json(f"https://api.dexscreener.com/tokens/v1/solana/{mint}", timeout=10)
            pairs = js.get("pairs") if isinstance(js, dict) else []
            for p in (pairs or []):
                pid = str(p.get("pairAddress") or "")
                if pid and pid not in seen_pairs:
                    out.append(p); seen_pairs.add(pid)
        except Exception:
            continue
    return out

# ========= Haupt-Discovery =========
async def discover_candidates_ds_only(
    *,
    top_n: int = 15,
    max_age_min: int = 90,
    min_lp_sol: float = 1.0,
    min_vol24_usd: float = 2000.0,
    min_tx24: int = 50,
    prefer_sol_quote: bool = True,
    hotlist: str = "off",      # off|trending|approx|boosts|profiles
    pumpfun_only: bool = False,
    auto_relax: bool = True,
) -> List[Candidate]:

    def _run_filter(pairs, lp, vol, tx, prefer_quote, max_age):
        out_local: List[Tuple[int, Candidate]] = []
        for p in pairs or []:
            cid  = (p.get("chainId") or "").lower()
            base = (p.get("baseToken") or {})
            addr = (base.get("address") or "").strip()

            if cid and cid != "solana" and not _looks_like_solana_addr(addr):
                continue
            if pumpfun_only and not _is_pumpfun_pair(p):
                continue

            age = _pair_age_min(p)
            if (age is not None) and (age > max_age):
                continue

            if _lp_sol_of_pair(p) < lp:
                continue
            if _safe_float((p.get("volume") or {}).get("h24")) < vol:
                continue
            txh = (p.get("txns") or {}).get("h24") or {}
            if (_safe_int(txh.get("buys")) + _safe_int(txh.get("sells"))) < tx:
                continue
            if prefer_quote and ((p.get("quoteToken") or {}).get("symbol") or "").upper() != "SOL":
                continue

            if hotlist == "approx":
                m5 = (p.get("txns") or {}).get("m5") or {}
                if _safe_int(m5.get("buys")) <= _safe_int(m5.get("sells")):
                    continue

            score, reasons = _score_pair(p)
            if hotlist == "trending":
                score = min(100, score + 5)

            out_local.append((score, _to_candidate(p, score, reasons)))

        out_local.sort(key=lambda t: t[0], reverse=True)
        return [c for _s, c in out_local[:top_n]]

    # Quelle wählen
    pairs: List[dict] = []
    if hotlist == "trending":
        pairs = await _fetch_pairs_trending() or await _fetch_pairs_new_sol()
        if not pairs:
            hotlist = "approx"
    elif hotlist == "boosts":
        pairs = await _fetch_pairs_from_boosts(max_items=200)
    elif hotlist == "profiles":
        pairs = await _fetch_pairs_from_profiles(max_items=300)
    else:  # off|approx
        pairs = await _fetch_pairs_search_multi()

    # Fallback-Quellen
    if not pairs:
        pairs = await _fetch_pairs_from_boosts(max_items=200) or await _fetch_pairs_from_profiles(max_items=300)
    if not pairs:
        return []

    # 1. strikter Pass
    out = _run_filter(pairs, lp=min_lp_sol, vol=min_vol24_usd, tx=min_tx24,
                      prefer_quote=prefer_sol_quote, max_age=max_age_min)
    if out or not auto_relax:
        return out

    # 2. Relaxter Pass
    return _run_filter(pairs, lp=0.05, vol=20.0, tx=1, prefer_quote=False,
                       max_age=max(1440, max_age_min))

# ========= Sanity / Safety‑Report (Onchain + Route + Konzentration) =========
def rpc_get_mint_info_jsonparsed(mint_b58: str) -> dict:
    """
    Holt Mint-Info via getAccountInfo (jsonParsed).
    Rückgabe: info-Dict oder {}.
    """
    payload = {
        "jsonrpc": "2.0", "id": 1, "method": "getAccountInfo",
        "params": [mint_b58, {"encoding": "jsonParsed", "commitment": "confirmed"}],
    }
    try:
        r = requests.post(RPC_URL, json=payload, timeout=15)
        v = ((r.json() or {}).get("result") or {}).get("value") or {}
        data = (v.get("data") or {})
        parsed = (data.get("parsed") or {})
        info = parsed.get("info") or {}
        return info if isinstance(info, dict) else {}
    except Exception:
        return {}

def rpc_get_token_largest_accounts(mint_b58: str, top_n: int = 10) -> list[dict]:
    """
    RPC: getTokenLargestAccounts. Liefert Liste mit uiAmount/decimals.
    """
    payload = {"jsonrpc": "2.0", "id": 1, "method": "getTokenLargestAccounts", "params": [mint_b58, {"commitment":"confirmed"}]}
    try:
        r = requests.post(RPC_URL, json=payload, timeout=15)
        return ((r.json() or {}).get("result") or {}).get("value") or []
    except Exception:
        return []
        
# =========================
# AUTO-WATCHLIST (Discovery-Loop + Add/Prune)
# =========================
# nutzt: discover_candidates_ds_only, sanity_check_token, WATCHLIST, _ds_get_json,
#        _ds_pick_best_sol_pair, _pair_age_min, _safe_int, _safe_float, _lp_sol_of_pair,
#        send, tg_post, logger

AUTO_DISC_TASK: Optional[asyncio.Task] = None
AW_LOCK = asyncio.Lock()
AW_STATE_PATH = "autowatch_state.json"

AW_ENABLED_DEFAULT      = int(os.getenv("AW_ENABLED_DEFAULT", 1))
AW_INTERVAL_SEC         = int(os.getenv("AW_INTERVAL_SEC", 60))
AW_TOP                  = int(os.getenv("AW_TOP", 12))
AW_MAX_AGE_MIN          = int(os.getenv("AW_MAX_AGE_MIN", 0))
AW_MIN_LP_SOL           = float(os.getenv("AW_MIN_LP_SOL", 0))
AW_MIN_VOL24_USD        = float(os.getenv("AW_MIN_VOL24_USD", 0))
AW_MIN_TX24             = int(os.getenv("AW_MIN_TX24", 0))
AW_QUOTE                = os.getenv("AW_QUOTE", "sol")
AW_HOTLIST              = os.getenv("AW_HOTLIST", "profiles")
AW_PUMPFUN_ONLY         = bool(int(os.getenv("AW_PUMPFUN_ONLY", 0)))
AW_MIN_SCORE            = int(os.getenv("AW_MIN_SCORE", 0))
AW_REQUIRE_OK           = bool(int(os.getenv("AW_REQUIRE_OK", 1)))
AW_PRUNE_INACTIVE_MIN   = int(os.getenv("AW_PRUNE_INACTIVE_MIN", 10))
AW_PRUNE_AGE_MAX_MIN    = int(os.getenv("AW_PRUNE_AGE_MAX_MIN", 0))
AW_MAX_WATCHLIST        = int(os.getenv("AW_MAX_WATCHLIST", 25))
AW_M5_DELTA             = float(os.getenv("AW_M5_DELTA", 0))
AW_SANITY_CONC          = int(os.getenv("AW_SANITY_CONC", 6))
AW_QSCORE_MIN_ADD       = int(os.environ.get("AW_QSCORE_MIN_ADD", "60"))
AW_QSCORE_MIN_OBS       = int(os.environ.get("AW_QSCORE_MIN_OBS", "40"))
AW_SSCORE_MIN_ADD       = int(os.environ.get("AW_SSCORE_MIN_ADD", "70"))
AW_SSCORE_MIN_OBS        = int(os.environ.get("AW_SSCORE_MIN_OBS", "60"))
AW_OBS_TTL_MIN          = int(os.environ.get("AW_OBS_TTL_MIN", "30"))

AW_CFG = {
    "enabled":            AW_ENABLED_DEFAULT,   # 1/0 -> ON/OFF at boot
    "interval_sec":       max(1,   AW_INTERVAL_SEC),
    "run_timeout_sec":    max(5,   AW_RUN_TIMEOUT_SEC),
    "top": AW_TOP,
    "max_age": AW_MAX_AGE_MIN,
    "min_lp": AW_MIN_LP_SOL,
    "min_vol": AW_MIN_VOL24_USD,
    "min_tx": AW_MIN_TX24,
    "quote": AW_QUOTE if AW_QUOTE in ("sol", "any") else "sol",
    "hotlist": AW_HOTLIST if AW_HOTLIST in ("off","trending","approx","boosts","profiles") else "profiles",
    "pumpfun": AW_PUMPFUN_ONLY,
    "min_score": max(0, min(100, AW_MIN_SCORE)),
    "require_ok": AW_REQUIRE_OK,
    "prune_inactive_min": max(5, AW_PRUNE_INACTIVE_MIN),
    "prune_age_max_min": max(0, AW_PRUNE_AGE_MAX_MIN),
    "max_size": max(1, AW_MAX_WATCHLIST),
    "m5_delta": max(0.0, AW_M5_DELTA),
    "sanity_conc": max(1, AW_SANITY_CONC),
    "qscore_min_add":     max(0, min(100, int(os.environ.get("AW_QSCORE_MIN_ADD", "60")))),
    "qscore_min_observe": max(0, min(100, int(os.environ.get("AW_QSCORE_MIN_OBS", "40")))),
    "sscore_min_add":     max(0, min(100, int(os.environ.get("AW_SSCORE_MIN_ADD", "70")))),
    "sscore_min_observe": max(0, min(100, int(os.environ.get("AW_SSCORE_MIN_OBS", "60")))),    
    "mom_enable":        (os.environ.get("AW_MOM_PASS_ENABLE","1").strip().lower() in ("1","true","yes","on")),
    "mom_top":           int(os.environ.get("AW_MOM_TOP","8")),
    "mom_max_age":       int(os.environ.get("AW_MOM_MAX_AGE","180")),
    "mom_min_lp":      float(os.environ.get("AW_MOM_MIN_LP","0.3")),
    "mom_min_vol":     float(os.environ.get("AW_MOM_MIN_VOL","300")),
    "mom_min_tx":        int(os.environ.get("AW_MOM_MIN_TX","8")),
    "mom_m5_min_delta":  int(os.environ.get("AW_MOM_M5_MIN_DELTA","3")),
}

#=================================================================================================

def _aw_load_state() -> dict:
    try:
        with open(AW_STATE_PATH, "r", encoding="utf-8") as f:
            s = json.load(f) or {}
        if not isinstance(s, dict):
            return {"mints": {}, "observed": {}, "last_run_ts": 0}  # ← observed neu
        s.setdefault("mints", {})
        s.setdefault("observed", {})   # ← observed neu
        s.setdefault("last_run_ts", 0)
        return s
    except Exception:
        return {"mints": {}, "observed": {}, "last_run_ts": 0}       # ← observed neu

#=================================================================================================

def _aw_save_state(st: dict) -> None:
    try:
        with open(AW_STATE_PATH, "w", encoding="utf-8") as f:
            json.dump(st, f, ensure_ascii=False, indent=2)
    except Exception:
        pass

#=================================================================================================

AW_STATE = _aw_load_state()

def _aw_extract_best_pair(mint: str) -> dict | None:
    try:
        js = _ds_get_json(f"https://api.dexscreener.com/token-pairs/v1/solana/{mint}", timeout=10)
        pairs = js if isinstance(js, list) else (js.get("pairs") or [])
        return _ds_pick_best_sol_pair(pairs)
    except Exception:
        return None

#=================================================================================================

def _aw_pair_activity(p: dict) -> tuple[int, int | None]:
    """
    Liefert (m5_delta, age_min) für ein Pair.
    """
    try:
        m5 = (p.get("txns") or {}).get("m5") or {}
        m5_delta = _safe_int(m5.get("buys")) - _safe_int(m5.get("sells"))
    except Exception:
        m5_delta = 0
    return m5_delta, _pair_age_min(p)

#=================================================================================================

async def _aw_check_activity_and_age(mint: str) -> tuple[bool, int, int | None]:
    """
    True, wenn 'aktiv' (m5_delta >= cfg.m5_delta). Gibt außerdem delta und age_min zurück.
    """
    p = _aw_extract_best_pair(mint)
    if not p:
        return False, 0, None
    delta, age_m = _aw_pair_activity(p)
    return (delta >= AW_CFG["m5_delta"]), int(delta), age_m

#=================================================================================================

async def _aw_sanity_batch(mints: list[str]) -> dict[str, dict]:
    """
    Sanity parallelisiert, aber mit pro-Token Timeout und sauberem Cancel,
    damit überhängende Tasks nicht den nächsten Run blockieren.
    """
    res: dict[str, dict] = {}
    sem = asyncio.Semaphore(AW_CFG.get("sanity_conc", 4))
    tasks: list[asyncio.Task] = []

    async def _run(m: str) -> tuple[str, dict]:
        async with sem:
            try:
                # pro-Token hart begrenzen
                r = await asyncio.wait_for(sanity_check_token(m), timeout=12)
                return m, r
            except asyncio.TimeoutError:
                return m, {"ok": False, "score": 0, "issues": ["sanity_timeout"], "metrics": {}}
            except Exception as e:
                return m, {"ok": False, "score": 0, "issues": [f"err:{e}"], "metrics": {}}

    for m in mints:
        tasks.append(asyncio.create_task(_run(m)))

    try:
        for t in asyncio.as_completed(tasks):
            m, r = await t
            res[m] = r
    finally:
        # hängende Tasks beenden, falls der aufrufende Run cancelled wurde
        for t in tasks:
            if not t.done():
                t.cancel()
                try:
                    await t
                except Exception:
                    pass

    return res

#=================================================================================================

def _aw_cfg_snapshot_text() -> list[str]:
    return [
        f"hotlist={AW_CFG['hotlist']} | quote={'SOL' if AW_CFG['quote']=='sol' else 'ANY'} | top={AW_CFG['top']}",
        f"gates: age≤{AW_CFG['max_age']}m  lp≥{AW_CFG['min_lp']}  vol24≥${int(AW_CFG['min_vol']):,}  tx24≥{AW_CFG['min_tx']}",
        f"sanity: min_score≥{AW_CFG['min_score']}  require_ok={AW_CFG['require_ok']}",
        f"observe: Q≥{AW_CFG['qscore_min_observe']} & S≥{AW_CFG['sscore_min_observe']}  |  add: Q≥{AW_CFG['qscore_min_add']} & S≥{AW_CFG['sscore_min_add']}",
        f"prune: inactive≥{AW_CFG['prune_inactive_min']}m  age_max={AW_CFG['prune_age_max_min']}m  cap={AW_CFG['max_size']}  m5_delta≥{AW_CFG['m5_delta']}",
        f"loop: every {AW_CFG['interval_sec']}s  conc={AW_CFG['sanity_conc']}",
    ]

#=================================================================================================
async def aw_discover_once() -> dict:
    """
    Budgetierter Durchlauf:
      – Quellen holen
      – Kandidaten stark begrenzen
      – Sanity mit Timeout
      – Add/Observe/Prune
    """
    async with AW_LOCK:
        now = int(time.time())
        added: list[tuple[str, str]] = []
        observed: list[tuple[str, str]] = []
        pruned: list[tuple[str, str]] = []

        prefer_sol = (AW_CFG["quote"] == "sol")
        try:
            core_cands = await discover_candidates_ds_only(
                top_n=AW_CFG["top"],
                max_age_min=AW_CFG["max_age"],
                min_lp_sol=AW_CFG["min_lp"],
                min_vol24_usd=AW_CFG["min_vol"],
                min_tx24=AW_CFG["min_tx"],
                prefer_sol_quote=prefer_sol,
                hotlist=AW_CFG["hotlist"],
                pumpfun_only=AW_CFG["pumpfun"],
                auto_relax=True,
            )
        except Exception as e:
            logger.exception(f"[autowatch] core discovery error: {e}")
            core_cands = []

        already = set(WATCHLIST)
        to_check: list[Candidate] = [c for c in core_cands if c.mint not in already]

        # Momentum-Pass (optional)
        mom_set: set[str] = set()
        if AW_CFG.get("mom_enable", False):
            try:
                mom_cands = await discover_candidates_ds_only(
                    top_n=AW_CFG.get("mom_top", 12),
                    max_age_min=AW_CFG.get("mom_max_age", 180),
                    min_lp_sol=AW_CFG.get("mom_min_lp", 0.3),
                    min_vol24_usd=AW_CFG.get("mom_min_vol", 300.0),
                    min_tx24=AW_CFG.get("mom_min_tx", 8),
                    prefer_sol_quote=True,
                    hotlist="approx",
                    pumpfun_only=False,
                    auto_relax=False,
                )
            except Exception as e:
                logger.exception(f"[autowatch] momentum discovery error: {e}")
                mom_cands = []

            for mc in mom_cands:
                if (mc.mint not in already) and all(c.mint != mc.mint for c in to_check):
                    to_check.append(mc)
                    mom_set.add(mc.mint)

        # Observe-Re-Eval (persist) – HART BEGRENZT, damit Sanity nicht explodiert
        obs_map = AW_STATE.setdefault("observed", {})
        ttl_sec = max(1, int(os.environ.get("AW_OBS_TTL_MIN", "30")) * 60)

        # Früh-TTL-Pruning
        for m, meta in list(obs_map.items()):
            saved_ts = int(meta.get("ts", 0) or 0)
            if now - saved_ts >= ttl_sec:
                obs_map.pop(m, None)
                pruned.append((m, "observe_ttl"))

        # nur die ersten N Observe-Kandidaten zusätzlich prüfen
        OBS_REEVAL_MAX = 20
        for m, meta in list(obs_map.items())[:OBS_REEVAL_MAX]:
            if m in already or any(c.mint == m for c in to_check):
                continue
            try:
                js = _ds_get_json(f"https://api.dexscreener.com/tokens/v1/solana/{m}", timeout=10)
                pairs = js.get("pairs") if isinstance(js, dict) else []
                best = _ds_pick_best_sol_pair(pairs) if pairs else None
                if not best:
                    continue
                score, reasons = _score_pair(best)
                cand = _to_candidate(best, score, reasons)
                to_check.append(cand)
            except Exception as ee:
                logger.debug(f"[autowatch] observe re-eval skip {m}: {ee}")

        # KANDIDATEN CAP – schützt die Sanity-Phase sicher vor Overrun
        MAX_SANITY = max(10, AW_CFG.get("top", 15) + AW_CFG.get("mom_top", 12) + 10)
        if len(to_check) > MAX_SANITY:
            to_check = to_check[:MAX_SANITY]

        # Sanity mit Timeout pro Token
        sanity: dict[str, dict] = await _aw_sanity_batch([c.mint for c in to_check]) if to_check else {}

        def _classify(c: Candidate) -> str:
            rep    = sanity.get(c.mint) or {}
            sscore = int(rep.get("score") or 0)
            ok     = bool(rep.get("ok"))
            qscore = int(c.score or 0)
            m5_delta = int(getattr(c, "m5_buys", 0)) - int(getattr(c, "m5_sells", 0))

            if ok and sscore >= AW_CFG.get("sscore_min_add", 70) and qscore >= AW_CFG.get("qscore_min_add", 60):
                return "add"
            if sscore >= AW_CFG.get("sscore_min_observe", 60) and qscore >= AW_CFG.get("qscore_min_observe", 40):
                return "observe"
            if (c.mint in mom_set) and (sscore >= AW_CFG.get("sscore_min_observe", 60) or m5_delta >= AW_CFG.get("mom_m5_min_delta", 3)):
                return "observe"
            return "drop"

        to_add: list[Candidate] = []
        for c in to_check:
            bucket = _classify(c)
            if bucket == "add":
                to_add.append(c)
            elif bucket == "observe":
                observed.append((c.mint, c.symbol))
                obs_map[c.mint] = {"sym": c.symbol, "ts": now}

        # Add in Watchlist (cap)
        for c in to_add:
            if c.mint in WATCHLIST:
                continue
            if len(WATCHLIST) >= AW_CFG["max_size"]:
                break
            WATCHLIST.append(c.mint)
            AW_STATE["mints"][c.mint] = {
                "added_ts": now,
                "last_active_ts": now,
                "last_score": int(c.score),
                "source": AW_CFG["hotlist"] or "search",
            }
            added.append((c.mint, c.symbol))
            obs_map.pop(c.mint, None)

        # Prune Inaktivität/Alter
        for m in list(WATCHLIST):
            active, delta, age_m = await _aw_check_activity_and_age(m)
            st = AW_STATE["mints"].setdefault(m, {"added_ts": now, "last_active_ts": now, "last_score": 0, "source": "unknown"})
            if active:
                st["last_active_ts"] = now
            if AW_CFG["prune_age_max_min"] > 0 and (age_m is not None) and (age_m > AW_CFG["prune_age_max_min"]):
                WATCHLIST.remove(m); AW_STATE["mints"].pop(m, None); pruned.append((m, "age")); continue
            if (now - int(st.get("last_active_ts") or now)) >= AW_CFG["prune_inactive_min"] * 60:
                WATCHLIST.remove(m); AW_STATE["mints"].pop(m, None); pruned.append((m, "inactive"))

        # Kappung
        if len(WATCHLIST) > AW_CFG["max_size"]:
            ordered = sorted(WATCHLIST,
                             key=lambda x: ((AW_STATE["mints"].get(x, {}).get("last_active_ts") or 0),
                                            (AW_STATE["mints"].get(x, {}).get("last_score") or 0)),
                             reverse=True)
            keep = set(ordered[:AW_CFG["max_size"]])
            for m in list(WATCHLIST):
                if m not in keep:
                    WATCHLIST.remove(m)
                    AW_STATE["mints"].pop(m, None)
                    pruned.append((m, "cap"))

        AW_STATE["last_run_ts"] = now
        _aw_save_state(AW_STATE)
        return {"added": added, "observed": observed, "pruned": pruned, "n": len(core_cands)}

        
#=================================================================================================

async def aw_loop():
    """
    Auto-Watchlist-Loop:
      – aw_discover_once() mit Run-Timeout
      – Telegram-Summary / Timeout-Hinweis
      – intervallgenaues Sleep
    """
    while AW_CFG.get("enabled"):
        t0 = time.time()
        res = None
        run_timeout = int(os.environ.get("AW_RUN_TIMEOUT_SEC", "60"))
        interval    = int(AW_CFG.get("interval_sec", 60))

        try:
            res = await asyncio.wait_for(aw_discover_once(), timeout=run_timeout)
            if res:
                a = ", ".join([f"{s}({m[:6]}…)" for m, s in res.get("added", [])]) or "-"
                o = ", ".join([f"{s}({m[:6]}…)" for m, s in res.get("observed", [])]) or "-"
                p = ", ".join([f"{m[:6]}…:{r}" for m, r in res.get("pruned", [])]) or "-"

                obs_persist_map = AW_STATE.get("observed", {}) or {}
                obs_persist = ", ".join([f"{v.get('sym','?')}({k[:6]}…)" for k, v in list(obs_persist_map.items())[:8]]) or "-"

                lines = [
                    "🤖 Auto-Watchlist (run)",
                    f"added: {a}",
                    f"observe: {o}",
                    f"observing(persist): {obs_persist}",
                    f"pruned: {p}",
                    *(_aw_cfg_snapshot_text()),
                ]
                try:
                    await tg_post("\n".join(lines))
                except Exception:
                    pass

        except asyncio.TimeoutError:
            logger.warning("autobot:[autowatch] discover timeout (> %ss)", run_timeout)
            try:
                await tg_post(f"⏱️ Auto-Watchlist: run timeout (> {run_timeout}s)")
            except Exception:
                pass
        except Exception as e:
            logger.exception("[autowatch loop] %s", e)

        elapsed = time.time() - t0
        sleep_left = max(0.0, float(interval) - float(elapsed))
        while sleep_left > 0 and AW_CFG.get("enabled"):
            await asyncio.sleep(min(1.0, sleep_left))
            sleep_left -= 1.0

# ======================= UNIFIED SANITY (extended) ============================
# Erweitert dein Sanity um:
#  (1) Liquidity-Layer: Raydium/Orca/Meteora Referenzen via getProgramAccounts
#  (2) Activity-Check  : letzte 60m (RPC-best effort; Helius optional)
#  (3) Holder-Plus     : Moralis (optional) + Burn-Anteil + RPC largest accounts
#  (4) Metaplex UpdateAuthority (optional via Helius)
#
# KEINE strengeren KO-Gates: KO bleibt nur bei no_ds_pair, route_wsol_fail, top10>=0.90
# Benötigt: http_get, _ds_get_json, _lp_sol_of_pair, _pair_age_min,
#           WSOL_MINT, USDC_MINT, WALLET_PUBKEY, GMGN_SLIPPAGE_PCT, GMGN_FEE_SOL,
#           gmgn_get_route_safe, client (solana.rpc.api.Client), get_mint_decimals_async, Pubkey

import os, time, base64, asyncio, requests
from typing import Dict, Any, List, Optional
from solders.pubkey import Pubkey

MORALIS_API_KEY = os.environ.get("MORALIS_API_KEY", "").strip()
HELIUS_API_KEY  = os.environ.get("HELIUS_API_KEY",  "").strip()

# ---- Program-IDs & Offsets (per ENV konfigurierbar; leer -> Skip) ----------
# CSV mit Program IDs; du kannst sie in ENV überschreiben:
RAYDIUM_PROGRAMS = [p.strip() for p in os.environ.get("RAYDIUM_PROGRAMS","").split(",") if p.strip()]
ORCA_PROGRAMS    = [p.strip() for p in os.environ.get("ORCA_PROGRAMS","").split(",") if p.strip()]
METEORA_PROGRAMS = [p.strip() for p in os.environ.get("METEORA_PROGRAMS","").split(",") if p.strip()]
# Memcmp-Offsets (Bytes) für mintA/mintB in den Pool-Accounts; je DEX verschieden.
# Per ENV überschreibbar; wenn unbekannt → leeres Array (Check wird übersprungen).
def _parse_offsets(env_key: str) -> List[int]:
    v = os.environ.get(env_key,"").strip()
    if not v: return []
    try:
        return [int(x) for x in v.split(",") if x.strip()!=""]
    except Exception:
        return []

OFFSETS_RAYDIUM = _parse_offsets("RAYDIUM_MINT_OFFSETS")  # z.B. "72,104"
OFFSETS_ORCA    = _parse_offsets("ORCA_MINT_OFFSETS")     # z.B. "8,40"
OFFSETS_METEORA = _parse_offsets("METEORA_MINT_OFFSETS")  # z.B. "120,152"

# Burn-/Dead-Wallets (heuristisch)
BURN_ADDRESSES = {
    "11111111111111111111111111111111",
    # ggf. weitere bekannte Burn-Receiver hier ergänzen
}

# ------------------------- Helfer: RPC Raw Calls -----------------------------
def _rpc(method: str, params: list, timeout: int = 15) -> dict:
    try:
        r = requests.post(RPC_URL, json={"jsonrpc":"2.0","id":1,"method":method,"params":params}, timeout=timeout)
        return r.json() or {}
    except Exception:
        return {}

def _b58(m: str) -> str:
    return m  # base58 als String in RPC-Filtern

def _memcmp_filter(offset: int, b58: str) -> dict:
    return {"memcmp": {"offset": offset, "bytes": b58}}

def _count_liquidity_refs(program_ids: List[str], mint: str, offsets: List[int]) -> int:
    """Zähle Pools, die mint an einem der Offsets enthalten (best-effort)."""
    if not program_ids or not offsets:
        return 0
    total = 0
    for pid in program_ids:
        try:
            filters = [{"dataSize": None}]  # dummy; dataSize optional
            # Für jedes Offset ein eigener Call; addiere Treffer
            for off in offsets:
                res = _rpc("getProgramAccounts", [
                    pid,
                    {"encoding":"base64", "filters":[_memcmp_filter(off, _b58(mint))]}
                ])
                arr = ((res.get("result") or []))
                total += len(arr)
        except Exception:
            continue
    return total

async def _count_liquidity_refs_async(mint: str) -> dict:
    """Zähle Referenzen auf Raydium/Orca/Meteora (parallel)."""
    async def _tgt(progs, offs):
        return await asyncio.to_thread(_count_liquidity_refs, progs, mint, offs)

    ray = await _tgt(RAYDIUM_PROGRAMS, OFFSETS_RAYDIUM) if RAYDIUM_PROGRAMS and OFFSETS_RAYDIUM else 0
    orc = await _tgt(ORCA_PROGRAMS,    OFFSETS_ORCA)    if ORCA_PROGRAMS    and OFFSETS_ORCA    else 0
    met = await _tgt(METEORA_PROGRAMS, OFFSETS_METEORA) if METEORA_PROGRAMS and OFFSETS_METEORA else 0
    return {"raydium_refs": ray, "orca_refs": orc, "meteora_refs": met, "total_liq_refs": ray+orc+met}

# ----------------------- Activity (60m) – best effort ------------------------
async def _rpc_async(method: str, params: list, timeout: int) -> dict:
    return await asyncio.to_thread(_rpc, method, params, timeout)

async def _recent_activity_60m(best_pair_addr: Optional[str]) -> dict:
    """
    Best-effort Aktivität: distinct signers & tx count der letzten ~60m.
    Weniger RPC-Last: nur wenige getTransaction-Reads.
    """
    out = {"tx_60m": 0, "uniq_signers_60m": 0}
    if not best_pair_addr:
        return out
    try:
        now = time.time()
        sigs_obj = _rpc("getSignaturesForAddress", [best_pair_addr, {"limit": 100}])
        sigs = sigs_obj.get("result") or []
        recent = [s for s in sigs if (abs(int(s.get("blockTime") or now) - now) <= 3600)]
        out["tx_60m"] = len(recent)

        # deutlich weniger Detail-Reads (war: 25)
        uniq = set()
        for s in recent[:8]:
            sig = s.get("signature")
            if not sig:
                continue
            tx = _rpc("getTransaction", [sig, {"encoding": "json"}]).get("result") or {}
            msg = ((tx.get("transaction") or {}).get("message") or {})
            accs = msg.get("accountKeys") or []
            if accs:
                pk = accs[0].get("pubkey") if isinstance(accs[0], dict) else accs[0]
                if pk:
                    uniq.add(pk)
        out["uniq_signers_60m"] = len(uniq)
    except Exception:
        pass
    return out



# ------------------------ Holder/Concentration --------------------------------
def _moralis_top_share(mint: str, limit: int = 10) -> Optional[float]:
    if not MORALIS_API_KEY:
        return None
    try:
        url = "https://solana-gateway.moralis.io/token/mainnet/holders"
        headers = {"accept":"application/json", "X-API-Key": MORALIS_API_KEY}
        params = {"address": mint, "limit": str(limit)}
        r = requests.get(url, headers=headers, params=params, timeout=12)
        if r.status_code != 200: return None
        j = r.json() or {}
        holders = j.get("result") or j.get("holders") or []
        supply  = float(j.get("supply") or 0.0)
        if not holders or supply <= 0: return None
        top = 0.0
        for h in holders[:limit]:
            try: top += float(h.get("uiAmount") or h.get("amount") or 0.0)
            except Exception: pass
        return top/supply if supply>0 else None
    except Exception:
        return None

def _burn_share_from_list(largest: list[dict]) -> float:
    """Anteil der Burn/Dead-Adressen in Top-Accounts (0..1)."""
    total = sum(float((a.get("uiAmount") or 0.0)) for a in largest[:10])
    if total <= 0: return 0.0
    burn = 0.0
    for a in largest[:10]:
        owner = a.get("address") or a.get("owner") or a.get("addressId") or ""
        if owner in BURN_ADDRESSES:
            try: burn += float(a.get("uiAmount") or 0.0)
            except Exception: pass
    return burn/total if total>0 else 0.0

# ------------------------ Metaplex UpdateAuthority (optional) -----------------
def _get_update_authority_via_helius(mint: str) -> Optional[str]:
    """Nur Info-Zusatz; KO-neutral. Benötigt HELIUS_API_KEY."""
    if not HELIUS_API_KEY:
        return None
    try:
        url = f"https://api.helius.xyz/v0/token-metadata?api-key={HELIUS_API_KEY}"
        data = {"mintAccounts":[mint], "disableCache": False}
        r = requests.post(url, json=data, timeout=12)
        if r.status_code != 200: return None
        j = r.json() or []
        if not j: return None
        au = ((j[0].get("onChainMetadata") or {}).get("metadata") or {}).get("updateAuthority")
        return au or None
    except Exception:
        return None

# --------------------------- Sanity (einheitlich) -----------------------------
async def sanity_check_token(
    mint: str,
    *,
    min_liq_sol: float = 1.0,
    min_vol24: float  = 2000.0,
    min_tx24: int     = 50,
    min_age_min: int  = 3,
) -> dict:
    # --- Mint normalisieren (URL/String → erstes Base58-Match 32..44) ---
    if not _looks_like_solana_addr(mint):
        m = _SOLANA_ADDR_RE.search(mint or "")
        if m:
            mint = m.group(0)

    rep: Dict[str, Any] = {"mint": mint, "ok": True, "issues": [], "score": 100, "metrics": {}}

    # a) DexScreener Basics (robustes Parsing: dict["pairs"] ODER direktes Array)
    js = _ds_get_json(f"https://api.dexscreener.com/token-pairs/v1/solana/{mint}", timeout=10)
    pairs = []
    if isinstance(js, list):
        pairs = js
    elif isinstance(js, dict):
        pairs = (js.get("pairs") or js.get("data") or [])
    if not pairs:
        rep["ok"] = False; rep["issues"].append("no_ds_pair"); rep["score"] -= 40; return rep

    # bestes Solana-Pair nach USD-LP wählen
    sol_pairs = [p for p in pairs if (p.get("chainId") or "").lower()=="solana"]
    cand = sol_pairs if sol_pairs else pairs
    def _liq_usd(p):
        try: return float(((p.get("liquidity") or {}).get("usd")) or 0.0)
        except Exception: return 0.0
    cand.sort(key=_liq_usd, reverse=True)
    best = cand[0]

    lp_sol  = _lp_sol_of_pair(best)
    vol24   = float(((best.get("volume") or {}).get("h24") or 0.0))
    txh     = (best.get("txns") or {}).get("h24") or {}
    tx24    = int(txh.get("buys") or 0) + int(txh.get("sells") or 0)
    age_min = _pair_age_min(best)
    pair_addr = best.get("pairAddress")

    rep["metrics"].update({"lp_sol": lp_sol, "vol24": vol24, "tx24": tx24, "age_min": age_min})

    # harte Gates
    if lp_sol < min_liq_sol: rep["ok"]=False; rep["issues"].append("low_liquidity"); rep["score"]-=20
    if vol24 < min_vol24:    rep["issues"].append("low_vol24");     rep["score"]-=10
    if tx24  < min_tx24:     rep["issues"].append("low_tx24");      rep["score"]-=10
    if (age_min is not None) and (age_min < min_age_min): rep["issues"].append("very_new"); rep["score"]-=10

    # b) Route-Checks (KO nur wSOL) – asynchron + hart begrenzt
    try:
        await asyncio.wait_for(
            gmgn_get_route_async(
                WSOL_MINT, mint, lamports(0.01),
                WALLET_PUBKEY, GMGN_SLIPPAGE_PCT, GMGN_FEE_SOL, True
            ),
            timeout=20
        )
    except Exception:
        rep["issues"].append("route_wsol_fail"); rep["score"] -= 15; rep["ok"] = False

    # USDC→mint optional (per ENV SANITY_SKIP_USDC_ROUTE=1 ausblendbar)
    if not (os.environ.get("SANITY_SKIP_USDC_ROUTE", "0").strip().lower() in ("1","true","on","yes")):
        try:
            await asyncio.wait_for(
                gmgn_get_route_async(
                    USDC_MINT, mint, 1_000_000,
                    WALLET_PUBKEY, GMGN_SLIPPAGE_PCT, GMGN_FEE_SOL, True
                ),
                timeout=20
            )
        except Exception:
            rep["issues"].append("route_usdc_fail"); rep["score"] -= 8

    # c) Liquidity-Refs
    liq_refs = await _count_liquidity_refs_async(mint)
    rep["metrics"].update(liq_refs)
    rep["score"] += min(4, liq_refs.get("total_liq_refs",0))

    # d) Activity 60m
    act = await _recent_activity_60m(pair_addr)
    rep["metrics"].update(act)
    if act.get("tx_60m",0) >= 50:      rep["score"] += 3
    elif act.get("tx_60m",0) >= 15:    rep["score"] += 1
    if act.get("uniq_signers_60m",0) >= 20:  rep["score"] += 2

    # e) Mint-Authorities & Supply
    info = rpc_get_mint_info_jsonparsed(mint)
    if info:
        freeze_auth = info.get("freezeAuthority")
        mint_auth   = info.get("mintAuthority")
        decimals    = int(info.get("decimals") or 9)
        supply_raw  = int(info.get("supply")   or 0)
        supply      = supply_raw / (10 ** max(decimals,0))
        rep["metrics"].update({"freezeAuthority": freeze_auth or None, "mintAuthority": mint_auth or None,
                               "decimals": decimals, "supply": supply})
        if freeze_auth: rep["issues"].append("freeze_authority_set"); rep["score"] -= 6
        if mint_auth:   rep["issues"].append("mint_authority_set");   rep["score"] -= 5
    else:
        rep["issues"].append("no_mint_info"); rep["score"] -= 5

    # f) Holder-Konzentration + Burn-Anteil
    share = _moralis_top_share(mint, limit=10)
    largest = []
    if share is None:
        try:
            largest = rpc_get_token_largest_accounts(mint, top_n=10)
            top10 = sum(float(a.get("uiAmount") or 0.0) for a in largest[:10])
            ts = await asyncio.to_thread(client.get_token_supply, Pubkey.from_string(mint))
            try:
                supply_total = int(ts.value.amount)/(10**int(ts.value.decimals))
            except Exception:
                dec = await get_mint_decimals_async(mint)
                supply_total = float(getattr(ts.value,"ui_amount_string",0.0)) or (int(ts.value.amount)/(10**dec))
            share = (top10/supply_total) if supply_total>0 else None
        except Exception:
            share = None
    if share is not None:
        rep["metrics"]["top10_share"] = share
        if share >= 0.90: rep["issues"].append("top10_concentration_very_high"); rep["score"] -= 15; rep["ok"]=False
        elif share >= 0.80: rep["issues"].append("top10_concentration_high");   rep["score"] -= 8
        elif share >= 0.70: rep["issues"].append("top10_concentration_elevated"); rep["score"] -= 4

    if not largest:
        try: largest = rpc_get_token_largest_accounts(mint, top_n=10)
        except Exception: largest = []
    burn_share = _burn_share_from_list(largest) if largest else 0.0
    rep["metrics"]["burn_share_top10"] = burn_share
    if burn_share >= 0.05: rep["score"] += 2

    # g) Metaplex UpdateAuthority (optional)
    upd = _get_update_authority_via_helius(mint)
    if upd:
        rep["metrics"]["updateAuthority"] = upd
        rep["score"] -= 2

    rep["score"] = max(0, min(100, int(rep["score"])))
    return rep


# ===================== END UNIFIED SANITY (extended) ==========================
# =========================
# Liquidity-Check Command
# =========================
async def cmd_check_liqui(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not guard(update):
        return
    if not context.args:
        return await send(update, "Nutzung: /check_liq <MINT>")
    mint = context.args[0].strip()

    await send(update, f"🔍 Prüfe Liquidity-Layer für {mint[:6]}…")

    try:
        refs = await _count_liquidity_refs_async(mint)
        ray = refs.get("raydium_refs", 0)
        orc = refs.get("orca_refs", 0)
        met = refs.get("meteora_refs", 0)
        tot = refs.get("total_liq_refs", 0)

        ray_txt = "✅" if ray > 0 else "❌"
        orc_txt = "✅" if orc > 0 else "❌"
        met_txt = "✅" if met > 0 else "❌"

        lines = [
            f"🧩 <b>Liquidity-Layer Check</b>",
            f"Raydium: {ray_txt} ({ray})",
            f"Orca: {orc_txt} ({orc})",
            f"Meteora: {met_txt} ({met})",
            "",
            f"Total Pools: <b>{tot}</b>",
        ]
        await update.effective_chat.send_message("\n".join(lines), parse_mode=ParseMode.HTML)

    except Exception as e:
        await send(update, f"❌ Fehler bei Liquidity-Check: {e}")
# ------------------------------------------------------------------------------
# --- GMGN Preis-Fallbacks ---
def gmgn_get_route(token_in: str, token_out: str, in_amount: int,
                   from_addr: str, slippage_pct: float, fee_sol: float,
                   anti_mev: bool = True) -> dict:
    """
    Holt eine Swap-Route + (falls möglich) eine rohe Swap-Transaction von GMGN.
    - in_amount: Basis-Einheiten (z.B. Lamports bei SOL)
    - slippage_pct: Prozent (z.B. 0.5 für 0,5 %)
    - fee_sol: GMGN/MEV-Fee in SOL
    Gibt ein Dict zurück, das mindestens 'quote' enthält und bei TX-Build 'raw_tx'.
    """
    url = "https://gmgn.ai/defi/router/v1/sol/tx/get_swap_route"
    hdr = {"accept": "application/json"}

    params = {
        "inTokenAddress": token_in,
        "outTokenAddress": token_out,
        "tokenIn": token_in,
        "tokenOut": token_out,
        "amount": str(in_amount),
        "inAmount": str(in_amount),
        "from": from_addr,
        "userPublicKey": from_addr,
        "slippage": float(slippage_pct),
        "slippageBps": int(round(slippage_pct * 100)),
        "fee": float(fee_sol),
        "platformFee": float(fee_sol),
        "antiMEV": "true" if anti_mev else "false",
        "antiMev": "true" if anti_mev else "false",
    }

    r = http_get(url, params=params, headers=hdr, timeout=GMGN_HTTP_TIMEOUT)
    ct = (r.headers.get("content-type") or "").lower()
    if "application/json" not in ct:
        raise RuntimeError(f"GMGN non-json ct={ct}")

    j = r.json() or {}
    if j.get("code") == 0 and "data" in j:
        return j["data"]
    if "data" in j:
        return j["data"]
    if "raw_tx" in j or "quote" in j:
        return j

    raise RuntimeError(f"GMGN route error: {j}")

#=================================================================================================

def gmgn_get_route_safe(token_in: str, token_out: str, in_amount: int,
                        from_addr: str, slippage_pct: float, fee_sol: float) -> dict:
    try:
        return gmgn_get_route(token_in, token_out, in_amount, from_addr, slippage_pct, fee_sol, True)
    except Exception:
        # Fallback ohne Anti-MEV
        return gmgn_get_route(token_in, token_out, in_amount, from_addr, slippage_pct, fee_sol, False)

#=================================================================================================

def _get_wsol_usd() -> float:
    # 1) Birdeye
    be, _ = birdeye_price_detailed(WSOL_MINT)
    if be > 0:
        return be
    # 2) GMGN Route wSOL -> USDC
    try:
        d = gmgn_get_route_safe(WSOL_MINT, USDC_MINT, int(0.01 * 1_000_000_000),
                                WALLET_PUBKEY, GMGN_SLIPPAGE_PCT, GMGN_FEE_SOL)
        out = float((d.get("quote") or {}).get("outAmount") or 0.0) / 1_000_000.0
        if out > 0:
            return out / 0.01
    except Exception:
        pass
    # 3) DexScreener
    ds = dexscreener_price_usd(WSOL_MINT)
    return ds if ds > 0 else 0.0

#=================================================================================================

def gmgn_quote_price_usd(mint: str, wsol_in_sol: float = 0.01) -> float:
    """
    Ermittelt den USD-Preis des Tokens über eine kleine WSOL→Token Route.
    Nutzt den WSOL/USD-Preis zur Umrechnung.
    """
    try:
        # WICHTIG: gmgn_get_route_safe hat KEIN anti_mev-Argument in der Signatur
        data = gmgn_get_route_safe(
            WSOL_MINT, mint, lamports(wsol_in_sol),
            WALLET_PUBKEY, GMGN_SLIPPAGE_PCT, GMGN_FEE_SOL
        )
        q = (data.get("quote") or {})
        out_amt = float(q.get("outAmount") or 0.0)
        out_dec = int(q.get("outDecimals") or q.get("outDecimal") or _DECIMALS_CACHE.get(mint) or 9)
        out_dec = max(0, min(18, out_dec))
        if out_amt <= 0:
            return 0.0
        token_qty = out_amt / (10 ** out_dec)
        if token_qty <= 0:
            return 0.0
        wsol_usd = _get_wsol_usd()
        if wsol_usd <= 0:
            return 0.0
        usd_in = wsol_in_sol * wsol_usd
        return usd_in / token_qty if token_qty > 0 else 0.0
    except Exception:
        return 0.0


#=================================================================================================

def gmgn_quote_price_usd_v2(mint: str) -> float:
    try:
        data = gmgn_get_route_safe(USDC_MINT, mint, 1_000_000, WALLET_PUBKEY, GMGN_SLIPPAGE_PCT, GMGN_FEE_SOL)
        q = (data.get("quote") or {})
        out_amt = float(q.get("outAmount") or 0.0)
        dec = int(q.get("outDecimals") or q.get("outDecimal") or _DECIMALS_CACHE.get(mint) or 9)
        dec = max(0, min(18, dec))
        if out_amt <= 0: return 0.0
        token_qty = out_amt / (10 ** dec)
        return 1.0 / token_qty if token_qty > 0 else 0.0
    except Exception:
        return 0.0
        
#=================================================================================================

def get_price_usd_src(mint: str) -> Tuple[float, str, str]:
    try:
        px, reason = birdeye_price_detailed(mint)
        if px > 0: return px, "birdeye", reason
        be_reason = reason
    except Exception as e:
        be_reason = f"exception {e}"
    try:
        px = gmgn_quote_price_usd(mint)
        if px > 0: return px, "gmgn-wsol", be_reason
    except Exception:
        pass
    try:
        px = gmgn_quote_price_usd_v2(mint)
        if px > 0: return px, "gmgn-usdc", be_reason
    except Exception:
        pass
    try:
        px = dexscreener_price_usd(mint)
        if px > 0: return px, "dexscreener", be_reason
    except Exception:
        pass
    return 0.0, "none", be_reason

def get_price_usd(mint: str) -> float:
    px,_,_=get_price_usd_src(mint); return px

# =========================
# On-chain / Token
# =========================
def rpc_get_spl_balance(owner_b58: str, mint_b58: str) -> float:
    payload = {
        "jsonrpc": "2.0", "id": 1, "method": "getTokenAccountsByOwner",
        "params": [owner_b58, {"mint": mint_b58}, {"encoding": "jsonParsed", "commitment": "confirmed"}],
    }
    try:
        r = requests.post(RPC_URL, json=payload, timeout=20); r.raise_for_status(); j=r.json()
        value = ((j.get("result") or {}).get("value") or [])
        if not value: return 0.0
        total = 0.0
        for acc in value:
            try:
                ui = acc["account"]["data"]["parsed"]["info"]["tokenAmount"]["uiAmount"]; total += float(ui or 0.0)
            except Exception:
                pass
        return total
    except Exception:
        return 0.0

_DECIMALS_CACHE: Dict[str,int]={}
async def get_mint_decimals_async(mint: str) -> int:
    if mint in _DECIMALS_CACHE: return _DECIMALS_CACHE[mint]
    resp = await asyncio.to_thread(client.get_token_supply, Pubkey.from_string(mint))
    dec = int(resp.value.decimals); _DECIMALS_CACHE[mint] = dec; return dec

def get_token_balance(owner:str, mint:str)->float: return rpc_get_spl_balance(owner, mint)
def lamports(sol: float)->int: return int(round(sol*1_000_000_000))

#=================================================================================================
# GMGN Routing/Exec (TX)
# =========================
def rpc_send_signed_b64(signed_b64: str) -> dict:
    payload = {"jsonrpc": "2.0", "id": 1, "method": "sendTransaction",
               "params": [signed_b64, {"encoding":"base64","preflightCommitment":"confirmed","skipPreflight":False}]}
    r = requests.post(RPC_URL, json=payload, timeout=20)
    j = r.json() if r.headers.get("content-type","").lower().startswith("application/json") else {}
    if "error" in j: raise RuntimeError(f"RPC error: {j['error']}")
    return {"result": j.get("result")}

def _shortvec_decode(b: bytes, start: int) -> tuple[int, int]:
    acc = 0; size = 0; shift = 0
    while True:
        v = b[start + size]; acc |= (v & 0x7F) << shift; size += 1
        if (v & 0x80) == 0: break; shift += 7
    return acc, size

def _shortvec_encode(n: int) -> bytes:
    out = bytearray()
    while True:
        w = n & 0x7F; n >>= 7; out.append(0x80|w if n else w)
        if not n: break
    return bytes(out)

def sign_raw_b64(raw_b64: str) -> str:
    raw = base64.b64decode(raw_b64); i = 0
    versioned = (raw[0] & 0x80) != 0
    if versioned: i = 1
    sig_count, n = _shortvec_decode(raw, i); i += n
    msg_off = i + sig_count*64
    if msg_off > len(raw): raise RuntimeError("Roh-TX beschädigt.")
    if sig_count not in (0,1): raise RuntimeError(f"Tx erwartet {sig_count} Signaturen – nur 0/1 unterstützt.")
    msg_bytes = raw[msg_off:]; sig = KP.sign_message(msg_bytes)
    out = bytearray(); 
    if versioned: out.append(raw[0])
    out += _shortvec_encode(1); out += bytes(sig); out += msg_bytes
    return base64.b64encode(bytes(out)).decode()

async def wait_for_confirmation(signature: str, timeout_sec: float = 60.0) -> str:
    sig_obj = Sig.from_string(signature); t0 = time.time()
    while time.time() - t0 < timeout_sec:
        try:
            resp = await asyncio.to_thread(client.get_signature_statuses, [sig_obj])
            s = resp.value[0]
            if s and s.confirmation_status and ("confirmed" in str(s.confirmation_status) or "finalized" in str(s.confirmation_status)):
                return "confirmed"
        except Exception:
            pass
        await asyncio.sleep(0.9)
    if HELIUS_API_KEY:
        try:
            url = f"https://api.helius.xyz/v0/transactions?api-key={HELIUS_API_KEY}"
            r = http_post(url, json_body={"transactions":[signature]}, timeout=12); j = r.json()
            if isinstance(j, list) and j:
                meta = j[0].get("meta") or {}; err = meta.get("err")
                conf = j[0].get("confirmationStatus") or j[0].get("confirmations")
                if err is None and (conf=="confirmed" or conf=="finalized" or (isinstance(conf,int) and conf>=1)):
                    return "confirmed"
        except Exception:
            pass
    return "timeout"


#=================================================================================================
# Positions- & PnL-Helpers
# =========================
class Position:
    def __init__(self, mint: str, entry_price_usd: float, qty_tokens: float):
        self.mint = mint; self.entry_price = entry_price_usd; self.qty = qty_tokens

OPEN_POS: Dict[str, Position] = {}

def position_unreal_pnl(pos: Position, px: float) -> float: return (px - pos.entry_price) * pos.qty

def total_unreal_pnl() -> tuple[float, list[str]]:
    mints = list(OPEN_POS.keys())
    if not mints: return 0.0, []
    price_map = birdeye_price_multi(mints); unreal = 0.0; rows=[]
    for m, pos in OPEN_POS.items():
        px = float(price_map.get(m, 0.0))
        if px > 0:
            u = position_unreal_pnl(pos, px); unreal += u
            rows.append(f"- {m[:6]}… qty={pos.qty:.4f} | cost={pos.entry_price:.6f} | px={px:.6f} | U={u:.2f} USD")
        else:
            rows.append(f"- {m[:6]}… qty={pos.qty:.4f} | Preis n/a")
    return unreal, rows

#=================================================================================================
# Execution Helpers (BUY/SELL)
# =========================
async def rpc_send_signed_b64_async(signed_b64: str) -> dict:
    return await asyncio.to_thread(rpc_send_signed_b64, signed_b64)

async def gmgn_get_route_async(token_in: str, token_out: str, in_amount: int,
                               from_addr: str, slippage_pct: float, fee_sol: float,
                               anti_mev: bool = True) -> dict:
    return await asyncio.to_thread(gmgn_get_route, token_in, token_out, in_amount, from_addr, slippage_pct, fee_sol, anti_mev)

async def birdeye_price_async(mint: str, chain: str = "sol") -> float:
    return await asyncio.to_thread(birdeye_price, mint, chain)

async def rpc_get_spl_balance_async(owner_b58: str, mint_b58: str) -> float:
    return await asyncio.to_thread(rpc_get_spl_balance, owner_b58, mint_b58)

async def refresh_qty_from_chain_async(mint: str) -> float:
    bal = await rpc_get_spl_balance_async(WALLET_PUBKEY, mint)
    if mint in OPEN_POS: OPEN_POS[mint].qty = bal
    return bal

# ======= PAPER MODE (ENV-gesteuert) =======
# PAPER_MODE=1         -> Papiersimulation EIN
# PAPER_FEE_BPS=20     -> simulierte Fee in Basispunkten (0.20 %)
# PAPER_MODE = os.environ.get("PAPER_MODE", "0").strip().lower() in ("1", "true", "yes", "on")
# PAPER_FEE_BPS = float(os.environ.get("PAPER_FEE_BPS", "20"))  # 20 bps = 0.20 %

def _paper_sig() -> str:
    return f"paper-{int(time.time()*1000)}"

#--- Robuste Preisbeschaffung für Executions (mit Retries + Hint) ---
def _try_sources_for_price(mint: str) -> float:
    """
    Versucht mehrere Quellen in sinnvoller Reihenfolge.
    Gibt 0.0 zurück, wenn *alle* Quellen versagen.
    """
    # 1) GMGN route basierend auf USDC (direkte USD-Quote)
    px = gmgn_quote_price_usd_v2(mint)
    if px > 0: return px
    # 2) GMGN route WSOL -> Token
    px = gmgn_quote_price_usd(mint)
    if px > 0: return px
    # 3) Birdeye (Single)
    px = birdeye_price(mint)
    if px > 0: return px
    # 4) DexScreener
    px = dexscreener_price_usd(mint)
    if px > 0: return px
    # 5) Als allerletztes: Multi-Call (falls Mint in Liste; spart Rate, wenn allein)
    try:
        mp = birdeye_price_multi([mint])
        px = float(mp.get(mint, 0.0) or 0.0)
        if px > 0: return px
    except Exception:
        pass
    return 0.0

def get_price_for_execution(mint: str, *, mkt_price_hint: float | None = None,
                            retries: int = 3, sleep_s: float = 0.4) -> float:
    """
    Robust für BUY/SELL-Logging: mehrere Versuche + optionaler Preis-Hint (z. B. letzter Bar-Close).
    Reihenfolge:
      - Direkter Versuch via _try_sources_for_price()
      - leichte Pausen/Retrys
      - Falls alles 0: benutze mkt_price_hint (>0) als letzte Instanz
      - Falls immer noch 0: Exception
    """
    # Direkt
    px = _try_sources_for_price(mint)
    if px > 0:
        return px

    # Retries mit kurzem Schlaf (vermeidet Race/Ratelimit)
    for _ in range(max(0, retries)):
        time.sleep(sleep_s)
        px = _try_sources_for_price(mint)
        if px > 0:
            return px

    # Notlösung: nutze den letzten bekannten Marktpreis (z. B. Bar-Close)
    if mkt_price_hint and float(mkt_price_hint) > 0:
        return float(mkt_price_hint)

    # Aufgeben: besser Exception als PnL=Katastrophe
    raise RuntimeError("Kein gültiger Preis für Execution erhalten (alle Quellen 0).")


#=================================================================================================

async def _paper_buy_wsol_to_token(mint: str, notional_sol: float, mkt_price_usd: float) -> dict:
    """
    Paper-Buy: SOL-Notional → Token-Menge; Fee in BPS wird abgezogen.
    """
    global OPEN_POS
    wsol_usd = _get_wsol_usd()
    if wsol_usd <= 0:
        raise RuntimeError("Paper-BUY: Kein WSOL-USD-Preis")

    if mkt_price_usd <= 0:
        mkt_price_usd = get_price_usd(mint)
        if mkt_price_usd <= 0:
            raise RuntimeError("Paper-BUY: Kein Token-USD-Preis")

    usd_in   = notional_sol * wsol_usd
    qty_gross = usd_in / mkt_price_usd
    fee_qty   = qty_gross * (PAPER_FEE_BPS / 10_000.0)
    qty_net   = max(0.0, qty_gross - fee_qty)

    if mint in OPEN_POS and OPEN_POS[mint].qty > 0:
        pos = OPEN_POS[mint]
        new_qty = pos.qty + qty_net
        pos.entry_price = (pos.entry_price * pos.qty + mkt_price_usd * qty_net) / new_qty
        pos.qty = new_qty
    else:
        OPEN_POS[mint] = Position(mint, entry_price_usd=mkt_price_usd, qty_tokens=qty_net)

    sig = _paper_sig()
    log_trade_detailed(
        "PAPER-BUY", mint, qty_net, sig, "ok",
        entry_px=mkt_price_usd, exit_px=None, realized_usd=None,
        note=f"notional={notional_sol} SOL; wsol={wsol_usd:.6f}"
    )
    return {"sig": sig, "status": "ok", "qty": qty_net}

#=================================================================================================

async def _paper_sell_partial(mint: str, fraction: float, mkt_price_hint: float | None = None) -> dict:
    """
    Paper-Teilverkauf: robust über get_price_for_execution().
    Nutzt optional mkt_price_hint (z. B. letzter Bar-Close) als letzte Instanz.
    """
    global REALIZED_PNL_USD, OPEN_POS
    pos = OPEN_POS.get(mint)
    if not pos or pos.qty <= 0:
        raise RuntimeError("Paper-SELL-PART: Keine offene Position")

    # robuster Preis
    sell_px = get_price_for_execution(mint, mkt_price_hint=mkt_price_hint)

    qty_sell = max(0.0, pos.qty * fraction)
    fee_qty  = qty_sell * (PAPER_FEE_BPS / 10_000.0)
    qty_net  = max(0.0, qty_sell - fee_qty)

    realized = (sell_px - pos.entry_price) * qty_net
    pos.qty -= qty_sell
    if pos.qty < 1e-12:
        pos.qty = 0.0

    REALIZED_PNL_USD += realized
    sig = _paper_sig()
    log_trade_detailed(
        "PAPER-SELL-PART", mint, qty_net, sig, "ok",
        entry_px=pos.entry_price, exit_px=sell_px, realized_usd=realized, note=""
    )
    return {"sig": sig, "status": "ok", "res": {"paper": True}, "realized_usd": realized}

#=================================================================================================

async def _paper_sell_all(mint: str, mkt_price_hint: float | None = None) -> dict:
    """
    Paper-Vollverkauf: robust über get_price_for_execution().
    Nutzt optional mkt_price_hint (z. B. letzter Bar-Close) als letzte Instanz.
    """
    global REALIZED_PNL_USD, OPEN_POS
    pos = OPEN_POS.get(mint)
    if not pos or pos.qty <= 0:
        raise RuntimeError("Paper-SELL-ALL: Keine offene Position")

    # robuster Preis
    sell_px = get_price_for_execution(mint, mkt_price_hint=mkt_price_hint)

    qty_sell = pos.qty
    fee_qty  = qty_sell * (PAPER_FEE_BPS / 10_000.0)
    qty_net  = max(0.0, qty_sell - fee_qty)

    realized = (sell_px - pos.entry_price) * qty_net
    REALIZED_PNL_USD += realized
    OPEN_POS.pop(mint, None)

    sig = _paper_sig()
    log_trade_detailed(
        "PAPER-SELL-ALL", mint, qty_net, sig, "ok",
        entry_px=pos.entry_price, exit_px=sell_px, realized_usd=realized, note=""
    )
    return {"sig": sig, "status": "ok", "res": {"paper": True}, "realized_usd": realized}

#=================================================================================================

async def buy_wsol_to_token(mint: str, notional_sol: float, mkt_price_usd: float) -> dict:
    if PAPER_MODE:
        return await _paper_buy_wsol_to_token(mint, notional_sol, mkt_price_usd)
    # --- echte Ausführung (unverändert) ---
    in_amount = lamports(notional_sol)
    data   = await gmgn_get_route_async(WSOL_MINT, mint, in_amount, WALLET_PUBKEY, GMGN_SLIPPAGE_PCT, GMGN_FEE_SOL, True)
    raw    = data["raw_tx"]["swapTransaction"]
    signed = sign_raw_b64(raw)
    send_res = await rpc_send_signed_b64_async(signed)
    sig      = send_res.get("result") or "NA"
    status   = await wait_for_confirmation(sig)
    qty = await refresh_qty_from_chain_async(mint)
    OPEN_POS[mint] = Position(mint, entry_price_usd=mkt_price_usd, qty_tokens=qty)
    log_trade_detailed(
        "BUY", mint, qty, sig, status,
        entry_px=mkt_price_usd, exit_px=None, realized_usd=None,
        note=f"notional={notional_sol} SOL"
    )
    return {"sig": sig, "status": status, "qty": qty}

#=================================================================================================

async def sell_partial(mint: str, fraction: float) -> dict:
    if PAPER_MODE:
        return await _paper_sell_partial(mint, fraction)
    # --- echte Ausführung (unverändert) ---
    global REALIZED_PNL_USD
    pos = OPEN_POS.get(mint)
    if not pos:
        raise RuntimeError("Keine offene Position für Teilverkauf.")
    bal = await rpc_get_spl_balance_async(WALLET_PUBKEY, mint)
    if bal <= 0:
        raise RuntimeError("Keine Token-Balance.")
    dec = await get_mint_decimals_async(mint)
    in_amount = int((bal * fraction) * (10 ** dec))
    data   = await gmgn_get_route_async(mint, WSOL_MINT, in_amount, WALLET_PUBKEY, GMGN_SLIPPAGE_PCT, GMGN_FEE_SOL, True)
    raw    = data["raw_tx"]["swapTransaction"]
    signed = sign_raw_b64(raw)
    send_res = await rpc_send_signed_b64_async(signed)
    sig      = send_res.get("result") or "NA"
    status   = await wait_for_confirmation(sig)
    sell_px  = await birdeye_price_async(mint)
    realized = (sell_px - pos.entry_price) * (bal * fraction)
    REALIZED_PNL_USD += realized
    await refresh_qty_from_chain_async(mint)
    log_trade_detailed(
        "SELL-PART", mint, bal * fraction, sig, status,
        entry_px=pos.entry_price, exit_px=sell_px, realized_usd=realized, note=""
    )
    return {"sig": sig, "status": status, "res": send_res, "realized_usd": realized}

#=================================================================================================

async def sell_all(mint: str) -> dict:
    if PAPER_MODE:
        return await _paper_sell_all(mint)
    # --- echte Ausführung (unverändert) ---
    global REALIZED_PNL_USD
    pos = OPEN_POS.get(mint)
    bal = await rpc_get_spl_balance_async(WALLET_PUBKEY, mint)
    if bal <= 0:
        raise RuntimeError("Keine Token-Balance.")
    dec = await get_mint_decimals_async(mint)
    in_amount = int(bal * (10 ** dec))
    data   = await gmgn_get_route_async(mint, WSOL_MINT, in_amount, WALLET_PUBKEY, GMGN_SLIPPAGE_PCT, GMGN_FEE_SOL, True)
    raw    = data["raw_tx"]["swapTransaction"]
    signed = sign_raw_b64(raw)
    send_res = await rpc_send_signed_b64_async(signed)
    sig      = send_res.get("result") or "NA"
    status   = await wait_for_confirmation(sig)
    sell_px  = await birdeye_price_async(mint)
    realized = 0.0
    if pos:
        realized = (sell_px - pos.entry_price) * bal
        REALIZED_PNL_USD += realized
        OPEN_POS.pop(mint, None)
    log_trade_detailed(
        "SELL-ALL", mint, bal, sig, status,
        entry_px=pos.entry_price if pos else None, exit_px=sell_px, realized_usd=realized, note=""
    )
    return {"sig": sig, "status": status, "res": send_res, "realized_usd": realized}

#=================================================================================================

async def cmd_pnl(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not guard(update):
        return

    rows = _load_trades_csv()

    # UTC-Grenzen für Day/Week
    now = time.time()
    dt_now = dt.datetime.now(UTC)
    dt_day0 = dt.datetime(dt_now.year, dt_now.month, dt_now.day, tzinfo=UTC)
    ts_day0 = int(dt_day0.timestamp())
    ts_week = int(now - 7 * 86400)

    def _sum_realized(rows: list, ts_from: int | None) -> Decimal:
        s = Decimal("0")
        for r in rows:
            side = (r.get("side") or "").upper()
            if "SELL" not in side:
                continue
            try:
                ts = int(r.get("ts") or 0)
            except Exception:
                ts = 0
            if ts_from is not None and ts < ts_from:
                continue
            s += _realized_from_row(r)
        return s

    d = _sum_realized(rows, ts_day0)
    w = _sum_realized(rows, ts_week)
    t = _sum_realized(rows, None)

    q2 = lambda x: float(Decimal(str(x)).quantize(Decimal("0.01"), rounding=ROUND_HALF_UP))
    realized_day, realized_week, realized_total = map(q2, (d, w, t))

    # Trades & Hit-Rate (nur SELL-Executions)
    sell_rows = [r for r in rows if "SELL" in (r.get("side") or "").upper()]
    num_trades = len(sell_rows)
    wins = sum(1 for r in sell_rows if _realized_from_row(r) > 0)
    losses = sum(1 for r in sell_rows if _realized_from_row(r) < 0)
    neutrals = num_trades - wins - losses
    hit_rate = (wins / (wins + losses) * 100.0) if (wins + losses) > 0 else 0.0

    # Chart
    labels = ["Day", "Week", "Total"]
    values = [realized_day, realized_week, realized_total]
    fig, ax = plt.subplots(figsize=(6.6, 3.2), dpi=160)
    ax.bar(labels, values)
    ax.set_title("Realized PnL")
    ax.set_ylabel("USD")
    for i, v in enumerate(values):
        ax.text(i, v, f"{v:+,.2f}", ha="center", va="bottom", fontsize=9)
    buf = io.BytesIO()
    plt.tight_layout()
    fig.savefig(buf, format="png")
    plt.close(fig)
    buf.seek(0)

    try:
        await update.effective_chat.send_photo(photo=buf, caption="📈 PnL – Day/Week/Total")
    except Exception:
        pass

    # Unrealized + offene Positionen
    unrealized_total, _rows_unreal = total_unreal_pnl()

    lines = [
        "📈 P&L",
        f"Realized (Day):   {realized_day:+,.2f} USD",
        f"Realized (Week):  {realized_week:+,.2f} USD",
        f"Realized (Total): {realized_total:+,.2f} USD",
        f"Unrealized (Open): {unrealized_total:+,.2f} USD",
        "",
        f"Trades (executions): {num_trades} | Wins: {wins} | Losses: {losses} | Flat: {neutrals} | Hit‑Rate: {hit_rate:.1f}%",
    ]
    await send(update, "\n".join(lines))

    # CSV beilegen
    if os.path.exists(PNL_CSV):
        try:
            with open(PNL_CSV, "rb") as f:
                await update.effective_chat.send_document(
                    document=f,
                    filename=os.path.basename(PNL_CSV),
                    caption="📄 Trades/PNL-CSV (v2)"
                )
        except Exception:
            pass


#=================================================================================================
# Strategy v1.6.3 (leicht erweitert mit Diag)
# =========================
def sma(series: deque, length: int) -> Optional[float]:
    if length <= 0 or len(series) < length: return None
    s = 0.0
    for v in list(series)[-length:]: s += v
    return s / float(length)

def ema_update(prev_ema: Optional[float], price: float, length: int) -> float:
    if length <= 1: return price
    k = 2.0 / (length + 1.0)
    return price if prev_ema is None else prev_ema + k * (price - prev_ema)

def true_range(h: float, l: float, c_prev: float) -> float:
    return max(h - l, abs(h - c_prev), abs(l - c_prev))

def atr_wilder_update(state, high: float, low: float, close: float, length: int) -> float:
    if state.prev_close is None: tr = high - low
    else: tr = true_range(high, low, state.prev_close)
    if state.atr is None:
        state.atr = tr; state.atr_count = 1
    else:
        if state.atr_count < length:
            state.atr = (state.atr * state.atr_count + tr) / (state.atr_count + 1); state.atr_count += 1
        else:
            state.atr = state.atr + (tr - state.atr) / float(length)
    return state.atr

def dmi_adx_update(state, high: float, low: float, close: float, length: int, smoothing: int) -> Tuple[float, float, float]:
    # 🔧 Sicherstellen, dass das Feld existiert (für alte State-Objekte)
    if not hasattr(state, "init_count"):
        state.init_count = 0

    # Erstes validierbares Bar?
    if state.prev_high is None or state.prev_low is None or state.prev_close is None:
        state.dm_pos_ema = 0.0
        state.dm_neg_ema = 0.0
        state.tr_ema_for_dmi = 1e-12
        state.adx = 0.0
        state.adx_count = 0
        state.init_count = 0      # 🔧 NEU
        return 0.0, 0.0, 0.0

    up_move = high - state.prev_high
    dn_move = state.prev_low - low
    dm_pos = up_move if (up_move > dn_move and up_move > 0.0) else 0.0
    dm_neg = dn_move if (dn_move > up_move and dn_move > 0.0) else 0.0
    tr = true_range(high, low, state.prev_close)

    # --- SMA-Anfahrphase ---
    if state.dm_pos_ema is None:
        state.dm_pos_ema = dm_pos
        state.dm_neg_ema = dm_neg
        state.tr_ema_for_dmi = tr
        state.init_count = 1
    elif state.init_count < length:
        state.dm_pos_ema = (state.dm_pos_ema * state.init_count + dm_pos) / (state.init_count + 1)
        state.dm_neg_ema = (state.dm_neg_ema * state.init_count + dm_neg) / (state.init_count + 1)
        state.tr_ema_for_dmi = (state.tr_ema_for_dmi * state.init_count + tr) / (state.init_count + 1)
        state.init_count += 1
    else:
        state.dm_pos_ema = state.dm_pos_ema + (dm_pos - state.dm_pos_ema) / float(length)
        state.dm_neg_ema = state.dm_neg_ema + (dm_neg - state.dm_neg_ema) / float(length)
        state.tr_ema_for_dmi = state.tr_ema_for_dmi + (tr - state.tr_ema_for_dmi) / float(length)

    tr_s = state.tr_ema_for_dmi if state.tr_ema_for_dmi != 0 else 1e-12
    di_pos = 100.0 * (state.dm_pos_ema / tr_s)
    di_neg = 100.0 * (state.dm_neg_ema / tr_s)
    dx_num = abs(di_pos - di_neg)
    dx_den = (di_pos + di_neg) if (di_pos + di_neg) != 0 else 1e-12
    dx = 100.0 * (dx_num / dx_den)

    # ADX (rma des DX) – SMA-Init
    if state.adx is None:
        state.adx = dx
        state.adx_count = 1
    else:
        if state.adx_count < smoothing:
            state.adx = (state.adx * state.adx_count + dx) / (state.adx_count + 1)
            state.adx_count += 1
        else:
            state.adx = state.adx + (dx - state.adx) / float(smoothing)

    return di_pos, di_neg, state.adx

# --------------------
# Strategy Config & State (einmalig definieren)
# --------------------
from dataclasses import dataclass, field
from collections import deque
from typing import Optional

@dataclass
class Config:
    tf_sec: float = 5.0
    atr_len: int = 14
    risk_atr: float = 1.2 # 1.6
    tp1_rr: float = 1.5 # 1.3
    tp2_rr: float = 2.5 # 2.6
    trail_after: bool = True
    trail_atr: float = 1.1 #1
    be_after: bool = True
    min_hold_bars: int = 2 # 3
    tp1_frac_pc: float = 30.0#40.0
    tp2_frac_pc: float = 60.0#50.0
    snap_lookback: int = 4 # 10
    base_momo: float = 0.1 # 0.2
    k_momo: float = 0.35 # 0.45
    bo_lookback: int = 10 # 16
    bo_pad_pct: float = 0.01 # 0.018
    use_pullback: bool = True
    ema_pb_len: int = 14 # 20
    pb_tol_pct: float = 0.3 # 0.15
    vol_mult: float = 1.05 # 1.25
    adx_length: int = 10 # 12
    adx_smoothing: int = 14
    adx_th: float = 14 # 20.0
    bo_vol_mult: float = 1.1 #1.25
    bbw_len: int = 20
    bbw_mult: float = 2.0
    bbw_min: float = 0.4 # 0.55
    cool_sec: int = 180  #300
    loss_cool: int = 360 #900
    sl_cool_sec: int = 240 #420
    pause_after_losses: int = 3
    pause_minutes: int = 10 # 15
    max_trades_per_hour: int = 30 # 24
    time_exit_bars: int = 60 # 900
    allowed_hours_csv: str  = "2,3,4,5,10,11,12,13,14,15,16,23"



@dataclass
class State:
    closes: deque = field(default_factory=_mkdq)
    highs:  deque = field(default_factory=_mkdq)
    lows:   deque = field(default_factory=_mkdq)
    vols:   deque = field(default_factory=_mkdq)

    prev_close: Optional[float] = None
    prev_high: Optional[float]  = None
    prev_low:  Optional[float]  = None

    atr: Optional[float] = None
    atr_count: int = 0

    dm_pos_ema: Optional[float] = None
    dm_neg_ema: Optional[float] = None
    tr_ema_for_dmi: Optional[float] = None
    adx: Optional[float] = None
    adx_count: int = 0

    # für SMA-Anfahrphase der DMI/ADX-Berechnung
    init_count: int = 0

    ema_pb: Optional[float] = None
    position_size: float = 0.0
    entry_price: Optional[float] = None
    sl_abs: Optional[float] = None
    tp1_done: bool = False
    tp2_done: bool = False
    be_armed: bool = False
    trail_on: bool = False
    trail_hi: Optional[float] = None
    sl_armed: bool = False
    entry_bar_index: Optional[float] = None
    loss_streak: int = 0
    next_entry_earliest_bar: Optional[int] = None
    trades_this_hour: int = 0
    last_hour_id: Optional[int] = None
    bar_index: int = 0


class SwingBotV163:
    def __init__(self, cfg: Config):
        self.cfg = cfg
        self.st = State()
        self.last_diag: Dict[str, object] = {}

    def _pc(self, a: Optional[float], b: Optional[float]) -> Optional[float]:
        return None if (a is None or b is None or a == 0) else (b - a) / a * 100.0

    def _hour_ok(self, epoch_ms: int) -> bool:
        """
        Whitelist der Stunden; allowed_hours_csv wird als *lokale* Stundenliste interpretiert.
        Die Lokalzeit ergibt sich aus UTC + ALLOWED_HOURS_TZ_OFFSET_MIN (ENV, Minuten).
        """
        # UTC -> "lokal" mit Offset in Minuten verschieben
        utc_dt   = dt.datetime.fromtimestamp(epoch_ms / 1000, UTC)
        local_dt = utc_dt + dt.timedelta(minutes=ALLOWED_HOURS_TZ_OFFSET_MIN)
        hour = int(local_dt.hour)

        allowed = {int(x.strip()) for x in self.cfg.allowed_hours_csv.split(",") if x.strip() != ""}
        if not allowed:   # leere Liste => Gate aus
            return True
        return hour in allowed    

    def _highest_excl_current(self, arr: deque, lookback: int) -> Optional[float]:
        if len(arr) < lookback + 1: return None
        seg = list(arr)[-(lookback+1):-1]; return max(seg) if seg else None

    def on_bar(self, candle: Dict[str, float]) -> List[Dict]:
        t=int(candle["time"]); o=float(candle["open"]); h=float(candle["high"]); l=float(candle["low"]); c=float(candle["close"]); v=float(candle["volume"])
        st, cfg = self.st, self.cfg; out: List[Dict] = []
        st.closes.append(c); st.highs.append(h); st.lows.append(l); st.vols.append(v); st.bar_index += 1

        cur_hour = int(dt.datetime.fromtimestamp(t/1000, UTC).replace(minute=0, second=0, microsecond=0).timestamp())
        if st.last_hour_id != cur_hour: st.last_hour_id = cur_hour; st.trades_this_hour = 0

        # ATR zuerst berechnen
        atr_val = atr_wilder_update(st, h, l, c, cfg.atr_len)

        # ATR%-Gate (in %)
        atr_pc = (atr_val / c * 100.0) if c else 0.0
        atr_ok = (atr_pc >= ATR_PC_MIN)

        # DMI/ADX IMMER updaten (auch wenn atr_ok False ist)
        di_pos, di_neg, adx_val = dmi_adx_update(st, h, l, c, cfg.adx_length, cfg.adx_smoothing)
        adx_ok = adx_val > cfg.adx_th
        trend_bias_ok = (di_pos > di_neg) or (adx_val > cfg.adx_th + 2)

        st.ema_pb = ema_update(st.ema_pb, c, cfg.ema_pb_len)
        vol_sma50 = sma(st.vols, 50) or 0.0

        ref = st.closes[-(cfg.snap_lookback+1)] if len(st.closes) >= cfg.snap_lookback + 1 else None
        momo_thresh = cfg.base_momo + cfg.k_momo * ((atr_val / c) * 100.0 if c else 0.0)
        momo_pc = self._pc(ref, c); momo_ok = (c > 0) and (ref is not None) and (momo_pc is not None) and (momo_pc >= momo_thresh)

        hh = self._highest_excl_current(st.highs, cfg.bo_lookback)
        bo_ok = (hh is not None) and (c > hh * (1.0 + cfg.bo_pad_pct / 100.0)) and (v > vol_sma50 * cfg.bo_vol_mult)

        basis = sma(st.closes, cfg.bbw_len); dev=None
        if basis is not None and len(st.closes) >= cfg.bbw_len:
            vals=list(st.closes)[-cfg.bbw_len:]; m=basis; dev=math.sqrt(sum((x-m)**2 for x in vals)/float(cfg.bbw_len))
        if basis is not None and dev is not None and basis != 0:
            upper=basis + cfg.bbw_mult*dev; lower=basis - cfg.bbw_mult*dev; bbw_pct=(upper-lower)/basis*100.0; bbw_ok = bbw_pct > cfg.bbw_min
        else: bbw_ok = False

        if cfg.use_pullback and st.ema_pb is not None:
            near_pb = l <= st.ema_pb * (1.0 + cfg.pb_tol_pct / 100.0); pullback_ok = near_pb and (c > st.ema_pb); gate_pb = pullback_ok
        else: gate_pb = True

        vol_ok = (vol_sma50 == 0.0) or (v > vol_sma50 * cfg.vol_mult)
        entry_signal = (atr_ok and (momo_ok or bo_ok) and gate_pb and vol_ok and adx_ok and trend_bias_ok and bbw_ok)

        can_enter_time = (st.next_entry_earliest_bar is None) or (st.bar_index >= st.next_entry_earliest_bar)
        hour_ok = st.trades_this_hour < cfg.max_trades_per_hour
        hour_whitelist_ok = self._hour_ok(t)

        self.last_diag = dict(t=t, close=c, vol=v, atr=atr_val, adx=adx_val, atr_pc=atr_pc, atr_ok=atr_ok, momo_ok=momo_ok, momo_pc=momo_pc, momo_thresh=momo_thresh,
                              bo_ok=bo_ok, bbw_ok=bbw_ok, gate_pb=gate_pb, vol_ok=vol_ok, entry_signal=entry_signal,
                              hour_ok=hour_ok, hour_whitelist_ok=hour_whitelist_ok)

        if st.position_size == 0.0 and can_enter_time and hour_ok and hour_whitelist_ok and entry_signal:
            out.append({"type": "entry", "side": "long", "comment": "LONG"})
            st.position_size = 1.0; st.entry_price = c; st.sl_abs = c - atr_val * cfg.risk_atr
            st.tp1_done = False; st.tp2_done = False; st.be_armed = False; st.trail_on = False
            st.trail_hi = c; st.entry_bar_index = st.bar_index; st.sl_armed = (cfg.min_hold_bars == 0)
            st.trades_this_hour += 1

        in_long = st.position_size > 0.0
        if in_long and st.entry_price is not None and st.sl_abs is not None:
            R = st.entry_price - st.sl_abs; tp1_px = st.entry_price + cfg.tp1_rr * R; tp2_px = st.entry_price + cfg.tp2_rr * R
            if (not st.sl_armed) and (st.entry_bar_index is not None) and ((st.bar_index - st.entry_bar_index) >= cfg.min_hold_bars): st.sl_armed = True
            if cfg.be_after and (not st.be_armed) and (c >= tp1_px): st.sl_abs = st.entry_price; st.be_armed = True
            if (not st.tp1_done) and (c >= tp1_px):
                out.append({"type": "reduce", "qty_frac": self.cfg.tp1_frac_pc / 100.0, "comment": "TP1"}); st.tp1_done = True
                if cfg.trail_after: st.trail_on = True; st.trail_hi = max(st.trail_hi or c, h)
            if st.tp1_done and (not st.tp2_done) and (c >= tp2_px):
                out.append({"type": "reduce", "qty_frac": self.cfg.tp2_frac_pc / 100.0, "comment": "TP2"}); st.tp2_done = True
            if st.trail_on:
                st.trail_hi = max(st.trail_hi or c, h); trail_sl = st.trail_hi - atr_val * cfg.trail_atr
                if c <= trail_sl:
                    out.append({"type": "close", "comment": "Trail"}); self._on_close_trade(final_price=c, exit_comment="Trail")
                    self._update_prev(c, h, l); return out
            if st.sl_armed and c <= st.sl_abs:
                out.append({"type": "close", "comment": "SL"}); self._on_close_trade(final_price=c, exit_comment="SL")
                self._update_prev(c, h, l); return out
            if cfg.time_exit_bars > 0 and st.entry_bar_index is not None:
                if (st.bar_index - st.entry_bar_index) >= cfg.time_exit_bars:
                    out.append({"type":"close","comment":"TimeExit"}); self._on_close_trade(final_price=c, exit_comment="TimeExit")
                    self._update_prev(c, h, l); return out

        self._update_prev(c, h, l); return out

    def _update_prev(self, close: float, high: float, low: float):
        self.st.prev_close = close; self.st.prev_high = high; self.st.prev_low = low

    def _on_close_trade(self, final_price: float, exit_comment: str):
        cfg, st = self.cfg, self.st
        profit = 0.0; was_loss = False; was_sl = (exit_comment == "SL")
        if st.entry_price is not None: profit = final_price - st.entry_price; was_loss = profit <= 0.0
        dyn_cool = cfg.cool_sec
        if was_loss: dyn_cool = max(dyn_cool, cfg.loss_cool); st.loss_streak += 1
        else: st.loss_streak = 0
        if was_sl: dyn_cool = max(dyn_cool, cfg.sl_cool_sec)
        if st.loss_streak >= cfg.pause_after_losses:
            dyn_cool = max(dyn_cool, cfg.pause_minutes * 60); st.loss_streak = 0
        dyn_bars = int(round(dyn_cool / cfg.tf_sec))
        st.next_entry_earliest_bar = (st.bar_index or 0) + dyn_bars
        st.position_size = 0.0; st.entry_price = None; st.sl_abs = None
        st.tp1_done = False; st.tp2_done = False; st.be_armed = False
        st.trail_on = False; st.trail_hi = None; st.sl_armed = False
        st.entry_bar_index = None


# ----------- 1m CONFIG (Preset nach der Klassendefinition) -----------
CONFIG_1M = Config(
    # Zeitbasis
    tf_sec=60.0,

    # Risiko/Targets (1m etwas enger/glatter)
    atr_len=3,
    risk_atr=1.15,
    tp1_rr=1.5,
    tp2_rr=3.10,
    trail_after=True,
    trail_atr=1.20,
    be_after=True,

    # Mindesthaltezeit/Exits in Bars (1m)
    min_hold_bars=2,
    time_exit_bars=75,

    # Teilverkäufe
    tp1_frac_pc=30.0,
    tp2_frac_pc=60.0,

    # Entry-Logik skaliert
    snap_lookback=3,
    base_momo=0.08,
    k_momo=0.30,
    bo_lookback=4,
    bo_pad_pct=0.015,
    use_pullback=True,
    ema_pb_len=3,
    pb_tol_pct=0.20,

    # Filter/ADX/Volumen
    vol_mult=1.15,
    adx_length=10,
    adx_smoothing=14,
    adx_th=20.0,
    bo_vol_mult=1.20,

    # BB-Breite
    bbw_len=20,
    bbw_mult=2.0,
    bbw_min=0.45,

    # Cooldowns/Limits 1m
    cool_sec=180,
    loss_cool=600,
    sl_cool_sec=600,
    pause_after_losses=3,
    pause_minutes=12,
    max_trades_per_hour=8,
    allowed_hours_csv="2,3,4,5,10,11,12,13,14,15,16,23",
)

# =========================
# 5s Candle Builder
# =========================
class Bar5sBuilder:
    def __init__(self, tf_sec: float = 5.0):
        self.win_ms = int(tf_sec*1000); self.reset()
    def reset(self):
        self.start_ms: Optional[int] = None; self.o = self.h = self.l = self.c = None; self.v = 0.0
    def add(self, price: float, vol_per_sec: float, now_ms: int):
        if price <= 0: return
        if self.start_ms is None:
            self.start_ms = now_ms; self.o = self.h = self.l = self.c = price
        else:
            self.h = max(self.h, price); self.l = min(self.l, price); self.c = price
        self.v += float(max(0.0, vol_per_sec))
    def maybe_finish(self, now_ms: int) -> Optional[Dict[str, float]]:
        if self.start_ms is None: return None
        if now_ms - self.start_ms >= self.win_ms:
            cdict = {"time": self.start_ms + self.win_ms, "open": self.o, "high": self.h, "low": self.l, "close": self.c, "volume": self.v}
            self.reset(); return cdict
        return None
        
# =========================
# AUTO-LIQUIDITY MONITOR
# =========================
# Prüft periodisch pro Mint:
#  - DEX-Layer-Referenzen (Raydium/Orca/Meteora) via _count_liquidity_refs_async
#  - beste Pool-LP (≈SOL) via _aw_extract_best_pair + _lp_sol_of_pair
#  - optionales Auto-Pruning, Alerts bei starken Änderungen
#
# Kommandos:
#  /check_liq <MINT>                -> einmaliger Check + Summary
#  /auto_liq on|off                 -> Autoloop an/aus
#  /liq_config [Flags]              -> Schwellwerte setzen / anzeigen
#
# Flags für /liq_config:
#   --interval SEC
#   --prune-empty {0|1}
#   --delta-refs N
#   --delta-lp-pct PCT
#   --min-lp-sol X
#   --min-total-refs N

# ---- ENV Defaults (einheitlich mit setdefault) ----
os.environ.setdefault("LIQ_CHECK_INTERVAL_SEC",  "7200")   # 2h
os.environ.setdefault("LIQ_PRUNE_EMPTY",         "1")      # 1=True: Mints mit 0 Refs automatisch entfernen
os.environ.setdefault("LIQ_ALERT_DELTA_REFS",    "2")      # ab +/-2 Refs Veränderung alerten
os.environ.setdefault("LIQ_ALERT_DELTA_LP_PCT",  "30")     # ab +/-30% LP-Änderung alerten
os.environ.setdefault("LIQ_MIN_LP_SOL",          "0.0")    # rein informativ / weiches Gate
os.environ.setdefault("LIQ_MIN_TOTAL_REFS",      "0")      # rein informativ / weiches Gate
os.environ.setdefault("AUTO_LIQ_ENABLED_DEFAULT","0")      # 1=True: Auto-Loop beim Start aktiv

# ---- Laufzeit-Konfiguration ----
LIQ_CFG = {
    "enabled": (os.environ.get("AUTO_LIQ_ENABLED_DEFAULT","0").strip().lower() in ("1","true","yes","on")),
    "interval_sec": int(os.environ.get("LIQ_CHECK_INTERVAL_SEC","7200") or 7200),
    "prune_empty": (os.environ.get("LIQ_PRUNE_EMPTY","1").strip() in ("1","true","yes","on")),
    "delta_refs": int(os.environ.get("LIQ_ALERT_DELTA_REFS","2") or 2),
    "delta_lp_pct": float(os.environ.get("LIQ_ALERT_DELTA_LP_PCT","30") or 30.0),
    "min_lp_sol": float(os.environ.get("LIQ_MIN_LP_SOL","0.0") or 0.0),
    "min_total_refs": int(os.environ.get("LIQ_MIN_TOTAL_REFS","0") or 0),
}

LIQ_LOCK = asyncio.Lock()
LIQ_STATE_PATH = "auto_liq_state.json"

def _liq_load_state() -> dict:
    try:
        with open(LIQ_STATE_PATH, "r", encoding="utf-8") as f:
            s = json.load(f) or {}
        if not isinstance(s, dict):
            return {"mints": {}, "last_run_ts": 0}
        s.setdefault("mints", {})
        s.setdefault("last_run_ts", 0)
        return s
    except Exception:
        return {"mints": {}, "last_run_ts": 0}

def _liq_save_state(st: dict) -> None:
    try:
        with open(LIQ_STATE_PATH, "w", encoding="utf-8") as f:
            json.dump(st, f, ensure_ascii=False, indent=2)
    except Exception:
        pass

LIQ_STATE = _liq_load_state()
AUTO_LIQ_TASK: Optional[asyncio.Task] = None

def _fmt_lp(x: float) -> str:
    try: return f"{float(x):.2f}"
    except: return "0.00"

def _fmt_pct(x: float) -> str:
    try: return f"{float(x):.0f}%"
    except: return "0%"

async def _measure_liquidity(mint: str) -> dict:
    """
    Liefert:
      {
        'raydium_refs': int, 'orca_refs': int, 'meteora_refs': int,
        'total_refs': int, 'lp_sol': float
      }
    """
    refs = await _count_liquidity_refs_async(mint)
    best = _aw_extract_best_pair(mint)
    lp_sol = _lp_sol_of_pair(best) if best else 0.0
    return {
        "raydium_refs": int(refs.get("raydium_refs",0)),
        "orca_refs":    int(refs.get("orca_refs",0)),
        "meteora_refs": int(refs.get("meteora_refs",0)),
        "total_refs":   int(refs.get("total_liq_refs",0)),
        "lp_sol":       float(lp_sol or 0.0),
    }

def _liq_snapshot_text() -> list[str]:
    return [
        f"interval={LIQ_CFG['interval_sec']}s | prune_empty={LIQ_CFG['prune_empty']}",
        f"alerts: Δrefs≥{LIQ_CFG['delta_refs']} | ΔLP≥{_fmt_pct(LIQ_CFG['delta_lp_pct'])}",
        f"soft gates: min_lp_sol≥{_fmt_lp(LIQ_CFG['min_lp_sol'])} | min_total_refs≥{LIQ_CFG['min_total_refs']}",
    ]

def _calc_delta_pct(old: float, new: float) -> float:
    if old <= 0: 
        return 999.0 if new>0 else 0.0
    return (new - old) / old * 100.0

async def _liq_check_one_and_report(mint: str) -> tuple[str, dict, dict]:
    """
    Führt einen Check aus, vergleicht mit letztem Snapshot, aktualisiert LIQ_STATE
    und gibt (mint, current, prev) zurück.
    """
    cur = await _measure_liquidity(mint)
    prev = LIQ_STATE["mints"].get(mint) or {}
    LIQ_STATE["mints"][mint] = {
        "last_ts": int(time.time()),
        "last_lp_sol": float(cur["lp_sol"]),
        "last_total_refs": int(cur["total_refs"]),
        "last_r": int(cur["raydium_refs"]),
        "last_o": int(cur["orca_refs"]),
        "last_m": int(cur["meteora_refs"]),
    }
    _liq_save_state(LIQ_STATE)
    return mint, cur, prev

def _liq_format_line(mint: str, cur: dict, prev: dict) -> str:
    refs = cur["total_refs"]; lp = cur["lp_sol"]
    # Delta berechnen
    prev_refs = int(prev.get("last_total_refs") or 0)
    prev_lp   = float(prev.get("last_lp_sol") or 0.0)
    d_refs = refs - prev_refs
    d_lp_pct = _calc_delta_pct(prev_lp, lp)
    # Icons
    ico_r = "✅" if cur["raydium_refs"]>0 else "❌"
    ico_o = "✅" if cur["orca_refs"]>0    else "❌"
    ico_m = "✅" if cur["meteora_refs"]>0 else "❌"
    # Delta-Text
    d_refs_txt = f"{'+' if d_refs>=0 else ''}{d_refs}"
    d_lp_txt   = f"{'+' if d_lp_pct>=0 else ''}{int(d_lp_pct)}%"
    return (f"{mint[:6]}…  Refs={refs} ({ico_r}R {ico_o}O {ico_m}M, Δ={d_refs_txt})  "
            f"LP≈{_fmt_lp(lp)} SOL (Δ={d_lp_txt})")

async def _liq_maybe_prune(mint: str, cur: dict) -> Optional[str]:
    if not LIQ_CFG["prune_empty"]:
        return None
    if int(cur.get("total_refs", 0)) == 0:
        if mint in WATCHLIST:
            WATCHLIST.remove(mint)
        LIQ_STATE["mints"].pop(mint, None)
        # <<< FIX: State freigeben, sofern keine offene Position
        if mint not in OPEN_POS:
            _drop_mint_state(mint)
        return "pruned: no pools"
    return None

def _liq_should_alert(cur: dict, prev: dict) -> tuple[bool, list[str]]:
    msgs = []
    # Refs-Alert
    prev_refs = int(prev.get("last_total_refs") or 0)
    cur_refs  = int(cur.get("total_refs") or 0)
    if abs(cur_refs - prev_refs) >= LIQ_CFG["delta_refs"]:
        if cur_refs > prev_refs:
            msgs.append(f"Refs +{cur_refs - prev_refs}")
        else:
            msgs.append(f"Refs {cur_refs - prev_refs}")
    # LP-Alert
    prev_lp = float(prev.get("last_lp_sol") or 0.0)
    cur_lp  = float(cur.get("lp_sol") or 0.0)
    delta_lp_pct = abs(_calc_delta_pct(prev_lp, cur_lp))
    if delta_lp_pct >= LIQ_CFG["delta_lp_pct"]:
        sign = "+" if cur_lp >= prev_lp else "−"
        msgs.append(f"LP {sign}{int(delta_lp_pct)}%")
    return (len(msgs)>0, msgs)

async def liq_check_watchlist_once() -> dict:
    """
    Check über aktuelle WATCHLIST (optional inkl. Observe-Mints per ENV):
      - misst Refs/LP
      - optionales Pruning bei 0 Refs
      - Alerts bei starken Änderungen
      - Telegram-Summary
    Rückgabe: {"n": <anzahl geprüfter tokens>, "added": [], "pruned": [(mint, reason)], "alerted": [(mint, msg)]}
    """
    async with LIQ_LOCK:
        # --- Tokenmenge bilden: WATCHLIST (+ optional OBSERVE) ---
        incl_obs = (os.environ.get("LIQ_INCLUDE_OBSERVE", "1").strip().lower() in ("1", "true", "yes", "on"))
        observe_mints = set(AW_STATE.get("observed", {}).keys())
        tokens = list(set(WATCHLIST) | (observe_mints if incl_obs else set()))

        if not tokens:
            return {"n": 0, "added": [], "pruned": [], "alerted": []}

        lines = ["💧 Liquidity Report"]
        added = []
        pruned = []
        alerted = []

        for mint in tokens:
            try:
                m, cur, prev = await _liq_check_one_and_report(mint)
                # formatierte Zeile anhängen
                line = _liq_format_line(m, cur, prev)
                lines.append("• " + line)

                # optionales Pruning (no pools)
                why = await _liq_maybe_prune(m, cur)
                if why:
                    pruned.append((m, why))
                    lines[-1] += "  → 🗑 " + why

                # Alerts (Δrefs / ΔLP%)
                do_alert, msg = _liq_should_alert(cur, prev)
                if do_alert:
                    alerted.append((m, "; ".join(msg)))
            except Exception as e:
                lines.append(f"• {mint[:6]}… error: {e}")

        # Timestamp aktualisieren & persistieren
        LIQ_STATE["last_run_ts"] = int(time.time())
        _liq_save_state(LIQ_STATE)

        # Summary posten
        await tg_post("\n".join(lines))
        if alerted:
            txt = "⚠️ Liquidity Alerts:\n" + "\n".join([f"- {m[:6]}… {t}" for m, t in alerted])
            await tg_post(txt)

        return {"n": len(tokens), "added": added, "pruned": pruned, "alerted": alerted}

async def auto_liq_loop():
    while LIQ_CFG["enabled"]:
        try:
            await liq_check_watchlist_once()
        except Exception as e:
            logger.exception(f"[auto_liq_loop] {e}")
        # Sleep in Sekunden mit sauberem vorzeitigem Exit
        for _ in range(int(LIQ_CFG["interval_sec"])):
            if not LIQ_CFG["enabled"]:
                break
            await asyncio.sleep(1.0)

# ---------- Commands ----------
def _liq_parse_flags(args) -> dict:
    out = {}
    it = iter(args or [])
    for tok in it:
        t = (tok or "").lower()
        def _ival(default=None):
            try: return int(next(it))
            except StopIteration: return default
        def _fval(default=None):
            try: return float(next(it))
            except StopIteration: return default
        if t in ("--interval","-i"):        out["interval_sec"] = _ival(LIQ_CFG["interval_sec"])
        elif t == "--prune-empty":          out["prune_empty"] = (next(it).lower() in ("1","true","yes","on"))
        elif t == "--delta-refs":           out["delta_refs"] = _ival(LIQ_CFG["delta_refs"])
        elif t == "--delta-lp-pct":         out["delta_lp_pct"] = _fval(LIQ_CFG["delta_lp_pct"])
        elif t == "--min-lp-sol":           out["min_lp_sol"] = _fval(LIQ_CFG["min_lp_sol"])
        elif t == "--min-total-refs":       out["min_total_refs"] = _ival(LIQ_CFG["min_total_refs"])
    return out
#===============================================================================

async def cmd_liq_config(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not guard(update): return
    if context.args:
        ch = _liq_parse_flags(context.args)
        LIQ_CFG.update({k:v for k,v in ch.items() if v is not None})
    lines = ["⚙️ Liquidity Monitor config"] + _liq_snapshot_text()
    await send(update, "\n".join(lines))
#===============================================================================

async def cmd_auto_liq(update: Update, context: ContextTypes.DEFAULT_TYPE):
    global AUTO_LIQ_TASK
    if not guard(update): return
    arg = (context.args[0].strip().lower() if context.args else "")
    if arg in ("on","start","1","true"):
        if LIQ_CFG["enabled"] and AUTO_LIQ_TASK and not AUTO_LIQ_TASK.done():
            return await send(update, "ℹ️ Auto-Liquidity: läuft bereits.")
        LIQ_CFG["enabled"] = True
        AUTO_LIQ_TASK = asyncio.create_task(auto_liq_loop())
        return await send(update, "✅ Auto-Liquidity: gestartet.")
    if arg in ("off","stop","0","false"):
        LIQ_CFG["enabled"] = False
        try:
            if AUTO_LIQ_TASK and not AUTO_LIQ_TASK.done():
                AUTO_LIQ_TASK.cancel()
                try: await AUTO_LIQ_TASK
                except asyncio.CancelledError: pass
        finally:
            AUTO_LIQ_TASK = None
        return await send(update, "🛑 Auto-Liquidity: gestoppt.")
    # Status
    st = LIQ_STATE
    last = st.get("last_run_ts") or 0
    age = int(time.time()) - last if last>0 else None
    lines = [
        f"ℹ️ Auto-Liquidity = {'ON' if LIQ_CFG['enabled'] else 'OFF'}",
        f"last run: {dt.datetime.fromtimestamp(last, dt.UTC).strftime('%Y-%m-%d %H:%M:%S')}Z ({age}s ago)" if last else "last run: n/a",
        *_liq_snapshot_text(),
    ]
    await send(update, "\n".join(lines))
#===============================================================================

async def cmd_check_liq(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not guard(update): return
    if not context.args:
        return await send(update, "Nutzung: /check_liq <MINT>")
    mint = context.args[0].strip()
    try:
        m, cur, prev = await _liq_check_one_and_report(mint)
        line = _liq_format_line(m, cur, prev)
        why = await _liq_maybe_prune(m, cur)
        if why:
            line += f"  → 🗑 {why}"
        await send(update, "💧 Liquidity Check\n" + line)
    except Exception as e:
        await send(update, f"❌ check_liq Fehler: {e}")

#===============================================================================
# INDICATORS & IO (integriertes Zusatz-Modul)
#===============================================================================
from typing import Deque

@dataclass
class IndiState:
    closes: Deque[float] = field(default_factory=_mkdq)
    highs:  Deque[float] = field(default_factory=_mkdq)
    lows:   Deque[float] = field(default_factory=_mkdq)
    vols:   Deque[float] = field(default_factory=_mkdq)

    prev_close: Optional[float] = None
    prev_high:  Optional[float] = None
    prev_low:   Optional[float] = None
    atr: Optional[float] = None
    atr_count: int = 0
    dm_pos_ema: Optional[float] = None
    dm_neg_ema: Optional[float] = None
    tr_ema_for_dmi: Optional[float] = None
    adx: Optional[float] = None
    adx_count: int = 0
    init_count: int = 0
    ema_pb: Optional[float] = None
    sma_vol_50: Optional[float] = None
    bar_index: int = 0    
#===============================================================================
# ---------- Optionaler OHLCV-Fetcher (Birdeye) MIT HTTP-STATUS ----------
def fetch_birdeye_ohlcv_5s(mint: str, api_key: str, limit: int = 120, chain: str = "sol") -> tuple[list[dict], int]:
    if not api_key:
        return [], 401
    url = "https://public-api.birdeye.so/defi/ohlcv"
    params = {"address": mint, "chain": chain, "resolution": 5, "limit": limit}
    headers = {"X-API-KEY": api_key}
    try:
        r = http_get(url, params=params, headers=headers, timeout=10)
        status = r.status_code
        try:
            j = r.json() or {}
        except Exception:
            return [], status
        data = j.get("data") or []
        out: list[dict] = []
        for row in data:
            ts_sec = int(row.get("unixTime") or 0)
            if ts_sec <= 0:
                continue
            out.append({
                "time": ts_sec * 1000,
                "open":  float(row.get("open", 0.0)),
                "high":  float(row.get("high", 0.0)),
                "low":   float(row.get("low", 0.0)),
                "close": float(row.get("close", 0.0)),
                "volume": float(row.get("volume", 0.0)),
            })
        return out, status
    except Exception:
        return [], -1
#===============================================================================
        
def fetch_birdeye_ohlcv_60s(mint: str, api_key: str, limit: int = 200, chain: str = "sol") -> tuple[list[dict], int]:
    if not api_key:
        return [], 401
    url = "https://public-api.birdeye.so/defi/ohlcv"
    params = {"address": mint, "chain": chain, "resolution": 60, "limit": limit}
    headers = {"X-API-KEY": api_key}
    try:
        r = http_get(url, params=params, headers=headers, timeout=10)
        status = r.status_code
        j = r.json() or {}
        data = j.get("data") or []
        out = [{
            "time": int(row.get("unixTime") or 0) * 1000,
            "open": float(row.get("open", 0.0)),
            "high": float(row.get("high", 0.0)),
            "low":  float(row.get("low", 0.0)),
            "close":float(row.get("close", 0.0)),
            "volume":float(row.get("volume", 0.0)),
        } for row in data if int(row.get("unixTime") or 0) > 0]
        return out, status
    except Exception:
        return [], -1

#===============================================================================
# --- am Dateianfang sicherstellen:
from io import BytesIO
import matplotlib.pyplot as plt

def _as_ohlcv_arrays(data):
    """
    Akzeptiert:
      - Liste von Dicts: {'time','open','high','low','close','volume'}
      - Liste von Tupeln/Listen: [time, open, high, low, close, volume]
    Liefert: t, o, h, l, c, v  (jeweils Liste[float])
    """
    t, o, h, l, c, v = [], [], [], [], [], []
    for row in data:
        if isinstance(row, dict):
            t.append(float(row.get("time", 0)))
            o.append(float(row.get("open", 0)))
            h.append(float(row.get("high", 0)))
            l.append(float(row.get("low", 0)))
            c.append(float(row.get("close", 0)))
            v.append(float(row.get("volume", 0)))
        else:
            # Sequenz / Tuple
            t.append(float(row[0] if len(row) > 0 else 0))
            o.append(float(row[1] if len(row) > 1 else 0))
            h.append(float(row[2] if len(row) > 2 else 0))
            l.append(float(row[3] if len(row) > 3 else 0))
            c.append(float(row[4] if len(row) > 4 else 0))
            v.append(float(row[5] if len(row) > 5 else 0))
    return t, o, h, l, c, v
#===============================================================================

def render_mint_chart_png(mint: str, bars, *, entry_price: float | None = None, title_suffix: str = "") -> bytes:
    """
    Erzeugt ein PNG aus OHLCV-Daten.
    - bars: Liste[Dict] oder Liste[Tuple]
    - entry_price: falls gesetzt, wird als horizontale Linie eingezeichnet
    - title_suffix: z. B. 'src=be5' oder 'src=be60'
    """
    t, o, h, l, c, v = _as_ohlcv_arrays(bars)
    if not c:
        raise ValueError("keine Daten")

    # einfache EMA(20) auf Close
    ema = []
    k = 2.0 / (20 + 1.0)
    e = None
    for px in c:
        e = px if e is None else (e + k * (px - e))
        ema.append(e)

    fig, ax = plt.subplots(figsize=(8, 4.2), dpi=160)

    # Close-Kurve + EMA
    ax.plot(range(len(c)), c, label="Close", linewidth=1.5)
    ax.plot(range(len(ema)), ema, label="EMA20", linewidth=1.2)

    # Entry-Linie (optional)
    if entry_price and entry_price > 0:
        ax.axhline(entry_price, linestyle="--", linewidth=1.0, label=f"Entry {entry_price:.6f}")

    ax.set_title(f"{mint[:6]}  px={c[-1]:.6f}  |  ATR/ADX in Caption  {title_suffix}".strip())
    ax.set_xlabel("Bars (neu → rechts)")
    ax.set_ylabel("Preis (USD)")
    ax.legend(loc="upper left")

    buf = BytesIO()
    plt.tight_layout()
    fig.savefig(buf, format="png")
    plt.close(fig)
    buf.seek(0)
    return buf.getvalue()
#===============================================================================

def update_indicators_and_debug(st: IndiState, candle: Dict[str, float], *, atr_len: int, adx_len: int, adx_smooth: int, ema_pb_len: int, vol_mult: float) -> Dict[str, float]:
    t=int(candle["time"]); o=float(candle["open"]); h=float(candle["high"]); l=float(candle["low"]); c=float(candle["close"]); v=float(candle["volume"])
    st.closes.append(c); st.highs.append(h); st.lows.append(l); st.vols.append(v); st.bar_index += 1
    atr_val = atr_wilder_update(st, h, l, c, atr_len); di_pos, di_neg, adx_val = dmi_adx_update(st, h, l, c, adx_len, adx_smooth)
    st.ema_pb = ema_update(st.ema_pb, c, ema_pb_len); st.sma_vol_50 = sma(st.vols, 50)
    vol_ok = (st.sma_vol_50 is None) or (v > (st.sma_vol_50 or 0.0) * vol_mult)
    st.prev_close, st.prev_high, st.prev_low = c, h, l
    return {"px": c, "ATR": atr_val, "ADX": adx_val, "vol_ok": bool(vol_ok), "ema_pb": st.ema_pb if st.ema_pb is not None else 0.0, "sma_vol_50": st.sma_vol_50 if st.sma_vol_50 is not None else 0.0, "bar": st.bar_index}
#===============================================================================

def format_debug_line(mint: str, dbg: Dict[str, float], lookback_secs: int) -> str:
    return (f"🔎 {mint[:6]} px={dbg['px']:.6f} v5s≈{lookback_secs} | ATR={dbg['ATR']:.6f} ADX={dbg['ADX']:.1f} | vol_ok={'True' if dbg['vol_ok'] else 'False'}")
#===============================================================================
    
async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not guard(update):
        return
    helius_txt = "Helius" if is_helius_url(RPC_URL) else "Custom RPC"
    lines = [
        f"🤖 <b>SwingBot v1.6.3 online</b>",
        f"Wallet: <code>{WALLET_PUBKEY}</code>",
        f"RPC: <code>{RPC_URL}</code> ({helius_txt})",
        f"Watchlist: {', '.join(WATCHLIST) or '-'}",
        "",
        "— <b>Core</b>",
        "<code>/boot</code> / <code>/shutdown</code> – Bot an/aus, <code>/diag_webhook</code>",
        "<code>/status</code>, <code>/health</code>, <code>/diag</code>, <code>/set_proxy &lt;url|off&gt;</code>",
        "",
        "— <b>Trading</b>",
        "<code>/buy &lt;MINT&gt; [sol]</code>, <code>/sell_all &lt;MINT&gt;</code>",
        "<code>/set_notional &lt;sol&gt;</code>, <code>/set_slippage &lt;pct&gt;</code>, <code>/set_fee &lt;SOL&gt;</code>",
        "<code>/positions</code>, <code>/open_trades</code>",
        "",
        "— <b>Discovery &amp; Sanity</b>",
        "<code>/scan_ds</code> [Flags], <code>/sanity &lt;MINT&gt;</code>",
        "<code>/dsdiag</code>, <code>/dsraw</code>, <code>/ds_trending</code>, <code>/trending</code> [n [focus] [quote]]",
        "",
        "— <b>Auto-Watchlist</b>",
        "<code>/autowatch on|off</code>, <code>/aw_status</code>, <code>/aw_config</code> [Flags], <code>/aw_now</code>",
        "",
        "— <b>Watchlist</b>",
        "<code>/list_watch</code>, <code>/add_watch &lt;MINT&gt;</code>, <code>/remove_watch &lt;MINT&gt;</code>",
        "",
        "— <b>Charts &amp; P&amp;L</b>",
        "<code>/chart &lt;MINT&gt; [bars]</code>, <code>/pnl</code>, <code>/debug on|off</code>",
        "",
        "— <b>Liquidity</b>",
        "<code>/check_liq &lt;MINT&gt;</code>, <code>/auto_liq on|off</code>, <code>/liq_config</code> [Flags]",
    ]
    await update.message.reply_text("\n".join(lines), parse_mode=ParseMode.HTML)    
#===============================================================================
    
async def cmd_sanity(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not guard(update): 
        return
    if not context.args:
        return await send(update, "Nutzung: /sanity <MINT>")
    raw = context.args[0].strip()
    # erlaubt: DS-/pump.fun-URLs oder lange Strings → extrahiere erstes Base58-Match
    m = _SOLANA_ADDR_RE.search(raw)
    mint = m.group(0) if m else raw
    try:
        rep = await sanity_check_token(mint)
        mtr = rep.get("metrics", {})
        lines = [
            f"🛡️ Sanity {mint[:6]}…  Score={rep['score']}  OK={rep['ok']}",
            f"LP≈{mtr.get('lp_sol',0):.2f} SOL  •  vol24≈${int(mtr.get('vol24',0)):,}  •  tx24={int(mtr.get('tx24',0))}  •  age={mtr.get('age_min','n/a')}m",
        ]
        if "top10_share" in mtr:
            lines.append(f"Top10 Share: {mtr['top10_share']*100:.1f}%")
        fa = mtr.get("freezeAuthority"); ma = mtr.get("mintAuthority")
        if fa or ma:
            lines.append(f"Auth: freeze={fa or '-'}  •  mint={ma or '-'}")
        issues = rep.get("issues") or []
        if issues:
            lines.append("Issues: " + ", ".join(issues))
        await send(update, "\n".join(lines))
    except Exception as e:
        await send(update, f"❌ Sanity-Fehler: {e}")
#===============================================================================

async def cmd_status(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not guard(update): 
        return
    sol_balance = client.get_balance(Pubkey.from_string(WALLET_PUBKEY)).value/1e9
    lines = [
        f"ℹ️ RUNNING={RUNNING} | POLLING={'ON' if POLLING_STARTED else 'OFF'}",
        f"Slippage={GMGN_SLIPPAGE_PCT}% | Fee={GMGN_FEE_SOL} SOL",
        f"Debug={DEBUG_SCAN} | Default Notional={DEFAULT_NOTIONAL_SOL} SOL",
        f"PaperMode={'ON' if PAPER_MODE else 'OFF'}",
        f"SOL: {sol_balance:.6f}",
    ]
    await send(update, "\n".join(lines))
#===============================================================================
# Bot Kommandos (SCAN DS)
#===============================================================================
from typing import Dict, Any
from telegram import constants

def _parse_scan_flags(args) -> Dict[str, Any]:
    """
    Flags für /scan_ds:
      --top N
      --max-age M
      --min-lp X
      --min-vol V
      --min-tx T
      --quote {sol|any}
      --hotlist {off|trending|approx|boosts|profiles}
      --pumpfun | --pf
      --safe-only
      --min-score N   (0..100)
    """
    d: Dict[str, Any] = {
        "top": 15,
        "max_age": 90,
        "min_lp": 1.0,
        "min_vol": 2000.0,
        "min_tx": 50,
        "quote": "sol",
        "hotlist": "off",
        "pumpfun": False,
        "safe_only": False,
        "min_score": 0,
    }

    def _norm(tok: str) -> str:
        return (tok
                .replace("—", "-")
                .replace("–", "-")
                .replace("−", "-")
                .replace("-", "-"))

    it = iter([_norm(t) for t in (args or [])])
    for tok in it:
        t = tok.lower()

        # --key=value
        if t.startswith("--top="):
            try: d["top"] = int(t.split("=",1)[1])
            except: pass; continue
        if t.startswith("--max-age=") or t.startswith("--age="):
            try: d["max_age"] = int(t.split("=",1)[1])
            except: pass; continue
        if t.startswith("--min-lp=") or t.startswith("--lp="):
            try: d["min_lp"] = float(t.split("=",1)[1])
            except: pass; continue
        if t.startswith("--min-vol=") or t.startswith("--vol="):
            try: d["min_vol"] = float(t.split("=",1)[1])
            except: pass; continue
        if t.startswith("--min-tx=") or t.startswith("--tx="):
            try: d["min_tx"] = int(t.split("=",1)[1])
            except: pass; continue
        if t.startswith("--quote="):
            q = t.split("=",1)[1].strip().lower()
            d["quote"] = q if q in ("sol","any") else "sol"; continue
        if t.startswith("--hotlist="):
            h = t.split("=",1)[1].strip().lower()
            d["hotlist"] = h; continue
        if t.startswith("--min-score=") or t.startswith("--score="):
            try: d["min_score"] = max(0, min(100, int(t.split("=",1)[1])))
            except: pass; continue

        # klassische --key <value>
        try:
            if t in ("--top","-n"):               d["top"] = int(next(it))
            elif t in ("--max-age","--age"):      d["max_age"] = int(next(it))
            elif t in ("--min-lp","--lp"):        d["min_lp"] = float(next(it))
            elif t in ("--min-vol","--vol"):      d["min_vol"] = float(next(it))
            elif t in ("--min-tx","--tx"):        d["min_tx"] = int(next(it))
            elif t == "--quote":                  d["quote"] = (next(it).strip().lower())
            elif t == "--hotlist":                d["hotlist"] = next(it).strip().lower()
            elif t in ("--pumpfun","--pf"):       d["pumpfun"] = True
            elif t in ("--min-score","--score"):  d["min_score"] = max(0, min(100, int(next(it))))
            elif t in ("--safe-only","--safe"):   d["safe_only"] = True
        except StopIteration:
            break

    if d["hotlist"] not in ("off","trending","approx","boosts","profiles"):
        d["hotlist"] = "off"
    if d["quote"] not in ("sol","any"):
        d["quote"] = "sol"
    return d
#===============================================================================

async def cmd_scan_ds(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not guard(update):
        return

    f = _parse_scan_flags(context.args)
    prefer_sol = (f["quote"] == "sol")
    hot = f["hotlist"]
    safe_only = bool(f.get("safe_only"))
    min_score = int(f.get("min_score") or 0)

    t0 = time.time()
    try:
        # Stage 1: Discovery + Grundgates (LP/Vol/Tx/Age/Quote) laut discover_candidates_ds_only
        cands = await discover_candidates_ds_only(
            top_n=f["top"],
            max_age_min=f["max_age"],
            min_lp_sol=f["min_lp"],
            min_vol24_usd=f["min_vol"],
            min_tx24=f["min_tx"],
            prefer_sol_quote=prefer_sol,
            hotlist=hot,
            pumpfun_only=f["pumpfun"],
        )
    except Exception as e:
        return await send(update, f"❌ scan_ds Fehler: {e}")

    dt = f"{(time.time()-t0):.2f}s"
    src_txt = {
        "off": "search",
        "trending": "trending",
        "approx": "approx-hot",
        "boosts": "boosts",
        "profiles": "profiles",
    }[hot]
    pf_txt  = "on" if f["pumpfun"] else "off"

    if not cands:
        return await send(
            update,
            f"(DexScreener-{src_txt}) keine Kandidaten.\n"
            f"[n={f['top']} age={f['max_age']} lp≥{f['min_lp']} vol24≥{f['min_vol']:.1f} "
            f"tx24≥{f['min_tx']} quote={'SOL' if prefer_sol else 'ANY'} hotlist={hot} pf={pf_txt}] in {dt}"
        )

    # -------- Stage 2: Sanity‑Checks (optional / je nach Flags) ----------
    sanity_map: Dict[str, dict] = {}
    if safe_only or min_score > 0:
        # begrenze Parallelität, damit RPC/GMGN nicht flooden
        MAX_CONC = int(os.environ.get("SANITY_CONC", "6") or 6)
        sem = asyncio.Semaphore(MAX_CONC)

        async def _run(mint: str) -> tuple[str, dict]:
            async with sem:
                try:
                    rep = await sanity_check_token(mint)
                except Exception as e:
                    rep = {"ok": False, "score": 0, "issues": [f"sanity_fail:{e}"], "metrics": {}}
                return mint, rep

        tasks = [asyncio.create_task(_run(c.mint)) for c in cands]
        for coro in asyncio.as_completed(tasks):
            mint, rep = await coro
            sanity_map[mint] = rep

        # Filter anwenden
        def _keep(c):
            rep = sanity_map.get(c.mint) or {}
            score = int(rep.get("score") or 0)
            ok = bool(rep.get("ok"))
            if safe_only and not (ok and score >= max(70, min_score)):  # 70 default
                return False
            if (not safe_only) and (min_score > 0) and score < min_score:
                return False
            return True

        cands = [c for c in cands if _keep(c)]

        if not cands:
            return await send(
                update,
                f"(DexScreener-{src_txt}) keine Kandidaten nach Sanity‑Filter.\n"
                f"[safe_only={safe_only} min_score={min_score}]"
            )

    # -------- Ausgabe bauen ----------
    lines = [f"🧭 Kandidaten (DexScreener {src_txt}){ ' + Sanity' if sanity_map else ''}:"]
    rows_btns = []
    for i, c in enumerate(cands, 1):
        rsn = ",".join(c.reasons)
        # Sanity Felder (falls vorhanden)
        srep = sanity_map.get(c.mint)
        sscore_txt = ""
        issues_txt = ""
        if srep:
            sscore_txt = f" SScore={int(srep.get('score',0))}"
            issues = srep.get("issues") or []
            # nur die wichtigsten kurz darstellen
            key_issues = [x for x in issues if x in (
                "low_liquidity","low_vol24","low_tx24","very_new",
                "route_wsol_fail","top10_concentration_high","top10_concentration_elevated",
                "freeze_authority_set","mint_authority_set"
            )]
            if key_issues:
                issues_txt = " [" + ",".join(key_issues[:3]) + "]"

        lines.append(
            f"{i:02d}. <a href='{c.url}'>{c.symbol}</a> "
            f"(LP≈{c.lp_sol:.1f} SOL, MCAP≈{int(c.mcap_usd):,} USD, "
            f"Vol24≈{int(c.vol24_usd):,} USD, Tx24={c.tx24}, m5 {c.m5_buys}/{c.m5_sells}) "
            f"QScore={c.score:.0f}{sscore_txt} [{rsn}]{issues_txt}"
        )
        rows_btns.append(
            [InlineKeyboardButton(f"➕ {c.symbol} zur Watchlist", callback_data=f"scanadd|{c.mint}")]
        )

    await update.message.reply_text(
        "\n".join(lines) + "\n\n" +
        f"[n={f['top']} age={f['max_age']} lp≥{f['min_lp']} vol24≥{f['min_vol']:.1f} "
        f"tx24≥{f['min_tx']} quote={'SOL' if prefer_sol else 'ANY'} hotlist={hot} pf={pf_txt} "
        f"{'safe-only ' if safe_only else ''}{'min-score='+str(min_score) if min_score>0 else ''}] in {dt}",
        parse_mode=ParseMode.HTML,
        disable_web_page_preview=True,
        reply_markup=InlineKeyboardMarkup(rows_btns)
    )
#===============================================================================

async def on_scan_add_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not guard(update): 
        return
    q = update.callback_query
    if not q:
        return
    try:
        data = q.data or ""
        if data.startswith("scanadd|"):
            mint = data.split("|", 1)[1].strip()
            msg = ""
            if mint and mint not in WATCHLIST:
                WATCHLIST.append(mint)
                msg = f"✅ In Watchlist: {mint[:6]}…"
            else:
                msg = f"ℹ️ Bereits in Watchlist: {mint[:6]}…"
            await q.answer("OK")
            await q.edit_message_reply_markup(reply_markup=None)
            await q.message.reply_text(msg)
    except Exception as e:
        await q.answer("Fehler")
        await q.message.reply_text(f"❌ add Fehler: {e}")
#===============================================================================

async def cmd_dsdiag(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not guard(update): return
    p = _get_ds_proxy()
    await send(update, f"DS_PROXY_URL env={'SET' if os.environ.get('DS_PROXY_URL') else 'unset'} | active={'ON' if p else 'OFF'} ({p or '-'})")



    def _probe(u: str) -> str:
        try:
            r = http_get(_wrap(u), headers=_ds_headers(), timeout=10)
            ct = (r.headers.get("content-type") or "")[:30]
            head = (r.text[:120] if hasattr(r, "text") else str(r)[:120]).replace("\n"," ")
            return f"{u.replace(DS_BASE,'/dex')} -> {r.status_code}, ct={ct}, len={len(r.text)}, head='{head}'"
        except Exception as e:
            return f"{u.replace(DS_BASE,'/dex')} FAIL: {e}"

    urls = [
        f"{DS_BASE}/trending?include=solana",
        "https://api.dexscreener.com/token-boosts/latest/v1",
        "https://api.dexscreener.com/token-boosts/top/v1",
        "https://api.dexscreener.com/token-profiles/latest/v1",
        f"{DS_BASE}/search?q=solana",
        f"{DS_BASE}/search?q=raydium",
        # /new-pairs kann 403 liefern → rein informativ:
        f"{DS_BASE}/new-pairs?include=solana",
    ]
    lines = [_probe(u) for u in urls]
    await send(update, "\n".join(lines))
#===============================================================================

async def cmd_set_proxy(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not guard(update):
        return
    arg = " ".join(context.args).strip() if context.args else ""
    if not arg or arg.lower() in ("status", "show"):
        p = _get_ds_proxy()
        return await send(
            update,
            f"🔌 DexScreener-Proxy: {'ON → ' + p if p else 'OFF'}\n"
            f"Nutze: /set_proxy off  |  /set_proxy https://dein-proxy.example"
        )

    if arg.lower() in ("off", "0", "none", "disable", "disabled"):
        os.environ.pop("DS_PROXY_URL", None)
        return await send(update, "🔌 DexScreener-Proxy: OFF")

    # sonst: Wert als URL interpretieren
    val = arg.strip()
    try:
        u = urlparse(val)
        if u.scheme in ("http", "https") and u.netloc:
            os.environ["DS_PROXY_URL"] = val.rstrip("/")
            return await send(update, f"🔌 DexScreener-Proxy: ON → {os.environ['DS_PROXY_URL']}")
        else:
            return await send(
                update,
                "❌ Ungültige URL. Beispiel:\n/set_proxy https://mein-proxy.example"
            )
    except Exception:
        return await send(update, "❌ Konnte URL nicht parsen. Bitte vollständige http(s)-URL angeben.")

#===============================================================================        
# --- NEU: /trending (kompakte Top-Liste auf Basis der DS-Search) ---
async def cmd_trending(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not guard(update):
        return

    # Args: N [focus] [quote]
    n = 20
    focus = "volume24"   # volume24 | liquidity | tx24 | new | momentum
    quote = "sol"        # sol | any
    try:
        if len(context.args) >= 1: n = max(1, int(context.args[0]))
        if len(context.args) >= 2:
            f = context.args[1].lower()
            if f in ("vol","volume","volume24"): focus = "volume24"
            elif f in ("liq","liquidity"):       focus = "liquidity"
            elif f in ("tx","tx24"):             focus = "tx24"
            elif f in ("new","fresh"):           focus = "new"
            elif f in ("mom","momo","momentum"): focus = "momentum"
        if len(context.args) >= 3:
            q = context.args[2].lower()
            if q in ("sol","any"): quote = q
    except Exception:
        pass

    # Wir nutzen die bereits vorhandene Discovery-Routine mit lockeren Filtern
    prefer_sol = (quote == "sol")
    # lockere baseline, damit etwas kommt
    cands = await discover_candidates_ds_only(
        top_n=n,
        max_age_min=1440,
        min_lp_sol=0.3,
        min_vol24_usd=300.0,
        min_tx24=8,
        prefer_sol_quote=prefer_sol,
        hotlist="approx" if focus in ("new","momentum") else "off",   # approx ist Search-basiert
        pumpfun_only=False,
    )

    if not cands:
        return await update.effective_chat.send_message(
            f"(Trending) keine Treffer. n={n} focus={focus} quote={quote}"
        )
#===============================================================================

    # Sortierung je nach Fokus
    def key(c):
        if focus == "liquidity": return c.lp_sol
        if focus == "tx24":      return c.tx24
        if focus == "new":       return -1  # Reihenfolge aus DS (nahe genug)
        if focus == "momentum":  return c.m5_buys - c.m5_sells
        return c.vol24_usd  # volume24 default
    rev = (focus != "new")
    cands.sort(key=key, reverse=rev)

    lines = []
    for i, c in enumerate(cands[:n], 1):
        lines.append(
            f"{i:02d}. <a href='{c.url}'>{c.symbol}</a> "
            f"| vol24≈ ${int(c.vol24_usd):,} | liq≈{c.lp_sol:.1f} SOL | tx24={c.tx24} | m5 {c.m5_buys}/{c.m5_sells}"
        )
    await update.effective_chat.send_message(
        "🔥 Trending (Search-basiert):\n" + "\n".join(lines),
        parse_mode=ParseMode.HTML,
        disable_web_page_preview=True,
    )
#===============================================================================
# --- RAW: DS search helper mit Alias-Normalisierung
async def cmd_dsraw(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not guard(update):
        return

    # 1) Query aus Args, sonst eine kleine Default-Kaskade (ohne 'chain:solana')
    user_q = " ".join(context.args).strip() if context.args else None
    queries = [user_q] if user_q else ["quoteToken:SOL", "raydium", "sol usdc", "pumpfun"]

    def _fmt_usd(x: float) -> str:
        try:
            return f"${int(float(x)):,}"
        except Exception:
            try:
                return f"${float(x):,.2f}"
            except Exception:
                return "$0"

    async def _search(q: str) -> list[dict]:
        js = await _get_json(_wrap(f"{DS_BASE}/search?q={quote_plus(q)}"))
        pairs = (js or {}).get("pairs") or []
        return [p for p in pairs if (p.get("chainId") or "").lower() == "solana"]

    # Telegram texts können 4096 Zeichen – wir schicken in Seiten
    PAGE_SIZE = 12  # wie viele Paare pro Nachricht
    for q in queries:
        if not q:
            continue

        try:
            pairs = await _search(q)
        except Exception as e:
            await send(update, f"dsraw:\n🔎 q='{q}' → Fehler: {e}")
            continue

        header = f"dsraw:\n🔎 q='{q}' → {len(pairs)} Solana-Paare"
        if not pairs:
            await update.effective_chat.send_message(header, parse_mode=ParseMode.HTML)
            continue

        # Seitenweise ausgeben
        for i in range(0, len(pairs), PAGE_SIZE):
            chunk = pairs[i:i + PAGE_SIZE]
            lines = [header] if i == 0 else [f"(weiter q='{q}')"]

            for p in chunk:
                base = (p.get("baseToken") or {})
                sym  = (base.get("symbol") or "").strip()
                name = (base.get("name") or "").strip()
                display = sym or name or "?"
                mint = (base.get("address") or "").strip()

                # Link: bevorzugt DS-URL; sonst pairAddress; sonst Mint
                pair_addr = (p.get("pairAddress") or "").strip()
                url = (p.get("url") or
                       (f"https://dexscreener.com/solana/{pair_addr}" if pair_addr else
                        f"https://dexscreener.com/solana/{mint}"))

                liq_usd = float(((p.get("liquidity") or {}).get("usd") or 0.0))
                vol24   = float(((p.get("volume") or {}).get("h24") or 0.0))
                txh     = (p.get("txns") or {}).get("h24") or {}
                tx24    = int(txh.get("buys") or 0) + int(txh.get("sells") or 0)

                open_tag = ""
                if mint in OPEN_POS:
                    pos = OPEN_POS[mint]
                    try:
                        open_tag = f" • <b>OPEN</b> qty={pos.qty:.6f} @ {pos.entry_price:.6f}"
                    except Exception:
                        open_tag = " • <b>OPEN</b>"

                # Zeile mit anklickbarem Namen
                lines.append(
                    f"- <a href='{url}'>{display}</a> | "
                    f"liq≈{_fmt_usd(liq_usd)} | vol24≈{_fmt_usd(vol24)} | tx24={tx24}"
                    f"{open_tag}"
                )

            await update.effective_chat.send_message(
                "\n".join(lines),
                parse_mode=ParseMode.HTML,
                disable_web_page_preview=True,
            )


#===============================================================================
# ---- Telegram Command: /ds_trending --------------------------------------
# ===== Stable "Trending" Builder (Boosts + Profiles) =====
async def _collect_trending_like_pairs_from_boosts_profiles(max_items: int = 400) -> list[dict]:
    """
    Baut eine Solana-Hotlist aus stabilen Quellen:
      - token-boosts/latest + token-boosts/top
      - token-profiles/latest
    und lädt zu jeder Mint die Pair-Details via /latest/dex/tokens/solana/<mint>.
    """
    # a) Quelle 1: Boosts
    boosts_pairs = await _fetch_pairs_from_boosts(max_items=max_items // 2)

    # b) Quelle 2: Profiles
    prof_pairs = await _fetch_pairs_from_profiles(max_items=max_items // 2)

    # c) Merge + Dedupe (nach pairAddress)
    out: list[dict] = []
    seen_pairs: set[str] = set()
    for src in (boosts_pairs or []):
        pid = str(src.get("pairAddress") or "")
        if pid and pid not in seen_pairs:
            out.append(src); seen_pairs.add(pid)
    for src in (prof_pairs or []):
        pid = str(src.get("pairAddress") or "")
        if pid and pid not in seen_pairs:
            out.append(src); seen_pairs.add(pid)
    return out
#===============================================================================

async def _ds_trending_solana_pairs_v2(limit: int = 25) -> list[dict]:
    """
    Stabiler Trending-Fetch:
      1) Ein Versuch via /latest/dex/trending?include=solana (kann 403/leer sein)
      2) Fallback: "Trending-ähnlich" aus Boosts + Profiles, nach vol24/tx24/Momentum sortiert.
    """
    # --- 1) "weicher" Versuch: echter Endpoint (kann 403/HTML liefern) ---
    try:
        js = await _get_json(_wrap(f"{DS_BASE}/trending?include=solana"))
        if isinstance(js, dict):
            pairs = (js.get("pairs") or [])
            pairs = [p for p in pairs if (p.get("chainId") or "").lower() == "solana"]
            if pairs:
                def _vol24(p):
                    try:
                        return float(((p.get("volume") or {}).get("h24") or 0.0))
                    except Exception:
                        return 0.0
                pairs.sort(key=_vol24, reverse=True)
                return pairs[:max(1, int(limit))]
    except Exception:
        # ignorieren – wir fallen unten sauber zurück
        pass

    # --- 2) Robuster Fallback: Boosts + Profiles zusammenziehen ---
    pairs = await _collect_trending_like_pairs_from_boosts_profiles(max_items=limit * 6)
    if not pairs:
        return []

    # Scoring ~ UI-Feeling: vol24 (dominant) + tx24 + kurzes Momentum (m5 Buys - Sells) + etwas LP
    def _score(p: dict) -> tuple:
        try:
            vol24 = float(((p.get("volume") or {}).get("h24") or 0.0))
        except Exception:
            vol24 = 0.0
        txh = (p.get("txns") or {}).get("h24") or {}
        try:
            tx24 = int(txh.get("buys") or 0) + int(txh.get("sells") or 0)
        except Exception:
            tx24 = 0
        m5 = (p.get("txns") or {}).get("m5") or {}
        try:
            m5_momo = int(m5.get("buys") or 0) - int(m5.get("sells") or 0)
        except Exception:
            m5_momo = 0
        lp = _lp_sol_of_pair(p)
        # Vol24 am stärksten, dann Tx, dann Momentum, dann LP
        return (vol24, tx24, m5_momo, lp)

    pairs.sort(key=_score, reverse=True)

    # Unique nach baseToken.address, dann hart auf limit schneiden
    seen_mints: set[str] = set()
    out: list[dict] = []
    for p in pairs:
        if (p.get("chainId") or "").lower() != "solana":
            continue
        mint = ((p.get("baseToken") or {}).get("address")) or ""
        if not mint or mint in seen_mints:
            continue
        out.append(p)
        seen_mints.add(mint)
        if len(out) >= max(1, int(limit)):
            break
    return out
 #===============================================================================
 # Sichtarmachen Beobachtungsliste   
async def cmd_aw_observe(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """
    Zeigt die persistente Observe-Liste (AW_STATE['observed']) mit kompakten Kennzahlen:
      • Name (DexScreener-Link) + Mint-Kürzel
      • Alter (PairCreatedAt)
      • 24h-Volumen, FDV (mcap)
      • Momentum: m5_buys / m5_sells und Δ
      • Buttons: ➕ Add (in Watchlist übernehmen), 🗑 Remove (aus Observe entfernen)
    Sortiert nach Momentum (m5_buys - m5_sells) absteigend.
    Bei AutoWatch ON & leerer Liste: führt 1× sofort aw_discover_once() aus (Auto-Refresh),
    zeigt immer AW-Status (ON/OFF) und last run.
    """
    if not guard(update):
        return

    DS_TOKENS_URL = "https://api.dexscreener.com/tokens/v1/solana"
    ttl_sec = max(1, int(os.environ.get("AW_OBS_TTL_MIN", "30")) * 60)

    def _fmt_usd(x: float) -> str:
        try:
            return f"${int(x):,}"
        except Exception:
            try:
                return f'${float(x):,.2f}'
            except Exception:
                return "$0"

    async def _snapshot_for(mint: str, sym_hint: str, ts_saved: int) -> dict:
        """
        Holt DS-Paar für Mint (liquidestes Pair) und extrahiert Kennzahlen.
        Rückgabe: dict mit name,url,age_txt,vol24,mcap,m5_buys,m5_sells,delta,ttl
        """
        snap = {
            "mint": mint, "name": sym_hint or f"{mint[:6]}…",
            "url": f"https://dexscreener.com/solana/{mint}",
            "age_txt": "n/a", "vol24": 0.0, "mcap": 0.0,
            "m5_buys": 0, "m5_sells": 0, "delta": 0,
            "ttl": max(0, ttl_sec - (int(time.time()) - int(ts_saved))),
        }
        try:
            js = await _get_json(_wrap(f"{DS_TOKENS_URL}/{mint}"))
            pairs = (js or {}).get("pairs") or []
            best = _ds_pick_best_sol_pair(pairs) if pairs else None
            if best is None and pairs:
                best = pairs[0]
            if best:
                base = (best.get("baseToken") or {})
                name = (base.get("symbol") or "") or (base.get("name") or "")
                if name:
                    snap["name"] = name
                url = best.get("url")
                if url:
                    snap["url"] = url

                ms = int(best.get("pairCreatedAt") or best.get("createdAt") or best.get("poolCreatedAt") or 0)
                snap["age_txt"] = _fmt_age_from_ms(ms)

                vol = (best.get("volume") or {})
                snap["vol1h"] = float(vol.get("h1") or 0.0)    # optional
                snap["vol24"] = float(vol.get("h24") or 0.0)
                snap["mcap"]  = float(best.get("fdv")  or 0.0)

                m5 = (best.get("txns") or {}).get("m5") or {}
                b = int(m5.get("buys")  or 0)
                s = int(m5.get("sells") or 0)
                snap["m5_buys"], snap["m5_sells"], snap["delta"] = b, s, (b - s)
        except Exception:
            # Fallback: nur Name/Alter
            try:
                nm, ag = dexscreener_token_meta(mint)
                if nm: snap["name"] = nm
                if ag: snap["age_txt"] = ag
            except Exception:
                pass
        return snap

    # --- Status einlesen
    aw_on   = bool(AW_CFG.get("enabled"))
    last_ts = int(AW_STATE.get("last_run_ts") or 0)
    now_ts  = int(time.time())
    last_age = f"{now_ts - last_ts}s" if last_ts > 0 else "n/a"

    # --- Observe-Map initial laden
    observed_map = AW_STATE.get("observed", {}) or {}

    # --- Auto-Refresh, wenn AW ON & Liste leer
    if aw_on and not observed_map:
        try:
            await aw_discover_once()
            observed_map = AW_STATE.get("observed", {}) or {}
            last_ts = int(AW_STATE.get("last_run_ts") or last_ts)
            now_ts  = int(time.time())
            last_age = f"{now_ts - last_ts}s" if last_ts > 0 else "n/a"
        except Exception:
            pass

    # --- Wenn weiterhin leer: statusorientierte Meldung
    if not observed_map:
        if not aw_on:
            return await send(
                update,
                "👁️‍🗨️ Observe: – (leer)\n"
                "ℹ️ Auto-Watchlist ist AUS. Mit /autowatch on einschalten und Schwellen via /aw_config setzen."
            )
        else:
            return await send(
                update,
                "👁️‍🗨️ Observe: – (leer)\n"
                f"AW: ON • last run: {last_age}\n"
                "ℹ️ Aktuell erfüllt kein Kandidat die Observe-Schwellen.\n"
                "Tipp: /aw_now (sofortiger Run), /aw_status (Schwellen prüfen), ggf. Observe-Schwellen absenken."
            )

    # --- TTL-Prune (server-side)
    pruned_any = False
    for m, meta in list(observed_map.items()):
        saved_ts = int(meta.get("ts", 0) or 0)
        if now_ts - saved_ts >= ttl_sec:
            observed_map.pop(m, None)
            pruned_any = True
    if pruned_any:
        _aw_save_state(AW_STATE)

    # --- Snapshots (nach TTL-Prune)
    mints = list(observed_map.keys())
    tasks = [asyncio.create_task(_snapshot_for(m, observed_map[m].get("sym",""), int(observed_map[m].get("ts", 0)))) for m in mints]
    snaps = await asyncio.gather(*tasks)

    # sort by momentum Δ desc then vol24 desc
    snaps.sort(key=lambda x: (x.get("delta", 0), x.get("vol24", 0.0)), reverse=True)

    # --- Header
    header = [
        f"👁️‍🗨️ <b>Observe (persist.)</b> – {len(snaps)} Einträge  |  TTL≈{int(ttl_sec/60)} min",
        f"AW: {'ON' if aw_on else 'OFF'} • last run: {last_age}",
        "Sortierung: Δ(m5_buys−m5_sells) ⟶ Vol24",
        ""
    ]
    try:
        await update.effective_chat.send_message("\n".join(header), parse_mode=ParseMode.HTML)
    except Exception:
        pass

    # --- Chunked output (5 pro Nachricht)
    page: list[str] = []
    for i, s in enumerate(snaps, 1):
        mint = s["mint"]; name = s["name"]; url = s["url"]
        delta = s.get("delta", 0)
        vol24 = _fmt_usd(s.get("vol24", 0.0))
        mcap  = _fmt_usd(s.get("mcap", 0.0))
        age   = s.get("age_txt", "n/a")
        mb, ms = s.get("m5_buys", 0), s.get("m5_sells", 0)
        ttl_left = max(0, int(observed_map.get(mint,{}).get("ts",0) + ttl_sec - now_ts))
        ttl_min  = max(0, int(ttl_left/60))

        line = (f"{i:02d}. <a href=\"{url}\">{name}</a> ({mint[:6]}…)"
                f"\n   • age={age} • mcap≈{mcap} • vol24≈{vol24} • m5 {mb}/{ms} • Δ={delta:+d} • TTL≈{ttl_min}m")
        page.append(line)

        # flush every 5 lines or at end
        if len(page) == 5 or i == len(snaps):
            text = "\n".join(page)
            kb = [[InlineKeyboardButton("⟳ Refresh", callback_data="obs_refresh")]]
            await update.effective_chat.send_message(
                text, parse_mode=ParseMode.HTML,
                disable_web_page_preview=False,
                reply_markup=InlineKeyboardMarkup(kb)
            )
            # Per-Entry Aktionszeilen (Add/Remove)
            start_idx = i - len(page) + 1
            for j in range(start_idx, i + 1):
                s2 = snaps[j-1]
                m2 = s2["mint"]; nm2 = s2["name"]; url2 = s2["url"]
                pos = OPEN_POS.get(m2)
                entry_px = float(getattr(pos, 'entry_price', 0.0)) if pos else 0.0
                open_tag = f" • <b>OPEN</b> qty={pos.qty:.6f} @ {entry_px:.6f}" if (pos and getattr(pos, 'qty', 0.0)) else ""
                row_text = f"↳ <a href=\"{url2}\">{nm2}</a> ({m2[:6]}…){open_tag}"
                row_kb = InlineKeyboardMarkup([
                    [
                        InlineKeyboardButton("➕ Add to Watchlist", callback_data=f"obsadd|{m2}"),
                        InlineKeyboardButton("🗑 Remove",          callback_data=f"obsrm|{m2}")
                    ]
                ])
                await update.effective_chat.send_message(
                    row_text, parse_mode=ParseMode.HTML,
                    reply_markup=row_kb, disable_web_page_preview=True
                )
            page = []

    if pruned_any:
        await send(update, "🧹 Abgelaufene Observe-Einträge wurden entfernt.")
        
async def on_observe_add_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """
    Callback: Kandidat aus Observe in die WATCHLIST übernehmen und aus Observe streichen.
    """
    q = update.callback_query
    try:
        await q.answer()
    except Exception:
        pass

    data = (q.data or "")
    if not data.startswith("obsadd|"):
        return
    mint = data.split("|", 1)[1].strip()

    # Add to watchlist
    added = False
    if mint not in WATCHLIST:
        WATCHLIST.append(mint)
        AW_STATE["mints"][mint] = {
            "added_ts": int(time.time()), "last_active_ts": int(time.time()),
            "last_score": 0, "source": "observe"
        }
        added = True

    # Remove from observe store
    try:
        AW_STATE.setdefault("observed", {}).pop(mint, None)
        _aw_save_state(AW_STATE)
    except Exception:
        pass

    # Feedback
    name, _ag = dexscreener_token_meta(mint)
    if added:
        await q.message.reply_text(f"✅ In Watchlist: {name or mint[:6] + '…'}")
    else:
        await q.message.reply_text(f"ℹ️ Bereits in Watchlist: {name or mint[:6] + '…'}")
    try:
        await q.edit_message_reply_markup(reply_markup=None)
    except Exception:
        pass


async def on_observe_remove_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """
    Callback: Kandidat aus der Observe-Merkliste entfernen (ohne zur Watchlist zu nehmen).
    """
    q = update.callback_query
    try:
        await q.answer()
    except Exception:
        pass

    data = (q.data or "")
    if not data.startswith("obsrm|"):
        return

    mint = data.split("|", 1)[1].strip()
    removed = False
    try:
        AW_STATE.setdefault("observed", {})
        if mint in AW_STATE["observed"]:
            AW_STATE["observed"].pop(mint, None)
            _aw_save_state(AW_STATE)
            removed = True
    except Exception:
        pass

    name, _ag = dexscreener_token_meta(mint)
    if removed:
        await q.message.reply_text(f"🗑 Entfernt aus Observe: {name or mint[:6] + '…'}")
    else:
        await q.message.reply_text(f"ℹ️ Nicht in Observe gefunden: {name or mint[:6] + '…'}")
    try:
        await q.edit_message_reply_markup(reply_markup=None)
    except Exception:
        pass

#===============================================================================
# ---- Telegram Command: /ds_trending  (ersetzt alte Version) --------------
async def cmd_ds_trending(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not guard(update):
        return

    # Optional: Anzahl
    try:
        limit = int(context.args[0]) if (context.args and context.args[0].strip()) else 25
    except Exception:
        limit = 25

    pairs = await _ds_trending_solana_pairs_v2(limit)
    if not pairs:
        return await send(update, "(trending) keine Paare gefunden (Boosts/Profiles leer).")

    lines = []
    for i, p in enumerate(pairs, 1):
        base = (p.get("baseToken") or {})
        sym  = (base.get("symbol")  or "?").strip()
        addr = (base.get("address") or "").strip()

        px   = float(p.get("priceUsd") or p.get("price") or 0.0)
        liq  = float(((p.get("liquidity") or {}).get("usd")  or 0.0))
        vol  = float(((p.get("volume")   or {}).get("h24")   or 0.0))
        txh  = (p.get("txns") or {}).get("h24") or {}
        tx24 = int(txh.get("buys") or 0) + int(txh.get("sells") or 0)

        age  = _fmt_age_from_ms(
            p.get("pairCreatedAt") or p.get("createdAt") or p.get("poolCreatedAt")
        )

        url  = p.get("url") or f"https://dexscreener.com/solana/{addr}"
        lines.append(
            f"{i:02d}. <a href='{url}'>{sym}</a> "
            f"px={px:.8f} | liq≈${int(liq):,} | vol24≈${int(vol):,} | tx24={tx24} | age={age}"
        )

    await update.message.reply_text(
        "\n".join(lines),
        parse_mode=ParseMode.HTML,
        disable_web_page_preview=True,
    )
# ===== P&L / CSV v2 (Decimal, token name, entry/exit, realized column) =====
from decimal import Decimal, ROUND_HALF_UP, getcontext
getcontext().prec = 28  # ausreichend Präzision

# CSV-Schema v2
CSV_FIELDS_V2 = [
    "ts", "ts_iso",
    "side", "mint", "token",
    "qty",
    "entry_px", "exit_px",
    "realized_usd",
    "sig", "status", "note",
]
# Altes Schema (Migration)
CSV_FIELDS_OLD = ["ts","side","mint","qty","sig","status","note"]

def _ts_to_iso(ts: int) -> str:
    try:
        return dt.datetime.fromtimestamp(int(ts), dt.UTC).strftime("%Y-%m-%d %H:%M:%S")
    except Exception:
        return ""
#===============================================================================

def _q(x, nd=2, default="0"):
    """Decimal-Quantize mit nd Nachkommastellen → String."""
    try:
        q = "0." + ("0"*(nd-1)) + "1" if nd>0 else "1"
        return str(Decimal(str(x)).quantize(Decimal(q), rounding=ROUND_HALF_UP))
    except Exception:
        return default
#===============================================================================

def _safe_name_for_mint(mint: str) -> str:
    try:
        name, _age = dexscreener_token_meta(mint)
        return name
    except Exception:
        return mint[:6] + "…"
#===============================================================================

def ensure_csv() -> None:
    """
    - legt v2-CSV an, wenn nicht vorhanden
    - migriert CSV mit altem Header automatisch auf v2
    """
    if not os.path.exists(PNL_CSV):
        with open(PNL_CSV, "w", newline="", encoding="utf-8") as f:
            w = csv.DictWriter(f, fieldnames=CSV_FIELDS_V2); w.writeheader()
        return

    # Header prüfen
    try:
        with open(PNL_CSV, "r", newline="", encoding="utf-8") as f:
            rd = csv.reader(f)
            header = next(rd, [])
    except Exception:
        header = []

    if header == CSV_FIELDS_V2:
        return

    if header == CSV_FIELDS_OLD:
        # Upgrade: alte Zeilen in neues Schema mappen
        try:
            with open(PNL_CSV, "r", newline="", encoding="utf-8") as f:
                rdr = csv.DictReader(f)
                old_rows = list(rdr)
        except Exception:
            old_rows = []

        new_rows = []
        for r in old_rows:
            ts = r.get("ts") or ""
            note = r.get("note") or ""
            new_rows.append({
                "ts": ts,
                "ts_iso": _ts_to_iso(ts) if ts else "",
                "side": r.get("side") or "",
                "mint": r.get("mint") or "",
                "token": "",  # historisch unbekannt
                "qty": _q(r.get("qty") or 0, 6, "0"),
                "entry_px": "",
                "exit_px":  "",
                "realized_usd": _q(_extract_realized(note), 2, "0"),
                "sig": r.get("sig") or "",
                "status": r.get("status") or "",
                "note": note,
            })

        with open(PNL_CSV, "w", newline="", encoding="utf-8") as f:
            w = csv.DictWriter(f, fieldnames=CSV_FIELDS_V2)
            w.writeheader()
            for r in new_rows:
                w.writerow(r)
        return

    # unbekannter Header → sichern & neu anlegen
    try:
        os.replace(PNL_CSV, PNL_CSV + ".bak")
    except Exception:
        pass
    with open(PNL_CSV, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=CSV_FIELDS_V2); w.writeheader()
#===============================================================================

def log_trade_detailed(
    side: str, mint: str, qty: float, sig: str, status: str,
    *, entry_px: float | None = None, exit_px: float | None = None,
    realized_usd: float | None = None, note: str = ""
) -> None:
    """
    Neuer, detaillierter Logger (v2-Schema).
    - schreibt Token-Name, Entry/Exit, Realized, ISO-Timestamp
    - robust gegen Rundungs-/Formatfehler (Decimal)
    """
    ensure_csv()
    ts = int(time.time())
    row = {
        "ts": ts,
        "ts_iso": _ts_to_iso(ts),
        "side": side,
        "mint": mint,
        "token": _safe_name_for_mint(mint),
        "qty": _q(qty, 6, "0"),
        "entry_px": _q(entry_px, 6, "") if entry_px is not None else "",
        "exit_px":  _q(exit_px,  6, "") if exit_px  is not None else "",
        "realized_usd": _q(realized_usd, 2, "") if realized_usd is not None else "",
        "sig": sig,
        "status": status,
        "note": note or "",
    }
    with open(PNL_CSV, "a", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=CSV_FIELDS_V2)
        if f.tell() == 0:
            w.writeheader()
        w.writerow(row)
#===============================================================================
# Rückwärtskompatibel: alte Signatur auf neuen Logger mappen
def log_trade(side: str, mint: str, qty: float, sig: str, status: str, note: str = ""):
    log_trade_detailed(side, mint, qty, sig, status, note=note)
#===============================================================================
# ---------- CSV lesen / Realized extrahieren (Decimal-sicher) ----------
def _load_trades_csv() -> list:
    if not os.path.exists(PNL_CSV):
        return []
    try:
        with open(PNL_CSV, "r", newline="", encoding="utf-8") as f:
            return list(csv.DictReader(f))
    except Exception:
        return []

# robustes Parsing von "realized=..." (mit Tausenderpunkten/‑kommas)
_REALIZED_RE = re.compile(
    r"realized\s*=\s*([+-]?\d{1,3}(?:[.,]\d{3})*(?:[.,]\d+)?|[+-]?\d+(?:[.,]\d+)?)",
    re.I
)
#===============================================================================

def _parse_num_like(s: str) -> Decimal:
    s = (s or "").strip().replace(" ", "")
    if not s:
        return Decimal("0")
    # 9.327,35  ->  9327.35
    if s.count(",")==1 and s.count(".")>=1 and s.rfind(",")>s.rfind("."):
        s = s.replace(".", "").replace(",", ".")
    # 9,327.35 -> 9327.35
    elif s.count(".")==1 and s.count(",")>=1 and s.rfind(".")>s.rfind(","):
        s = s.replace(",", "")
    # 9327,35  -> 9327.35
    elif s.count(",")==1 and s.count(".")==0:
        s = s.replace(",", ".")
    else:
        s = s.replace(",", "")
    try:
        return Decimal(s)
    except Exception:
        return Decimal("0")
#===============================================================================

def _extract_realized(note: str) -> float:
    m = _REALIZED_RE.search(note or "")
    if not m:
        return 0.0
    val = _parse_num_like(m.group(1))
    return float(val.quantize(Decimal("0.01"), rounding=ROUND_HALF_UP))
#===============================================================================

def _realized_from_row(r: dict) -> Decimal:
    # bevorzugt v2-Spalte
    v = (r.get("realized_usd") or "").strip()
    if v != "":
        return _parse_num_like(v)
    # Fallback: aus alter Note
    return Decimal(str(_extract_realized(r.get("note") or "")))
#===============================================================================

def _pnl_by_mint_from_csv() -> Dict[str, float]:
    """Aggregiert realisierte PnL pro Mint aus SELL-/PAPER‑SELL‑Zeilen."""
    rows = _load_trades_csv()
    agg: Dict[str, Decimal] = {}
    for r in rows:
        side = (r.get("side") or "").upper()
        if "SELL" not in side:
            continue
        mint = r.get("mint") or ""
        agg[mint] = agg.get(mint, Decimal("0")) + _realized_from_row(r)
    # sauber auf 2 NK runden
    return {k: float(v.quantize(Decimal("0.01"), rounding=ROUND_HALF_UP)) for k, v in agg.items()}

#===============================================================================
# Watchlist (nach Volumen sortiert + DexScreener-Link)
#===============================================================================
async def on_cb_remove_watch(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Callback für '🗑 Remove' in /list_watch."""
    q = update.callback_query
    try:
        await q.answer()
    except Exception:
        pass

    data = (q.data or "")
    if not data.startswith("rmw|"):
        return

    mint = data.split("|", 1)[1].strip()

    removed = False
    if mint in WATCHLIST:
        WATCHLIST.remove(mint)
        removed = True
        # <<< FIX: State freigeben, wenn keine offene Position vorhanden
        if mint not in OPEN_POS:
            _drop_mint_state(mint)

    try:
        await q.edit_message_reply_markup(reply_markup=None)
    except Exception:
        pass

    try:
        name, _age = dexscreener_token_meta(mint)
    except Exception:
        name = mint[:6] + "…"

    if removed:
        await q.message.chat.send_message(f"🗑 Entfernt: {name} ({mint[:6]}…)")
    else:
        await q.message.chat.send_message(f"ℹ️ Bereits nicht mehr in Watchlist: {name} ({mint[:6]}…)")



async def cmd_list_watch(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """
    Zeigt die Watchlist (nach 24h-Volumen absteigend) mit:
      - Name als anklickbaren DexScreener-Link
      - Alter (Pair-Erstellungszeit)
      - FDV (mcap) und 24h-Volumen
      - OPEN-Status (qty @ entry) falls Position existiert
    """
    if not guard(update):
        return

    if not WATCHLIST:
        return await send(update, "👀 Watchlist: -")

    # Formatter
    def _fmt_usd(x: float) -> str:
        try:
            return f"${int(x):,}"
        except Exception:
            try:
                return f"${float(x):,.2f}"
            except Exception:
                return "$0"

    def _age_from_pair(p: dict) -> str:
        try:
            ms = (p.get("pairCreatedAt") or p.get("createdAt") or p.get("poolCreatedAt") or 0)
            return _fmt_age_from_ms(int(ms) if ms else 0)
        except Exception:
            return "n/a"

    # DS-Daten pro Mint (konkurrenzbegrenzt) holen
    sem = asyncio.Semaphore(6)

    async def _fetch_row(mint: str) -> Tuple[str, str, str, float, float]:
        """
        Rückgabe: (mint, html_name_link, age_txt, mcap_usd, vol24_usd)
        """
        async with sem:
            # Defaults
            default_name = mint[:6] + "…"
            name = default_name
            url = f"https://dexscreener.com/solana/{mint}"
            age_txt = "n/a"
            mcap_usd = 0.0
            vol24_usd = 0.0

            try:
                js = _ds_get_json(f"https://api.dexscreener.com/tokens/v1/solana/{mint}", timeout=10)
                pairs = js.get("pairs") if isinstance(js, dict) else []
                best = _ds_pick_best_sol_pair(pairs) if pairs else None
                if best:
                    base = (best.get("baseToken") or {})
                    sym  = (base.get("symbol") or "").strip()
                    nm   = (base.get("name")   or "").strip()
                    name = sym or nm or name
                    url  = best.get("url") or url
                    age_txt = _age_from_pair(best)
                    try:
                        vol24_usd = float(((best.get("volume") or {}).get("h24") or 0.0))
                    except Exception:
                        vol24_usd = 0.0
                    try:
                        mcap_usd = float(best.get("fdv") or 0.0)
                    except Exception:
                        mcap_usd = 0.0
            except Exception:
                # keine Netzwerkausgabe/Send hier – nur Fallbacks
                pass

            # Zusätzlicher Fallback nur für Name/Alter
            if name == default_name or age_txt == "n/a":
                try:
                    nm2, ag2 = dexscreener_token_meta(mint)
                    if name == default_name and nm2:
                        name = nm2
                    if age_txt == "n/a" and ag2:
                        age_txt = ag2
                except Exception:
                    pass

            html_link = f"<a href='{url}'>{name}</a>"
            return (mint, html_link, age_txt, mcap_usd, vol24_usd)

    # Daten holen
    tasks = [asyncio.create_task(_fetch_row(m)) for m in WATCHLIST]
    results = await asyncio.gather(*tasks, return_exceptions=False)

    # Sortierung: Volumen 24h absteigend
    results.sort(key=lambda r: (r[4] or 0.0), reverse=True)

    # Kopfzeile
    try:
        await update.effective_chat.send_message(
            "👀 Watchlist (nach 24h-Volumen absteigend):",
            parse_mode=ParseMode.HTML
        )
    except Exception:
        pass

    # Ausgabe pro Token + Buttons
    for (mint, html_name_link, age_txt, mcap_usd, vol24_usd) in results:
        # OPEN-Status
        pos = OPEN_POS.get(mint)
        open_txt = ""
        if pos and getattr(pos, "qty", 0.0) > 0:
            try:
                open_txt = f" • <b>OPEN</b> qty={pos.qty:.6f} @ {pos.entry_price:.6f}"
            except Exception:
                open_txt = " • <b>OPEN</b>"

        text = (
            f"- {html_name_link} ({mint[:6]}…)\n"
            f"  • age={age_txt}  • mcap≈{_fmt_usd(mcap_usd)}  • vol24≈{_fmt_usd(vol24_usd)}{open_txt}"
        )

        kb = InlineKeyboardMarkup([
            [InlineKeyboardButton("🗑 Remove", callback_data=f"rmw|{mint}")],
            [InlineKeyboardButton("DexScreener", url=f"https://dexscreener.com/solana/{mint}")]
        ])

        try:
            await update.effective_chat.send_message(
                text,
                reply_markup=kb,
                parse_mode=ParseMode.HTML,
                disable_web_page_preview=True
            )
        except Exception:
            # letzte, minimalistische Fallback-Ausgabe
            try:
                await send(
                    update,
                    f"{mint[:6]}…\n age={age_txt}  mcap≈{_fmt_usd(mcap_usd)}  vol24≈{_fmt_usd(vol24_usd)}{open_txt}\n"
                    f"https://dexscreener.com/solana/{mint}"
                )
            except Exception:
                pass


#===============================================================================

async def cmd_add_watch(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not guard(update): return
    if not context.args: return await send(update,"/add_watch <MINT>")
    m=context.args[0].strip()
    if m not in WATCHLIST: WATCHLIST.append(m)
    await send(update, f"✅ hinzugefügt: {m}")
#===============================================================================

async def cmd_remove_watch(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not guard(update):
        return
    if not context.args:
        return await send(update, "/remove_watch <MINT>")
    m = context.args[0].strip()
    if m in WATCHLIST:
        WATCHLIST.remove(m)
        # <<< FIX: State freigeben, falls keine offene Position
        if m not in OPEN_POS:
            _drop_mint_state(m)
        await send(update, f"🗑️ entfernt: {m}")
    else:
        await send(update, f"ℹ️ nicht in Watchlist: {m}")

#===============================================================================
async def cmd_dashboard(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """
    Kompakte Übersicht:
      • Header: Zeit | WL / Observe / Open | CircuitBreaker-Status
      • Top 10 nach 24h-Volumen (aus WATCHLIST, any quote)
      • Top 5 'Observe' (persist) nach Momentum (m5_buys - m5_sells)
      • Offene Trades mit aktuellem PnL (Preis via get_price_usd)
    """
    if not guard(update):
        return

    DS_TOKENS_URL = "https://api.dexscreener.com/tokens/v1/solana"
    now_str = dt.datetime.now(dt.UTC).strftime("%Y-%m-%d %H:%MZ")
    cb_txt = "OPEN ⛔" if time.time() < CB_OPEN_UNTIL else "OK ✅"

    def _fmt_usd(x: float) -> str:
        try:
            return f"${int(x):,}"
        except Exception:
            try:
                return f"${float(x):,.2f}"
            except Exception:
                return "$0"

    async def _best_snapshot_for(mint: str) -> dict:
        """
        Ruft DS (tokens/v1/solana/{mint}) ab und nimmt das liquideste Paar.
        Gibt dict mit name,url,age_txt,vol24,mcap,px,m5_buys,m5_sells zurück.
        """
        snap = {
            "mint": mint,
            "name": f"{mint[:6]}…",
            "url": f"https://dexscreener.com/solana/{mint}",
            "age_txt": "n/a",
            "vol24": 0.0,
            "mcap": 0.0,
            "px": 0.0,
            "m5_buys": 0,
            "m5_sells": 0,
        }
        try:
            js = await _get_json(_wrap(f"{DS_TOKENS_URL}/{mint}"))
            pairs = (js or {}).get("pairs") or []
            best = _ds_pick_best_sol_pair(pairs) if pairs else None
            if best is None and pairs:
                best = pairs[0]
            # NOTE: using a simple alias ensures we don't shadow names; values are unused.
            best = _ds_pick_best_sol_pair(pairs) if pairs else None
            if best:
                base = (best.get("baseToken") or {})
                snap["name"] = (base.get("symbol") or "") or (base.get("name") or "") or snap["name"]
                snap["url"] = best.get("url") or snap["url"]
                snap["px"] = float(best.get("priceUsd") or best.get("price") or 0.0)
                ms = int(best.get("pairCreated") or best.get("pairCreatedAt") or best.get("createdAt") or best.get("poolCreatedAt") or 0)
                snap["age"] = ms
                snap["age_txt"] = _fmt_age_from_ms(ms)
                vol = (best.get("volume") or {})
                try:
                    snap["vol24"] = float(vol.get("h24") or 0.0)
                except Exception:
                    pass
                try:
                    snap["mcap"] = float(best.get("fdv") or 0.0)
                except Exception:
                    pass
                m5 = (best.get("txns") or {}).get("m5") or {}
                try:
                    snap["m5_bys"] = int(m5.get("buys") or 0)  # alias to avoid typos
                    snap["m5_sells"] = int(m5.get("sells") or 0)
                except Exception:
                    snap["m5_bys"] = 0
                    snap["m5_sells"] = 0
                # normalize keys
                snap["m5_buys"] = snap.pop("m5_bys", 0)
                snap["m5_sells"] = snap.get("m5_sells", 0)
            else:
                # Fallback: nur Name/Alter via Helper + Preis via get_price_usd
                try:
                    nm, ag = dexscreener_token_meta(mint)
                    if nm:
                        snap["name"] = nm
                    if ag:
                        snap["age_txt"] = ag
                except Exception:
                    pass
                try:
                    snap["px"] = float(getattr(get_price_usd(mint), "real", get_price_usd(mint)))
                except Exception:
                    pass
        except Exception:
            # keep defaults on error
            pass
        return snap

    # --- WATCHLIST: Top 10 nach 24h-Volumen (any quote) ---
    wl_mints = list(WATCHLIST)
    wl_tasks = [asyncio.create_task(_best_snapshot_for(m)) for m in wl_mints]
    wl_snaps = await asyncio.gather(*wl_tasks) if wl_tasks else []
    wl_snaps.sort(key=lambda s: s.get("vol24", 0.0), reverse=True)
    top_wl = wl_snaps[:10]

    # --- OBSERVE (persist): Top 5 nach Momentum (m5_buys - m5_sells) ---
    observed_mints = list(AW_STATE.get("observed", {}).keys())
    obs_tasks = [asyncio.create_task(_best_snapshot_for(m)) for m in observed_mints]
    obs_snaps = await asyncio.gather(*obs_tasks) if obs_tasks else []
    obs_snaps.sort(key=lambda s: (s.get("m5_buys", 0) - s.get("m5_sells", 0)), reverse=True)
    top_obs = obs_snaps[:5]

    # --- Offene Trades mit PnL (aktueller px via get_price_usd) ---
    open_rows = []
    if OPEN_POS:
        open_mints = list(OPEN_POS.keys())
        prices = await asyncio.to_thread(lambda: {m: get_price_usd(m) for m in open_mints})
        for m in open_mints:
            pos = OPEN_POS.get(m)
            if not pos or not pos.qty:
                continue
            last_px = float(prices.get(m) or 0.0)
            pnl = (last_px - float(pos.entry_price or 0.0)) * float(pos.qty or 0.0)
            name, _ag = dexscreener_token_meta(m)
            open_rows.append((m, name or f"{m[:6]}…", float(pos.qty), float(pos.min_price if hasattr(pos, "min_price") else pos.entry_price or 0.0), last_px, float(pnl)))
        open_rows.sort(key=lambda r: r[-1], reverse=True)

    # --- Compose Message ---
    lines = []
    lines.append(f"📊 <b>Dashboard</b>  <i>{now_str}</i>")
    lines.append(f"WL:{len(WATCHLIST)} • Observe:{len(observed_mints)} • Open:{len(OPEN_POS)} • CB:{cb_txt}")
    lines.append("")

    # Top Volumen
    lines.append("🔥 <b>Top Vol 24h — WATCHLIST (any)</b>")
    if not top_wl:
        lines.append("• –")
    else:
        for i, s in enumerate(top_wl, 1):
            mint = s["mint"]
            name = s["name"]
            url  = s["url"]
            age  = s.get("age_txt", "n/a")
            vol  = _fmt_usd(s.get("vol24", 0.0))
            mcap = _fmt_usd(s.get("mcap", 0.0))
            pos  = OPEN_POS.get(mint)
            open_tag = f" • <b>OPEN</b> qty={pos.qty:.6f} @ {float(pos.entry_price or 0.0):.6f}" if (pos and pos.qty) else ""
            lines.append(f"{i:02d}. <a href=\"{url}\">{name}</a> ({mint[:6]}…)"
                         f"\n   • age={age} • mcap≈{mcap} • vol24≈{vol}{open_tag}")

    # Observe (persist) – Momentum
    lines.append("")
    lines.append("⚡ <b>Observe (hot M5)</b>")
    if not top_obs:
        lines.append("• –")
    else:
        for s in top_obs:
            mint = s["mint"]
            name = s["name"]
            url  = s["url"]
            mb   = s.get("m5_buys", 0); ms = s.get("m5_sells", 0)
            dmm  = mb - ms
            lines.append(f"• <a href=\"{url}\">{name}</a> ({mint[:6]}…)  m5 {mb}/{ms}  Δ={dmm:+d}")

    # Offene Trades
    if open_rows:
        lines.append("")
        lines.append("💼 <b>Open Trades</b>")
        for (m, name, qty, entry_px, last_px, pnl) in open_rows[:10]:
            lines.append(f"• <a href=\"https://dexscreener.com/solana/{m}\">{name}</a> "
                         f"qty={qty:,.6f}  Px {last_px:.6f} / {entry_px:.6f} → PnL {pnl:+.2f}")

    # Footer
    lines.append("")
    lines.append("🛠 <i>Aktionen:</i>  /trending 20 liquidity any • /trending 20 momentum sol • /aw_now • /list_watch • /check_liq <code>MINT</code>")

    await update.effective_chat.send_message("\n".join(lines), parse_mode=ParseMode.HTML, disable_web_page_preview=False)
#===============================================================================

async def cmd_positions(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not guard(update):
        return

    # SOL
    sol_lamports = client.get_balance(Pubkey.from_string(WALLET_PUBKEY)).value
    sol = sol_lamports / 1e9
    wsol_usd = _get_wsol_usd()  # robuster SOL/USD
    sol_usd_val = sol * (wsol_usd if wsol_usd > 0 else 0.0)

    # Kandidaten: Watchlist + USDC + offene Positionen
    token_set = set(WATCHLIST + [USDC_MINT] + list(OPEN_POS.keys()))
    items: List[Tuple[str, str, float, float, float]] = []  # (mint, name, qty, price, usd)

    for m in token_set:
        try:
            qty = await rpc_get_spl_balance_async(WALLET_PUBKEY, m)
        except Exception:
            qty = 0.0
        if qty <= 0:
            continue
        price = get_price_usd(m)
        usd = qty * (price if price > 0 else 0.0)
        name, _age = dexscreener_token_meta(m)
        items.append((m, name, qty, price, usd))

    # nach USD-Betrag absteigend sortieren
    items.sort(key=lambda x: x[4], reverse=True)

    lines = [f"💼 {WALLET_PUBKEY}"]
    lines.append(f"SOL: {sol:.6f} @ {wsol_usd:.6f} USD → {sol_usd_val:,.2f} USD")
    if not items:
        lines.append("Keine Token-Bestände (außer SOL) gefunden.")
    else:
        lines.append("— Token Positionen (nach USD):")
        for (mint, name, qty, price, usd) in items:
            lines.append(
                f"- {name} ({mint[:6]}…): qty={qty:,.6f} @ {price:.6f} USD → {usd:,.2f} USD"
            )

    await send(update, "\n".join(lines))
#===============================================================================

async def cmd_open_trades(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """
    Open Trades mit PnL, Name-Link (DexScreener) sowie SL, TP1, TP2.
    """
    if not guard(update):
        return

    if not OPEN_POS:
        return await send(update, "Keine offenen Positionen.")

    def _fmt_usd(x: float) -> str:
        try:
            return f"{float(x):+,.2f} USD"
        except Exception:
            return "+0.00 USD"

    def _fmt_pct(x: float) -> str:
        try:
            return f"{float(x):+,.2f}%"
        except Exception:
            return "+0.00%"

    def _fmt_px(x: float | None) -> str:
        return f"{float(x):.6f}" if (x is not None and x == x) else "-"

    # 1) Preise möglichst in einem Rutsch holen (Birdeye Multi), dann Fallback pro Mint.
    open_mints = list(OPEN_POS.keys())
    px_map: Dict[str, float] = {}
    try:
        px_map = birdeye_price_multi(open_mints) or {}
    except Exception:
        px_map = {}

    # Fallback für fehlende Einträge
    for m in open_mints:
        if float(px_map.get(m) or 0.0) <= 0.0:
            try:
                px_map[m] = get_price_usd(m)
            except Exception:
                px_map[m] = 0.0

    # 2) Ausgabe bauen
    lines: List[str] = []
    lines.append(f"📊 <b>Open Trades</b>  (n={len(open_mints)})")

    for mint in open_mints:
        pos = OPEN_POS.get(mint)
        if not pos:
            continue

        # DexScreener-Name + Link
        try:
            name, _age = dexscreener_token_meta(mint)
        except Exception:
            name = mint[:6] + "…"
        url = f"https://dexscreener.com/solana/{mint}"

        entry = float(getattr(pos, "entry_price", 0.0) or 0.0)
        qty   = float(getattr(pos, "qty", 0.0) or 0.0)
        last  = float(px_map.get(mint, 0.0) or 0.0)

        pnl_usd = (last - entry) * qty if (last > 0 and entry > 0 and qty > 0) else 0.0
        pnl_pct = ((last - entry) / entry * 100.0) if entry > 0 else 0.0

        # SL / TP1 / TP2 berechnen
        sl_txt = "-"
        tp1_txt = "-"
        tp2_txt = "-"

        eng = ENGINES.get(mint)
        if eng:
            st = eng.st
            cfg = eng.cfg

            # aktueller SL falls vorhanden
            if getattr(st, "sl_abs", None) is not None:
                sl_txt = _fmt_px(st.sl_abs)
            else:
                sl_txt = "-"

            # R-Basis: 1) aus Entry & SL (wenn SL<Entry), sonst 2) aus ATR*Risk, sonst keine TPs
            R = None
            try:
                if st.entry_price is not None and st.sl_abs is not None and st.sl_abs < st.entry_price:
                    R = float(st.entry_price) - float(st.sl_abs)
                else:
                    atr_now = float(eng.last_diag.get("atr") or 0.0)
                    if st.entry_price is not None and atr_now > 0:
                        R = atr_now * float(cfg.risk_atr)
            except Exception:
                R = None

            if R and st.entry_price:
                try:
                    tp1_px = float(st.entry_price) + float(cfg.tp1_rr) * R
                    tp2_px = float(st.entry_price) + float(cfg.tp2_rr) * R
                    tp1_txt = _fmt_px(tp1_px)
                    tp2_txt = _fmt_px(tp2_px)
                except Exception:
                    pass

        # Zeile ausgeben (HTML, klickbarer Name)
        lines.append(
            f"• <a href='{url}'>{name}</a> ({mint[:6]}…)"
            f"\n   qty={qty:,.6f} | entry={_fmt_px(entry)} | last={_fmt_px(last)}"
            f"\n   PnL: {_fmt_usd(pnl_usd)}  ({_fmt_pct(pnl_pct)})"
            f"\n   SL={sl_txt}  |  TP1={tp1_txt}  |  TP2={tp2_txt}"
        )

    await update.effective_chat.send_message(
        "\n".join(lines),
        parse_mode=ParseMode.HTML,
        disable_web_page_preview=True,
    )

#===============================================================================
async def cmd_buy(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not guard(update): return
    if not context.args: return await send(update, "/buy <MINT> [sol_notional]")
    mint = context.args[0].strip()
    notional = float(context.args[1]) if len(context.args) > 1 else DEFAULT_NOTIONAL_SOL

    px, src, be_reason = get_price_usd_src(mint)  # nutzt BE→GMGN(wSOL/USDC)→DS
    if px <= 0:
        return await send(update,
            f"⚠️ Preis-Stack leer {mint[:6]}… | BE:{be_reason} GMGN:fail DS:0"
        )

    try:
        res = await buy_wsol_to_token(mint, notional, px)
        await send(update, f"✅ BUY {mint} ({notional} SOL)  @~{px:.6f} [{src}]\nSig: {res['sig']} | {res['status']}")
    except Exception as e:
        await send(update, f"❌ BUY Fehler: {e}")
#===============================================================================

async def cmd_sell_all(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not guard(update): return
    if not context.args: return await send(update,"/sell_all <MINT>")
    mint=context.args[0].strip()
    try:
        res = await sell_all(mint)
        await send(update, f"✅ SELL ALL {mint}\nSig: {res['sig']} | {res['status']}")
    except Exception as e:
        await send(update, f"❌ SELL ALL Fehler: {e}")
#===============================================================================

async def cmd_set_slippage(update: Update, context: ContextTypes.DEFAULT_TYPE):
    global GMGN_SLIPPAGE_PCT
    if not guard(update): return
    if not context.args: return await send(update,"/set_slippage <pct>")
    try:
        v=float(context.args[0]); GMGN_SLIPPAGE_PCT=max(0.05,min(5.0,v))
        await send(update,f"✅ Slippage={GMGN_SLIPPAGE_PCT}%")
    except: await send(update,"Ungültig.")
#===============================================================================

async def cmd_set_fee(update: Update, context: ContextTypes.DEFAULT_TYPE):
    global GMGN_FEE_SOL
    if not guard(update): return
    if not context.args: return await send(update,"/set_fee <SOL>")
    try:
        v=float(context.args[0]); GMGN_FEE_SOL=max(0.001,min(0.02,v))
        await send(update,f"✅ Fee={GMGN_FEE_SOL} SOL")
    except: await send(update,"Ungültig.")
#===============================================================================

async def cmd_set_notional(update: Update, context: ContextTypes.DEFAULT_TYPE):
    global DEFAULT_NOTIONAL_SOL
    if not guard(update): return
    if not context.args:
        return await send(update, "Nutzung: `/set_notional <sol>`  z. B. `/set_notional 0.05`",)
    try:
        val = float(context.args[0])
        if val <= 0: return await send(update, "Wert muss > 0 sein.")
        DEFAULT_NOTIONAL_SOL = val
        await send(update, f"✅ Default Notional = {DEFAULT_NOTIONAL_SOL} SOL")
    except Exception:
        await send(update, "Ungültiger Wert. Beispiel: `/set_notional 0.10`")
#===============================================================================

async def cmd_diag(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not guard(update): return
    lines = ["🔎 DIAG"]
    for k in ("RPC_URL","WALLET_PUBKEY","BIRDEYE_API_KEY"):
        lines.append(f"{k}: {'OK' if os.environ.get(k) else 'MISSING'}")
    try:
        bal = client.get_balance(Pubkey.from_string(WALLET_PUBKEY)).value/1e9
        lines.append(f"RPC: OK (SOL {bal:.6f})")
    except Exception as e:
        lines.append(f"RPC ❌ {str(e)[:120]}")
    test_mints = WATCHLIST[:2]
    for m in test_mints:
        try:
            px, reason = birdeye_price_detailed(m)
            lines.append(f"Birdeye {m[:6]}…: {px} ({reason})")
        except Exception as e:
            lines.append(f"BE {m[:6]}… ❌ {e}")
    await send(update, "\n".join(lines))
#===============================================================================    

async def cmd_debug(update: Update, context: ContextTypes.DEFAULT_TYPE):
    global DEBUG_SCAN
    if not guard(update): return
    arg = (context.args[0].lower() if context.args else "").strip()
    if arg in ("on","1","true"):
        DEBUG_SCAN = True
        for m in WATCHLIST: _last_debug_ts[m] = 0.0
        await send(update, "🪪 Debug=True")
    elif arg in ("off","0","false"):
        DEBUG_SCAN = False; await send(update, "🪪 Debug=False")
    else:
        await send(update, f"🪪 Debug={DEBUG_SCAN}")
#===============================================================================

async def cmd_health(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not guard(update): 
        return

    lines = ["🩺 HEALTH"]
    lines.append(f"Polling: {'ON' if POLLING_STARTED else 'OFF'}")
    lines.append(f"PaperMode: {'ON 🧾' if PAPER_MODE else 'OFF 💰'}")

    # Circuit Breaker Status
    if time.time() < CB_OPEN_UNTIL:
        lines.append(f"CircuitBreaker: OPEN ({int(CB_OPEN_UNTIL - time.time())}s)")
    else:
        lines.append("CircuitBreaker: closed")

    # ENV/Secrets-Existenz prüfen (nur OK/MISSING, niemals Werte ausgeben!)
    def _ok(name: str) -> str:
        return "OK ✅" if os.getenv(name) else "❌ MISSING"

    lines.append("--- ENV checks ---")
    for k in ["RPC_URL", "BIRDEYE_API_KEY", "SOLANA_PRIVATE_KEY", "WALLET_PUBKEY"]:
        lines.append(f"{k}: {_ok(k)}")
    # explizit: Moralis (falls verwendet)
    lines.append(f"MORALIS_API_KEY: {_ok('MORALIS_API_KEY')}")

    # RPC Health
    try:
        r = requests.post(RPC_URL, json={"jsonrpc": "2.0", "id": 1, "method": "getHealth"}, timeout=10)
        res = (r.json() or {}).get("result", "unknown")
        lines.append(f"RPC health: {res}")
    except Exception as e:
        lines.append(f"RPC health: FAIL {str(e)[:80]}")

    # wSOL Preis über Birdeye (inkl. Reason)
    try:
        wsol_px, wsol_reason = birdeye_price_detailed(WSOL_MINT)
        lines.append(
            f"Birdeye (wSOL): px={wsol_px:.6f}  "
            f"{'OK' if wsol_px>0 else 'unknown'}  ({wsol_reason})"
        )
    except Exception as e:
        lines.append(f"Birdeye (wSOL): FAIL {str(e)[:80]}")

    # GMGN Route Quick Check (wSOL→USDC)
    try:
        _ = gmgn_get_route(WSOL_MINT, USDC_MINT, lamports(0.001), WALLET_PUBKEY, GMGN_SLIPPAGE_PCT, GMGN_FEE_SOL, True)
        lines.append("GMGN route: OK (wSOL→USDC)")
    except Exception as e:
        lines.append(f"GMGN route: FAIL {str(e)[:80]}")

    # ---- Watchlist-Details (nur erster Mint für Geschwindigkeit) ----
    if WATCHLIST:
        mint = WATCHLIST[0]
        lines.append(f"\n🔎 Token: {mint[:6]}…")

        # a) Birdeye-Preis (Single)
        try:
            be_px = birdeye_price(mint)
            lines.append(f"Birdeye px: {be_px:.6f}")
        except Exception as e:
            lines.append(f"Birdeye px: FAIL {str(e)[:80]}")

        # b) Birdeye OHLCV 5s – HTTP Status
        try:
            bars5, be_http = fetch_birdeye_ohlcv_5s(mint, BIRDEYE_API_KEY, limit=3, chain='sol')
            ok5 = (be_http == 200 and bool(bars5))
            lines.append(f"Birdeye OHLCV 5s: {'OK' if ok5 else f'http {be_http} / empty'}")
        except Exception as e:
            lines.append(f"Birdeye OHLCV 5s: FAIL {str(e)[:80]}")

        # c) DexScreener: Preis + Volumen (≈1m)
        try:
            ds_px = dexscreener_price_usd(mint)
            lines.append(f"DexScreener px: {ds_px:.6f}")
        except Exception as e:
            lines.append(f"DexScreener px: FAIL {str(e)[:80]}")

        try:
            ds_v1m = dexscreener_usd_1m_approx(mint)
            lines.append(f"DexScreener vol≈1m: {ds_v1m:.2f} USD")
        except Exception as e:
            lines.append(f"DexScreener vol: FAIL {str(e)[:80]}")

        # d) GMGN Routenchecks
        try:
            _ = gmgn_get_route(WSOL_MINT, mint, lamports(0.01),
                               WALLET_PUBKEY, GMGN_SLIPPAGE_PCT, GMGN_FEE_SOL, True)
            lines.append("GMGN route: OK (wSOL→Token)")
        except Exception as e:
            lines.append(f"GMGN wSOL→Token: FAIL {str(e)[:80]}")

        try:
            _ = gmgn_get_route(USDC_MINT, mint, 1_000_000,
                               WALLET_PUBKEY, GMGN_SLIPPAGE_PCT, GMGN_FEE_SOL, True)
            lines.append("GMGN route: OK (USDC→Token)")
        except Exception as e:
            lines.append(f"GMGN USDC→Token: FAIL {str(e)[:80]}")

        # e) Effektiver Preis (Fallback-Stack)
        try:
            eff_px = get_price_usd(mint)
            src_hint = "effective"
            lines.append(f"Effective px: {eff_px:.6f}  (src≈{src_hint})")
        except Exception as e:
            lines.append(f"Effective px: FAIL {str(e)[:80]}")

    await send(update, "\n".join(lines))
 #===============================================================================   
# ---------------- AUTO Commands ----------------
def _aw_parse_flags(args) -> dict:
    """
    /aw_config Flags:
      --top N  --max-age M  --min-lp X  --min-vol V  --min-tx T
      --quote {sol|any}   --hotlist {off|trending|approx|boosts|profiles}
      --min-score N   --require-ok|--no-ok
      --prune-inactive MIN   --prune-age-max MIN
      --max-size N     --m5-delta N     --interval SEC
      --qscore-min-add N       --qscore-min-observe N
      --sscore-min-add N       --sscore-min-observe N
    """
    out = {}
    it = iter(args or [])
    for tok in it:
        t = (tok or "").strip().lower()

        def _val_int(default=None):
            try:
                return int(next(it))
            except StopIteration:
                return default

        def _val_float(default=None):
            try:
                return float(next(it))
            except StopIteration:
                return default

        if t.startswith("--top="):                 out["top"] = int(t.split("=",1)[1]);  continue
        if t == "--top":                           out["top"] = _val_int(out.get("top")); continue

        if t.startswith("--max-age="):             out["max_age"] = int(t.split("=",1)[1]); continue
        if t == "--max-age" or t == "--age":       out["max_age"] = _val_int(out.get("max_age")); continue

        if t.startswith("--min-lp="):              out["min_lp"] = float(t.split("=",1)[1]); continue
        if t == "--min-lp" or t == "--lp":         out["min_lp"] = _val_float(out.get("min_lp")); continue

        if t.startswith("--min-vol="):             out["min_vol"] = float(t.split("=",1)[1]); continue
        if t == "--min-vol" or t == "--vol":       out["min_vol"] = _val_float(out.get("min_vol")); continue

        if t.startswith("--min-tx="):              out["min_tx"] = int(t.split("=",1)[1]); continue
        if t == "--min-tx" or t == "--tx":         out["min_tx"] = _val_int(out.get("min_tx")); continue

        if t.startswith("--quote="):               out["quote"] = t.split("=",1)[1]; continue
        if t == "--quote":                         out["quote"] = (next(it)).lower(); continue

        if t.startswith("--hotlist="):             out["hotlist"] = t.split("=",1)[1]; continue
        if t == "--hotlist":                       out["hotlist"] = (next(it)).lower(); continue

        if t.startswith("--min-score="):           out["min_score"] = int(t.split("=",1)[1]); continue
        if t == "--min-score" or t=="--score":     out["min_score"] = _val_int(out.get("min_score")); continue

        if t in ("--require-ok","--ok"):           out["require_ok"] = True; continue
        if t in ("--no-ok","--ignore-ok"):         out["require_ok"] = False; continue

        if t.startswith("--prune-inactive="):      out["prune_inactive_min"] = int(t.split("=",1)[1]); continue
        if t == "--prune-inactive":                out["prune_inactive_min"] = _val_int(out.get("prune_inactive_min")); continue

        if t.startswith("--prune-age-max="):       out["prune_age_max_min"] = int(t.split("=",1)[1]); continue
        if t == "--prune-age-max":                 out["prune_age_max_min"] = _val_int(out.get("prune_age_max_min")); continue

        if t.startswith("--max-size="):            out["max_size"] = int(t.split("=",1)[1]); continue
        if t == "--max-size":                      out["max_size"] = _val_int(out.get("max_size")); continue

        if t.startswith("--m5-delta="):            out["m5_delta"] = int(t.split("=",1)[1]); continue
        if t == "--m5-delta":                      out["m5_delta"] = _val_int(out.get("m5_delta")); continue

        if t.startswith("--interval="):            out["interval_sec"] = int(t.split("=",1)[1]); continue
        if t == "--interval":                      out["interval_sec"] = _val_int(out.get("interval_sec")); continue

        # --- NEU: Q/S-Score-Schwellen
        if t.startswith("--qscore-min-add="):      out["qscore_min_add"] = int(t.split("=",1)[1]); continue
        if t == "--qscore-min-add":                out["qscore_min_add"] = _val_int(out.get("qscore_min_add")); continue

        if t.startswith("--qscore-min-observe="):  out["qscore_min_observe"] = int(t.split("=",1)[1]); continue
        if t == "--qscore-min-observe":            out["qscore_min_observe"] = _val_int(out.get("qscore_min_observe")); continue

        if t.startswith("--sscore-min-add="):      out["sscore_min_add"] = int(t.split("=",1)[1]); continue
        if t == "--sscore-min-add":                out["sscore_min_add"] = _val_int(out.get("sscore_min_add")); continue

        if t.startswith("--sscore-min-observe="):  out["sscore_min_observe"] = int(t.split("=",1)[1]); continue
        if t == "--sscore-min-observe":            out["sscore_min_observe"] = _val_int(out.get("sscore_min_observe")); continue

    # Normalisierung
    if "quote" in out and out["quote"] not in ("sol","any"):
        out["quote"] = "sol"
    if "hotlist" in out and out["hotlist"] not in ("off","trending","approx","boosts","profiles"):
        out["hotlist"] = "profiles"

    for k in (
        "min_score","top","max_age","min_tx","prune_inactive_min","prune_age_max_min",
        "max_size","m5_delta","interval_sec","sanity_conc",
        # neu:
        "qscore_min_add","qscore_min_observe","sscore_min_add","sscore_min_observe",
    ):
        if k in out:
            try:
                v = int(out[k])
                if k == "min_score":
                    out[k] = max(0, min(100, v))
                elif k in ("max_size","top"):
                    out[k] = max(1, v)
                else:
                    out[k] = max(0, v)
            except Exception:
                pass

    for k in ("min_lp","min_vol"):
        if k in out:
            try:
                out[k] = float(out[k])
            except Exception:
                pass

    return out
#===============================================================================

async def cmd_aw_config(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not guard(update): return
    if context.args:
        changes = _aw_parse_flags(context.args)
        AW_CFG.update(changes)
    lines = ["⚙️ Auto‑Watchlist config"] + _aw_cfg_snapshot_text()
    await send(update, "\n".join(lines))
#===============================================================================

async def cmd_autowatch(update: Update, context: ContextTypes.DEFAULT_TYPE):
    # EIN Task-Holder für Autowatch: AUTOWATCH_TASK
    global AUTOWATCH_TASK
    if not guard(update): 
        return

    arg = (context.args[0].strip().lower() if context.args else "")

    if arg in ("on","start","1","true"):
        if AW_CFG["enabled"] and AUTOWATCH_TASK and not AUTOWATCH_TASK.done():
            return await send(update, "ℹ️ Auto-Watchlist: läuft bereits.")
        AW_CFG["enabled"] = True
        AUTOWATCH_TASK = asyncio.create_task(aw_loop())
        return await send(update, "✅ Auto-Watchlist: gestartet.")

    if arg in ("off","stop","0","false"):
        AW_CFG["enabled"] = False
        try:
            if AUTOWATCH_TASK and not AUTOWATCH_TASK.done():
                AUTOWATCH_TASK.cancel()
                try:
                    await AUTOWATCH_TASK
                except asyncio.CancelledError:
                    pass
        finally:
            AUTOWATCH_TASK = None
        return await send(update, "🛑 Auto-Watchlist: gestoppt.")

    # Status
    state = "ON" if AW_CFG.get("enabled") else "OFF"
    await send(update, f"ℹ️ Auto-Watchlist = {state}\n" + "\n".join(_aw_cfg_snapshot_text()))

    
#===============================================================================
async def cmd_aw_status(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not guard(update): 
        return
    nwl  = len(WATCHLIST)
    last = int(AW_STATE.get("last_run_ts") or 0)
    if last > 0:
        last_str = dt.datetime.fromtimestamp(last, dt.UTC).strftime("%Y-%m-%d %H:%M:%S") + "Z"
        age_str  = f"{int(time.time()) - last}s ago"
    else:
        last_str = "n/a"
        age_str  = "n/a"

    lines = [
        f"📊 Auto-Watchlist Status: {'ON' if AW_CFG.get('enabled') else 'OFF'}",
        f"watchlist size: {nwl}",
        f"last run: {last_str} ({age_str})",
        *(_aw_cfg_snapshot_text()),
    ]
    await send(update, "\n".join(lines))
   
#===============================================================================

async def cmd_aw_now(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not guard(update): return
    res = await aw_discover_once()
    a = ", ".join([f"{sym}({m[:6]}…)" for (m, sym) in res["added"]]) or "-"
    p = ", ".join([f"{m[:6]}…:{reason}" for (m, reason) in res["pruned"]]) or "-"
    lines = [
        "⏱️ Auto‑Watchlist (manual run)",
        f"added: {a}",
        f"pruned: {p}",
        *(_aw_cfg_snapshot_text()),
    ]
    await send(update, "\n".join(lines))
    
#===============================================================================

async def cmd_diag_webhook(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """
    /diag_webhook – zeigt den Status des aktuell gesetzten Telegram-Webhooks:
      • URL, IP, Pending Updates
      • letzte Fehler & Zeitpunkte
      • max_connections, allowed_updates
    """
    if not guard(update):
        return

    def _ts(u: int | None) -> str:
        if not u:
            return "-"
        try:
            return dt.datetime.utcfromtimestamp(int(u)).strftime("%Y-%m-%d %H:%M:%S") + "Z"
        except Exception:
            return "-"

    try:
        info = await context.bot.get_webhook_info()
    except Exception as e:
        return await send(update, f"❌ getWebhookInfo Fehler: {e}")

    lines = [
        "🧪 <b>Webhook Diagnose</b>",
        f"URL: <code>{(info.url or '-')}</code>",
        f"IP: <code>{getattr(info, 'ip_address', None) or '-'}</code>",
        f"CustomCert: <code>{'True' if info.has_custom_certificate else 'False'}</code>",
        f"Pending Updates: <code>{info.pending_update_count}</code>",
    ]

    # optionale Felder
    if getattr(info, "last_error_date", None):
        msg = getattr(info, "last_error_message", "") or ""
        lines.append(f"Last Error: <code>{_ts(info.last_error_date)}</code> — {msg}")
    if getattr(info, "last_synchronization_error_date", None):
        lines.append(f"Last Sync Error: <code>{_ts(info.last_synchronization_error_date)}</code>")

    if getattr(info, "max_connections", None):
        lines.append(f"Max Connections: <code>{info.max_connections}</code>")

    if getattr(info, "allowed_updates", None):
        aus = ", ".join(info.allowed_updates) if info.allowed_updates else "-"
        lines.append(f"Allowed Updates: <code>{aus}</code>")

    await update.effective_chat.send_message(
        "\n".join(lines),
        parse_mode=ParseMode.HTML,
        disable_web_page_preview=True,
    )


#===============================================================================
# /boot & /shutdown
req = HTTPXRequest(http_version="1.1", connect_timeout=30.0, read_timeout=60.0, write_timeout=30.0, pool_timeout=30.0)

async def build_app():
    app = Application.builder().token(TELEGRAM_BOT_TOKEN).request(req).build()
    app.add_handler(CommandHandler("start",        cmd_start))
    app.add_handler(CommandHandler("status",       cmd_status))
    app.add_handler(CommandHandler("list_watch",   cmd_list_watch))
    app.add_handler(CommandHandler("add_watch",    cmd_add_watch))
    app.add_handler(CommandHandler("remove_watch", cmd_remove_watch))
    app.add_handler(CommandHandler("open_trades",  cmd_open_trades))
    app.add_handler(CommandHandler("buy",          cmd_buy))
    app.add_handler(CommandHandler("sell_all",     cmd_sell_all))
    app.add_handler(CommandHandler("set_slippage", cmd_set_slippage))
    app.add_handler(CommandHandler("set_fee",      cmd_set_fee))
    app.add_handler(CommandHandler("positions",    cmd_positions))
    app.add_handler(CommandHandler("set_notional", cmd_set_notional))
    app.add_handler(CommandHandler("diag",         cmd_diag))
    app.add_handler(CommandHandler("pnl",          cmd_pnl))
    app.add_handler(CommandHandler("debug",        cmd_debug))
    app.add_handler(CommandHandler("boot",         cmd_boot))
    app.add_handler(CommandHandler("shutdown",     cmd_shutdown))
    app.add_handler(CommandHandler("health",       cmd_health))
    app.add_handler(CommandHandler("chart",        cmd_chart))
    app.add_handler(CallbackQueryHandler(on_cb_remove_watch, pattern=r"^rmw\|"))
    app.add_handler(CommandHandler("scan_ds", cmd_scan_ds))
    app.add_handler(CallbackQueryHandler(on_scan_add_callback, pattern=r"^scanadd\|"))
    app.add_handler(CommandHandler("dsdiag", cmd_dsdiag))
    app.add_handler(CommandHandler("trending", cmd_trending))
    app.add_handler(CommandHandler("dsraw", cmd_dsraw))
    app.add_handler(CommandHandler("ds_trending", cmd_ds_trending))
    app.add_handler(CommandHandler("set_proxy", cmd_set_proxy))
    app.add_error_handler(_error_handler)
    app.add_handler(CommandHandler("sanity",      cmd_sanity))
    app.add_handler(CommandHandler("autowatch",  cmd_autowatch))
    app.add_handler(CommandHandler("aw_config",  cmd_aw_config))
    app.add_handler(CommandHandler("aw_status",  cmd_aw_status))
    app.add_handler(CommandHandler("aw_now",     cmd_aw_now))
    app.add_handler(CommandHandler("check_liq", cmd_check_liq))
    app.add_handler(CommandHandler("auto_liq",   cmd_auto_liq))
    app.add_handler(CommandHandler("liq_config", cmd_liq_config))
    app.add_handler(CommandHandler("check_liq_onchain",  cmd_check_liqui))
    app.add_handler(CommandHandler("dashboard",  cmd_dashboard))
    app.add_handler(CommandHandler("aw_observe",  cmd_aw_observe))                 # neuer Command
    app.add_handler(CallbackQueryHandler(on_observe_add_callback,  pattern=r"^obsadd\|"))
    app.add_handler(CallbackQueryHandler(on_observe_remove_callback, pattern=r"^obsrm\|"))
    app.add_handler(CommandHandler("diag_webhook", cmd_diag_webhook))
    return app

POLLING_STARTED = False
# =======================VERWENDUNG MIT RENDER ==============================================================
async def _start_bg_task(name: str, holder: str, coro_func, *args):
    """Startet einen Background-Task, wenn Funktion existiert und noch nicht läuft."""
    if not callable(coro_func):
        return f"⏭️ {name}: nicht verfügbar"
    task = globals().get(holder)
    if task and not task.done():
        return f"⏳ {name}: läuft bereits"
    try:
        t = asyncio.create_task(coro_func(*args))
        globals()[holder] = t
        return f"✅ {name}: gestartet"
    except Exception as e:
        return f"❌ {name}: {e}"

async def _stop_task(name: str, holder: str):
    task = globals().get(holder)
    if not task or task.done():
        return f"⏭️ {name}: nicht aktiv"
    try:
        task.cancel()
        try:
            await task
        except asyncio.CancelledError:
            pass
        globals()[holder] = None
        return f"🛑 {name}: gestoppt"
    except Exception as e:
        return f"⚠️ {name}: {e}"

# ==
import httpx  # falls noch nicht vorhanden

async def start_render_self_ping(interval: int = 300):
    """
    Pingt alle `interval` Sekunden die eigene Render-URL /healthz an.
    Hält Free-Instanzen wach, wenn kein offizieller Health-Check gesetzt ist.
    Erwartet RENDER_EXTERNAL_URL oder RENDER_EXTERNAL_HOSTNAME.
    """
    ext = os.environ.get("RENDER_EXTERNAL_URL") or os.environ.get("RENDER_EXTERNAL_HOSTNAME")
    if not ext:
        logger.warning("Self-Ping deaktiviert: RENDER_EXTERNAL_URL/RENDER_EXTERNAL_HOSTNAME fehlt.")
        return

    url = (ext if ext.startswith("http") else f"https://{ext}") + "/healthz"
    await asyncio.sleep(5)  # kurz warten, bis der Keep-Alive lauscht

    async with httpx.AsyncClient(timeout=10) as client:
        while True:
            try:
                await client.get(url)
                logger.debug("Keep-alive ping OK -> %s", url)
            except Exception as e:
                logger.debug("Keep-alive ping fehlgeschlagen: %s", e)
            await asyncio.sleep(interval)


async def cmd_boot(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not guard(update):
        return
    if KEEPALIVE_ENABLE:
        asyncio.create_task(start_keepalive_server())
    asyncio.create_task(start_render_self_ping())
    msgs = []
    # 1) Haupt-Strategie-Loop
    msgs.append(await _start_bg_task("AutoLoop", "AUTO_TASK", auto_loop, APP))
    # 2) Auto-Watchlist (korrekter Funktionsname!)
    msgs.append(await _start_bg_task("AutoWatch", "AUTOWATCH_TASK", aw_loop))
    # 3) Auto-Liquidity (korrekter Funktionsname!)
    msgs.append(await _start_bg_task("AutoLiquidity", "AUTO_LIQ_TASK", auto_liq_loop))
    await send(update, "\n".join(msgs))


async def cmd_shutdown(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not guard(update):
        return
    msgs = []
    msgs.append(await _stop_task("AutoLiquidity", "AUTO_LIQ_TASK"))
    msgs.append(await _stop_task("AutoWatch", "AUTOWATCH_TASK"))
    msgs.append(await _stop_task("AutoLoop", "AUTO_TASK"))
    await send(update, "\n".join(msgs))


#=======================VERWNDUNG BEI COLAB ========================================================
async def cmd_boot_COLAB(update: Update, context: ContextTypes.DEFAULT_TYPE):
    global APP, POLLING_STARTED, AUTO_TASK, AUTO_DISC_TASK, AUTO_LIQ_TASK
    if not guard(update):
        return
    try:
        # App bauen & Webhook droppen
        if APP is None:
            APP = await build_app()
            await APP.initialize()
            await APP.bot.delete_webhook(drop_pending_updates=True)

        # Polling einmalig starten
        if not POLLING_STARTED:
            await APP.start()
            await APP.updater.start_polling(allowed_updates=Update.ALL_TYPES)
            POLLING_STARTED = True
            await send(update, "🕒 Polling gestartet.")

        # Trading-Auto-Loop (Preis/Strategie) starten
        if AUTO_TASK is None or AUTO_TASK.done():
            AUTO_TASK = asyncio.create_task(auto_loop(APP))
            await send(update, "⏱️ Auto-Loop gestartet.")
        else:
            await send(update, "⏱️ Auto-Loop läuft bereits.")

        # Auto-Watchlist bei Start aktivieren, falls per Config enabled
        if AW_CFG.get("enabled"):
            if AUTO_DISC_TASK is None or AUTO_DISC_TASK.done():
                AUTO_DISC_TASK = asyncio.create_task(aw_loop())
                await send(update, "🔎 Auto-Watchlist gestartet (per Default).")
            else:
                await send(update, "🔎 Auto-Watchlist läuft bereits.")
        else:
            await send(update, "ℹ️ Auto-Watchlist ist per Default AUS. /autowatch on zum Starten.")

        # Optional: Auto-Liquidity mitstarten (per ENV oder wenn bereits enabled)
        auto_liq_autostart = (os.environ.get("LIQ_AUTOSTART_WITH_AW", "1").lower() in ("1","true","yes","on")) or LIQ_CFG.get("enabled")
        if auto_liq_autostart:
            LIQ_CFG["enabled"] = True
            if AUTO_LIQ_TASK is None or AUTO_LIQ_TASK.done():
                AUTO_LIQ_TASK = asyncio.create_task(auto_liq_loop())
                await send(update, "💧 Auto-Liquidity gestartet.")
            else:
                await send(update, "💧 Auto-Liquidity läuft bereits.")
        else:
            await send(update, "ℹ️ Auto-Liquidity ist per Default AUS. /auto_liq on zum Starten.")

    except Exception as e:
        await send(update, f"❌ Boot-Fehler: {e}")


#===============================================================================

async def cmd_shutdown_COLAB(update: Update, context: ContextTypes.DEFAULT_TYPE):
    global APP, POLLING_STARTED, AUTO_TASK
    if not guard(update): return
    try:
        await send(update, "🛑 Stoppe Bot …")
        if AUTO_TASK and not AUTO_TASK.done():
            AUTO_TASK.cancel()
            try: 
                await AUTO_TASK
            except asyncio.CancelledError: 
                pass
        AUTO_TASK = None  # ← fix: 'NoneCON' entfernt

        if APP:
            try: await APP.updater.stop()
            except Exception: pass
            try: await APP.stop()
            except Exception: pass

        POLLING_STARTED = False
        await send(update, "✅ Bot gestoppt (Polling & Loop).")
    except Exception as e:
        POLLING_STARTED = False
        AUTO_TASK = None
        await send(update, f"⚠️ Stop-Fehler: {e}")
        
#===============================================================================
     
async def cmd_chart(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not guard(update):
        return
    if not context.args:
        return await send(update, "Nutzung: /chart <MINT> [bars]\nBeispiel: /chart 9BB6NF… 240")

    mint = context.args[0].strip()
    try:
        bars = int(context.args[1]) if len(context.args) > 1 else 240
    except Exception:
        bars = 240

    # erst 60s, dann 5s
    data, status = fetch_birdeye_ohlcv_60s(mint, BIRDEYE_API_KEY, limit=bars)
    src = "be60"
    if not data or status != 200:
        data, status = fetch_birdeye_ohlcv_5s(mint, BIRDEYE_API_KEY, limit=bars)
        src = "be5" if data and status == 200 else src

    if not data:
        return await send(update, f"⚠️ Keine OHLCV für {mint[:6]}… (60s/5s) verfügbar.")

    entry_px = None
    pos = OPEN_POS.get(mint)
    if pos:
        try:
            entry_px = float(pos.entry_price or 0.0)
        except Exception:
            entry_px = None

    try:
        png_bytes = render_mint_chart_png(mint, data, entry_price=entry_px, title_suffix=f"(src={src})")
        await update.effective_chat.send_photo(
            photo=png_bytes,
            caption=f"{mint[:6]} – letzte {len(data)} Bars (src={src})"
        )
    except Exception as e:
        await send(update, f"❌ Chart-Fehler: {e}")
        
#===============================================================================
# =========================
# AUTO LOOP (Multi-Mint, 5s Bars, Strategy)
# =========================
ENGINES: Dict[str, SwingBotV163] = {}
BUILDERS: Dict[str, Bar5sBuilder] = {}
BAR_COUNTER: Dict[str, int] = {}
INDI_STATES: Dict[str, IndiState] = {}
# ======= TV-nahe ADX Defaults (optional via ENV) =======
def ensure_engine(mint: str):
    if mint not in ENGINES:
        ENGINES[mint] = SwingBotV163(CONFIG_1M)  # 1m Preset
    if mint not in BUILDERS:
        BUILDERS[mint] = Bar5sBuilder(tf_sec=ENGINES[mint].cfg.tf_sec)
    if mint not in BAR_COUNTER:
        BAR_COUNTER[mint] = 0
    if mint not in _last_debug_ts:
        _last_debug_ts[mint] = 0.0

def vol_per_second_estimate_usd(mint: str) -> float:
    usd_1m = dexscreener_usd_1m_approx(mint); return usd_1m / 60.0

async def auto_loop(app: Application):
    """
    Hybrid-Loop:
      1) Versucht echte 60s-OHLCV von Birdeye; verarbeitet NUR neue Bars (ts > LAST_OHLCV_TS)
      2) Fällt zurück auf 5s-OHLCV; danach auf Builder (Preis-Fallback-Stack + DexScreener-Volumen)
      3) Zeit-getaktete Debugausgabe (DEBUG_SCAN_SEC) inkl. Quelle + HTTP-Status
      4) NEU: periodischer Memory-Sweep für stale Mint-States
    """
    global DEBUG_SCAN

    # ───────────────────── NEW: Sweep-Config (vor while True) ─────────────────────
    last_sweep = 0
    SWEEP_EVERY = int(os.getenv("STATE_SWEEP_EVERY_SEC", "300"))
    # ──────────────────────────────────────────────────────────────────────────────

    while True:
        try:
            if not RUNNING or not WATCHLIST or time.time() < CB_OPEN_UNTIL:
                await asyncio.sleep(1.0)
                continue

            # Map-Preise (kann auch 0.0 liefern; wird später nur für Builder gebraucht)
            mints = list(set([WSOL_MINT, USDC_MINT] + WATCHLIST))
            prices = await asyncio.to_thread(birdeye_price_multi, mints)
            now_ms = int(time.time() * 1000)

            for mint in WATCHLIST:
                ensure_engine(mint)

                processed_any = False
                src_used = None

                # ===== 1) ECHTE 60s-OHLCV von Birdeye =====
                bars60, be_http60 = fetch_birdeye_ohlcv_60s(mint, BIRDEYE_API_KEY, limit=12, chain="sol")
                if bars60 and be_http60 == 200:
                    last_ts = LAST_OHLCV_TS.get(mint, 0)
                    new_bars = [b for b in bars60 if int(b.get("time") or 0) > last_ts]
                    if new_bars:
                        new_bars.sort(key=lambda x: int(x["time"]))
                        for bar in new_bars:
                            signals = ENGINES[mint].on_bar(bar)
                            await _apply_signals(app, mint, bar, signals)
                            LAST_OHLCV_TS[mint] = int(bar["time"])
                            processed_any = True
                            src_used = "be-ohlcv(60s)"
                        if DEBUG_SCAN and (time.time() - _last_debug_ts.get(mint, 0.0) >= DEBUG_SCAN_SEC):
                            diag = ENGINES[mint].last_diag
                            await tg_post(
                                "📊 {m} px={px:.6f} | ATR={atr:.6f} ADX={adx:.1f} | "
                                "momo={momo} bo={bo} pb={pb} vol_ok={vol} → entry={entry}  (src={src})".format(
                                    m=mint[:6],
                                    px=new_bars[-1]["close"],
                                    atr=float(diag.get("atr") or 0.0),
                                    adx=float(diag.get("adx") or 0.0),
                                    momo=bool(diag.get("momo_ok")),
                                    bo=bool(diag.get("bo_ok")),
                                    pb=bool(diag.get("gate_pb")),
                                    vol=bool(diag.get("vol_ok")),
                                    entry=bool(diag.get("entry_signal")),
                                    src=src_used
                                )
                            )
                            _last_debug_ts[mint] = time.time()

                # ===== 2) ECHTE 5s-OHLCV (falls 60s nichts brachte) =====
                if not processed_any:
                    bars5, be_http5 = fetch_birdeye_ohlcv_5s(mint, BIRDEYE_API_KEY, limit=12, chain="sol")
                    if bars5 and be_http5 == 200:
                        last_ts = LAST_OHLCV_TS.get(mint, 0)
                        new_bars = [b for b in bars5 if int(b.get("time") or 0) > last_ts]
                        if new_bars:
                            new_bars.sort(key=lambda x: int(x["time"]))
                            for bar in new_bars:
                                signals = ENGINES[mint].on_bar(bar)
                                await _apply_signals(app, mint, bar, signals)
                                LAST_OHLCV_TS[mint] = int(bar["time"])
                                processed_any = True
                                src_used = "be-ohlcv(5s)"
                            if DEBUG_SCAN and (time.time() - _last_debug_ts.get(mint, 0.0) >= DEBUG_SCAN_SEC):
                                diag = ENGINES[mint].last_diag
                                await tg_post(
                                    "📊 {m} px={px:.6f} | ATR={atr:.6f} ADX={adx:.1f} | "
                                    "momo={momo} bo={bo} pb={pb} vol_ok={vol} → entry={entry}  (src={src})".format(
                                        m=mint[:6],
                                        px=new_bars[-1]["close"],
                                        atr=float(diag.get("atr") or 0.0),
                                        adx=float(diag.get("adx") or 0.0),
                                        momo=bool(diag.get("momo_ok")),
                                        bo=bool(diag.get("bo_ok")),
                                        pb=bool(diag.get("gate_pb")),
                                        vol=bool(diag.get("vol_ok")),
                                        entry=bool(diag.get("entry_signal")),
                                        src=src_used
                                    )
                                )
                                _last_debug_ts[mint] = time.time()

                # ===== 3) FALLBACK auf Builder (wenn keine echten Bars verarbeitet wurden) =====
                if not processed_any:
                    # Preis (Fallback-Stack): Birdeye -> GMGN -> GMGN(USDC) -> DexScreener
                    px = float(prices.get(mint, 0.0) or 0.0)
                    if px <= 0:
                        px = get_price_usd(mint)
                    if px <= 0:
                        if DEBUG_SCAN and (time.time() - _last_debug_ts.get(mint, 0.0) >= DEBUG_SCAN_SEC):
                            await tg_post(f"⚠️ {mint[:6]} kein Preis (Birdeye/GMGN/Dex) – skip.")
                            _last_debug_ts[mint] = time.time()
                        continue

                    # Volumen (DexScreener 1m -> pro Sekunde); Minimalwert
                    vps = dexscreener_usd_1m_approx(mint) / 60.0
                    if vps <= 0:
                        vps = 0.01

                    BUILDERS[mint].add(px, vps, now_ms)
                    bar = BUILDERS[mint].maybe_finish(now_ms)
                    if not bar:
                        continue

                    signals = ENGINES[mint].on_bar(bar)
                    await _apply_signals(app, mint, bar, signals)
                    src_used = "builder"

                    if DEBUG_SCAN and (time.time() - _last_debug_ts.get(mint, 0.0) >= DEBUG_SCAN_SEC):
                        diag = ENGINES[mint].last_diag
                        st = ENGINES[mint].st
                        cfg = ENGINES[mint].cfg
                        tms = int(bar["time"]) if isinstance(bar, dict) and "time" in bar else now_ms
                        hour_ok  = ENGINES[mint]._hour_ok(tms)
                        cool_ok  = (st.next_entry_earliest_bar is None) or (st.bar_index >= (st.next_entry_earliest_bar or 0))
                        open_ok  = (mint not in OPEN_POS)
                        cap_ok   = (st.trades_this_hour < cfg.max_trades_per_hour)

                        await tg_post(
                            "📊 {m} px={px:.6f} | ATR={atr:.6f} ADX={adx:.1f} | "
                            "momo={momo} bo={bo} pb={pb} vol_ok={vol} → signal={sig} | "
                            "allow: hour={hour} cool={cool} cap={cap} open={open} (src={src})"
                            .format(
                                m=mint[:6], px=bar["close"], atr=float(diag.get("atr") or 0.0),
                                adx=float(diag.get("adx") or 0.0), momo=bool(diag.get("momo_ok")),
                                bo=bool(diag.get("bo_ok")), pb=bool(diag.get("gate_pb")),
                                vol=bool(diag.get("vol_ok")), sig=bool(diag.get("entry_signal")),
                                hour=hour_ok, cool=cool_ok, cap=cap_ok, open=open_ok, src=src_used
                            )
                        )
                        _last_debug_ts[mint] = time.time()

            # ───────────────────── NEW: Memory-Sweep (nach der Mint-Schleife) ─────────────────────
            if time.time() - last_sweep > SWEEP_EVERY:
                live = set(WATCHLIST) | set(OPEN_POS.keys())
                for m in list(ENGINES.keys()):
                    if m not in live:
                        _drop_mint_state(m)
                last_sweep = time.time()
            # ─────────────────────────────────────────────────────────────────────────────────────

            await asyncio.sleep(1.0)

        except Exception as e:
            logger.exception(f"[auto_loop] Fehler: {e}")
            await asyncio.sleep(2.0)


async def _apply_signals(app: Application, mint: str, bar: dict, signals: list[dict]):
    """
    Hilfsfunktion: setzt Entry/Reduce/Close Signale um (wiederverwendbar in beiden Pfaden).
    """
    for s in signals:
        typ = s.get("type")

        if typ == "entry" and mint not in OPEN_POS:
            if float(bar.get("close") or 0.0) <= 0:
                continue
            try:
                # BUY
                res = await buy_wsol_to_token(mint, DEFAULT_NOTIONAL_SOL, bar["close"])
                # --- NEU: SL/TPs für die Meldung berechnen ---                
                eng = ENGINES.get(mint)
                if eng:
                    st  = eng.st; cfg = eng.cfg
                    entry = float(bar["close"])
                    atr   = float(eng.last_diag.get("atr") or 0.0)
                    atr_pc = float(eng.last_diag.get("atr_pc") or ((atr/entry)*100.0 if entry else 0.0))
                    sl_abs = entry - atr * cfg.risk_atr
                    R      = entry - sl_abs
                    tp1_px = entry + cfg.tp1_rr * R
                    tp2_px = entry + cfg.tp2_rr * R
                    extra  = (
                        f"\nSL≈{sl_abs:.6f}  TP1≈{tp1_px:.6f}  TP2≈{tp2_px:.6f}  "
                        f"(ATR≈{atr:.6f} / {atr_pc:.2f}%)"
                    )                

                else:
                    extra = ""
                await app.bot.send_message(
                    ALLOWED_CHAT_ID,
                    f"🚀 ENTRY {mint[:6]} @~{bar['close']:.6f} | {DEFAULT_NOTIONAL_SOL} SOL\nSig:{res['sig']} {res['status']}{extra}"
                )
            except Exception as e:
                await app.bot.send_message(ALLOWED_CHAT_ID, f"❌ BUY-Fehler {mint[:6]}: {e}")

        elif typ == "reduce":
            frac = float(s.get("qty_frac") or 0.0)
            try:
                hint = float(bar.get("close") or 0.0)
                if PAPER_MODE:
                    res = await _paper_sell_partial(mint, frac, mkt_price_hint=hint if hint > 0 else None)
                else:
                    res = await sell_partial(mint, frac)
                # Label:
                label = "TP1" if abs(frac- (ENGINES[mint].cfg.tp1_frac_pc/100.0)) < 1e-6 else \
                        "TP2" if abs(frac- (ENGINES[mint].cfg.tp2_frac_pc/100.0)) < 1e-6 else "REDUCE"
                await app.bot.send_message(
                    ALLOWED_CHAT_ID,
                    f"✅ {label} {mint[:6]} {int(frac*100)}% @~{bar['close']:.6f}\nSig:{res['sig']} {res['status']}"
                )
            except Exception as e:
                await app.bot.send_message(ALLOWED_CHAT_ID, f"❌ Reduce-Fehler {mint[:6]}: {e}")

        elif typ == "close":
            # 0-Preis-Guard
            if float(bar.get("close") or 0.0) <= 0:
                continue
            try:
                res = await sell_all(mint)
                await app.bot.send_message(
                    ALLOWED_CHAT_ID,
                    f"🏁 CLOSE {mint[:6]} @~{bar['close']:.6f}\nSig:{res['sig']} {res['status']}"
                )
            except Exception as e:
                await app.bot.send_message(ALLOWED_CHAT_ID, f"❌ Close-Fehler {mint[:6]}: {e}")

# =========================
# Starter (Notebook/Colab)
# =========================
#import nest_asyncio
#nest_asyncio.apply()
# Nur in Notebook/Colab sinnvoll. In Produktion mit uvicorn/uvloop NICHT patchen.

async def run_with_reconnect():
    global POLLING_STARTED, APP
    if POLLING_STARTED:
        print("⛔ Polling läuft bereits – Start abgebrochen."); return
    POLLING_STARTED = True; backoff = 2
    try:
        APP = await build_app(); await APP.initialize(); await APP.bot.delete_webhook(drop_pending_updates=True)
        await APP.bot.set_my_commands([
            # Core
            ("start",       "Befehle"),
            ("dashboard",  "Kompakt-Übersicht"),
            ("boot",        "Bot starten"),
            ("shutdown",    "Bot stoppen"),
            ("status",      "Status"),
            ("health",      "Gesundheit"),
            ("diag",        "Diagnose"),
            ("set_proxy",   "DexScreener-Proxy setzen"),

            # Trading / Portfolio
            ("buy",         "Kaufen: /buy <MINT> [sol]"),
            ("sell_all",    "Alles verkaufen: /sell_all <MINT>"),
            ("set_notional","Positionsgröße setzen"),
            ("set_slippage","Slippage setzen"),
            ("set_fee",     "MEV-Fee setzen"),
            ("positions",   "Token-Bestände"),
            ("open_trades", "Offene Positionen"),

            # Watchlist
            ("list_watch",  "Watchlist zeigen"),
            ("add_watch",   "Watchlist add"),
            ("remove_watch","Watchlist remove"),
            ("aw_observe", "Observe-Liste anzeigen"),

            # Discovery & Sanity
            ("scan_ds",     "DexScreener-Scan"),
            ("sanity",      "Sanity-Check <MINT>"),
            ("dsdiag",      "DS-Diagnose"),
            ("dsraw",       "DS-Suche raw"),
            ("ds_trending", "DS Trending (stabil)"),
            ("trending",    "Trending (kompakt)"),

            # Auto-Watchlist
            ("autowatch",   "Auto-Watchlist on/off"),
            ("aw_status",   "Auto-Watchlist Status"),
            ("aw_config",   "Auto-Watchlist Config"),
            ("aw_now",      "Auto-Watchlist Run"),

            # Liquidity
            ("check_liq",   "Liquidity-Check <MINT>"),
            ("auto_liq",    "Auto-Liquidity on/off"),
            ("liq_config",  "Liquidity-Config"),

            # Charts & PnL / Debug
            ("chart",       "Chart <MINT> [bars]"),
            ("pnl",         "P&L Übersicht"),
            ("debug",       "Debug on/off"),
        ])

        while True:
            try:
                await APP.start(); await APP.updater.start_polling(allowed_updates=Update.ALL_TYPES)
                print("✅ Bot läuft. Sende /start in Telegram.")
                while True: await asyncio.sleep(60)
            except Conflict:
                print("⛔ Conflict: Andere Instanz nutzt den Token."); raise
            except (TimedOut, NetworkError) as e:
                print(f"[Polling] Netzwerkproblem: {e} – retry in {backoff}s")
                await asyncio.sleep(backoff); backoff=min(backoff*2, 30); continue
            except Exception as e:
                print(f"[Polling] Unerwarteter Fehler: {e} – retry in {backoff}s")
                await asyncio.sleep(backoff); backoff=min(backoff*2, 30); continue
    finally:
        POLLING_STARTED = False


# ===== ASGI / Webhook + Health + Background Tasks (Option A) =====
# Voraussetzungen:
#   - pip: fastapi, uvicorn, httpx
#   - Render ENV:
#       TELEGRAM_BOT_TOKEN           (hast du)
#       RENDER_EXTERNAL_URL          (bei Web-Service automatisch gesetzt)
#       # optional:
#       WEBHOOK_BASE_URL             z.B. https://<dein-service>.onrender.com
#       KEEPALIVE_ENABLE            ("1" / "true" / "on" aktiviert self-ping; auf Web-Service meist nicht nötig)

import os
import asyncio
import contextlib
import httpx
from fastapi import FastAPI, Request
from fastapi.responses import JSONResponse, PlainTextResponse

# ---- Basiskonfiguration ------------------------------------------------------
KEEPALIVE_ENABLE = os.getenv("KEEPALIVE_ENABLE", "0").lower() in ("1", "true", "yes", "on")

# Basis-URL für den Webhook ermitteln (WEBHOOK_BASE_URL > RENDER_EXTERNAL_URL)
_render_host = os.getenv("RENDER_EXTERNAL_URL") or os.getenv("RENDER_EXTERNAL_HOSTNAME") or ""
if _render_host and not _render_host.startswith("http"):
    _render_host = f"https://{_render_host}"
WEBHOOK_BASE_URL = (os.getenv("WEBHOOK_BASE_URL") or _render_host).rstrip("/")
WEBHOOK_PATH = f"/tg/{TELEGRAM_BOT_TOKEN}"
WEBHOOK_URL = f"{WEBHOOK_BASE_URL}{WEBHOOK_PATH}" if WEBHOOK_BASE_URL else None

# ---- FastAPI-App -------------------------------------------------------------
svc = FastAPI(title="LuViNoCryptoBot")

@svc.get("/", include_in_schema=False)
async def root_ok():
    return PlainTextResponse("ok", status_code=200)

@svc.get("/healthz", include_in_schema=False)
async def healthz():
    return JSONResponse({"status": "ok"})

@svc.post(WEBHOOK_PATH if WEBHOOK_URL else "/_tg_disabled")
async def telegram_webhook(req: Request):
    """Webhook-Entry – leitet das JSON 1:1 an PTB weiter."""
    if APP is None:
        return PlainTextResponse("App not ready", status_code=503)
    update = await req.json()
    await APP.update_queue.put(update)
    return {"ok": True}

# ---- Self-Ping (optional, nur wenn KEEPALIVE_ENABLE=True) --------------------
async def _keepalive_loop():
    assert WEBHOOK_BASE_URL, "No base URL for keepalive"
    ping_url = f"{WEBHOOK_BASE_URL}/healthz"
    async with httpx.AsyncClient(timeout=10) as client:
        while True:
            try:
                r = await client.get(ping_url)
                logger.info("keepalive %s -> %s %s", ping_url, r.request.method, r.status_code)
            except Exception as exc:
                logger.warning("keepalive error: %s", exc)
            await asyncio.sleep(55)

# ---- Startup / Shutdown Hooks ------------------------------------------------
@svc.on_event("startup")
async def on_startup():
    """Startet PTB ohne Polling, setzt den Telegram-Webhook und startet Background-Tasks."""
    global APP, AUTOWATCH_TASK, AUTO_LIQ_TASK

    # 1) PTB-App initialisieren und starten (NICHT .updater.start_polling()!)
    if APP is None:
        APP = await build_app()
        await APP.initialize()
    await APP.start()
    logger.info("telegram.ext.Application:Application started")

    # 2) Webhook setzen (vorher sicherheitshalber löschen)
    if WEBHOOK_URL:
        try:
            await APP.bot.delete_webhook(drop_pending_updates=True)
            await APP.bot.set_webhook(WEBHOOK_URL, drop_pending_updates=True)
            logger.info("Telegram webhook set: %s", WEBHOOK_URL)
        except Exception as exc:
            logger.exception("Failed to set webhook: %s", exc)
    else:
        logger.warning("No WEBHOOK_BASE_URL/RENDER_EXTERNAL_URL -> webhook not set")

    # 3) Background-Tasks **nicht** blockierend starten
    if KEEPALIVE_ENABLE and WEBHOOK_BASE_URL:
        svc.state.keepalive_task = asyncio.create_task(_keepalive_loop())
    if AW_CFG.get("enabled") and (AUTOWATCH_TASK is None or AUTOWATCH_TASK.done()):
        AUTOWATCH_TASK = asyncio.create_task(aw_loop())
    if LIQ_CFG.get("enabled") and (AUTO_LIQ_TASK is None or AUTO_LIQ_TASK.done()):
        AUTO_LIQ_TASK = asyncio.create_task(auto_liq_loop())

@svc.on_event("shutdown")
async def on_shutdown():
    """Hintergrund-Tasks sauber abbrechen und PTB/Webhook stoppen."""
    # Hintergrund-Tasks stoppen
    task = getattr(svc, "state", None) and getattr(svc.state, "keepalive_task", None)
    if task:
        task.cancel()
        with contextlib.suppress(Exception):
            await task

    await _stop_task("AutoLiquidity", "AUTO_LIQ_TASK")
    await _stop_task("AutoWatch", "AUTOWATCH_TASK")

    # Webhook entfernen und PTB stoppen
    try:
        await APP.bot.delete_w ebhook(drop_pending_updates=True)
    except Exception:
        pass
    if APP:
        with contextlib.suppress(Exception):
            await APP.stop()
            await APP.shutdown()
# ===== Ende ASGI-Block ========================================================
