#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
TrackSync 2 - Voice-first Railway Station Accessibility System   (ots2.py)
==========================================================================
Pure Python. Front end = Tkinter window (same look and feel as ots.py),
back end = SQLite + a background scheduler + a background location tracker.

PASSENGER FLOW
    1. LOGIN PAGE      The app SPEAKS and asks your name. Say it (or type it). Name only - no
                       password, no phone number, no other details are asked.
    2. LOCATION        The app asks permission (speech or button) to use this device's location
                       to track your progress and PREDICT YOUR WAY to the station and platform.
    3. SCAN TICKET     Hold the ticket QR code up to the camera (or speak / type the details).
    4. MENU            The app asks WHICH MENU you want (speech or text) and answers in speech
                       and text.  Say e.g. "route planner", "navigation", "my location".

RUN
    python ots2.py                 -> opens the TrackSync window (passenger app)
    python ots2.py --scheduler     -> runs ONLY the check-in scheduler (no window)

NOTHING IS REQUIRED TO START (Tkinter and SQLite ship with Python).  Optional, for the full voice
experience (or press "Set up speech input" on the login page and the app installs it for you):
    pip install vosk sounddevice         + the small Vosk Indian-English model (~40 MB) unzipped next to
                                           this file as  vosk-model-small-en-in-0.4
        (alternative engine:  pip install SpeechRecognition pyaudio pocketsphinx)
    pip install opencv-python            -> camera QR scanning (otherwise speak or type the ticket)
    Spoken English uses what the computer already has: Windows (built-in voice), macOS ("say"),
    Linux (espeak-ng / espeak / spd-say), or pyttsx3 if installed.

LOCATION (Python only, asked from the passenger first)
    The app tries, in this order:  1) a GPS receiver through gpsd (any OS),  2) the operating system
    location service (Windows: PowerShell GeoCoordinateWatcher - Windows asks you to allow it;
    Linux: GeoClue "where-am-i"),  3) an APPROXIMATE location from your internet address
    (city-level only; sends your IP address to ip-api.com / ipapi.co - set TRACKSYNC_IP_LOCATION=0 to
    switch this off).  If none works you can tell the app where you are standing by choosing a place.
    The location trail lives in memory only; it is never written to the database or a file.

PRIVACY
    * Only your NAME is asked, and only for this session.  At log-out (or when the window closes)
      every passenger record - name, ticket, notifications, alerts, rides - is deleted.
    * Your location is shared with station staff ONLY inside an SOS / missed check-in alert.

STAFF LOGINS (use "Driver / staff sign-in" on the login page)
    driver : Ravi            password: driver123   -> mobility vehicle driver console
    staff  : Station Staff   password: staff123    -> safety alerts + station notices

HONEST LIMITS OF THIS PROTOTYPE
  * GPS is weak indoors (subways, platforms under roofs).  Inside the station the way prediction
    snaps your position to the nearest point on a ROUGH station map (NODE_XY below) and asks you to
    confirm with a marker code (TS-P1 ...) for exact position.  Use "Set this spot as station
    entrance" on the My Location page to calibrate the map anywhere.
  * Crowd levels, lift status, coach positions, vehicle locations and energy values come from lists
    inside this file - they are not live railway data.
  * Alerts go to the staff console on this computer. Set STATION_RELAY to a real (host, port) on your
    station LAN to forward alerts; the app never claims emergency services were contacted.
"""
import sys, os, re, json, time, math, heapq, random, socket, sqlite3, hashlib, hmac, queue, base64
import secrets, shutil, platform, threading, subprocess, traceback, importlib, zipfile
import urllib.request
import array
from collections import deque
from datetime import datetime
import tkinter as tk
from tkinter import ttk, messagebox, simpledialog

# ----------------------------------------------------------------------------
# CONFIGURATION
# ----------------------------------------------------------------------------
APP_DIR = os.path.dirname(os.path.abspath(__file__))
DB_PATH = os.path.join(APP_DIR, "tracksync2_data.db")
ERR_LOG = os.path.join(APP_DIR, "tracksync2_errors.log")
STATION_RELAY = None          # e.g. ("192.168.1.20", 9000) to forward alerts over a LAN
CREDITS_PER_WH = float(os.environ.get("TRACKSYNC_CREDITS_PER_WH", "10"))
CROWD_WEIGHT_M = 6            # route cost = metres + 6 x crowd level (0-10); safety filters come first
WALK_SPEED = {"default": 1.2, "elderly": 0.8, "wheelchair": 1.0}   # metres per second
VEHICLE_ACCEPT_DELAY_S = 10   # a vehicle request shows only "Request submitted" for this long, then a driver accepts
# Green energy: each time the passenger adds a walking contribution, ONE value is picked at random from these 20 kWh readings
ENERGY_KWH_DATA = [0.004, 0.005, 0.006, 0.007, 0.008, 0.008, 0.009, 0.010, 0.010, 0.011,
                   0.012, 0.012, 0.013, 0.014, 0.015, 0.016, 0.017, 0.018, 0.020, 0.022]

# Where the station entrance is on the map (default value near Chennai Egmore - EDIT for your station,
# or set the environment variable TRACKSYNC_STATION="lat,lon", or use the calibrate button in the app).
STATION = {"ll": (13.0732, 80.2609)}
try:
    _s = os.environ.get("TRACKSYNC_STATION", "")
    if _s:
        STATION["ll"] = tuple(float(x) for x in _s.split(","))[:2]
except ValueError:
    pass
STATION_RADIUS_M = 250        # inside this circle the app uses the station map instead of street directions
ALLOW_IP_LOCATION = os.environ.get("TRACKSYNC_IP_LOCATION", "1") != "0"
LOCATION_INTERVAL_S = 8       # how often the position is refreshed while tracking is on

VOSK_MODEL_NAME = "vosk-model-small-en-in-0.4"      # Indian English - recognises Indian accents better
VOSK_MODEL_URL = f"https://alphacephei.com/vosk/models/{VOSK_MODEL_NAME}.zip"
VOSK_MODEL_DIRS = [VOSK_MODEL_NAME, "vosk-model-en-in-0.5", "vosk-model-small-en-us-0.15", "model"]

# ----------------------------------------------------------------------------
# STATION DATA (rough values kept inside this file)
# ----------------------------------------------------------------------------
NODES = {
    "ENTRY": dict(name="Subway entrance (street side)", level=-1, phrase="the subway entrance", signs="the subway"),
    "SUB_W": dict(name="West subway landing", level=-1, phrase="the west landing of the subway", signs="Platforms 1 and 2"),
    "SUB_C": dict(name="Central subway landing", level=-1, phrase="the central landing of the subway", signs="Platforms 3 and 4"),
    "SUB_E": dict(name="East subway landing", level=-1, phrase="the east landing of the subway", signs="Platforms 5, 6 and 7"),
    "P1": dict(name="Platform 1", level=0, phrase="Platform 1", signs="Platform 1"),
    "P2": dict(name="Platform 2", level=0, phrase="Platform 2", signs="Platform 2"),
    "P3": dict(name="Platform 3", level=0, phrase="Platform 3", signs="Platform 3"),
    "P4": dict(name="Platform 4", level=0, phrase="Platform 4", signs="Platform 4"),
    "P5": dict(name="Platform 5", level=0, phrase="Platform 5", signs="Platform 5"),
    "P6": dict(name="Platform 6", level=0, phrase="Platform 6", signs="Platform 6"),
    "P7": dict(name="Platform 7", level=0, phrase="Platform 7", signs="Platform 7"),
}
# Rough positions in metres (east, north) from the station entrance - used to snap a GPS fix
# to the nearest station point.  Replace with surveyed values for a real station.
NODE_XY = {"ENTRY": (0, 0), "SUB_W": (-30, 40), "SUB_C": (30, 40), "SUB_E": (90, 40),
           "P1": (-40, 75), "P2": (-20, 95), "P3": (20, 75), "P4": (40, 95),
           "P5": (80, 75), "P6": (100, 95), "P7": (120, 75)}
MARKERS = {"TS-ENTRY": "ENTRY", "TS-SUBW": "SUB_W", "TS-SUBC": "SUB_C", "TS-SUBE": "SUB_E",
           "TS-P1": "P1", "TS-P2": "P2", "TS-P3": "P3", "TS-P4": "P4", "TS-P5": "P5", "TS-P6": "P6", "TS-P7": "P7"}
PLATFORM_KEYS = ["P1", "P2", "P3", "P4", "P5", "P6", "P7"]
POINT_CHOICES = ["ENTRY", "SUB_W", "SUB_C", "SUB_E"] + PLATFORM_KEYS     # start / pickup choices

# id, from, to, mode, metres, crowd(0-10), fixed wait (s), in service, name
_EDGES = [
    ("E1", "ENTRY", "SUB_W", "flat", 60, 3, 0, True, "Entrance corridor"),
    ("E2", "P1", "SUB_W", "stairs", 25, 6, 0, True, "Platform 1 stairs"),
    ("E3", "P1", "SUB_W", "escalator", 25, 5, 0, True, "Platform 1 escalator"),
    ("E4", "P1", "SUB_W", "lift", 15, 3, 40, True, "Platform 1 lift"),
    ("E5", "P1", "SUB_W", "ramp", 70, 2, 0, True, "Platform 1 ramp"),
    ("E6", "P2", "SUB_W", "stairs", 25, 8, 0, True, "Platform 2 stairs"),
    ("E7", "P2", "SUB_W", "lift", 15, 4, 40, True, "Platform 2 lift"),
    ("E8", "P2", "SUB_W", "ramp", 70, 3, 0, True, "Platform 2 ramp"),
    ("E9", "SUB_W", "SUB_C", "flat", 60, 5, 0, True, "Main subway (west)"),
    ("E10", "SUB_W", "SUB_C", "travelator", 60, 2, 0, True, "Subway travelator, west (wheelchair compatible)"),
    ("E11", "P3", "SUB_C", "stairs", 25, 5, 0, True, "Platform 3 stairs"),
    ("E12", "P3", "SUB_C", "escalator", 25, 4, 0, True, "Platform 3 escalator"),
    ("E13", "P3", "SUB_C", "lift", 15, 2, 40, True, "Platform 3 lift"),
    ("E14", "P4", "SUB_C", "stairs", 25, 7, 0, True, "Platform 4 stairs"),
    ("E15", "P4", "SUB_C", "lift", 15, 3, 40, True, "Platform 4 lift"),
    ("E16", "SUB_C", "SUB_E", "flat", 60, 4, 0, True, "Main subway (east)"),
    ("E17", "SUB_C", "SUB_E", "travelator", 60, 2, 0, True, "Subway travelator, east (wheelchair compatible)"),
    ("E18", "P5", "SUB_E", "stairs", 25, 4, 0, True, "Platform 5 stairs"),
    ("E19", "P5", "SUB_E", "escalator", 25, 3, 0, True, "Platform 5 escalator"),
    ("E20", "P5", "SUB_E", "lift", 15, 2, 40, True, "Platform 5 lift"),
    ("E21", "P5", "SUB_E", "ramp", 70, 2, 0, True, "Platform 5 ramp"),
    ("E22", "P6", "SUB_E", "stairs", 25, 6, 0, True, "Platform 6 stairs"),
    ("E23", "P6", "SUB_E", "lift", 15, 3, 40, True, "Platform 6 lift"),
    ("E24", "P6", "SUB_E", "ramp", 70, 3, 0, True, "Platform 6 ramp"),
    ("E25", "P7", "SUB_E", "stairs", 25, 7, 0, True, "Platform 7 stairs"),
    ("E26", "P7", "SUB_E", "lift", 15, 3, 40, True, "Platform 7 lift"),
]
EDGES = [dict(id=i, a=a, b=b, mode=m, dist=d, crowd=c, wait=w, ok=ok, name=n)
         for (i, a, b, m, d, c, w, ok, n) in _EDGES]

# ---- LIFT STATUS LIST -----------------------------------------------------------------
# After the passenger's ticket is scanned the app picks ONE entry from this list at random and tells the
# passenger.  Each entry is the list of lift edge ids that are NOT working.  An empty list [] means
# "everything is working properly" (it is repeated so that this is the most common answer).
LIFT_STATUS_DATA = [[], [], [], [], ["E7"], ["E4"], ["E13"], ["E15"], ["E20"], ["E23"], ["E26"], ["E7", "E20"]]
LIFT_OUT = set()

# ---- MOBILITY VEHICLE DATA --------------------------------------------------------------
# When a driver accepts a request, the vehicle location is picked at random from this list.
VEHICLE_LOCATION_DATA = ["Station parking bay", "Subway entrance - street side drop-off", "West subway landing",
                         "East subway landing", "Platform 1 lift lobby", "Platform 2 ramp, subway side",
                         "Platform 3 lift lobby", "Platform 4 lift lobby", "Booking hall charging point",
                         "Main subway, near the travelator"]

# Time taken by each stage of a mobility-vehicle journey, in SECONDS. One value is picked at random from each list of 20
# readings.  The three limits below are never exceeded - not on screen and not in the spoken announcements:
#   vehicle arrives  : at most 2 minutes after the driver accepted
#   journey starts   : at most 10 seconds after the vehicle arrived
#   destination      : at most 3.5 minutes after the journey started
ARRIVE_MAX_S, START_MAX_S, TRIP_MAX_S = 120, 10, 210
ARRIVE_DELAY_DATA = [20, 25, 30, 35, 40, 45, 50, 55, 60, 65, 70, 75, 80, 85, 90, 95, 100, 105, 110, 120]
START_DELAY_DATA = [2, 3, 3, 4, 4, 5, 5, 5, 6, 6, 6, 7, 7, 8, 8, 8, 9, 9, 10, 10]
TRIP_DURATION_DATA = [60, 75, 90, 100, 110, 120, 130, 140, 150, 155, 160, 165, 170, 175, 180, 190, 195, 200, 205, 210]

MODE_NAMES = {"stairs": "Stairs", "escalator": "Escalator", "lift": "Lift", "stepfree": "Step-free"}
MODE_ALLOWED = {
    "stairs": {"flat", "stairs"},
    "escalator": {"flat", "escalator", "travelator"},
    "lift": {"flat", "lift", "travelator"},
    "stepfree": {"flat", "lift", "ramp", "travelator"},
}
ALT_ORDER = ["stepfree", "lift", "escalator", "stairs"]

# Typical coach zones along a platform: zone -> (metres from platform access point, coaches)
ZONES = {"A": (20, ["SLR", "GS1", "S1", "S2"]), "B": (65, ["S3", "S4", "S5", "S6"]),
         "C": (110, ["S7", "S8", "S9", "B1"]), "D": (155, ["B2", "A1", "H1", "GS2"])}

# Train timetable (platform assignment per train)
TRAINS = {"12637": {"name": "Pandian Express", "platform": "P2"},
          "12635": {"name": "Vaigai Express", "platform": "P4"},
          "16127": {"name": "Guruvayur Express", "platform": "P1"},
          "22671": {"name": "Tejas Express", "platform": "P3"},
          "12631": {"name": "Nellai Express", "platform": "P5"},
          "12661": {"name": "Pothigai Express", "platform": "P6"},
          "12693": {"name": "Muthunagar Express", "platform": "P7"}}

NEED_LABELS = {"deaf": "Deaf / hard of hearing", "blind": "Blind / low vision",
               "wheelchair": "Wheelchair / step-free access",
               "elderly": "Elderly / mobility assistance", "none": "No assistance required"}

# Menus the passenger can ask for by speech:  key, tile label, words that select it
MENUS = [("scan", "Scan Ticket", ["scan", "ticket"]),
         ("prefs", "Accessibility Preferences", ["preference", "accessib", "assistance"]),
         ("route", "Route Planner", ["route", "planner", "plan"]),
         ("nav", "Navigation", ["navigat", "guide", "direction"]),
         ("where", "My Location & Way", ["location", "where", "tracking", "track", "way"]),
         ("energy", "Green Energy & Credits", ["energy", "credit", "green"]),
         ("mobility", "Mobility Vehicle", ["mobility", "vehicle", "ride", "buggy"]),
         ("checkin", "Safety Check-ins", ["check", "safety"]),
         ("notifs", "Notifications", ["notif", "message"])]
MENU_QUESTION = ("Which menu would you like? You can say: scan ticket, preferences, route planner, navigation, "
                 "my location, green energy, mobility vehicle, safety check-ins, or notifications.")
MENU_GRAMMAR = ["scan", "ticket", "preferences", "preference", "accessibility", "assistance", "route", "planner", "plan",
                "navigation", "guide", "directions", "my", "location", "where", "am", "i", "tracking", "way", "green",
                "energy", "credits", "mobility", "vehicle", "ride", "check", "ins", "safety", "notifications",
                "messages", "home", "menu", "log", "out", "sos", "help", "me", "emergency", "[unk]"]
YES_WORDS = {"yes", "yeah", "yep", "yup", "ok", "okay", "sure", "continue", "correct", "right", "allow", "proceed", "please"}
NO_WORDS = {"no", "nope", "not", "skip", "deny", "cancel", "don't", "never", "later"}

# ----------------------------------------------------------------------------
# THEME  (identical to ots.py)
# ----------------------------------------------------------------------------
NAVY, TEAL, WHITE, BG = "#0B2545", "#0E7C7B", "#FFFFFF", "#F1F9F9"
RED, YELLOW, GREY = "#B3261E", "#FFD166", "#4A5D78"
FONT = "Arial"
SCALE = 1.0


def F(size, bold=False):
    return (FONT, max(8, int(size * SCALE)), "bold" if bold else "normal")


# ----------------------------------------------------------------------------
# UI QUEUE  (background threads never touch Tk directly - they post here)
# ----------------------------------------------------------------------------
UIQ = queue.Queue()


def call_ui(fn, *args):
    UIQ.put((fn, args))


# ----------------------------------------------------------------------------
# DATABASE  (passenger rows live only for the session)
# ----------------------------------------------------------------------------
SCHEMA = """
CREATE TABLE IF NOT EXISTS users(id INTEGER PRIMARY KEY, name TEXT, salt TEXT DEFAULT '', pw TEXT DEFAULT '',
  role TEXT DEFAULT 'passenger', needs TEXT DEFAULT '', available INTEGER DEFAULT 1, last_notice INTEGER DEFAULT 0);
CREATE TABLE IF NOT EXISTS tickets(user_id INTEGER PRIMARY KEY, data TEXT);
CREATE TABLE IF NOT EXISTS notifs(id INTEGER PRIMARY KEY, user_id INTEGER, kind TEXT, text TEXT, created TEXT, urgent INTEGER DEFAULT 0);
CREATE TABLE IF NOT EXISTS notices(id INTEGER PRIMARY KEY, kind TEXT, text TEXT, created TEXT);
CREATE TABLE IF NOT EXISTS energy(id INTEGER PRIMARY KEY, user_id INTEGER, wh REAL, credits REAL, source TEXT, created TEXT);
CREATE TABLE IF NOT EXISTS rides(id INTEGER PRIMARY KEY, user_id INTEGER, pickup TEXT, dest TEXT, status TEXT,
  driver_id INTEGER, eta_min INTEGER, loc TEXT, loc_time TEXT, created TEXT, created_ts REAL, start_at REAL, acc_at REAL, arrive_at REAL, end_at REAL);
CREATE TABLE IF NOT EXISTS sched(user_id INTEGER PRIMARY KEY, interval_min REAL DEFAULT 10, state TEXT DEFAULT 'stopped',
  next_due REAL, remaining REAL, window_s INTEGER DEFAULT 60);
CREATE TABLE IF NOT EXISTS checkins(id INTEGER PRIMARY KEY, user_id INTEGER, prompted REAL, deadline REAL, status TEXT, alert_id INTEGER);
CREATE TABLE IF NOT EXISTS alerts(id INTEGER PRIMARY KEY, user_id INTEGER, kind TEXT, message TEXT, created REAL,
  status TEXT DEFAULT 'open', delivery TEXT DEFAULT 'queued', warned INTEGER DEFAULT 0, ack_by TEXT, ack_time REAL);
"""
PASSENGER_TABLES = ("tickets", "notifs", "energy", "rides", "sched", "checkins", "alerts")


def _con():
    con = sqlite3.connect(DB_PATH, timeout=15)
    con.row_factory = sqlite3.Row
    return con


def qall(sql, args=()):
    con = _con()
    try:
        return [dict(r) for r in con.execute(sql, args).fetchall()]
    finally:
        con.close()


def qone(sql, args=()):
    rows = qall(sql, args)
    return rows[0] if rows else None


def ex(sql, args=()):
    con = _con()
    try:
        cur = con.execute(sql, args)
        con.commit()
        return cur.lastrowid
    finally:
        con.close()


def exn(sql, args=()):
    """Like ex() but returns how many rows were changed (used for safe 'accept only once' updates)."""
    con = _con()
    try:
        cur = con.execute(sql, args)
        con.commit()
        return cur.rowcount
    finally:
        con.close()


def log_error():
    try:
        with open(ERR_LOG, "a", encoding="utf-8") as f:
            f.write(datetime.now().isoformat() + "\n" + traceback.format_exc() + "\n")
    except OSError:
        pass


def hash_pw(pw, salt=None):
    salt = salt or secrets.token_hex(16)
    h = hashlib.pbkdf2_hmac("sha256", pw.encode("utf-8"), bytes.fromhex(salt), 200_000).hex()
    return salt, h


def check_pw(pw, salt, h):
    return bool(salt) and hmac.compare_digest(hash_pw(pw, salt)[1], h)


def add_staff(name, pw, role):
    salt, h = hash_pw(pw)
    return ex("INSERT INTO users(name,salt,pw,role) VALUES(?,?,?,?)", (name, salt, h, role))


def now_s():
    return datetime.now().strftime("%d %b %H:%M")


def init_db():
    con = _con()
    con.executescript(SCHEMA)
    con.commit()
    con.close()
    if not qone("SELECT id FROM users WHERE role='driver'"):
        add_staff("Ravi", "driver123", "driver")
    if not qone("SELECT id FROM users WHERE role='staff'"):
        add_staff("Station Staff", "staff123", "staff")
    # lift status is no longer a fixed notice: it comes from LIFT_STATUS_DATA after a ticket is scanned
    ex("DELETE FROM notices WHERE text LIKE 'The lift at Platform 2 is out of service%'")
    cols = {r["name"] for r in qall("PRAGMA table_info(rides)")}          # upgrade an older database file
    for col in ("created_ts", "start_at", "acc_at", "arrive_at", "end_at"):
        if col not in cols:
            ex(f"ALTER TABLE rides ADD COLUMN {col} REAL")


def purge_passengers(uid=None):
    """Delete passenger data. uid=None wipes every passenger (used at start-up)."""
    con = _con()
    try:
        ids = [uid] if uid else [r["id"] for r in con.execute("SELECT id FROM users WHERE role='passenger'")]
        for i in ids:
            for t in PASSENGER_TABLES:
                con.execute(f"DELETE FROM {t} WHERE user_id=?", (i,))
            con.execute("DELETE FROM users WHERE id=?", (i,))
        con.commit()
    finally:
        con.close()


def hhmm(ts):
    return datetime.fromtimestamp(ts).strftime("%H:%M") if ts else ""


def hms(ts):
    return datetime.fromtimestamp(ts).strftime("%H:%M:%S") if ts else ""


def fmt_secs(s):
    s = max(0, int(round(s)))
    if s < 120:
        return f"{s} second" + ("" if s == 1 else "s")
    m, r = divmod(s, 60)
    return f"{m} min" + (f" {r} s" if r else "")


def needs_of(u):
    return {x for x in (u.get("needs") or "").split(",") if x}


def notify(uid, text, kind="info", urgent=False):
    ex("INSERT INTO notifs(user_id,kind,text,created,urgent) VALUES(?,?,?,?,?)",
       (uid, kind, text, now_s(), 1 if urgent else 0))


def get_ticket(uid):
    r = qone("SELECT data FROM tickets WHERE user_id=?", (uid,))
    return json.loads(r["data"]) if r else None


def save_ticket(uid, data):
    ex("INSERT OR REPLACE INTO tickets(user_id,data) VALUES(?,?)", (uid, json.dumps(data)))


# ---- the only thing asked of a passenger: a name ------------------------------
def clean_name(text):
    t = re.sub(r"[^A-Za-z\u00C0-\u024F\u0900-\u0DFF .'\-]", "", text or "").strip()
    return re.sub(r"\s+", " ", t)[:40]


def extract_name(spoken):
    """Turn 'my name is arun kumar' into 'Arun Kumar'."""
    t = (spoken or "").lower().replace("[unk]", " ").strip()
    t = re.sub(r"^(?:hello|hi|hey)[ ,]+", "", t)
    t = re.sub(r"^(?:my name is|my name's|this is|i am|i'm|it is|it's|name is|call me|myself)\s+", "", t)
    t = re.sub(r"\s+(?:please|thanks|thank you)$", "", t)
    return clean_name(t).title() if len(clean_name(t)) >= 2 else ""


def new_passenger(name):
    uid = ex("INSERT INTO users(name,role) VALUES(?, 'passenger')", (name,))
    top = qone("SELECT MAX(id) m FROM notices")["m"] or 0
    ex("UPDATE users SET last_notice=? WHERE id=?", (max(0, top - 3), uid))
    return qone("SELECT * FROM users WHERE id=?", (uid,))


def staff_login(name, pw, roles):
    u = qone("SELECT * FROM users WHERE name=? COLLATE NOCASE", ((name or "").strip(),))
    if u and u["role"] in roles and check_pw(pw, u["salt"], u["pw"]):
        return u
    return None


# ---- alerts / check-ins (shared by UI and scheduler) ---------------------------
def alert_status_text(a):
    if a["status"] == "cancelled":
        return "Alert cancelled"
    if a["status"] == "closed":
        return "Closed by staff"
    if a["status"] == "acknowledged":
        return f"Acknowledged by {a['ack_by']} at {hhmm(a['ack_time'])}"
    if a["delivery"] == "delivered":
        return "Sent to station staff - not acknowledged yet"
    return "NOT delivered yet (no connection) - retrying"


def attempt_delivery(aid):
    a = qone("SELECT * FROM alerts WHERE id=?", (aid,))
    if not a or a["status"] != "open" or a["delivery"] == "delivered":
        return
    ok = True
    if STATION_RELAY:
        try:
            with socket.create_connection(STATION_RELAY, timeout=2) as s:
                s.sendall((json.dumps({"alert": a["id"], "message": a["message"]}) + "\n").encode("utf-8"))
        except OSError:
            ok = False
    if ok:
        ex("UPDATE alerts SET delivery='delivered' WHERE id=?", (aid,))
        if a["warned"]:
            notify(a["user_id"], "Connection restored. Your alert has now been delivered to station staff.", "safety", True)
        else:
            notify(a["user_id"], "Your alert was delivered to station staff. Waiting for a staff member to acknowledge it.", "safety", True)
    elif not a["warned"]:
        ex("UPDATE alerts SET warned=1 WHERE id=?", (aid,))
        notify(a["user_id"], "No network connection: your alert could not be delivered yet. It will keep retrying. "
               "Please ask someone nearby for help, or call 112.", "safety", True)


def create_alert(uid, kind, message):
    u = qone("SELECT * FROM users WHERE id=?", (uid,))
    t = get_ticket(uid) or {}
    needs = ", ".join(NEED_LABELS[n] for n in sorted(needs_of(u)) if n in NEED_LABELS) or "not stated"
    ctx = (f"Passenger: {u['name']}. Needs: {needs}. Train: {t.get('train_no', '-')} {t.get('train_name', '')}. "
           f"Coach {t.get('coach', '-')}, seat {t.get('seat', '-')}. Last known position: {LOC.describe()}.")
    aid = ex("INSERT INTO alerts(user_id,kind,message,created) VALUES(?,?,?,?)", (uid, kind, f"{message} {ctx}", time.time()))
    attempt_delivery(aid)
    return aid


def plan_ride_times(now, arrive_s=None):
    """Pick the time of each stage from the 20-reading lists, never above the stage limits."""
    a = min(arrive_s if arrive_s is not None else random.choice(ARRIVE_DELAY_DATA), ARRIVE_MAX_S)
    s = min(random.choice(START_DELAY_DATA), START_MAX_S)
    t = min(random.choice(TRIP_DURATION_DATA), TRIP_MAX_S)
    arrive_at = now + a
    start_at = arrive_at + s
    return a, arrive_at, start_at, start_at + t


def ride_plan_text(a, arrive_at, start_at, end_at):
    return (f"The vehicle will arrive in about {fmt_secs(a)} (at {hms(arrive_at)}). The journey starts at {hms(start_at)}. "
            f"You will reach your destination at {hms(end_at)}.")


def auto_accept_rides():
    """10 seconds after a mobility-vehicle request, an on-duty driver accepts it. The stage times come from the lists
    ARRIVE_DELAY_DATA / START_DELAY_DATA / TRIP_DURATION_DATA and the vehicle location from VEHICLE_LOCATION_DATA."""
    now = time.time()
    for r in qall("SELECT * FROM rides WHERE status='submitted' AND created_ts IS NOT NULL AND created_ts<=?",
                  (now - VEHICLE_ACCEPT_DELAY_S,)):
        d = qone("SELECT id, name FROM users WHERE role='driver' AND available=1 ORDER BY id LIMIT 1")
        if not d:
            break
        loc = random.choice(VEHICLE_LOCATION_DATA)
        a, arrive_at, start_at, end_at = plan_ride_times(now)
        if exn("UPDATE rides SET status='accepted', driver_id=?, eta_min=?, loc=?, loc_time=?, acc_at=?, arrive_at=?, "
               "start_at=?, end_at=? WHERE id=? AND status='submitted'",
               (d["id"], max(1, int(math.ceil(a / 60.0))), loc, datetime.now().strftime("%H:%M"), now, arrive_at,
                start_at, end_at, r["id"])):
            notify(r["user_id"], f"Driver {d['name']} accepted your request. {ride_plan_text(a, arrive_at, start_at, end_at)} "
                                 f"The vehicle was last reported at: {loc}.", "vehicle")


def advance_rides():
    """vehicle arrived -> journey started -> destination arrived, each when its planned time is reached."""
    now = time.time()
    for r in qall("SELECT * FROM rides WHERE status IN ('accepted','vehicle_arrived','started')"):
        if r["status"] == "accepted" and r["arrive_at"] and r["arrive_at"] <= now:
            if exn("UPDATE rides SET status='vehicle_arrived' WHERE id=? AND status='accepted'", (r["id"],)):
                notify(r["user_id"], f"The vehicle has arrived at {NODES[r['pickup']]['name']}.", "vehicle")
        elif r["status"] == "vehicle_arrived" and r["start_at"] and r["start_at"] <= now:
            if exn("UPDATE rides SET status='started' WHERE id=? AND status='vehicle_arrived'", (r["id"],)):
                notify(r["user_id"], "Your journey has started.", "vehicle")
        elif r["status"] == "started" and r["end_at"] and r["end_at"] <= now:
            if exn("UPDATE rides SET status='arrived' WHERE id=? AND status='started'", (r["id"],)):
                notify(r["user_id"], "You have arrived at your destination.", "vehicle")


def process_schedules():
    now = time.time()
    for s in qall("SELECT * FROM sched WHERE state='running' AND next_due IS NOT NULL AND next_due<=?", (now,)):
        if qone("SELECT id FROM checkins WHERE user_id=? AND status='prompt'", (s["user_id"],)):
            continue
        ex("INSERT INTO checkins(user_id,prompted,deadline,status) VALUES(?,?,?,'prompt')",
           (s["user_id"], now, now + s["window_s"]))
        ex("UPDATE sched SET next_due=? WHERE user_id=?", (now + s["window_s"] + s["interval_min"] * 60, s["user_id"]))
    for c in qall("SELECT * FROM checkins WHERE status='prompt' AND deadline<=?", (now,)):
        aid = create_alert(c["user_id"], "missed_checkin", "Passenger did not answer a welfare check-in.")
        ex("UPDATE checkins SET status='missed', alert_id=? WHERE id=?", (aid, c["id"]))
        notify(c["user_id"], "You did not answer your check-in, so an alert was created for station staff.", "safety", True)
    for a in qall("SELECT id FROM alerts WHERE status='open' AND delivery='queued'"):
        attempt_delivery(a["id"])
    auto_accept_rides()
    advance_rides()


class Scheduler(threading.Thread):
    """Background check-in scheduler; keeps running independently of which page is open."""
    def __init__(self):
        super().__init__(daemon=True)
        self.stop_flag = threading.Event()

    def run(self):
        while not self.stop_flag.is_set():
            try:
                process_schedules()
            except Exception:
                log_error()
            self.stop_flag.wait(1.0)



# ----------------------------------------------------------------------------
# ROUTING (inside the station)
# ----------------------------------------------------------------------------
def norm_modes(modes):
    """One travel type (text) or several (list) -> list in a fixed order."""
    chosen = {modes} if isinstance(modes, str) else set(modes or [])
    return [m for m in ALT_ORDER if m in chosen] or ["stairs"]


def modes_label(modes):
    return " + ".join(MODE_NAMES[m] for m in norm_modes(modes))


def allowed_edge_modes(modes):
    out = set()
    for m in norm_modes(modes):
        out |= MODE_ALLOWED[m]
    return out


def edge_ok(e):
    return e["ok"] and e["id"] not in LIFT_OUT


def lift_status_text():
    if not LIFT_OUT:
        return "All lifts, ramps and step-free routes are working properly."
    names = [e["name"] for e in EDGES if e["id"] in LIFT_OUT]
    verb = "is" if len(names) == 1 else "are"
    return (f"The {' and the '.join(names)} {verb} not working at the moment. Please use a ramp or another "
            "step-free route, ask station staff, or request a mobility vehicle.")


def refresh_lift_status():
    """Pick a fresh lift status from LIFT_STATUS_DATA (called after the ticket is scanned)."""
    global LIFT_OUT
    LIFT_OUT = set(random.choice(LIFT_STATUS_DATA))
    return lift_status_text()


def clear_lift_status():
    global LIFT_OUT
    LIFT_OUT = set()


def default_mode(needs):
    return "stepfree" if "wheelchair" in needs else "lift" if "elderly" in needs else "stairs"


def find_route(src, dst, mode):
    """mode = one travel type or a list of several; the cheapest route using ANY of the chosen types is returned."""
    modes = norm_modes(mode)
    allowed = allowed_edge_modes(modes)
    adj = {}
    for e in EDGES:
        if edge_ok(e) and e["mode"] in allowed:
            adj.setdefault(e["a"], []).append((e["b"], e))
            adj.setdefault(e["b"], []).append((e["a"], e))
    best, prev, heap = {src: 0}, {}, [(0, src)]
    while heap:
        c, n = heapq.heappop(heap)
        if n == dst:
            break
        if c > best.get(n, 1e18):
            continue
        for m, e in adj.get(n, []):
            nc = c + e["dist"] + CROWD_WEIGHT_M * e["crowd"]
            if nc < best.get(m, 1e18):
                best[m], prev[m] = nc, (n, e)
                heapq.heappush(heap, (nc, m))
    if dst not in best:
        return None
    path, edges = [dst], []
    while path[-1] != src:
        n, e = prev[path[-1]]
        edges.append(e)
        path.append(n)
    path.reverse()
    edges.reverse()
    crowds = [e["crowd"] for e in edges] or [0]
    return {"mode": modes_label(modes), "modes": modes, "path": path, "edges": edges, "dist": sum(e["dist"] for e in edges),
            "wait": sum(e["wait"] for e in edges), "avg_crowd": sum(crowds) / len(crowds), "max_crowd": max(crowds)}


def walk_speed(needs):
    return WALK_SPEED["wheelchair" if "wheelchair" in needs else "elderly" if "elderly" in needs else "default"]


def est_minutes(route, needs):
    return max(1, round((route["dist"] / walk_speed(needs) + route["wait"]) / 60))


def crowd_label(x):
    return "Low" if x <= 3.5 else "Moderate" if x <= 6 else "High"


def step_text(e, a, b):
    A, B = NODES[a], NODES[b]
    d = f"About {int(round(e['dist']))} metres."
    vert = "up" if B["level"] > A["level"] else "down"
    m = e["mode"]
    if m == "flat":
        return f"Continue straight towards {B['phrase']}. Follow the signs for {B['signs']}. {d}"
    if m == "travelator":
        return f"Step onto the travelator and ride towards {B['phrase']}. Follow the signs for {B['signs']}. {d}"
    if m == "stairs":
        return f"Take the stairs {vert} to {B['phrase']}. Hold the handrail. {d}"
    if m == "escalator":
        return f"Take the escalator {vert} to {B['phrase']}. Hold the handrail. {d}"
    if m == "lift":
        return f"Take the lift {vert} to {B['phrase']}. Press the button for that level. {d}"
    return f"Follow the ramp {vert} to {B['phrase']}. {d}"


def build_steps(route, ticket, needs, pre=None):
    p, steps = route["path"], list(pre or [])
    steps.append({"text": f"You are at {NODES[p[0]]['name']}. Station marker codes such as TS-P1 help confirm exactly "
                          f"where you are.", "node": p[0]})
    for i, e in enumerate(route["edges"]):
        steps.append({"text": step_text(e, p[i], p[i + 1]), "node": p[i + 1]})
    dst = p[-1]
    t = ticket or {}
    coach = (t.get("coach") or "").upper().replace(" ", "")
    if t.get("platform") == dst and coach:
        zone = next((z for z, (_, cl) in ZONES.items() if coach in cl), None)
        if zone:
            dist, cl = ZONES[zone]
            steps.append({"text": f"You are now on {NODES[dst]['phrase']}. Walk about {dist} metres along the platform "
                                  f"towards Zone {zone} (coaches {', '.join(cl)}). Look for the coach position display.", "node": dst})
        else:
            steps.append({"text": f"You are now on {NODES[dst]['phrase']}. Coach {coach} is not on our station map, "
                                  f"so please check the coach position display.", "node": dst})
        extra = " If you need a boarding ramp, please ask station staff on the platform." if "wheelchair" in needs else ""
        steps.append({"text": f"Stop at the marker for coach {coach}. Coach positions here are typical; if the train is "
                              f"formed differently, follow the coach position display or ask station staff.{extra}", "node": dst})
        if t.get("seat"):
            steps.append({"text": f"Board coach {coach} and look for seat {t['seat']}. A seat number alone cannot tell us exactly "
                                  f"where the seat is inside the coach, so follow the seat numbers shown in the coach.", "node": dst})
    else:
        steps.append({"text": f"You have arrived at {NODES[dst]['phrase']}.", "node": dst})
    return steps


# ----------------------------------------------------------------------------
# TICKET PARSING / SPOKEN NUMBERS
# ----------------------------------------------------------------------------
TICKET_FIELDS = [("train_no", "Train number"), ("train_name", "Train name"), ("date", "Journey date"),
                 ("from", "Boarding station"), ("to", "Destination station"), ("coach", "Coach"), ("seat", "Seat number")]
_ALIASES = {"train_no": ["trainno", "trainnumber", "tn", "trainnum"], "train_name": ["trainname", "name"],
            "date": ["date", "doj", "journeydate", "dateofjourney"],
            "from": ["from", "boarding", "boardingstation", "src", "source", "frm"],
            "to": ["to", "destination", "destinationstation", "dest", "dst"],
            "coach": ["coach", "coachno", "coachnumber"], "seat": ["seat", "seatno", "seatnumber", "berth"]}


def parse_ticket(text):
    """Reads ticket fields only. Any passenger name inside a ticket is deliberately ignored."""
    raw = {}
    try:
        obj = json.loads(text)
        if isinstance(obj, dict):
            raw = {re.sub(r"[^a-z0-9]", "", str(k).lower()): str(v) for k, v in obj.items()}
    except ValueError:
        pass
    if not raw:
        for part in re.split(r"[;\n|,]+", text):
            if ":" in part or "=" in part:
                k, v = re.split(r"[:=]", part, 1)
                raw[re.sub(r"[^a-z0-9]", "", k.lower())] = v.strip()
    out = {}
    for field, names in _ALIASES.items():
        for n in names:
            if n in raw and raw[n]:
                out[field] = raw[n]
                break
    if "train" in raw:
        m = re.match(r"(\d{4,5})\s*(.*)", raw["train"])
        if m:
            out.setdefault("train_no", m.group(1))
            if m.group(2):
                out.setdefault("train_name", m.group(2))
        else:
            out.setdefault("train_name", raw["train"])
    return out


_ONES = {"zero": 0, "oh": 0, "one": 1, "two": 2, "to": 2, "too": 2, "three": 3, "four": 4, "for": 4, "five": 5,
         "six": 6, "seven": 7, "eight": 8, "ate": 8, "nine": 9, "ten": 10, "eleven": 11, "twelve": 12, "thirteen": 13,
         "fourteen": 14, "fifteen": 15, "sixteen": 16, "seventeen": 17, "eighteen": 18, "nineteen": 19}
_TENS = {"twenty": 20, "thirty": 30, "forty": 40, "fifty": 50, "sixty": 60, "seventy": 70, "eighty": 80, "ninety": 90}
_LETTERS = {"s": "S", "es": "S", "ess": "S", "b": "B", "bee": "B", "be": "B", "a": "A", "ay": "A", "h": "H", "aitch": "H",
            "g": "G", "gee": "G", "slr": "SLR"}
DIGIT_GRAMMAR = list(_ONES) + list(_TENS) + ["hundred", "[unk]"]


def spoken_number(text):
    """'one two six three seven' -> '12637'; 'forty five' -> '45'; '45' -> '45'."""
    toks, out, i = re.findall(r"[a-z]+|\d+", (text or "").lower()), "", 0
    while i < len(toks):
        t = toks[i]
        if t.isdigit():
            out += t
        elif t in _TENS:
            v = _TENS[t]
            if i + 1 < len(toks) and toks[i + 1] in _ONES and 1 <= _ONES[toks[i + 1]] <= 9:
                v += _ONES[toks[i + 1]]
                i += 1
            out += str(v)
        elif t in _ONES:
            out += str(_ONES[t])
        i += 1
    return out


def spoken_coach(text):
    """'s five' -> 'S5'."""
    toks = re.findall(r"[a-z]+|\d+", (text or "").lower())
    letters = next((_LETTERS[t] for t in toks if t in _LETTERS), "")
    return letters + spoken_number(" ".join(t for t in toks if t not in _LETTERS))


def yes_no(text):
    w = set(re.findall(r"[a-z']+", (text or "").lower()))
    if w & NO_WORDS:
        return "no"
    if w & YES_WORDS:
        return "yes"
    return None


def match_menu(text):
    t = (text or "").lower()
    for key, _label, words in MENUS:
        if any(w in t for w in words):
            return key
    if any(x in t for x in ("home", "menu", "dashboard")):
        return "dashboard"
    return None


# ----------------------------------------------------------------------------
# LOCATION  (Python only; asked from the passenger first)
# ----------------------------------------------------------------------------
def haversine(a, b):
    r = 6371000.0
    p1, p2 = math.radians(a[0]), math.radians(b[0])
    dp, dl = p2 - p1, math.radians(b[1] - a[1])
    h = math.sin(dp / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2
    return 2 * r * math.asin(min(1, math.sqrt(h)))


def bearing(a, b):
    p1, p2, dl = math.radians(a[0]), math.radians(b[0]), math.radians(b[1] - a[1])
    y = math.sin(dl) * math.cos(p2)
    x = math.cos(p1) * math.sin(p2) - math.sin(p1) * math.cos(p2) * math.cos(dl)
    return (math.degrees(math.atan2(y, x)) + 360) % 360


_COMPASS = ["north", "north-east", "east", "south-east", "south", "south-west", "west", "north-west"]


def compass(deg):
    return _COMPASS[int((deg + 22.5) // 45) % 8]


def to_xy(ll, origin):
    """Metres east / north of origin."""
    return ((ll[1] - origin[1]) * 111320.0 * math.cos(math.radians(origin[0])), (ll[0] - origin[0]) * 110540.0)


def fmt_dist(m):
    return f"{m / 1000:.1f} kilometres" if m >= 1500 else f"{int(round(m, -1)) if m >= 100 else int(m)} metres"


def _num(x, default):
    try:
        v = float(x)
        return default if math.isnan(v) else v
    except (TypeError, ValueError):
        return default


def _fix_gpsd(timeout=4.0):
    """A GPS receiver served by gpsd (works on any OS where gpsd runs)."""
    try:
        s = socket.create_connection(("127.0.0.1", 2947), timeout=1.5)
    except OSError:
        return None
    try:
        s.settimeout(1.0)
        s.sendall(b'?WATCH={"enable":true,"json":true}\n')
        end, buf = time.time() + timeout, b""
        while time.time() < end:
            try:
                chunk = s.recv(4096)
            except socket.timeout:
                continue
            if not chunk:
                break
            buf += chunk
            lines = buf.split(b"\n")
            buf = lines[-1]
            for ln in lines[:-1]:
                try:
                    o = json.loads(ln)
                except ValueError:
                    continue
                if o.get("class") == "TPV" and o.get("mode", 0) >= 2 and "lat" in o and "lon" in o:
                    return dict(lat=o["lat"], lon=o["lon"], acc=_num(o.get("eph") or o.get("epx"), 15.0), source="GPS receiver")
    except OSError:
        pass
    finally:
        s.close()
    return None


def _fix_windows():
    """Windows location service (Windows asks the user to allow location for this app)."""
    ps = ("Add-Type -AssemblyName System.Device;"
          "$w=New-Object System.Device.Location.GeoCoordinateWatcher([System.Device.Location.GeoPositionAccuracy]::High);"
          "[void]$w.TryStart($false,[TimeSpan]::FromSeconds(8));"
          "$l=$w.Position.Location; if($l.IsUnknown){exit 3};"
          "$c=[Globalization.CultureInfo]::InvariantCulture;"
          "Write-Output ($l.Latitude.ToString($c)+','+$l.Longitude.ToString($c)+','+$l.HorizontalAccuracy.ToString($c))")
    exe = shutil.which("powershell")
    if not exe:
        return None
    r = subprocess.run([exe, "-NoProfile", "-NonInteractive", "-Command", ps], capture_output=True, text=True,
                       timeout=25, creationflags=0x08000000)
    parts = (r.stdout or "").strip().split(",")
    if r.returncode != 0 or len(parts) < 2:
        return None
    return dict(lat=float(parts[0]), lon=float(parts[1]), acc=_num(parts[2] if len(parts) > 2 else None, 50.0),
                source="Windows location service")


def _fix_geoclue():
    """Linux GeoClue (the 'where-am-i' client that ships with geoclue)."""
    exe = shutil.which("where-am-i")
    for p in ("/usr/libexec/geoclue-2.0/demos/where-am-i", "/usr/lib/geoclue-2.0/demos/where-am-i"):
        if not exe and os.path.exists(p):
            exe = p
    if not exe:
        return None
    r = subprocess.run([exe, "-t", "8"], capture_output=True, text=True, timeout=20)
    m1 = re.search(r"Latitude:\s*(-?[\d.]+)", r.stdout or "")
    m2 = re.search(r"Longitude:\s*(-?[\d.]+)", r.stdout or "")
    m3 = re.search(r"Accuracy:\s*([\d.]+)", r.stdout or "")
    if not (m1 and m2):
        return None
    return dict(lat=float(m1.group(1)), lon=float(m2.group(1)), acc=_num(m3.group(1) if m3 else None, 100.0),
                source="Linux location service")


def _fix_ip():
    """Approximate, city-level position from the internet address (sends the IP to a lookup service)."""
    if not ALLOW_IP_LOCATION:
        return None
    for url in ("http://ip-api.com/json/?fields=status,lat,lon", "https://ipapi.co/json/"):
        try:
            with urllib.request.urlopen(urllib.request.Request(url, headers={"User-Agent": "TrackSync2"}), timeout=6) as r:
                o = json.loads(r.read().decode("utf-8"))
            lat, lon = o.get("lat", o.get("latitude")), o.get("lon", o.get("longitude"))
            if lat is not None and lon is not None and o.get("status", "success") == "success":
                return dict(lat=float(lat), lon=float(lon), acc=5000.0, source="approximate (internet address)")
        except Exception:
            continue
    return None


class LocationService:
    """Asks the operating system / GPS for the passenger's position every few seconds while the passenger
    has allowed it. Positions are kept ONLY in memory and forgotten at stop()."""
    def __init__(self):
        self.on = False
        self.gen = 0
        self.lock = threading.Lock()
        self.wake = threading.Event()
        self.latest = None
        self.trail = deque(maxlen=40)
        self.err = ""
        self.manual_node = None      # "I am at ..." chosen by the passenger
        self.nav_point = None        # name of the current navigation step (used in alerts)
        self.pref = None             # source function that worked last time

    def sources(self):
        native = _fix_windows if sys.platform.startswith("win") else _fix_geoclue if sys.platform.startswith("linux") else None
        order = [_fix_gpsd] + ([native] if native else []) + [_fix_ip]
        if self.pref in order:
            order.remove(self.pref)
            order.insert(0, self.pref)
        return order

    def get_fix(self):
        for fn in self.sources():
            try:
                f = fn()
            except Exception:
                f = None
            if f and -90 <= f["lat"] <= 90 and -180 <= f["lon"] <= 180:
                self.pref = fn
                return f
        return None

    def start(self):
        if self.on:
            return
        self.on, self.err = True, ""
        self.gen += 1
        self.wake.clear()
        threading.Thread(target=self._run, args=(self.gen,), daemon=True).start()

    def stop(self):
        self.on = False
        self.gen += 1
        self.wake.set()
        with self.lock:
            self.latest = None
            self.trail.clear()
        self.manual_node = self.nav_point = None
        self.err = ""

    def poke(self):
        self.wake.set()

    def _run(self, gen):
        while self.on and gen == self.gen:
            f = self.get_fix()
            if self.on and gen == self.gen:
                if f:
                    f["t"] = time.time()
                    with self.lock:
                        self.latest = f
                        self.trail.append(f)
                    self.err = ""
                else:
                    self.err = ("No location source answered. Check that location is allowed for this computer, "
                                "or tell the app where you are.")
            self.wake.wait(LOCATION_INTERVAL_S)
            self.wake.clear()

    # ---- derived values ---------------------------------------------------
    def dist_to_station(self, f=None):
        f = f or self.latest
        return haversine((f["lat"], f["lon"]), STATION["ll"]) if f else None

    def motion(self):
        """(speed m/s or None, heading degrees or None, 'closer'/'further'/None) from the recent trail."""
        with self.lock:
            pts = [p for p in self.trail if p["acc"] <= 100][-5:]
        if len(pts) < 2:
            return None, None, None
        a, b = pts[0], pts[-1]
        dt = b["t"] - a["t"]
        d = haversine((a["lat"], a["lon"]), (b["lat"], b["lon"]))
        if dt < 8 or d < max(10.0, a["acc"] / 2):
            return 0.0, None, None
        da, db = self.dist_to_station(a), self.dist_to_station(b)
        trend = "closer" if db < da - 10 else "further" if db > da + 10 else None
        return d / dt, bearing((a["lat"], a["lon"]), (b["lat"], b["lon"])), trend

    def describe(self):
        f = self.latest
        if f:
            return (f"{f['lat']:.5f}, {f['lon']:.5f} (accuracy about {int(f['acc'])} m, {f['source']}), "
                    f"{int(self.dist_to_station(f))} m from the station entrance")
        if self.manual_node:
            return f"passenger said they are at {NODES[self.manual_node]['name']}"
        if self.nav_point:
            return f"navigation step near {self.nav_point}"
        return "not known (location not shared)"


LOC = LocationService()


def snap_node(fix):
    x, y = to_xy((fix["lat"], fix["lon"]), STATION["ll"])
    node, (nx, ny) = min(NODE_XY.items(), key=lambda kv: math.hypot(kv[1][0] - x, kv[1][1] - y))
    return node, math.hypot(nx - x, ny - y)


def predict_way(ticket, needs, mode=None):
    """Predict the passenger's way to the platform from the tracked position.
    Returns dict(lines, start, route, pre, outside)."""
    res = {"lines": [], "start": None, "route": None, "pre": [], "outside": False}
    mode = mode or default_mode(needs)
    sp = walk_speed(needs)
    f = LOC.latest
    plat = (ticket or {}).get("platform")
    if f is None and LOC.manual_node:
        res["start"] = LOC.manual_node
        res["lines"].append(f"You told us you are at {NODES[LOC.manual_node]['name']}.")
    elif f is None:
        res["lines"].append("Your position is not known yet. " + (LOC.err or
                            ("Location tracking is on - waiting for the first position." if LOC.on else
                             "Turn on location, or tell us where you are.")))
        return res
    else:
        d = LOC.dist_to_station(f)
        coarse = f["acc"] > 1500
        if d > STATION_RADIUS_M:
            res["outside"] = True
            b = bearing((f["lat"], f["lon"]), STATION["ll"])
            mins = max(1, round(d / sp / 60))
            _spd, _hd, trend = LOC.motion()
            res["lines"].append(f"You are about {fmt_dist(d)} from the station entrance. Head {compass(b)}; "
                                f"walking takes about {mins} minutes.")
            if trend:
                res["lines"].append("You are getting closer to the station." if trend == "closer"
                                    else "You are moving away from the station.")
            if coarse:
                res["lines"].append(f"Caution: this position is approximate (about {fmt_dist(f['acc'])}, from your internet "
                                    "address), so the distance and direction may be wrong.")
            res["pre"] = [{"text": f"Walk about {fmt_dist(d)} {compass(b)} to the station entrance, the subway entrance on "
                                   f"the street side. About {mins} minutes.", "node": "ENTRY"}]
            res["start"] = "ENTRY"
        else:
            node, off = snap_node(f)
            if f["acc"] > 80 or off > 150:
                node = "ENTRY"
                res["lines"].append("You are at the station, but the position is too rough inside the building to say exactly "
                                    "where. We will start from the entrance; confirm a marker code for an exact position.")
            else:
                res["lines"].append(f"You are near {NODES[node]['name']} (position accuracy about {int(f['acc'])} metres).")
            res["start"] = node
    start = res["start"]
    if not plat or plat not in NODES:
        res["lines"].append("Scan your ticket so we can predict your way to your platform.")
        return res
    if start == plat:
        res["lines"].append(f"You are already at {NODES[plat]['name']}.")
        return res
    r = find_route(start, plat, mode)
    if r is None:
        res["lines"].append(f"No {modes_label(mode).lower()} route to {NODES[plat]['name']} is available right now. "
                            "Please ask station staff or choose another travel type in the Route Planner.")
        return res
    res["route"] = r
    mins = est_minutes(r, needs)
    res["lines"].append(f"Predicted way ({modes_label(mode).lower()}): " + ", then ".join(NODES[n]["name"] for n in r["path"])
                        + f". About {int(r['dist'])} metres inside the station, about {mins} minutes.")
    return res



# ----------------------------------------------------------------------------
# SPEECH OUTPUT / INPUT
# ----------------------------------------------------------------------------
class Speaker:
    """Offline English speech via the operating system voice, run as a separate process so it can
    always be stopped (pause) and never freezes the window. done() is called on the UI thread when
    the speech has finished (or immediately if no voice is available)."""
    def __init__(self):
        self.proc, self.gen, self.kind, self.exe = None, 0, None, None
        if sys.platform.startswith("win"):
            self.exe = shutil.which("powershell") or shutil.which("pwsh")
            self.kind = "win" if self.exe else None
        elif sys.platform == "darwin":
            self.kind = "mac" if shutil.which("say") else None
        else:
            for exe in ("espeak-ng", "espeak", "spd-say"):
                if shutil.which(exe):
                    self.kind, self.exe = exe, exe
                    break
        if self.kind is None:
            try:
                import pyttsx3  # noqa: F401
                self.kind = "pyttsx3"
            except ImportError:
                pass
        self.available = self.kind is not None

    def _cmd(self, text):
        env, flags = os.environ.copy(), 0
        if self.kind == "win":
            env["TS_TEXT"] = text
            script = ("Add-Type -AssemblyName System.Speech;$s=New-Object System.Speech.Synthesis.SpeechSynthesizer;"
                      "$s.Rate=-1;$s.Speak($env:TS_TEXT)")
            return [self.exe, "-NoProfile", "-NonInteractive", "-Command", script], env, 0x08000000
        if self.kind == "mac":
            return ["say", "-r", "165", text], env, flags
        if self.kind == "spd-say":
            return ["spd-say", "-w", text], env, flags
        if self.kind in ("espeak", "espeak-ng"):
            return [self.exe, "-s", "150", text], env, flags
        return [sys.executable, "-c", "import pyttsx3,sys;e=pyttsx3.init();e.setProperty('rate',150);e.say(sys.argv[1]);e.runAndWait()",
                text], env, flags

    def say(self, text, done=None):
        self.stop()
        text = re.sub(r"\s+", " ", (text or "").replace(">", ",").replace("|", " ").replace("\n", ". ")).strip()
        if not (self.available and text):
            if done:
                call_ui(done)
            return
        self.gen += 1
        gen = self.gen
        try:
            args, env, flags = self._cmd(text)
            proc = subprocess.Popen(args, env=env, stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
                                    stderr=subprocess.DEVNULL, creationflags=flags)
        except Exception:
            self.proc = None
            if done:
                call_ui(done)
            return
        self.proc = proc

        def waiter():
            proc.wait()
            if gen == self.gen and done:
                call_ui(done)
        threading.Thread(target=waiter, daemon=True).start()

    def stop(self):
        self.gen += 1
        p, self.proc = self.proc, None
        try:
            if p is not None and p.poll() is None:
                p.terminate()
        except Exception:
            pass


SPEAKER = Speaker()


class Listener:
    """Speech input, tried in this order:
      1. Vosk            - offline; needs  pip install vosk sounddevice  + the model folder next to this file
      2. sounddevice + SpeechRecognition (Google, needs internet) - used when the Vosk model is missing
      3. SpeechRecognition + pyaudio (pocketsphinx offline, else Google)
    MICROPHONE: the default microphone is tried first. A microphone that stays completely silent for 1.5 s is dropped and
    the next input device is tried (the working one is remembered).  Set TRACKSYNC_MIC=<device number> to force one.
    After every attempt  .info  says which microphone was used and how loud it was, and  .hint  explains a failure."""
    HELP = ("Speech input is not set up yet. Press 'Set up speech input' (internet needed once), or run:  "
            "pip install vosk sounddevice  and unzip the model " + VOSK_MODEL_NAME + " next to ots2.py.")
    SILENT_RMS = 4.0          # below this level a microphone is treated as silent / muted
    QUIET_RMS = 60.0          # below this the sound is too weak to recognise

    def __init__(self):
        self.gen, self.lock, self.model, self.model_dir, self.engine = 0, threading.Lock(), None, None, None
        self.dev, self.bad, self.peak, self.info, self.hint = None, set(), 0.0, "no recording yet", ""
        self.available = self.check()

    @staticmethod
    def find_model():
        for d in VOSK_MODEL_DIRS:
            path = os.path.join(APP_DIR, d)
            if os.path.isdir(path):
                return path
        try:                                    # any vosk-model-* folder, also when it was unzipped into a sub-folder
            for name in sorted(os.listdir(APP_DIR)):
                p = os.path.join(APP_DIR, name)
                if os.path.isdir(p) and name.lower().startswith("vosk-model"):
                    if os.path.isdir(os.path.join(p, "am")):
                        return p
                    for sub in sorted(os.listdir(p)):
                        q = os.path.join(p, sub)
                        if os.path.isdir(os.path.join(q, "am")):
                            return q
        except OSError:
            pass
        return None

    def check(self):
        self.engine = None
        try:
            import sounddevice, vosk  # noqa: F401
            mp = self.find_model()
            if mp:
                if mp != self.model_dir:
                    self.model = None
                self.model_dir, self.engine = mp, "vosk"
                return True
        except Exception:
            pass
        try:
            import sounddevice, speech_recognition  # noqa: F401
            self.engine = "sdsr"
            return True
        except Exception:
            pass
        try:
            import speech_recognition, pyaudio  # noqa: F401
            self.engine = "sr"
            return True
        except Exception:
            return False

    def cancel(self):
        self.gen += 1

    def install(self, progress, done):
        """pip-install the speech packages and download the Indian English Vosk model (runs on a thread)."""
        def pip(*pkgs):
            return subprocess.run([sys.executable, "-m", "pip", "install", *pkgs], capture_output=True, text=True)

        def run():
            err = ""
            try:
                offline_ok = False
                call_ui(progress, "Installing speech packages (vosk, sounddevice) ...")
                r = pip("vosk", "sounddevice")
                if r.returncode == 0:
                    importlib.invalidate_caches()
                    try:
                        if not os.path.isdir(os.path.join(APP_DIR, VOSK_MODEL_NAME)):
                            call_ui(progress, "Downloading the Indian English speech model (about 40 MB) ...")
                            zpath = os.path.join(APP_DIR, VOSK_MODEL_NAME + ".zip")
                            urllib.request.urlretrieve(VOSK_MODEL_URL, zpath)
                            call_ui(progress, "Unpacking the speech model ...")
                            with zipfile.ZipFile(zpath) as z:
                                z.extractall(APP_DIR)
                            os.remove(zpath)
                        offline_ok = True
                    except Exception as exc:
                        err = str(exc)
                        offline_ok = bool(self.find_model())          # an older model folder is still usable
                if not offline_ok:
                    call_ui(progress, "Offline speech engine not ready - installing the online speech engine instead ...")
                    r2 = pip("SpeechRecognition", "sounddevice")
                    if r2.returncode != 0:
                        raise RuntimeError((r2.stderr or r.stderr or err or "pip install failed")[-300:])
                    importlib.invalidate_caches()
                    err = ""
            except Exception as exc:
                err = str(exc)
            self.model = None
            ok = self.check()
            call_ui(done, ok, err)
        threading.Thread(target=run, daemon=True).start()

    def listen(self, done, grammar=None, seconds=7):
        """Record up to `seconds`; calls done(text, error) on the UI thread (not called if cancelled)."""
        if not self.available:
            call_ui(done, "", "Speech input is not set up.")
            return
        self.gen += 1
        gen = self.gen

        def run():
            text, err = "", ""
            with self.lock:
                if gen != self.gen:
                    return
                self.peak, self.hint = 0.0, ""
                try:
                    if self.engine == "vosk":
                        text = self._vosk(gen, grammar, seconds)
                    elif self.engine == "sdsr":
                        text = self._sdsr(gen, seconds)
                    else:
                        text = self._sr(gen, seconds)
                except Exception as exc:
                    err = "The microphone could not be used (" + (str(exc)[:80] or "unknown problem") + ")."
                text = (text or "").replace("[unk]", "").strip()
                if not text and not err and self.engine in ("vosk", "sdsr"):
                    if self.peak < self.QUIET_RMS:
                        self.hint = ("The microphone picked up almost no sound. Make sure it is not muted, speak close to it, "
                                     "and in Windows Settings > Privacy > Microphone allow desktop apps. Press 'Test microphone' to check.")
                    else:
                        self.hint = ("The microphone works, but the words were not understood. Speak slowly and clearly, "
                                     "or press 'Set up / update speech input' to get the Indian English model.")
            if gen == self.gen:
                call_ui(done, text, err)
        threading.Thread(target=run, daemon=True).start()

    # ---- microphone handling ------------------------------------------------------------------
    @staticmethod
    def _rms(data):
        a = array.array("h", data)
        return math.sqrt(sum(x * x for x in a) / len(a)) if len(a) else 0.0

    @staticmethod
    def _to16k(data, rate):
        if rate == 16000:
            return data
        a = array.array("h", data)
        n = len(a) * 16000 // rate
        if rate % 16000 == 0:
            k = rate // 16000
            out = array.array("h", (sum(a[i * k:(i + 1) * k]) // k for i in range(n)))
        else:
            out = array.array("h", (a[min(len(a) - 1, j * rate // 16000)] for j in range(n)))
        return out.tobytes()

    def _devices(self, sd):
        order = []
        pick = os.environ.get("TRACKSYNC_MIC", "").strip()
        if pick.isdigit():
            order.append(int(pick))
        if self.dev is not None:
            order.append(self.dev)
        order.append(None)                                  # the system default microphone
        try:
            order += [i for i, d in enumerate(sd.query_devices()) if d.get("max_input_channels", 0) > 0]
        except Exception:
            pass
        uniq = []
        for d in order:
            if d not in uniq:
                uniq.append(d)
        good = [d for d in uniq if d not in self.bad]
        if not good:
            self.bad.clear()
            good = uniq
        return good

    @staticmethod
    def _dev_name(sd, dev):
        try:
            return str(sd.query_devices(dev, "input")["name"])[:40]
        except Exception:
            return "device " + str(dev)

    @staticmethod
    def _open(sd, dev, cb):
        try:
            s = sd.RawInputStream(samplerate=16000, blocksize=4000, dtype="int16", channels=1, callback=cb, device=dev)
            s.start()
            return s, 16000
        except Exception as first:
            try:                                            # some devices only run at their own rate (e.g. 44100 / 48000)
                rate = int(sd.query_devices(dev, "input")["default_samplerate"])
                s = sd.RawInputStream(samplerate=rate, blocksize=max(1, rate // 4), dtype="int16", channels=1, callback=cb, device=dev)
                s.start()
                return s, rate
            except Exception:
                raise first

    def _capture(self, gen, seconds, on_block):
        """Feed 16 kHz mono blocks to on_block(bytes) until it returns True or the time is up."""
        import sounddevice as sd
        end, last_err, opened = time.time() + seconds, None, False
        for dev in self._devices(sd):
            if time.time() >= end or gen != self.gen:
                break
            q = queue.Queue()

            def cb(indata, frames, t, status, q=q):
                q.put(bytes(indata))
            try:
                stream, rate = self._open(sd, dev, cb)
            except Exception as exc:
                last_err = exc
                self.bad.add(dev)
                continue
            opened = True
            t0, peak, stop = time.time(), 0.0, False
            try:
                while time.time() < end and gen == self.gen:
                    try:
                        data = q.get(timeout=0.5)
                    except queue.Empty:
                        if time.time() - t0 > 1.5 and peak < self.SILENT_RMS:
                            break
                        continue
                    data = self._to16k(data, rate)
                    peak = max(peak, self._rms(data))
                    if on_block(data):
                        stop = True
                        break
                    if peak < self.SILENT_RMS and time.time() - t0 > 1.5:
                        break                                # dead / muted device: try the next one
            finally:
                try:
                    stream.stop()
                    stream.close()
                except Exception:
                    pass
            self.peak = max(self.peak, peak)
            self.info = f"microphone: {self._dev_name(sd, dev)}, level {int(peak)}"
            if stop or peak >= self.SILENT_RMS:
                self.dev = dev
                self.bad.discard(dev)
                return
            self.bad.add(dev)
        if not opened:
            raise last_err or RuntimeError("no microphone found")

    # ---- engines -------------------------------------------------------------------------------
    def _vosk(self, gen, grammar, seconds):
        import vosk
        if self.model is None:
            vosk.SetLogLevel(-1)
            self.model = vosk.Model(self.model_dir)
        rec = vosk.KaldiRecognizer(self.model, 16000, json.dumps(grammar)) if grammar else vosk.KaldiRecognizer(self.model, 16000)
        st = {"text": ""}

        def on_block(data):
            if rec.AcceptWaveform(data):
                t = json.loads(rec.Result()).get("text", "").replace("[unk]", "").strip()
                if t:
                    st["text"] = t
                    return True
            return False
        self._capture(gen, seconds, on_block)
        if not st["text"]:
            st["text"] = json.loads(rec.FinalResult()).get("text", "")
        return st["text"]

    def _sdsr(self, gen, seconds):
        """Record (stops after a short silence), then recognise with SpeechRecognition - needs internet."""
        import speech_recognition as sr
        chunks, st = [], {"started": False, "quiet": 0, "noise": None}

        def on_block(data):
            r = self._rms(data)
            if st["noise"] is None:
                st["noise"] = r
            if r > max(150.0, st["noise"] * 2.5):
                st["started"], st["quiet"] = True, 0
            elif st["started"]:
                st["quiet"] += 1
            if st["started"]:
                chunks.append(data)
            return st["started"] and st["quiet"] >= 5          # about 1.2 s of silence after speaking
        self._capture(gen, seconds, on_block)
        if not chunks or gen != self.gen:
            return ""
        try:
            return sr.Recognizer().recognize_google(sr.AudioData(b"".join(chunks), 16000, 2), language="en-IN").lower()
        except sr.UnknownValueError:
            return ""
        except sr.RequestError:
            raise RuntimeError("online speech service not reachable")

    def _sr(self, gen, seconds):
        import speech_recognition as sr
        r = sr.Recognizer()
        with sr.Microphone() as src:
            r.adjust_for_ambient_noise(src, 0.4)
            if gen != self.gen:
                return ""
            try:
                audio = r.listen(src, timeout=5, phrase_time_limit=seconds)
            except sr.WaitTimeoutError:
                return ""
        try:
            return r.recognize_sphinx(audio).lower()
        except Exception:
            pass
        try:
            return r.recognize_google(audio).lower()
        except Exception:
            return ""


LISTENER = Listener()


# ----------------------------------------------------------------------------
# UI HELPERS (same as ots.py)
# ----------------------------------------------------------------------------
class Btn(tk.Label):
    """Large, keyboard-focusable button."""
    def __init__(self, master, text, command, bg=None, fg=WHITE, size=14, pady=10, **kw):
        bg = bg or TEAL
        super().__init__(master, text=text, bg=bg, fg=fg, font=F(size, True), padx=16, pady=pady, cursor="hand2",
                         takefocus=1, highlightthickness=3, highlightbackground=bg, highlightcolor=YELLOW, **kw)
        self._cmd = command
        for ev in ("<Button-1>", "<Return>", "<space>"):
            self.bind(ev, self._go)

    def _go(self, _e=None):
        self._cmd()


def lbl(parent, text, size=14, bold=False, fg=NAVY, bg=BG, wrap=1000, **kw):
    w = tk.Label(parent, text=text, font=F(size, bold), fg=fg, bg=bg, wraplength=wrap, justify="left", anchor="w", **kw)
    w.pack(anchor="w", pady=2)
    return w



YN_GRAMMAR = ["yes", "no", "yeah", "yep", "okay", "ok", "sure", "allow", "skip", "not", "now", "later", "continue",
              "correct", "right", "cancel", "never", "please", "[unk]"]


# ----------------------------------------------------------------------------
# APPLICATION
# ----------------------------------------------------------------------------
class App:
    def __init__(self):
        self.root = tk.Tk()
        self.root.title("TrackSync")
        self.root.geometry("1100x800")
        self.root.minsize(900, 650)
        self.root.configure(bg=BG)
        self.root.option_add("*TCombobox*Listbox.font", (FONT, 14))
        st = ttk.Style()
        st.configure("Treeview", rowheight=30, font=(FONT, 12))
        st.configure("Treeview.Heading", font=(FONT, 12, "bold"))
        self.user = None
        self.route, self.steps, self.step_i, self.pre = None, [], 0, []
        self.nav_paused = False
        self.refresh_cb = None
        self.last_notif = 0
        self.prompt_win = self.prompt_id = self.sos_win = None
        self.current = "login"
        self.flow = 0                     # changes on every page change; stale voice callbacks check it
        self.voice_out = True
        self.cap = self.cv2 = self.qr = self.cam_label = None
        self.seen_fix, self.geo_inside = None, None
        self.menu_tries = 0
        self.menu_intro = ""
        self.mob_event = ""
        self.lift_msg = ""
        self._vt_fail = 0
        self.ask_until = 0.0              # while a spoken question is open, routine notifications wait
        self.build_shell()
        self.show("login")
        self.root.after(100, self.pump)
        self.root.after(1000, self.tick)
        self.root.protocol("WM_DELETE_WINDOW", self.quit)

    # ---- shell ---------------------------------------------------------------
    def build_shell(self):
        self.header = tk.Frame(self.root, bg=NAVY)
        self.header.pack(fill="x")
        tk.Label(self.header, text="TrackSync", font=(FONT, 24, "bold"), fg=WHITE, bg=NAVY, padx=16, pady=8).pack(side="left")
        self.hbtns = tk.Frame(self.header, bg=NAVY)
        self.hbtns.pack(side="right", padx=8)
        self.voice_btn = Btn(self.header, "Voice: ON", self.toggle_voice, bg=GREY, size=12)
        self.voice_btn.pack(side="right", padx=4, pady=6)
        self.banner = tk.Label(self.root, text="Welcome to TrackSync.", bg=TEAL, fg=WHITE, font=(FONT, 14, "bold"),
                               anchor="w", justify="left", padx=14, pady=8, wraplength=1050)
        self.banner.pack(side="bottom", fill="x")
        self.body = tk.Frame(self.root, bg=BG, padx=24, pady=14)
        self.body.pack(fill="both", expand=True)

    def banner_say(self, text, urgent=False):
        self.banner.config(text=text, bg=RED if urgent else TEAL)

    def voice_on(self):
        return self.voice_out and not (self.user and "deaf" in needs_of(self.user))

    def speak(self, text, done=None):
        if self.voice_on():
            SPEAKER.say(text, done)
        elif done:
            done()

    def toggle_voice(self):
        self.voice_out = not self.voice_out
        self.voice_btn.config(text="Voice: ON" if self.voice_out else "Voice: OFF")
        if not self.voice_out:
            SPEAKER.stop()
        self.banner_say("Spoken answers are " + ("ON." if self.voice_out else "OFF. Everything is shown as text."))

    def pump(self):
        while True:
            try:
                fn, args = UIQ.get_nowait()
            except queue.Empty:
                break
            try:
                fn(*args)
            except Exception:
                log_error()
        self.root.after(100, self.pump)

    def show(self, name, **kw):
        self.flow += 1
        self.refresh_cb = None
        SPEAKER.stop()
        LISTENER.cancel()
        self.ask_until = 0.0
        self.stop_cam()
        for w in self.body.winfo_children():
            w.destroy()
        self.current = name
        getattr(self, "page_" + name)(**kw)

    def title(self, text, back=True):
        row = tk.Frame(self.body, bg=BG)
        row.pack(fill="x", pady=(0, 8))
        if back:
            Btn(row, "< Dashboard", lambda: self.show("dashboard"), bg=NAVY, size=12).pack(side="left", padx=(0, 16))
        tk.Label(row, text=text, font=F(24, True), fg=NAVY, bg=BG).pack(side="left")

    def reload_user(self):
        self.user = qone("SELECT * FROM users WHERE id=?", (self.user["id"],))

    def apply_scale(self):
        global SCALE
        n = needs_of(self.user) if self.user else set()
        SCALE = 1.3 if ({"elderly", "blind"} & n) else 1.0

    # ---- speech helpers ----------------------------------------------------------
    def ask(self, question, handler, grammar=None, seconds=7, retry=1):
        """Show the question as text, speak it (unless voice is off), then listen for the answer.
        handler(text) is called with the words heard. If speech input is unavailable the text stays on screen
        and the passenger uses the buttons / typing instead."""
        flow = self.flow
        self.banner_say(question)
        self.ask_until = time.time() + 35

        def heard(text, err):
            if flow != self.flow:
                return
            self.ask_until = 0.0
            if err:
                return self.banner_say(err + " Please use the buttons or type instead.", True)
            text = (text or "").lower().strip()
            if any(w in text for w in ("sos", "emergency", "help me")) and self.user:
                return self.send_sos()
            if not text:
                if retry > 0:
                    return self.ask("Sorry, I did not hear anything. " + question, handler, grammar, seconds, retry - 1)
                return self.banner_say("I did not hear anything. " + LISTENER.hint + " (" + LISTENER.info + ")  "
                                       "Please use the buttons or type instead.", True)
            self.banner_say(f'You said: "{text}"')
            handler(text)

        def go():
            if flow != self.flow:
                return
            if not LISTENER.available:
                self.ask_until = 0.0
                return self.banner_say(question + "    [Speech input is not set up - please use the buttons or type.]")
            self.banner_say("Listening... speak now.    " + question)
            LISTENER.listen(heard, grammar, seconds)
        self.speak(question, go)

    def ask_yes_no(self, question, on_yes, on_no=None, tries=2):
        def h(text):
            yn = yes_no(text)
            if yn == "yes":
                return on_yes()
            if yn == "no":
                return on_no() if on_no else self.banner_say("Okay.")
            if tries > 1:
                return self.ask_yes_no("Sorry, please say yes or no. " + question, on_yes, on_no, tries - 1)
            self.banner_say("Please use the buttons.")
        self.ask(question, h, YN_GRAMMAR, 6)

    # ---- session -------------------------------------------------------------
    def start_session(self, user):
        self.user = user
        self.apply_scale()
        m = qone("SELECT MAX(id) m FROM notifs WHERE user_id=?", (user["id"],))
        self.last_notif = m["m"] or 0
        self.seen_fix, self.geo_inside = None, None
        for w in self.hbtns.winfo_children():
            w.destroy()
        Btn(self.hbtns, "Home", lambda: self.show("dashboard"), bg=GREY, size=12).pack(side="left", padx=4, pady=6)
        Btn(self.hbtns, "Voice command", self.voice_command, bg=GREY, size=12).pack(side="left", padx=4, pady=6)
        Btn(self.hbtns, "Log out", self.logout, bg=GREY, size=12).pack(side="left", padx=4, pady=6)
        Btn(self.hbtns, "SOS", self.send_sos, bg=RED, size=16).pack(side="left", padx=(12, 4), pady=6)
        self.show("locask")

    def logout(self):
        if self.user:
            a = qone("SELECT id FROM alerts WHERE user_id=? AND status IN ('open','acknowledged')", (self.user["id"],))
            if a and not messagebox.askyesno("Log out", "You have an alert that station staff have not closed yet. "
                                             "Logging out deletes it. Log out anyway?"):
                return
        self.end_session("You have logged out. Your name, ticket and location were deleted.")

    def end_session(self, msg):
        SPEAKER.stop()
        LISTENER.cancel()
        self.stop_cam()
        self.close_prompt()
        if self.sos_win and self.sos_win.winfo_exists():
            self.sos_win.destroy()
        if self.user:
            purge_passengers(self.user["id"])
        LOC.stop()
        self.user = None
        self.route, self.steps, self.pre = None, [], []
        for w in self.hbtns.winfo_children():
            w.destroy()
        clear_lift_status()
        self.lift_msg = ""
        self.apply_scale()
        self.banner_say(msg)
        self.show("login")

    def quit(self):
        SPEAKER.stop()
        LISTENER.cancel()
        self.stop_cam()
        try:
            if self.user:
                purge_passengers(self.user["id"])
        except Exception:
            log_error()
        LOC.stop()
        self.root.destroy()

    # ---- background polling (notifications, prompts, location) ---------------------
    def tick(self):
        try:
            if self.user:
                self.poll()
            if self.refresh_cb:
                self.refresh_cb()
        except Exception:
            log_error()
        self.root.after(1500, self.tick)

    def poll(self):
        u = self.user
        for n in qall("SELECT * FROM notices WHERE id>? ORDER BY id", (u["last_notice"],)):
            notify(u["id"], n["text"], n["kind"], n["kind"] in ("lift", "platform"))
            u["last_notice"] = n["id"]
            ex("UPDATE users SET last_notice=? WHERE id=?", (n["id"], u["id"]))
        new = qall("SELECT * FROM notifs WHERE user_id=? AND id>? ORDER BY id", (u["id"], self.last_notif))
        urgent = any(n["urgent"] for n in new)
        if new and (urgent or time.time() >= self.ask_until):      # routine notices wait until a spoken question is answered
            self.last_notif = new[-1]["id"]
            self.banner_say(new[-1]["text"], bool(new[-1]["urgent"]))
            if not (self.current == "mobility" and all(n["kind"] == "vehicle" for n in new)):
                self.speak(" ".join(n["text"] for n in new))
        c = qone("SELECT * FROM checkins WHERE user_id=? AND status='prompt' ORDER BY id DESC LIMIT 1", (u["id"],))
        if c and c["deadline"] > time.time():
            if self.prompt_id != c["id"]:
                self.open_prompt(c)
        elif self.prompt_win:
            self.close_prompt()
        self.watch_location()

    def watch_location(self):
        f = LOC.latest
        if not f or f is self.seen_fix:
            return
        self.seen_fix = f
        uid, d = self.user["id"], LOC.dist_to_station(f)
        inside = d <= STATION_RADIUS_M * (1.3 if self.geo_inside else 1.0)
        if self.geo_inside is None:
            p = predict_way(get_ticket(uid), needs_of(self.user))
            notify(uid, "Location found. " + " ".join(p["lines"][:2]), "route")
        elif inside and not self.geo_inside:
            notify(uid, "You have reached the station area. Please confirm a marker code for your exact position.", "route")
        elif self.geo_inside and not inside:
            notify(uid, "You have left the station area.", "route")
        self.geo_inside = inside

    # ---- check-in prompt (can be answered by voice) ----------------------------------
    def open_prompt(self, c):
        self.close_prompt()
        self.prompt_id = c["id"]
        w = self.prompt_win = tk.Toplevel(self.root)
        w.title("Are you okay?")
        w.configure(bg=NAVY, padx=30, pady=24)
        w.attributes("-topmost", True)
        tk.Label(w, text="Are you okay?", font=(FONT, 40, "bold"), fg=WHITE, bg=NAVY).pack()
        cd = tk.Label(w, text="", font=(FONT, 18), fg=YELLOW, bg=NAVY)
        cd.pack(pady=8)
        Btn(w, "I'm okay", lambda: self.answer_prompt(c["id"], "ok"), size=24, pady=18).pack(fill="x", pady=8)
        Btn(w, "I need help", lambda: self.answer_prompt(c["id"], "help"), bg=RED, size=24, pady=18).pack(fill="x", pady=8)

        def upd():
            if not w.winfo_exists():
                return
            left = int(c["deadline"] - time.time())
            cd.config(text=f"Please answer within {max(left, 0)} seconds")
            w.after(500, upd)
        upd()
        self.banner_say("Are you okay? Please answer the check-in.", True)
        self.speak("Are you okay? Please say: I'm okay, or I need help.", lambda: self.prompt_listen(c["id"]))

    def prompt_listen(self, cid):
        if self.prompt_id != cid or not self.prompt_win or not LISTENER.available:
            return
        LISTENER.listen(lambda t, e: self.prompt_heard(cid, t), ["okay", "ok", "i", "am", "i'm", "fine", "yes", "need", "help",
                                                                  "no", "[unk]"], 8)

    def prompt_heard(self, cid, text):
        if self.prompt_id != cid or not self.prompt_win:
            return
        t = (text or "").lower()
        if "help" in t or "need" in t or yes_no(t) == "no":
            self.answer_prompt(cid, "help")
        elif "ok" in t or "fine" in t or yes_no(t) == "yes":
            self.answer_prompt(cid, "ok")
        else:
            self.prompt_listen(cid)

    def close_prompt(self):
        if self.prompt_win and self.prompt_win.winfo_exists():
            self.prompt_win.destroy()
        self.prompt_win = None

    def answer_prompt(self, cid, ans):
        c = qone("SELECT * FROM checkins WHERE id=?", (cid,))
        s = qone("SELECT * FROM sched WHERE user_id=?", (self.user["id"],))
        if c and c["status"] == "prompt":
            if ans == "ok":
                ex("UPDATE checkins SET status='ok' WHERE id=?", (cid,))
                notify(self.user["id"], "Thank you. Your check-in was recorded: you are okay.", "safety")
            else:
                aid = create_alert(self.user["id"], "help", "Passenger asked for help during a welfare check-in.")
                ex("UPDATE checkins SET status='help', alert_id=? WHERE id=?", (aid, cid))
                notify(self.user["id"], "You asked for help. An alert was created for station staff.", "safety", True)
            if s and s["state"] == "running":
                ex("UPDATE sched SET next_due=? WHERE user_id=?", (time.time() + s["interval_min"] * 60, self.user["id"]))
        self.close_prompt()

    # ---- SOS -------------------------------------------------------------------
    def send_sos(self):
        if not self.user:
            return
        a = qone("SELECT id FROM alerts WHERE user_id=? AND kind='sos' AND status IN ('open','acknowledged') ORDER BY id DESC LIMIT 1",
                 (self.user["id"],))
        aid = a["id"] if a else create_alert(self.user["id"], "sos", "SOS: passenger needs urgent assistance.")
        self.open_sos_window(aid)

    def open_sos_window(self, aid):
        if self.sos_win and self.sos_win.winfo_exists():
            self.sos_win.destroy()
        w = self.sos_win = tk.Toplevel(self.root)
        w.title("SOS")
        w.configure(bg=WHITE, padx=30, pady=24)
        w.attributes("-topmost", True)
        tk.Label(w, text="SOS", font=(FONT, 44, "bold"), fg=RED, bg=WHITE).pack()
        st = tk.Label(w, text="", font=(FONT, 18, "bold"), fg=NAVY, bg=WHITE, wraplength=700, justify="left")
        st.pack(pady=8)
        tk.Label(w, text="This app alerts station staff only. It does not contact emergency services. "
                         "If life is in danger, call 112 (Railway helpline: 139). Your last known position is included in the alert.",
                 font=(FONT, 13), fg=NAVY, bg=WHITE, wraplength=700, justify="left").pack(pady=6)

        def cancel():
            ex("UPDATE alerts SET status='cancelled' WHERE id=? AND status='open'", (aid,))
            notify(self.user["id"], "Your alert was cancelled.", "safety")
            refresh()

        cbtn = Btn(w, "Cancel alert (pressed by mistake)", cancel, bg=GREY, size=14)
        cbtn.pack(fill="x", pady=6)
        Btn(w, "Close window", w.destroy, bg=NAVY, size=14).pack(fill="x", pady=6)

        def refresh():
            if not w.winfo_exists() or not self.user:
                return
            a = qone("SELECT * FROM alerts WHERE id=?", (aid,))
            if not a:
                return
            st.config(text=f"Alert at {hhmm(a['created'])}: {alert_status_text(a)}")
            if a["status"] != "open":
                cbtn.pack_forget()
            w.after(1500, refresh)
        refresh()

    # ---- voice commands ---------------------------------------------------------
    def voice_command(self):
        if not self.user:
            return
        if not LISTENER.available:
            return self.type_command(LISTENER.HELP)
        self.banner_say("Listening... say a menu or a command, for example: route planner, next, repeat, my location, sos.")

        def heard(text, err):
            if err or not text:
                return self.type_command(err or "I did not hear anything.")
            self.banner_say(f'You said: "{text}"')
            self.run_command(text.lower())
        LISTENER.listen(heard, None, 6)

    def type_command(self, prefix=""):
        text = simpledialog.askstring("Command", f"{prefix}\n\nType a command, for example: next, repeat, pause, route, "
                                      "navigation, location, mobility, energy, sos, home", parent=self.root)
        if text:
            self.run_command(text.lower())

    def run_command(self, t):
        if not self.user:
            return
        has = lambda *w: any(x in t for x in w)
        if has("sos", "emergency", "help me"):
            return self.send_sos()
        if has("okay", "i'm ok", "i am ok") and self.prompt_win:
            return self.answer_prompt(self.prompt_id, "ok")
        if has("log out", "logout", "sign out"):
            return self.logout()
        if self.current == "nav":
            if has("next"):
                return self.nav_move(1)
            if has("back", "previous"):
                return self.nav_move(-1)
            if has("repeat", "again"):
                return self.nav_repeat()
            if has("pause", "stop"):
                return self.nav_pause()
        k = match_menu(t)
        if k:
            return self.show("dashboard" if k == "dashboard" else k)
        self.banner_say("Sorry, I did not understand that command.")

    # ---- pages: login (speech is available right here) ---------------------------------------
    def page_login(self):
        page = self.scroll_body()                 # scrollable, so every button stays reachable on small screens
        card = tk.Frame(page, bg=WHITE, padx=40, pady=22, highlightbackground=TEAL, highlightthickness=3)
        card.pack(pady=16)
        tk.Label(card, text="Welcome to TrackSync", font=(FONT, 26, "bold"), fg=NAVY, bg=WHITE).pack()
        tk.Label(card, text="Accessible, personalised help at the railway station", font=(FONT, 14), fg=NAVY, bg=WHITE).pack(pady=(0, 10))
        tk.Label(card, text="Please tell us your name - speak it or type it.", font=(FONT, 17, "bold"), fg=TEAL, bg=WHITE,
                 wraplength=640).pack(pady=(0, 8))
        tk.Label(card, text="Your name", font=(FONT, 14, "bold"), fg=NAVY, bg=WHITE, anchor="w").pack(fill="x")
        self.name_var = tk.StringVar()
        e1 = tk.Entry(card, textvariable=self.name_var, font=(FONT, 18), width=28)
        e1.pack(pady=4)
        e1.bind("<Return>", lambda e: self.do_login())

        def ubtn(parent, text, cmd, bg):          # every login button has exactly the same size, font and padding
            return Btn(parent, text, cmd, bg=bg, size=14, pady=8, width=30)
        row1 = tk.Frame(card, bg=WHITE)
        row1.pack(pady=(14, 4))
        ubtn(row1, "Speak my name", self.login_voice, NAVY).grid(row=0, column=0, padx=8)
        ubtn(row1, "Continue", self.do_login, TEAL).grid(row=0, column=1, padx=8)
        tk.Label(card, text="Only your name is asked. It is kept for this visit only and deleted when you log out.",
                 font=(FONT, 12), fg=GREY, bg=WHITE, wraplength=640).pack(pady=(8, 0))
        if not LISTENER.available:
            tk.Label(card, text="Speech input is not set up on this computer yet.", font=(FONT, 12, "bold"), fg=RED, bg=WHITE).pack(pady=(10, 2))
        row2 = tk.Frame(card, bg=WHITE)
        row2.pack(pady=(10, 4))
        ubtn(row2, "Test microphone", self.mic_test, GREY).grid(row=0, column=0, padx=8)
        ubtn(row2, "Set up / update speech input", self.setup_speech, GREY).grid(row=0, column=1, padx=8)
        row3 = tk.Frame(card, bg=WHITE)
        row3.pack(pady=(4, 0))
        ubtn(row3, "Driver / staff sign-in", self.do_staff, GREY).grid(row=0, column=0)
        e1.focus_set()
        self.root.after(700, self.login_voice)

    def login_voice(self):
        if self.current != "login":
            return
        self.ask("Welcome to TrackSync. Please say your name.", self._login_heard, None, 6)

    def _login_heard(self, text):
        name = extract_name(text)
        if not name:
            return self.ask("Sorry, I could not get a name. Please say your name again, or type it.", self._login_heard, None, 6, 0)
        self.name_var.set(name)
        self.ask(f"I heard {name}. Say yes to continue, or say your name again.", self._login_confirm, None, 6)

    def _login_confirm(self, text):
        yn = yes_no(text)
        if yn == "yes":
            return self.do_login()
        if yn == "no":
            return self.ask("Okay. Please say your name again.", self._login_heard, None, 6)
        self._login_heard(text)          # a new name was spoken instead of yes / no

    def do_login(self):
        name = clean_name(self.name_var.get())
        if len(name) < 2:
            self.banner_say("Please say or type your name (at least 2 letters).", True)
            return self.speak("Please say or type your name.")
        self.start_session(new_passenger(name))

    def do_staff(self):
        n = simpledialog.askstring("Driver / staff sign-in", "Staff name:", parent=self.root)
        if not n:
            return
        p = simpledialog.askstring("Driver / staff sign-in", "Password:", show="*", parent=self.root)
        u = staff_login(n, p or "", ("driver", "staff"))
        if u:
            self.open_console(u)
        else:
            messagebox.showwarning("Driver / staff sign-in", "Name or password is not correct.")

    def mic_test(self):
        if not LISTENER.available:
            return self.banner_say(LISTENER.HELP, True)
        self.banner_say("Microphone test: say 'hello TrackSync' now ... (5 seconds)")

        def heard(text, err):
            if err:
                return self.banner_say(err, True)
            if text:
                return self.banner_say(f'Microphone works. I heard: "{text}"   ({LISTENER.info})')
            self.banner_say("I heard nothing. " + LISTENER.hint + "  (" + LISTENER.info + ")", True)
        LISTENER.listen(heard, None, 5)

    def setup_speech(self):
        if not messagebox.askyesno("Set up speech input", "This installs 'vosk' and 'sounddevice' with pip and downloads the "
                                   "Indian English speech model (about 40 MB). Internet is needed once. Continue?"):
            return
        self.banner_say("Setting up speech input ... please wait.")
        LISTENER.install(self.banner_say, self.setup_done)

    def setup_done(self, ok, err):
        if ok:
            self.banner_say("Speech input is ready.")
            if self.current == "login":
                self.show("login")
        else:
            self.banner_say("Speech setup did not finish.", True)
            messagebox.showwarning("Set up speech input", (err or "Setup did not finish.") +
                                   "\n\nOn Linux you may also need:  sudo apt install libportaudio2")

    # ---- pages: location permission -------------------------------------------------------------
    def page_locask(self):
        u = self.user
        card = tk.Frame(self.body, bg=WHITE, padx=40, pady=24, highlightbackground=TEAL, highlightthickness=3)
        card.pack(pady=20)
        tk.Label(card, text=f"Welcome, {u['name']}", font=F(26, True), fg=NAVY, bg=WHITE).pack()
        tk.Label(card, text="May TrackSync use your location?", font=F(20, True), fg=TEAL, bg=WHITE).pack(pady=(8, 6))
        tk.Label(card, text="It lets the app track your progress and predict your way to the station and your platform. "
                            "Your position stays on this computer, is never saved to disk and is forgotten when you log out. "
                            "It is shared with station staff only if you press SOS or miss a safety check-in. "
                            "If no GPS is available, an approximate position from your internet address may be used.",
                 font=F(14), fg=NAVY, bg=WHITE, wraplength=720, justify="left").pack(pady=6)
        Btn(card, "Allow location", self.loc_allow, size=18, pady=14).pack(fill="x", pady=(14, 6))
        Btn(card, "Not now", self.loc_skip, bg=GREY, size=16).pack(fill="x", pady=4)
        self.ask_yes_no(f"Welcome, {u['name']}. May TrackSync use your location to track your progress and predict your way "
                        "to the station? Say yes or no.", self.loc_allow, self.loc_skip)

    def loc_allow(self):
        LOC.start()
        notify(self.user["id"], "Location is on. Finding your position now.", "route")
        self.show("scan")

    def loc_skip(self):
        notify(self.user["id"], "Location is off. You can turn it on later from My Location and Way.", "route")
        self.show("scan")

    # ---- pages: dashboard (asks which menu) -------------------------------------------------------
    def scroll_body(self):
        """A scrollable area (scroll bar + mouse wheel) so nothing at the bottom of the page is ever hidden."""
        wrap = tk.Frame(self.body, bg=BG)
        wrap.pack(fill="both", expand=True)
        canvas = tk.Canvas(wrap, bg=BG, highlightthickness=0)
        bar = ttk.Scrollbar(wrap, orient="vertical", command=canvas.yview)
        canvas.configure(yscrollcommand=bar.set)
        bar.pack(side="right", fill="y")
        canvas.pack(side="left", fill="both", expand=True)
        inner = tk.Frame(canvas, bg=BG)
        item = canvas.create_window((0, 0), window=inner, anchor="nw")
        inner.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.bind("<Configure>", lambda e: canvas.itemconfigure(item, width=e.width))

        def wheel(e):
            try:
                if not canvas.winfo_exists():
                    return
                step = -1 if (getattr(e, "num", 0) == 4 or getattr(e, "delta", 0) > 0) else 1
                canvas.yview_scroll(step * 2, "units")
            except tk.TclError:
                pass
        for seq in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
            self.root.bind_all(seq, wheel)
        return inner

    def page_dashboard(self, ask_menu=False, intro=""):
        u = self.user
        b = self.scroll_body()
        self.menu_intro = intro
        lbl(b, f"Hello, {u['name']}", 26, True)
        t = get_ticket(u["id"])
        card = tk.Frame(b, bg=WHITE, padx=16, pady=10, highlightbackground=TEAL, highlightthickness=2)
        card.pack(fill="x", pady=6)
        if t:
            plat = NODES[t["platform"]]["name"] if t.get("platform") in NODES else "platform not set"
            txt = (f"Your journey: Train {t.get('train_no', '')} {t.get('train_name', '')}  |  {t.get('date', '')}\n"
                   f"{t.get('from', '?')} to {t.get('to', '?')}  |  Coach {t.get('coach', '?')}, Seat {t.get('seat', '?')}  |  {plat}")
        else:
            txt = "No ticket added yet. Choose Scan Ticket to begin."
        tk.Label(card, text=txt, font=F(14, True), fg=NAVY, bg=WHITE, justify="left", anchor="w").pack(fill="x")
        s = qone("SELECT * FROM sched WHERE user_id=?", (u["id"],))
        info = ("Voice answers + text" if self.voice_on() else "Text only") + "   |   Location tracking: " + ("ON" if LOC.on else "OFF")
        if s and s["state"] == "running":
            info += f"   |   Safety check-ins ON (every {s['interval_min']:g} min)"
        lbl(b, info, 13, True)
        if self.lift_msg:
            lbl(b, self.lift_msg, 14, True, fg="#1B7F3B" if not LIFT_OUT else RED, wrap=1000)
        row = tk.Frame(b, bg=BG)
        row.pack(fill="x", pady=4)
        Btn(row, "Speak your menu choice", self.menu_voice, bg=NAVY, size=15).pack(side="left", padx=(0, 12))
        tk.Label(row, text="or type:", font=F(14), fg=NAVY, bg=BG).pack(side="left")
        self.menu_var = tk.StringVar()
        en = tk.Entry(row, textvariable=self.menu_var, font=F(15), width=22)
        en.pack(side="left", padx=6)
        en.bind("<Return>", lambda e: self.menu_typed())
        Btn(row, "Go", self.menu_typed, size=13, pady=4).pack(side="left")
        grid = tk.Frame(b, bg=BG)
        grid.pack(fill="both", expand=True, pady=6)
        for i, (key, label, _w) in enumerate(MENUS):
            last_odd = (i == len(MENUS) - 1 and len(MENUS) % 2 == 1)
            Btn(grid, label, lambda k=key: self.show(k), size=17, pady=14).grid(
                row=i // 2, column=i % 2, columnspan=2 if last_odd else 1, sticky="nsew", padx=8, pady=6)
        grid.columnconfigure((0, 1), weight=1)
        self.menu_tries = 0
        if ask_menu:
            self.root.after(300, self.menu_voice)

    def menu_voice(self):
        if self.current != "dashboard":
            return
        q = (self.menu_intro + " " if self.menu_intro else "") + MENU_QUESTION
        self.menu_intro = ""
        self.ask(q, self._menu_heard, MENU_GRAMMAR, 6)

    def _menu_heard(self, text):
        k = match_menu(text)
        if "log out" in text or "logout" in text:
            return self.logout()
        if k:
            names = {m[0]: m[1] for m in MENUS}
            self.banner_say(f"Opening {names.get(k, 'the dashboard')}.")
            return self.show("dashboard" if k == "dashboard" else k)
        self.menu_tries += 1
        if self.menu_tries < 2:
            return self.ask("Sorry, I did not catch a menu name. " + MENU_QUESTION, self._menu_heard, MENU_GRAMMAR, 6)
        self.banner_say("I could not match a menu. Please tap a menu button, or type your choice.")

    def menu_typed(self):
        k = match_menu(self.menu_var.get())
        if k:
            self.show("dashboard" if k == "dashboard" else k)
        else:
            self.banner_say("That menu name was not recognised. Try: route, navigation, location, energy, mobility, check-ins.", True)

    # ---- pages: scan ticket (camera inside the window; speech or typing also work) ----------------------
    def page_scan(self):
        self.title("Scan your ticket")
        b = self.body
        old = get_ticket(self.user["id"]) or {}
        self.tv = {k: tk.StringVar(value=old.get(k, "")) for k, _ in TICKET_FIELDS}
        self.tv["platform"] = tk.StringVar(value=NODES[old["platform"]]["name"] if old.get("platform") in NODES else "")
        row = tk.Frame(b, bg=BG)
        row.pack(anchor="w", pady=6)
        Btn(row, "Scan Ticket (camera)", lambda: self.start_cam(False), size=14).pack(side="left", padx=(0, 8))
        Btn(row, "Speak ticket details", self.voice_ticket, bg=NAVY, size=14).pack(side="left", padx=(0, 8))
        lbl(b, "Hold the ticket QR code in front of the camera. No camera? Speak or type the details instead.", 13)
        mid = tk.Frame(b, bg=BG)
        mid.pack(fill="x")
        form = tk.Frame(mid, bg=BG)
        form.pack(side="left", anchor="n")
        for i, (k, label) in enumerate(TICKET_FIELDS):
            tk.Label(form, text=label, font=F(14, True), fg=NAVY, bg=BG, anchor="w", width=18).grid(row=i, column=0, pady=3, sticky="w")
            tk.Entry(form, textvariable=self.tv[k], font=F(14), width=26).grid(row=i, column=1, pady=3)
        n = len(TICKET_FIELDS)
        tk.Label(form, text="Platform for your train", font=F(14, True), fg=NAVY, bg=BG, anchor="w", width=18).grid(row=n, column=0, sticky="w")
        ttk.Combobox(form, textvariable=self.tv["platform"], values=[NODES[k]["name"] for k in PLATFORM_KEYS], font=(FONT, 14),
                     width=24, state="readonly").grid(row=n, column=1, pady=3)
        cam = tk.Frame(mid, bg=BG)
        cam.pack(side="left", padx=24, anchor="n")
        self.cam_label = tk.Label(cam, text="Camera preview", width=44, height=15, bg=NAVY, fg=WHITE, font=F(12))
        self.cam_label.pack()
        bar = tk.Frame(b, bg=BG)
        bar.pack(anchor="w", pady=10)
        Btn(bar, "Save ticket", self.save_ticket_form, size=16).pack(side="left", padx=(0, 10))
        Btn(bar, "Skip - go to menu", lambda: self.show("dashboard", ask_menu=True), bg=GREY, size=14).pack(side="left")
        self.start_cam(True)
        self.ask("Next, please scan your train ticket. Hold the QR code in front of the camera. "
                 "Or say details to speak it, or say skip.", self._scan_heard,
                 ["details", "speak", "say", "type", "skip", "later", "menu", "[unk]"], 6, 0)

    def _scan_heard(self, text):
        if any(w in text for w in ("detail", "speak", "say")):
            return self.voice_ticket()
        if any(w in text for w in ("skip", "later", "menu")):
            return self.show("dashboard", ask_menu=True)
        self.banner_say("Hold the QR code in front of the camera, or type the details and press Save ticket.")

    def start_cam(self, auto=False):
        if self.cap is not None or self.current != "scan":
            return
        try:
            import cv2
        except ImportError:
            if auto:
                return
            if messagebox.askyesno("Camera", "Camera scanning needs 'opencv-python'. Install it now? (internet needed once)"):
                self.install_cv()
            return
        cap = cv2.VideoCapture(0)
        if not cap.isOpened():
            cap.release()
            if not auto:
                messagebox.showinfo("Camera", "No camera could be opened. Please speak or type the ticket details instead.")
            return
        self.cap, self.cv2, self.qr, self.cam_end = cap, cv2, cv2.QRCodeDetector(), time.time() + 60
        self.cam_step()

    def install_cv(self):
        self.banner_say("Installing camera support (opencv-python) ... please wait.")

        def run():
            r = subprocess.run([sys.executable, "-m", "pip", "install", "opencv-python"], capture_output=True, text=True)
            importlib.invalidate_caches()
            call_ui(self.cv_done, r.returncode == 0, (r.stderr or "")[-300:])
        threading.Thread(target=run, daemon=True).start()

    def cv_done(self, ok, err):
        if ok:
            self.banner_say("Camera support installed. Press Scan Ticket (camera).")
        else:
            self.banner_say("Camera support could not be installed. Please speak or type the ticket.", True)

    def cam_step(self):
        if self.cap is None:
            return
        try:
            ok, frame = self.cap.read()
            if ok:
                try:
                    data, _, _ = self.qr.detectAndDecode(frame)
                except Exception:
                    data = ""
                if data:
                    self.stop_cam()
                    return self.handle_qr(data)
                w = 360
                small = self.cv2.resize(frame, (w, max(1, int(frame.shape[0] * w / frame.shape[1]))))
                okp, png = self.cv2.imencode(".png", small)
                if okp and self.cam_label is not None and self.cam_label.winfo_exists():
                    img = tk.PhotoImage(data=base64.b64encode(png.tobytes()).decode("ascii"))
                    self.cam_img = img
                    self.cam_label.config(image=img, text="", width=0, height=0)
            if time.time() > self.cam_end:
                self.stop_cam()
                return self.banner_say("The camera stopped after one minute. Press Scan Ticket (camera) to try again.")
            self.root.after(80, self.cam_step)
        except Exception:
            log_error()
            self.stop_cam()

    def stop_cam(self):
        cap, self.cap = self.cap, None
        if cap is not None:
            try:
                cap.release()
            except Exception:
                pass
        try:
            if self.cam_label is not None and self.cam_label.winfo_exists():
                self.cam_label.config(image="", text="Camera preview", width=44, height=15)
        except Exception:
            pass

    def handle_qr(self, text):
        data = parse_ticket(text)
        if not data:
            self.banner_say("The code was read but no ticket details were found. Please type them in.", True)
            return self.speak("The code was read, but I found no ticket details. Please type them in.")
        self.fill_ticket(data)
        self.confirm_ticket()

    def fill_ticket(self, data):
        for k, v in data.items():
            if k in self.tv:
                self.tv[k].set(v)
        tr = TRAINS.get(self.tv["train_no"].get().strip())
        if tr:
            if not self.tv["train_name"].get():
                self.tv["train_name"].set(tr["name"])
            if not self.tv["platform"].get():
                self.tv["platform"].set(NODES[tr["platform"]]["name"])

    def ticket_summary(self):
        d = {k: self.tv[k].get().strip() for k, _ in TICKET_FIELDS}
        parts = ["Train " + " ".join(x for x in (d["train_no"], d["train_name"]) if x)]
        if d["coach"]:
            parts.append("coach " + d["coach"])
        if d["seat"]:
            parts.append("seat " + d["seat"])
        if self.tv["platform"].get():
            parts.append(self.tv["platform"].get())
        return ", ".join(parts) + "."

    def confirm_ticket(self):
        self.ask_yes_no("Ticket read. " + self.ticket_summary() + " Say yes to save it, or no to change it.", self.save_ticket_form,
                        lambda: self.banner_say("Please correct the details and press Save ticket."))

    def voice_ticket(self):
        self._vt_fail = 0
        self.ask("Please say your train number, digit by digit.", self._vt_train, DIGIT_GRAMMAR, 8)

    def _vt_train(self, text):
        n = spoken_number(text)
        if len(n) < 4:
            self._vt_fail += 1
            if self._vt_fail >= 3:
                return self.banner_say("I could not understand the train number. Please type it in the form.", True)
            return self.ask("Sorry, please say the train number again, digit by digit.", self._vt_train, DIGIT_GRAMMAR, 8)
        self.fill_ticket({"train_no": n})
        tr = TRAINS.get(n)
        self.ask(f"Train {n}{' ' + tr['name'] if tr else ''}. Now say your coach, for example S 5.", self._vt_coach, None, 7)

    def _vt_coach(self, text):
        c = spoken_coach(text)
        if c:
            self.tv["coach"].set(c)
        self.ask("Now say your seat number.", self._vt_seat, DIGIT_GRAMMAR, 7)

    def _vt_seat(self, text):
        s = spoken_number(text)
        if s:
            self.tv["seat"].set(s)
        self.confirm_ticket()

    def save_ticket_form(self):
        if self.current != "scan":
            return
        d = {k: self.tv[k].get().strip() for k, _ in TICKET_FIELDS}
        if not (d["train_no"] or d["train_name"]):
            self.banner_say("Please enter at least the train number or name.", True)
            return self.speak("Please enter at least the train number or name.")
        pname = self.tv["platform"].get()
        d["platform"] = next((k for k in PLATFORM_KEYS if NODES[k]["name"] == pname), "")
        save_ticket(self.user["id"], d)
        uid = self.user["id"]
        notify(uid, f"Ticket saved for train {d['train_no']} {d['train_name']}, coach {d['coach']}, seat {d['seat']}.", "info")
        self.lift_msg = refresh_lift_status()          # picked from LIFT_STATUS_DATA: sometimes all lifts are fine
        notify(uid, self.lift_msg, "lift" if LIFT_OUT else "info", bool(LIFT_OUT))
        self.last_notif = qone("SELECT MAX(id) m FROM notifs WHERE user_id=?", (uid,))["m"] or self.last_notif
        self.show("dashboard", ask_menu=True, intro="Ticket saved. " + self.lift_msg)

    # ---- pages: preferences ----------------------------------------------------------------
    def page_prefs(self):
        self.title("Accessibility preferences")
        b, u = self.body, self.user
        lbl(b, "Optional. Choose any that apply - kept only for this visit. You can change these at any time.", 14)
        cur = needs_of(u)
        self.pv = {k: tk.BooleanVar(value=k in cur) for k in NEED_LABELS}

        def toggled(k):
            if self.pv[k].get():
                for o in self.pv:
                    if (k == "none") != (o == "none") and o != k:
                        self.pv[o].set(False)
        for k, text in NEED_LABELS.items():
            tk.Checkbutton(b, text=text, variable=self.pv[k], command=lambda k=k: toggled(k), font=F(17, True), fg=NAVY, bg=BG,
                           activebackground=BG, selectcolor=WHITE, anchor="w").pack(anchor="w", pady=4)
        row = tk.Frame(b, bg=BG)
        row.pack(anchor="w", pady=14)
        Btn(row, "Answer by voice", self.prefs_voice, bg=NAVY, size=15).pack(side="left", padx=(0, 10))
        Btn(row, "Save preferences", self.save_prefs, size=16).pack(side="left")

    def prefs_voice(self):
        self.ask("Which assistance do you need? Say deaf, blind, wheelchair, elderly, or none.", self._prefs_heard,
                 ["deaf", "hard", "of", "hearing", "blind", "low", "vision", "wheelchair", "step", "free", "elderly", "older",
                  "senior", "mobility", "none", "no", "and", "assistance", "[unk]"], 7)

    def _prefs_heard(self, text):
        words = {"deaf": "deaf", "hearing": "deaf", "blind": "blind", "vision": "blind", "wheelchair": "wheelchair",
                 "step": "wheelchair", "elderly": "elderly", "older": "elderly", "senior": "elderly", "mobility": "elderly"}
        chosen = {v for k, v in words.items() if k in text}
        if not chosen and ("none" in text or re.search(r"\bno\b", text)):
            chosen = {"none"}
        if not chosen:
            return self.ask("Sorry, I did not catch that. Say deaf, blind, wheelchair, elderly, or none.", self._prefs_heard, None, 7, 0)
        for k, v in self.pv.items():
            v.set(k in chosen)
        names = ", ".join(NEED_LABELS[k] for k in NEED_LABELS if k in chosen)
        self.ask_yes_no(f"I selected: {names}. Say yes to save.", self.save_prefs, lambda: self.banner_say("Not saved. Change the boxes and press Save."))

    def save_prefs(self):
        if self.current != "prefs":
            return
        chosen = [k for k, v in self.pv.items() if v.get()]
        ex("UPDATE users SET needs=? WHERE id=?", (",".join(chosen), self.user["id"]))
        self.reload_user()
        self.apply_scale()
        mode = "spoken answers and text" if self.voice_on() else "text only"
        notify(self.user["id"], f"Preferences saved. Answers will use {mode}.", "info")
        self.show("dashboard", ask_menu=True)


    # ---- pages: route planner -----------------------------------------------------------------
    def current_point(self):
        """The station point the passenger is at, if known from location (snapped) or told by them."""
        f = LOC.latest
        if f and LOC.dist_to_station(f) <= STATION_RADIUS_M and f["acc"] <= 80:
            return snap_node(f)[0]
        return LOC.manual_node

    def page_route(self):
        self.title("Route planner")
        b, u = self.body, self.user
        nd, t = needs_of(u), get_ticket(self.user["id"]) or {}
        names = [NODES[k]["name"] for k in POINT_CHOICES]
        self.v_src = tk.StringVar(value=NODES[self.current_point() or "ENTRY"]["name"])
        self.v_dst = tk.StringVar(value=NODES[t["platform"]]["name"] if t.get("platform") in NODES else NODES["P1"]["name"])
        row = tk.Frame(b, bg=BG)
        row.pack(anchor="w", pady=4)
        tk.Label(row, text="Start", font=F(14, True), bg=BG, fg=NAVY).grid(row=0, column=0, padx=6)
        ttk.Combobox(row, textvariable=self.v_src, values=names, font=(FONT, 14), width=30, state="readonly").grid(row=0, column=1)
        Btn(row, "Use my location", self.route_use_location, bg=NAVY, size=12, pady=4).grid(row=0, column=2, padx=10)
        tk.Label(row, text="Destination platform", font=F(14, True), bg=BG, fg=NAVY).grid(row=1, column=0, padx=6, pady=6)
        ttk.Combobox(row, textvariable=self.v_dst, values=[NODES[k]["name"] for k in PLATFORM_KEYS], font=(FONT, 14), width=30,
                     state="readonly").grid(row=1, column=1)
        lbl(b, "Travel options - tick one or more:", 14, True)
        dm = default_mode(nd)
        self.v_modes = {k: tk.BooleanVar(value=(k == dm)) for k in ("stairs", "escalator", "lift", "stepfree")}
        mrow = tk.Frame(b, bg=BG)
        mrow.pack(anchor="w", pady=4)
        for key, label in (("stairs", "Stairs"), ("escalator", "Escalators"), ("lift", "Lifts"), ("stepfree", "Step-free")):
            tk.Checkbutton(mrow, text=label, variable=self.v_modes[key], font=F(15, True), bg=BG, fg=NAVY, activebackground=BG,
                           selectcolor=WHITE, state="disabled" if ("wheelchair" in nd and key != "stepfree") else "normal"
                           ).pack(side="left", padx=10)
        if "wheelchair" in nd:
            lbl(b, "Step-free access is set for you. Stairs and escalators will never be suggested.", 13)
        bar = tk.Frame(b, bg=BG)
        bar.pack(anchor="w", pady=6)
        Btn(bar, "Find least crowded route", self.plan, size=15).pack(side="left", padx=(0, 10))
        self.start_btn = Btn(bar, "Start navigation", self.begin_nav, bg=NAVY, size=15)
        self.out = tk.Text(b, height=12, font=F(14), wrap="word", bg=WHITE, fg=NAVY, relief="solid", bd=2)
        self.out.pack(fill="both", expand=True, pady=6)
        self.set_out("Choose where you are, where you are going and how you want to travel.")

    def route_use_location(self):
        p = predict_way(get_ticket(self.user["id"]) or {}, needs_of(self.user))
        if p["start"]:
            self.v_src.set(NODES[p["start"]]["name"])
        self.banner_say(" ".join(p["lines"][:2]))
        self.speak(" ".join(p["lines"][:2]))

    def set_out(self, text):
        self.out.config(state="normal")
        self.out.delete("1.0", "end")
        self.out.insert("end", text)
        self.out.config(state="disabled")

    def plan(self):
        u, nd = self.user, needs_of(self.user)
        src = next(k for k in POINT_CHOICES if NODES[k]["name"] == self.v_src.get())
        dst = next(k for k in PLATFORM_KEYS if NODES[k]["name"] == self.v_dst.get())
        mode = ["stepfree"] if "wheelchair" in nd else [k for k in ALT_ORDER if self.v_modes[k].get()]
        if not mode:
            self.banner_say("Please tick at least one travel option.", True)
            return self.speak("Please tick at least one travel option.")
        self.start_btn.pack_forget()
        self.pre = []
        if src == dst:
            self.set_out("You are already at your destination platform.")
            return
        r = find_route(src, dst, mode)
        note = ""
        outages = [e for e in EDGES if not edge_ok(e) and e["mode"] in allowed_edge_modes(mode) and {e["a"], e["b"]} & {src, dst}]
        for e in outages:
            note += f"Notice: {e['name']} is out of service.\n"
            notify(u["id"], f"Lift unavailable: {e['name']} is out of service.", "lift")
        if r is None:
            msg = f"There is no {modes_label(mode).lower()} route from {NODES[src]['name']} to {NODES[dst]['name']} right now. {note}"
            if "wheelchair" in nd:
                self.set_out(msg + "\nWe will not suggest stairs or escalators. Please ask station staff for help, "
                                   "or request a mobility vehicle from the dashboard.")
                notify(u["id"], "No verified step-free route is available. Please ask station staff or request a mobility vehicle.", "route", True)
                return
            if not messagebox.askyesno("Route not available", msg + "\nWould you like me to look for a different type of route?"):
                self.set_out(msg + "\nYour chosen travel type was kept. You can pick another type and try again.")
                return
            for alt in ALT_ORDER:
                if alt not in mode:
                    r = find_route(src, dst, alt)
                    if r:
                        note += f"Changed to {MODE_NAMES[alt].lower()} travel with your permission.\n"
                        break
            if r is None:
                self.set_out(msg + "\nNo other route is available. Please ask station staff for help.")
                return
        mins = est_minutes(r, nd)
        names = " > ".join(NODES[n]["name"] for n in r["path"])
        text = (f"{r['mode']} route\n{names}\n\nDistance: about {int(r['dist'])} metres\n"
                f"Estimated time: about {mins} min (from distance and typical walking speed)\n"
                f"Crowding on this route: {crowd_label(r['avg_crowd'])}\n\n{note}")
        if r["max_crowd"] >= 7:
            text += "Crowding warning: part of this route is busy. Take care.\n"
            notify(u["id"], "Crowding warning: part of your route is busy. Please take care.", "crowd")
        if self.route and self.route["path"] != r["path"]:
            notify(u["id"], "Your route has changed.", "route")
        self.route = r
        self.set_out(text)
        notify(u["id"], f"{r['mode']} route ready. About {int(r['dist'])} metres, {mins} minutes.", "route")
        self.start_btn.pack(side="left")

    def begin_nav(self):
        if not self.route:
            return
        self.steps = build_steps(self.route, get_ticket(self.user["id"]), needs_of(self.user), self.pre)
        self.step_i = 0
        self.nav_paused = False
        self.show("nav")

    # ---- pages: navigation ----------------------------------------------------------------------
    def page_nav(self):
        self.title("Navigation")
        b, u = self.body, self.user
        t = get_ticket(u["id"])
        if t:
            plat = NODES[t["platform"]]["name"] if t.get("platform") in NODES else "not set"
            info = (f"Train {t.get('train_no', '')} {t.get('train_name', '')}   |   {plat}   |   Coach {t.get('coach', '?')}   |   "
                    f"Seat {t.get('seat', '?')}\nA seat number alone cannot show the exact physical spot in the coach.")
            tk.Label(b, text=info, font=F(13, True), fg=NAVY, bg=WHITE, justify="left", anchor="w", padx=12, pady=6,
                     highlightbackground=TEAL, highlightthickness=2, wraplength=1000).pack(fill="x", pady=4)
        if not self.steps:
            lbl(b, "No route yet. Plan a route first.", 16, True)
            row = tk.Frame(b, bg=BG)
            row.pack(anchor="w", pady=8)
            Btn(row, "Open Route Planner", lambda: self.show("route"), size=15).pack(side="left", padx=(0, 10))
            Btn(row, "Predict my way from my location", self.nav_predicted, bg=NAVY, size=15).pack(side="left")
            return
        self.nav_head = lbl(b, "", 14, True)
        self.nav_text = tk.Label(b, text="", font=F(22, True), bg=WHITE, fg=NAVY, wraplength=950, justify="left", anchor="w",
                                 padx=20, pady=20, relief="solid", bd=2)
        self.nav_text.pack(fill="x", pady=6)
        bar = tk.Frame(b, bg=BG)
        bar.pack(anchor="w", pady=6)
        Btn(bar, "Previous", lambda: self.nav_move(-1), bg=NAVY, size=15).pack(side="left", padx=4)
        Btn(bar, "Repeat", self.nav_repeat, size=15).pack(side="left", padx=4)
        if self.voice_on():
            self.pause_btn = Btn(bar, "Resume speech" if self.nav_paused else "Pause speech", self.nav_pause, bg=GREY, size=15)
            self.pause_btn.pack(side="left", padx=4)
        Btn(bar, "Next", lambda: self.nav_move(1), size=15).pack(side="left", padx=4)
        Btn(bar, "Voice command", self.voice_command, bg=GREY, size=15).pack(side="left", padx=4)
        mrow = tk.Frame(b, bg=BG)
        mrow.pack(anchor="w", pady=4)
        tk.Label(mrow, text="Marker code (e.g. TS-P1):", font=F(13), bg=BG, fg=NAVY).pack(side="left")
        self.marker = tk.StringVar()
        tk.Entry(mrow, textvariable=self.marker, font=F(14), width=12).pack(side="left", padx=6)
        Btn(mrow, "Confirm my location", self.go_marker, bg=GREY, size=12, pady=4).pack(side="left", padx=(0, 8))
        Btn(mrow, "Use my tracked location", self.nav_locate, bg=GREY, size=12, pady=4).pack(side="left")
        self.nav_list = tk.Listbox(b, font=F(12), height=6, activestyle="none", exportselection=False)
        self.nav_list.pack(fill="both", expand=True, pady=6)
        for i, s in enumerate(self.steps):
            self.nav_list.insert("end", f"{i + 1}. {s['text']}")
        self.render_nav(speak=True)

    def render_nav(self, speak=False):
        s = self.steps[self.step_i]
        self.nav_head.config(text=f"Step {self.step_i + 1} of {len(self.steps)}")
        self.nav_text.config(text=s["text"])
        self.nav_list.selection_clear(0, "end")
        self.nav_list.selection_set(self.step_i)
        self.nav_list.see(self.step_i)
        LOC.nav_point = NODES[s["node"]]["name"]
        if speak and not self.nav_paused:
            self.speak(s["text"])

    def nav_move(self, d):
        if self.current != "nav" or not self.steps:
            return
        if d > 0 and self.step_i == len(self.steps) - 1:
            notify(self.user["id"], "You have completed your route.", "route")
            self.steps = []
            return self.show("dashboard", ask_menu=True)
        self.step_i = max(0, min(len(self.steps) - 1, self.step_i + d))
        self.render_nav(speak=True)

    def nav_repeat(self):
        if self.current != "nav" or not self.steps:
            return
        s = self.steps[self.step_i]["text"]
        self.banner_say(s)
        self.speak(s)

    def nav_pause(self):
        if self.current != "nav" or not self.voice_on():
            return
        self.nav_paused = not self.nav_paused
        if self.nav_paused:
            SPEAKER.stop()
        else:
            self.speak(self.steps[self.step_i]["text"])
        self.pause_btn.config(text="Resume speech" if self.nav_paused else "Pause speech")

    def confirm_node(self, node):
        idx = [i for i, s in enumerate(self.steps) if s["node"] == node]
        if not idx:
            return self.banner_say("That place is not on your route. Please check where you are.", True)
        self.step_i = min(idx[0] + 1, len(self.steps) - 1)
        self.render_nav(speak=True)

    def go_marker(self):
        node = MARKERS.get(self.marker.get().strip().upper())
        if not node:
            return self.banner_say("That marker code was not recognised.")
        self.confirm_node(node)

    def nav_locate(self):
        if LOC.latest is None and not LOC.manual_node:
            self.banner_say("Your position is not known yet. Turn on location in My Location and Way, or use a marker code.", True)
            return self.speak("Your position is not known yet. Turn on location, or use a marker code.")
        p = predict_way(get_ticket(self.user["id"]) or {}, needs_of(self.user))
        if p["outside"]:
            self.banner_say(p["lines"][0])
            return self.speak(p["lines"][0])
        self.confirm_node(p["start"])

    def nav_predicted(self):
        p = predict_way(get_ticket(self.user["id"]) or {}, needs_of(self.user))
        if not p["route"]:
            self.banner_say(" ".join(p["lines"]), True)
            return self.speak(" ".join(p["lines"]))
        self.route, self.pre = p["route"], p["pre"]
        self.begin_nav()

    # ---- pages: my location & way (tracking + way prediction) ---------------------------------------------
    def page_where(self):
        self.title("My location & way")
        b = self.body
        self.w_status = lbl(b, "", 16, True)
        self.w_detail = lbl(b, "", 13)
        bar = tk.Frame(b, bg=BG)
        bar.pack(anchor="w", pady=4)
        Btn(bar, "Turn location OFF" if LOC.on else "Turn location ON", self.toggle_loc, bg=GREY if LOC.on else TEAL, size=14).pack(side="left", padx=(0, 8))
        Btn(bar, "Update now", self.loc_now, bg=NAVY, size=14).pack(side="left", padx=(0, 8))
        if self.voice_on():
            Btn(bar, "Read my way aloud", self.say_way, bg=NAVY, size=14).pack(side="left", padx=(0, 8))
        Btn(bar, "Start navigation along this way", self.nav_predicted, size=14).pack(side="left")
        self.w_out = tk.Text(b, height=7, font=F(14), wrap="word", bg=WHITE, fg=NAVY, relief="solid", bd=2)
        self.w_out.pack(fill="x", pady=6)
        row = tk.Frame(b, bg=BG)
        row.pack(anchor="w", pady=2)
        tk.Label(row, text="No GPS? I am at:", font=F(13, True), bg=BG, fg=NAVY).pack(side="left")
        self.w_manual = tk.StringVar(value=NODES[LOC.manual_node or "ENTRY"]["name"])
        ttk.Combobox(row, textvariable=self.w_manual, values=[NODES[k]["name"] for k in POINT_CHOICES], font=(FONT, 13),
                     width=30, state="readonly").pack(side="left", padx=6)
        Btn(row, "Use this position", self.set_manual, bg=GREY, size=12, pady=4).pack(side="left", padx=(0, 8))
        Btn(row, "Set this spot as the station entrance", self.calibrate, bg=GREY, size=12, pady=4).pack(side="left")
        tree = self.w_tree = ttk.Treeview(b, columns=("t", "lat", "lon", "acc", "src"), show="headings", height=5)
        for c, h, w in (("t", "Time", 80), ("lat", "Latitude", 140), ("lon", "Longitude", 140), ("acc", "Accuracy (m)", 110), ("src", "Source", 380)):
            tree.heading(c, text=h)
            tree.column(c, width=w)
        tree.pack(fill="both", expand=True, pady=6)
        lbl(b, "Positions are kept in memory only and are erased when you turn location off or log out.", 12)
        self.w_sig = None

        def refresh():
            f = LOC.latest
            if LOC.on:
                status = "Location tracking is ON" + (" - position found." if f else " - looking for your position ...")
            else:
                status = "Location tracking is OFF." + (" Using the place you chose below." if LOC.manual_node else "")
            detail = ""
            if f:
                sp, hd, trend = LOC.motion()
                detail = (f"Position {f['lat']:.5f}, {f['lon']:.5f}   |   accuracy about {int(f['acc'])} m   |   {f['source']}   |   "
                          f"{fmt_dist(LOC.dist_to_station(f))} from the station entrance")
                if sp is not None:
                    detail += f"   |   speed {sp * 3.6:.1f} km/h" + (f", heading {compass(hd)}" if hd is not None else "")
            elif LOC.err:
                detail = LOC.err
            p = predict_way(get_ticket(self.user["id"]) or {}, needs_of(self.user))
            text = "\n".join(p["lines"])
            with LOC.lock:
                trail = list(LOC.trail)[-5:][::-1]
            sig = (status, detail, text, len(trail), trail[0]["t"] if trail else 0)
            if sig == self.w_sig:
                return
            self.w_sig = sig
            self.w_status.config(text=status)
            self.w_detail.config(text=detail)
            self.w_out.config(state="normal")
            self.w_out.delete("1.0", "end")
            self.w_out.insert("end", text)
            self.w_out.config(state="disabled")
            self.w_tree.delete(*self.w_tree.get_children())
            for q in trail:
                self.w_tree.insert("", "end", values=(datetime.fromtimestamp(q["t"]).strftime("%H:%M:%S"), f"{q['lat']:.5f}",
                                                      f"{q['lon']:.5f}", int(q["acc"]), q["source"]))
        refresh()
        self.refresh_cb = refresh
        flow = self.flow
        self.root.after(700, lambda: flow == self.flow and self.say_way())

    def way_text(self):
        return " ".join(predict_way(get_ticket(self.user["id"]) or {}, needs_of(self.user))["lines"])

    def say_way(self):
        t = self.way_text()
        self.banner_say(t)
        self.speak(t)

    def toggle_loc(self):
        if LOC.on:
            LOC.stop()
            self.seen_fix, self.geo_inside = None, None
            notify(self.user["id"], "Location is off. Your tracked positions were erased.", "route")
        else:
            LOC.start()
            notify(self.user["id"], "Location is on. Finding your position now.", "route")
        self.show("where")

    def loc_now(self):
        if not LOC.on:
            return self.banner_say("Location is off. Press Turn location ON first.", True)
        LOC.poke()
        self.banner_say("Updating your position ...")

    def set_manual(self):
        LOC.manual_node = next(k for k in POINT_CHOICES if NODES[k]["name"] == self.w_manual.get())
        self.w_sig = None
        self.banner_say(f"Okay. We will use {NODES[LOC.manual_node]['name']} when no better position is available.")

    def calibrate(self):
        f = LOC.latest
        if not f:
            return self.banner_say("No position yet. Turn location ON and wait for a position first.", True)
        STATION["ll"] = (f["lat"], f["lon"])
        self.seen_fix, self.geo_inside = None, None
        self.w_sig = None
        self.banner_say("This spot is now the station entrance for this session.")

    # ---- pages: green energy -------------------------------------------------------------------------
    def page_energy(self):
        self.title("Green energy & credits")
        b, uid = self.body, self.user["id"]
        rows = qall("SELECT * FROM energy WHERE user_id=? ORDER BY id DESC", (uid,))
        wh, cr = sum(r["wh"] for r in rows), sum(r["credits"] for r in rows)
        kwh = wh / 1000.0
        lbl(b, f"Your energy contribution: {kwh:.3f} kWh", 22, True)
        lbl(b, f"Credits earned: {cr:.1f}", 22, True)
        lbl(b, f"How credits are worked out: credits = energy in Wh x {CREDITS_PER_WH:g} credits per Wh.", 13)
        tree = ttk.Treeview(b, columns=("when", "src", "kwh", "cr"), show="headings", height=8)
        for c, h, w in (("when", "When", 160), ("src", "Source", 380), ("kwh", "Energy (kWh)", 130), ("cr", "Credits", 110)):
            tree.heading(c, text=h)
            tree.column(c, width=w)
        for r in rows:
            tree.insert("", "end", values=(r["created"], r["source"], f"{r['wh'] / 1000.0:.3f}", f"{r['credits']:.2f}"))
        tree.pack(fill="both", expand=True, pady=8)
        bar = tk.Frame(b, bg=BG)
        bar.pack(anchor="w")
        Btn(bar, "Add energy", self.add_energy, size=14).pack(side="left", padx=(0, 10))
        Btn(bar, "Read my summary", lambda: self.banner_say(f"You have {kwh:.3f} kWh and {cr:.1f} credits.") or
            self.speak(f"You have contributed {kwh:.3f} kilowatt hours and earned {cr:.1f} credits."), bg=NAVY, size=14).pack(side="left")

    def add_energy(self):
        kwh = random.choice(ENERGY_KWH_DATA)                 # one of the 20 readings in ENERGY_KWH_DATA
        wh = round(kwh * 1000.0, 4)
        cr = round(wh * CREDITS_PER_WH, 2)
        ex("INSERT INTO energy(user_id,wh,credits,source,created) VALUES(?,?,?,?,?)",
           (self.user["id"], wh, cr, "Walking energy contribution", now_s()))
        notify(self.user["id"], f"You generated {kwh:.3f} kWh and earned {cr:g} credits.", "energy")
        self.show("energy")

    # ---- pages: mobility vehicle (every line on this page is also read aloud) -----------------------------
    @staticmethod
    def ride_sig(r):
        return (r["status"], r["eta_min"], r["loc"], r["start_at"], r["arrive_at"], r["end_at"])

    @staticmethod
    def ride_stage_text(r):
        now = time.time()

        def left(t):
            return fmt_secs(max(0, int(math.ceil(t - now))))
        st = r["status"]
        if st == "accepted":
            return (f"Vehicle arrives at {hms(r['arrive_at'])} (in {left(r['arrive_at'])})" if r["arrive_at"]
                    else "Vehicle arrival time: the driver has not given a time yet")
        if st == "vehicle_arrived":
            return f"Journey starts at {hms(r['start_at'])} (in {left(r['start_at'])})" if r["start_at"] else "Waiting for the driver to start the journey"
        if st == "started":
            return f"Destination arrives at {hms(r['end_at'])} (in about {left(r['end_at'])})" if r["end_at"] else "Journey in progress"
        if st == "arrived":
            return "You have arrived at your destination."
        return ""

    def page_mobility(self):
        self.title("Mobility vehicle")
        b, u = self.body, self.user
        talk = ["Mobility vehicle."]

        def line(text, size=14, bold=False, said=None):
            w = lbl(b, text, size, bold)
            talk.append(text if said is None else said)
            return w

        def finish(brief=None):
            self.mob_talk = " ".join(t for t in talk if t)
            if self.voice_on():
                Btn(b, "Read aloud again", lambda: self.speak(self.mob_talk), bg=NAVY, size=14).pack(anchor="w", pady=6)
            ev, self.mob_event = self.mob_event, ""
            self.speak((ev + (" " + brief if brief else "")) if ev else self.mob_talk)       # a stage change is announced briefly

        allowed = bool(needs_of(u) - {"none"})
        line("A battery-powered vehicle driven by a person. It is not self-driving.", 13)
        on = qone("SELECT COUNT(*) c FROM users WHERE role='driver' AND available=1")["c"]
        line("Vehicle availability: " + ("a driver is on duty" if on else "no driver is on duty right now"), 15, True)
        if not allowed:
            line("This service is for passengers who need assistance. Update your preferences to request a vehicle.", 14)
            Btn(b, "Accessibility Preferences", lambda: self.show("prefs"), size=14).pack(anchor="w", pady=8)
            return finish()
        ride = qone("SELECT * FROM rides WHERE user_id=? AND status IN ('submitted','accepted','vehicle_arrived','started','arrived') "
                    "ORDER BY id DESC LIMIT 1", (u["id"],))
        if ride:
            self.ride_snapshot = self.ride_sig(ride)
            self.start_lbl = None
            brief = ""
            trip = f"From {NODES[ride['pickup']]['name']} to {NODES[ride['dest']]['name']}"
            line(trip, 16, True, said=f"Your vehicle goes {trip[0].lower() + trip[1:]}.")
            if ride["status"] == "submitted":
                line("[x] Request submitted", 18, True, said="Your request has been submitted.")
                line("Waiting for a driver to accept. This page updates by itself.", 14)
            else:
                order = ["submitted", "accepted", "vehicle_arrived", "started", "arrived"]
                names = {"submitted": "Request submitted", "accepted": "Driver accepted", "vehicle_arrived": "Vehicle arrived",
                         "started": "Journey started", "arrived": "Destination arrived"}
                for s in order:
                    done = order.index(s) <= order.index(ride["status"])
                    line(("[x] " if done else "[ ] ") + names[s], 18, done, said=(names[s] + ".") if done else "")
                stage = self.ride_stage_text(ride)
                self.start_lbl = line(stage, 16, True)
                if ride["status"] != "arrived":
                    brief = stage
                if ride["acc_at"] and ride["arrive_at"]:
                    line(f"Estimated waiting time: about {fmt_secs(ride['arrive_at'] - ride['acc_at'])} (reported by the driver)", 14)
                elif ride["eta_min"] is not None:
                    line(f"Estimated waiting time: {ride['eta_min']} minutes (reported by the driver)", 14)
                else:
                    line("Estimated waiting time: not available", 14)
                if ride["loc"]:
                    line(f"Last reported vehicle location: {ride['loc']} (at {ride['loc_time']})", 14,
                         said=f"The vehicle was last reported at {ride['loc']}, at {ride['loc_time']}.")
                else:
                    line("Last reported vehicle location: not reported", 14)
            if ride["status"] == "arrived":
                Btn(b, "Request another vehicle", self.finish_ride, size=14).pack(anchor="w", pady=10)
            else:
                Btn(b, "Cancel request", self.cancel_ride, bg=GREY, size=14).pack(anchor="w", pady=10)
            flow = self.flow
            said_for = {"vehicle_arrived": "The vehicle has arrived.", "started": "Your journey has started.",
                        "arrived": "You have arrived at your destination."}

            def chk():
                if flow != self.flow:
                    return
                r = qone("SELECT * FROM rides WHERE id=?", (ride["id"],))
                if not r or self.ride_sig(r) != self.ride_snapshot:
                    if r and r["status"] != self.ride_snapshot[0]:
                        self.mob_event = said_for.get(r["status"], "")
                    return self.show("mobility")
                if self.start_lbl is not None and self.start_lbl.winfo_exists():
                    self.start_lbl.config(text=self.ride_stage_text(r))
            self.refresh_cb = chk
            return finish(brief)
        names = [NODES[k]["name"] for k in POINT_CHOICES]
        here = self.current_point()
        self.rp, self.rd = tk.StringVar(value=NODES[here or "ENTRY"]["name"]), tk.StringVar(value=NODES["P1"]["name"])
        t = get_ticket(u["id"])
        if t and t.get("platform") in NODES:
            self.rd.set(NODES[t["platform"]]["name"])
        tk.Label(b, text="Pickup location" + (" (set from your tracked position)" if here and LOC.on else ""), font=F(14, True), bg=BG,
                 fg=NAVY).pack(anchor="w", pady=(10, 2))
        ttk.Combobox(b, textvariable=self.rp, values=names, font=(FONT, 14), width=34, state="readonly").pack(anchor="w")
        tk.Label(b, text="Destination platform", font=F(14, True), bg=BG, fg=NAVY).pack(anchor="w", pady=(10, 2))
        ttk.Combobox(b, textvariable=self.rd, values=[NODES[k]["name"] for k in PLATFORM_KEYS], font=(FONT, 14), width=34,
                     state="readonly").pack(anchor="w")
        Btn(b, "Request a mobility vehicle", self.request_ride, size=16).pack(anchor="w", pady=16)
        talk.append(f"Your pickup is {self.rp.get()} and your destination is {self.rd.get()}. "
                    "Press Request a mobility vehicle when you are ready.")
        finish()

    def request_ride(self):
        p = next(k for k in POINT_CHOICES if NODES[k]["name"] == self.rp.get())
        d = next(k for k in PLATFORM_KEYS if NODES[k]["name"] == self.rd.get())
        if p == d:
            return messagebox.showinfo("Mobility vehicle", "Pickup and destination are the same place.")
        ex("INSERT INTO rides(user_id,pickup,dest,status,created,created_ts) VALUES(?,?,?,'submitted',?,?)",
           (self.user["id"], p, d, now_s(), time.time()))
        notify(self.user["id"], "Your mobility vehicle request was submitted.", "vehicle")
        self.show("mobility")

    def finish_ride(self):
        ex("UPDATE rides SET status='completed' WHERE user_id=? AND status='arrived'", (self.user["id"],))
        self.show("mobility")

    def cancel_ride(self):
        ex("UPDATE rides SET status='cancelled' WHERE user_id=? AND status IN ('submitted','accepted','vehicle_arrived')", (self.user["id"],))
        notify(self.user["id"], "Your mobility vehicle request was cancelled.", "vehicle")
        self.show("mobility")

    # ---- pages: check-ins ----------------------------------------------------------------------------------------
    def page_checkin(self):
        self.title("Safety check-ins")
        b, uid = self.body, self.user["id"]
        top = tk.Frame(b, bg=BG)
        top.pack(fill="x")
        Btn(top, "SOS - urgent help", self.send_sos, bg=RED, size=22, pady=14).pack(side="left", padx=(0, 20))
        lbl(top, "Press SOS (or say SOS) for urgent assistance. If pressed by mistake, you can cancel it.", 13, wrap=600)
        s = qone("SELECT * FROM sched WHERE user_id=?", (uid,)) or {"interval_min": 10, "window_s": 60}
        row = tk.Frame(b, bg=BG)
        row.pack(anchor="w", pady=8)
        self.ci_int = tk.StringVar(value=f"{s['interval_min']:g}")
        self.ci_win = tk.StringVar(value=f"{s['window_s']} seconds")
        tk.Label(row, text="Check me every (minutes)", font=F(14, True), bg=BG, fg=NAVY).grid(row=0, column=0, padx=6)
        ttk.Combobox(row, textvariable=self.ci_int, values=["1", "5", "10", "15", "30"], width=10, font=(FONT, 14),
                     state="readonly").grid(row=0, column=1)
        tk.Label(row, text="Time to answer", font=F(14, True), bg=BG, fg=NAVY).grid(row=0, column=2, padx=(20, 6))
        ttk.Combobox(row, textvariable=self.ci_win, values=["30 seconds", "60 seconds", "120 seconds"], width=12, font=(FONT, 14),
                     state="readonly").grid(row=0, column=3)
        bar = tk.Frame(b, bg=BG)
        bar.pack(anchor="w", pady=6)
        Btn(bar, "Start", lambda: self.sched_set("start"), size=15).pack(side="left", padx=4)
        Btn(bar, "Pause", lambda: self.sched_set("pause"), bg=NAVY, size=15).pack(side="left", padx=4)
        Btn(bar, "Stop", lambda: self.sched_set("stop"), bg=GREY, size=15).pack(side="left", padx=4)
        self.ci_status = lbl(b, "", 15, True)
        tree = self.ci_tree = ttk.Treeview(b, columns=("when", "result"), show="headings", height=8)
        tree.heading("when", text="Time")
        tree.heading("result", text="Result")
        tree.column("when", width=100)
        tree.column("result", width=800)
        tree.pack(fill="both", expand=True, pady=8)

        def refresh():
            sc = qone("SELECT * FROM sched WHERE user_id=?", (uid,))
            state = sc["state"] if sc else "stopped"
            txt = {"running": f"Check-ins are ON (every {sc['interval_min']:g} min).", "paused": "Check-ins are PAUSED.",
                   "stopped": "Check-ins are OFF."}[state] if sc else "Check-ins are OFF."
            if sc and state == "running" and sc["next_due"]:
                txt += f" Next check-in around {hhmm(sc['next_due'])}."
            self.ci_status.config(text=txt)
            tree.delete(*tree.get_children())
            for c in qall("SELECT * FROM checkins WHERE user_id=? ORDER BY id DESC LIMIT 10", (uid,)):
                a = qone("SELECT * FROM alerts WHERE id=?", (c["alert_id"],)) if c["alert_id"] else None
                res = {"prompt": "Waiting for your answer", "ok": "Submitted: I'm okay"}.get(c["status"])
                if c["status"] == "help":
                    res = "You asked for help - " + (alert_status_text(a) if a else "")
                if c["status"] == "missed":
                    res = "No answer - alert created: " + (alert_status_text(a) if a else "")
                tree.insert("", "end", values=(hhmm(c["prompted"]), res))
        refresh()
        self.refresh_cb = refresh

    def sched_set(self, action):
        uid = self.user["id"]
        iv = float(self.ci_int.get().split()[0])
        win = int(self.ci_win.get().split()[0])
        s = qone("SELECT * FROM sched WHERE user_id=?", (uid,))
        if not s:
            ex("INSERT INTO sched(user_id) VALUES(?)", (uid,))
            s = qone("SELECT * FROM sched WHERE user_id=?", (uid,))
        now = time.time()
        if action == "start":
            rem = s["remaining"] if s["state"] == "paused" and s["interval_min"] == iv and s["remaining"] else iv * 60
            ex("UPDATE sched SET interval_min=?, window_s=?, state='running', next_due=?, remaining=NULL WHERE user_id=?", (iv, win, now + rem, uid))
            notify(uid, f"Check-ins started. You will be asked every {iv:g} minutes.", "safety")
        elif action == "pause" and s["state"] == "running":
            rem = max((s["next_due"] or now) - now, 0)
            if qone("SELECT id FROM checkins WHERE user_id=? AND status='prompt'", (uid,)):
                rem = s["interval_min"] * 60
            ex("UPDATE sched SET state='paused', remaining=?, next_due=NULL WHERE user_id=?", (rem, uid))
            notify(uid, "Check-ins paused.", "safety")
        elif action == "stop":
            ex("UPDATE sched SET state='stopped', next_due=NULL, remaining=NULL WHERE user_id=?", (uid,))
            notify(uid, "Check-ins stopped.", "safety")
        self.show("checkin")

    # ---- pages: notifications ----------------------------------------------------------------------------------------------
    def page_notifs(self):
        self.title("Notifications")
        rows = qall("SELECT * FROM notifs WHERE user_id=? ORDER BY id DESC LIMIT 40", (self.user["id"],))
        lb = tk.Listbox(self.body, font=F(14), activestyle="none")
        lb.pack(fill="both", expand=True, pady=6)
        for r in rows:
            lb.insert("end", f"{r['created']}   [{r['kind']}]   {r['text']}")
        if not rows:
            lb.insert("end", "No notifications yet.")
        Btn(self.body, "Read latest aloud" if self.voice_on() else "Show latest",
            lambda: (self.banner_say(rows[0]["text"]), self.speak(rows[0]["text"])) if rows else None, bg=NAVY, size=14).pack(anchor="w", pady=6)

    # ---- driver / staff console -----------------------------------------------------------------------------------------------
    def open_console(self, user):
        win = tk.Toplevel(self.root)
        win.title(f"TrackSync - {'Driver' if user['role'] == 'driver' else 'Staff'} console")
        win.geometry("1000x640")
        win.configure(bg=BG)
        tk.Label(win, text=f"{user['name']} - {'Mobility vehicle driver' if user['role'] == 'driver' else 'Station staff'}",
                 font=(FONT, 20, "bold"), fg=WHITE, bg=NAVY, padx=14, pady=8, anchor="w").pack(fill="x")
        nb = ttk.Notebook(win)
        nb.pack(fill="both", expand=True, padx=10, pady=10)
        refreshers = []
        if user["role"] == "driver":
            self._driver_tab(nb, win, user, refreshers)
        else:
            self._alerts_tab(nb, win, user, refreshers)
            self._notices_tab(nb, refreshers)

        def loop():
            if not win.winfo_exists():
                return
            try:
                for r in refreshers:
                    r()
            except Exception:
                log_error()
            win.after(2000, loop)
        loop()

    def _driver_tab(self, nb, win, user, refreshers):
        f = tk.Frame(nb, bg=BG, padx=10, pady=10)
        nb.add(f, text="Mobility requests")
        status = lbl(f, "", 16, True)
        tree = ttk.Treeview(f, columns=("id", "who", "pickup", "dest", "status", "eta"), show="headings", height=10)
        for c, h, w in (("id", "No.", 50), ("who", "Passenger", 180), ("pickup", "Pickup", 220), ("dest", "Destination", 150),
                        ("status", "Status", 120), ("eta", "Wait (min)", 90)):
            tree.heading(c, text=h)
            tree.column(c, width=w)
        tree.pack(fill="both", expand=True, pady=6)

        def sel():
            s = tree.selection()
            return qone("SELECT * FROM rides WHERE id=?", (int(s[0]),)) if s else None

        def me():
            return qone("SELECT * FROM users WHERE id=?", (user["id"],))

        def accept():
            r = sel()
            if not r or r["status"] != "submitted":
                return messagebox.showinfo("Accept", "Select a new request first.", parent=win)
            if not me()["available"]:
                return messagebox.showinfo("Accept", "You are marked Out of Service.", parent=win)
            if qone("SELECT id FROM rides WHERE driver_id=? AND status IN ('accepted','vehicle_arrived','started')", (user["id"],)):
                return messagebox.showinfo("Accept", "Please finish your current journey first.", parent=win)
            eta = simpledialog.askstring("Waiting time", "Estimated waiting time in minutes (leave empty if unsure):", parent=win)
            loc = simpledialog.askstring("Your location", "Where is the vehicle now? (optional)", parent=win)
            eta_v = int(eta) if eta and eta.strip().isdigit() else None
            now = time.time()
            a, arrive_at, start_at, end_at = plan_ride_times(now, max(10, min(eta_v * 60, ARRIVE_MAX_S)) if eta_v is not None else None)
            loc_v = (loc or "").strip() or None
            if not exn("UPDATE rides SET status='accepted', driver_id=?, eta_min=?, loc=?, loc_time=?, acc_at=?, arrive_at=?, "
                       "start_at=?, end_at=? WHERE id=? AND status='submitted'",
                       (user["id"], max(1, int(math.ceil(a / 60.0))), loc_v, datetime.now().strftime("%H:%M"), now, arrive_at,
                        start_at, end_at, r["id"])):
                return messagebox.showinfo("Accept", "This request was already accepted.", parent=win)
            notify(r["user_id"], "A driver accepted your request. " + ride_plan_text(a, arrive_at, start_at, end_at) +
                   (f" The vehicle was last reported at: {loc_v}." if loc_v else ""), "vehicle")
            refresh()

        def move(frm, to, msg):
            r = sel()
            if not r or r["status"] not in (frm if isinstance(frm, tuple) else (frm,)) or r["driver_id"] != user["id"]:
                return messagebox.showinfo("Update", "Select your own request that is ready for this step.", parent=win)
            ex("UPDATE rides SET status=? WHERE id=?", (to, r["id"]))
            notify(r["user_id"], msg, "vehicle")
            refresh()

        def toggle():
            m = me()
            if m["available"]:
                if qone("SELECT id FROM rides WHERE driver_id=? AND status IN ('vehicle_arrived','started')", (user["id"],)):
                    return messagebox.showinfo("Out of Service", "Please finish the journey in progress first.", parent=win)
                for r in qall("SELECT * FROM rides WHERE driver_id=? AND status='accepted'", (user["id"],)):
                    ex("UPDATE rides SET status='submitted', driver_id=NULL, eta_min=NULL, loc=NULL, start_at=NULL, acc_at=NULL, arrive_at=NULL, end_at=NULL WHERE id=?", (r["id"],))
                    notify(r["user_id"], "The vehicle is out of service. Your request is waiting for another driver.", "vehicle", True)
            ex("UPDATE users SET available=? WHERE id=?", (0 if m["available"] else 1, user["id"]))
            refresh()

        bar = tk.Frame(f, bg=BG)
        bar.pack(anchor="w")
        Btn(bar, "Accept Request", accept, size=14).pack(side="left", padx=4)
        Btn(bar, "Start Journey", lambda: move(("accepted", "vehicle_arrived"), "started", "Your journey has started."), bg=NAVY, size=14).pack(side="left", padx=4)
        Btn(bar, "Arrived", lambda: move("started", "arrived", "You have arrived at your destination."), bg=NAVY, size=14).pack(side="left", padx=4)
        oos = Btn(bar, "Out of Service", toggle, bg=RED, size=14)
        oos.pack(side="left", padx=4)

        def refresh():
            m = me()
            status.config(text="Status: " + ("Available" if m["available"] else "OUT OF SERVICE"))
            oos.config(text="Out of Service" if m["available"] else "Back in Service")
            keep = tree.selection()
            tree.delete(*tree.get_children())
            for r in qall("SELECT r.*, u.name pname FROM rides r JOIN users u ON u.id=r.user_id WHERE r.status IN "
                          "('submitted','accepted','vehicle_arrived','started') AND (r.driver_id IS NULL OR r.driver_id=?) ORDER BY r.id", (user["id"],)):
                tree.insert("", "end", iid=str(r["id"]), values=(r["id"], r["pname"], NODES[r["pickup"]]["name"], NODES[r["dest"]]["name"],
                                                                 r["status"], r["eta_min"] if r["eta_min"] is not None else "-"))
            for k in keep:
                if tree.exists(k):
                    tree.selection_set(k)
        refresh()
        refreshers.append(refresh)

    def _alerts_tab(self, nb, win, user, refreshers):
        f = tk.Frame(nb, bg=BG, padx=10, pady=10)
        nb.add(f, text="Safety alerts")
        tree = ttk.Treeview(f, columns=("id", "time", "who", "type", "status", "delivery"), show="headings", height=9)
        for c, h, w in (("id", "No.", 50), ("time", "Time", 70), ("who", "Passenger", 160), ("type", "Type", 130),
                        ("status", "Status", 140), ("delivery", "Delivery", 120)):
            tree.heading(c, text=h)
            tree.column(c, width=w)
        tree.pack(fill="x", pady=6)
        det = tk.Text(f, height=6, font=(FONT, 12), wrap="word", bg=WHITE)
        det.pack(fill="x", pady=6)
        kinds = {"sos": "SOS", "help": "Help requested", "missed_checkin": "Missed check-in"}

        def sel():
            s = tree.selection()
            return qone("SELECT * FROM alerts WHERE id=?", (int(s[0]),)) if s else None

        def show_detail(_e=None):
            a = sel()
            det.config(state="normal")
            det.delete("1.0", "end")
            if a:
                det.insert("end", a["message"] + "\n" + alert_status_text(a))
            det.config(state="disabled")

        def ack():
            a = sel()
            if not a or a["status"] != "open":
                return messagebox.showinfo("Acknowledge", "Select an open alert.", parent=win)
            ex("UPDATE alerts SET status='acknowledged', ack_by=?, ack_time=? WHERE id=?", (user["name"], time.time(), a["id"]))
            notify(a["user_id"], f"Station staff ({user['name']}) acknowledged your alert.", "safety", True)
            refresh()

        def close():
            a = sel()
            if a and a["status"] in ("open", "acknowledged"):
                ex("UPDATE alerts SET status='closed' WHERE id=?", (a["id"],))
                refresh()

        bar = tk.Frame(f, bg=BG)
        bar.pack(anchor="w")
        Btn(bar, "Acknowledge", ack, size=14).pack(side="left", padx=4)
        Btn(bar, "Close alert", close, bg=NAVY, size=14).pack(side="left", padx=4)
        tree.bind("<<TreeviewSelect>>", show_detail)

        def refresh():
            keep = tree.selection()
            tree.delete(*tree.get_children())
            for a in qall("SELECT a.*, u.name pname FROM alerts a JOIN users u ON u.id=a.user_id WHERE a.status!='closed' ORDER BY a.id DESC LIMIT 30"):
                tree.insert("", "end", iid=str(a["id"]), values=(a["id"], hhmm(a["created"]), a["pname"], kinds.get(a["kind"], a["kind"]),
                                                                 a["status"], a["delivery"]))
            for k in keep:
                if tree.exists(k):
                    tree.selection_set(k)
        refresh()
        refreshers.append(refresh)

    def _notices_tab(self, nb, refreshers):
        f = tk.Frame(nb, bg=BG, padx=10, pady=10)
        nb.add(f, text="Station notices")
        lbl(f, "Post a notice to all passengers (shown as text, and spoken for passengers who use speech).", 13)
        kinds = {"Platform change": "platform", "Lift unavailable": "lift", "Crowding warning": "crowd", "Route change": "route", "Information": "info"}
        k = tk.StringVar(value="Platform change")
        t = tk.StringVar()
        ttk.Combobox(f, textvariable=k, values=list(kinds), state="readonly", font=(FONT, 14), width=24).pack(anchor="w", pady=4)
        tk.Entry(f, textvariable=t, font=(FONT, 14), width=80).pack(anchor="w", pady=4)

        def post():
            if t.get().strip():
                ex("INSERT INTO notices(kind,text,created) VALUES(?,?,?)", (kinds[k.get()], t.get().strip(), now_s()))
                t.set("")
                refresh()
        Btn(f, "Post notice", post, size=14).pack(anchor="w", pady=6)
        lb = tk.Listbox(f, font=(FONT, 12), height=10)
        lb.pack(fill="both", expand=True)

        def refresh():
            lb.delete(0, "end")
            for n in qall("SELECT * FROM notices ORDER BY id DESC LIMIT 20"):
                lb.insert("end", f"{n['created']}  [{n['kind']}]  {n['text']}")
        refresh()
        refreshers.append(refresh)


# ----------------------------------------------------------------------------
# MAIN
# ----------------------------------------------------------------------------
def main():
    init_db()
    if "--scheduler" in sys.argv:
        print("TrackSync check-in scheduler running. Press Ctrl+C to stop.")
        sch = Scheduler()
        sch.start()
        try:
            while True:
                time.sleep(1)
        except KeyboardInterrupt:
            return
    purge_passengers()            # nothing about earlier passengers is ever kept
    sch = Scheduler()
    sch.start()
    app = App()
    try:
        app.root.mainloop()
    finally:
        sch.stop_flag.set()
        SPEAKER.stop()
        LOC.stop()


if __name__ == "__main__":
    main()
