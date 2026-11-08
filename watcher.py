#!/usr/bin/env python3
"""Veille RSS multi-sources -> alertes Telegram (sujets et sources définis dans la config).

Usage :
  python watcher.py                  # run normal (envoie sur Telegram)
  python watcher.py --dry-run        # affiche au lieu d'envoyer, ne sauvegarde rien
  python watcher.py --dry-run --no-bootstrap   # idem, mais montre aussi le contenu "déjà vu"
  python watcher.py --check          # teste chaque source et dit combien d'articles elle renvoie
  python watcher.py --test-telegram  # envoie un message de test
  python watcher.py --get-chat-id    # affiche ton chat_id (après avoir écrit au bot)
"""
import argparse, hashlib, html, json, os, re, sys, time, unicodedata
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timedelta, timezone
from urllib.parse import quote, urlparse
from zoneinfo import ZoneInfo

import feedparser
import requests
import yaml
from bs4 import BeautifulSoup

ROOT = os.path.dirname(os.path.abspath(__file__))
STATE_PATH = os.path.join(ROOT, "state.json")
UA = {"User-Agent": "Mozilla/5.0 (compatible; RSSTools/1.0)"}
CAT_EMOJI = {"mercato": "🔄", "actu": "📰", "joueurs": "👤", "veille": "🏁"}
CAT_LABEL = {"mercato": "MERCATO", "actu": "ACTU", "joueurs": "JOUEURS", "veille": "VEILLE CONCURRENTS"}

# ----------------------------------------------------------------- utilitaires

def norm(s):
    s = unicodedata.normalize("NFKD", (s or "").lower())
    s = "".join(c for c in s if not unicodedata.combining(c))
    return re.sub(r"[^\w\s]", " ", s)

CJK = re.compile(r"[\u3040-\u30ff\u4e00-\u9fff]")

class Matcher:
    def __init__(self, terms):
        self.subs, self.regs = [], []
        for t in terms:
            whole = t.startswith("=")          # "=bid" -> mot entier uniquement
            n = norm(t.lstrip("=")).strip()
            if not n:
                continue
            if CJK.search(n):
                self.subs.append(n)
            else:
                self.regs.append(re.compile(r"(?<!\w)" + re.escape(n) + (r"(?!\w)" if whole else "")))
    def has(self, text):
        return any(s in text for s in self.subs) or any(r.search(text) for r in self.regs)

def domain_of(url):
    d = urlparse(url or "").netloc.lower()
    return d[4:] if d.startswith("www.") else d

def in_list(domain, lst):
    return any(domain == d or domain.endswith("." + d) for d in lst)

STOP = set("le la les de du des un une et en au aux ol olympique lyon lyonnais the of a to in for sur pour avec dans qui que par est".split())

def tokens(title):
    return {w for w in norm(title).split() if len(w) > 2 and w not in STOP}

def jaccard(a, b):
    return len(a & b) / len(a | b) if a and b else 0.0

def now_utc():
    return datetime.now(timezone.utc)

# ----------------------------------------------------------------- configuration / état

def load_config():
    with open(os.path.join(ROOT, "config.yaml"), encoding="utf-8") as f:
        return yaml.safe_load(f)

def load_state():
    if os.path.exists(STATE_PATH):
        try:
            with open(STATE_PATH, encoding="utf-8") as f:
                st = json.load(f)
        except Exception:
            st = {}
    else:
        st = {}
    st.setdefault("seen", {})
    st.setdefault("clusters", [])
    st.setdefault("queue", [])
    st.setdefault("digest", {"start": "", "end": ""})
    return st

def save_state(st):
    cutoff = time.time() - 4 * 86400
    st["seen"] = {k: v for k, v in st["seen"].items() if v > cutoff}
    st["queue"] = st["queue"][-300:]
    with open(STATE_PATH, "w", encoding="utf-8") as f:
        json.dump(st, f, ensure_ascii=False, indent=0)

# ----------------------------------------------------------------- collecte

def gnews_url(q, loc):
    return (f"https://news.google.com/rss/search?q={quote(q + ' when:1d')}"
            f"&hl={loc['hl']}&gl={loc['gl']}&ceid={quote(loc['ceid'], safe=':')}")

def build_sources(cfg):
    L = cfg["locales"]
    src = []
    def add_gn(q, loc_code, origin, label, player=None, speed="fast"):
        loc = L[loc_code]
        src.append({"kind": "rss", "url": gnews_url(q, loc), "origin": origin,
                    "lang": loc["lang"], "label": label, "player": player,
                    "foreign": loc_code != "FRA", "speed": speed})
    for f in cfg.get("rss_feeds", []):
        src.append({"kind": "rss", "url": f["url"], "origin": "direct", "lang": f.get("lang", "fr"),
                    "label": f"flux:{f['name']}", "player": None, "foreign": f.get("lang", "fr") != "fr",
                    "speed": "direct", "trust": f.get("trust")})
    for h in cfg.get("html_pages", []):
        src.append({"kind": "html", "url": h["url"], "pattern": h["pattern"], "origin": "html",
                    "lang": h.get("lang", "fr"), "label": f"page:{h['name']}", "player": None,
                    "foreign": False, "speed": "direct", "trust": h.get("trust"),
                    "all_relevant": h.get("all_relevant", False), "name": h["name"]})
    for g in cfg.get("global_queries", []):
        add_gn(g["q"], g["locale"], "global", f"global:{g['q']} [{g['locale']}]",
               speed="fast" if g["locale"] == "FRA" else "slow")
    for s in cfg.get("site_queries", []):
        add_gn(f"{s['q']} site:{s['site']}", s["locale"], "site", f"site:{s['site']} [{s['locale']}]",
               speed="fast" if s["locale"] == "FRA" else "slow")
    for p in cfg.get("players", []) + cfg.get("targets", []):
        names = [p["name"]] + p.get("search_aliases", [])
        q = " OR ".join(f'"{n}"' for n in names)
        for lc in p["locales"]:
            add_gn(q, lc, "player", f"joueur:{p['name']} [{lc}]", p["name"], speed="slow")
    for p in cfg.get("staff", []):
        q = " OR ".join(f'"{n}"' for n in [p["name"]] + p.get("search_aliases", []))
        for lc in p.get("locales", ["FRA"]):
            add_gn(q, lc, "staff", f"staff:{p['name']} [{lc}]", None, speed="slow")
            src[-1]["foreign"] = False
    for n in cfg.get("academy", []):
        add_gn(f'"{n}" {cfg.get("academy_suffix", "")}'.strip(), "FRA", "player", f"académie:{n}", n, speed="slow")
    for c in cfg.get("youtube_channels", []):
        src.append({"kind": "rss", "url": f"https://www.youtube.com/feeds/videos.xml?channel_id={c['channel_id']}",
                    "origin": "youtube", "lang": "fr", "label": f"youtube:{c.get('name', c['channel_id'])}",
                    "player": None, "speed": "direct", "foreign": False, "trust": c.get("trust", "other")})
    for c in cfg.get("telegram_channels", []):
        src.append({"kind": "telegram", "name": c["name"], "origin": "telegram", "lang": c.get("lang", "fr"),
                    "label": f"telegram:{c['name']}", "player": None, "speed": "direct", "foreign": False, "trust": c.get("trust", "other")})
    for c in cfg.get("bluesky_accounts", []):
        src.append({"kind": "bluesky", "handle": c["handle"], "origin": "bluesky", "lang": c.get("lang", "fr"),
                    "label": f"bluesky:{c['handle']}", "player": None, "speed": "direct", "foreign": False, "trust": c.get("trust", "other")})
    return src

def to_dt(st):
    try:
        return datetime(*st[:6], tzinfo=timezone.utc)
    except Exception:
        return None

def mk_id(s):
    return hashlib.sha1(s.encode("utf-8", "ignore")).hexdigest()[:16]

def fetch_source(s):
    items = []
    try:
        if s["kind"] == "rss":
            r = requests.get(s["url"], headers=UA, timeout=20)
            r.raise_for_status()
            feed = feedparser.parse(r.content)
            for e in feed.entries:
                title = html.unescape(e.get("title", "")).strip()
                srcinfo = e.get("source") or {}
                sname = srcinfo.get("title") or domain_of(e.get("link", ""))
                sdom = domain_of(srcinfo.get("href", "")) or domain_of(e.get("link", ""))
                if srcinfo.get("title") and title.endswith(" - " + srcinfo["title"]):
                    title = title[: -len(srcinfo["title"]) - 3].strip()
                summ = BeautifulSoup(e.get("summary", ""), "html.parser").get_text(" ")[:400]
                items.append({"id": mk_id(e.get("id") or e.get("link", title)), "title": title,
                              "link": e.get("link", ""), "source": sname, "domain": sdom,
                              "published": to_dt(e.get("published_parsed") or e.get("updated_parsed")),
                              "summary": summ})
        elif s["kind"] == "html":
            r = requests.get(s["url"], headers=UA, timeout=20)
            r.raise_for_status()
            soup = BeautifulSoup(r.text, "html.parser")
            pat = re.compile(s["pattern"])
            seen_links = set()
            for a_tag in soup.find_all("a", href=True):
                href = requests.compat.urljoin(s["url"], a_tag["href"])
                if not pat.search(href) or href in seen_links:
                    continue
                title = " ".join(a_tag.get_text(" ").split())
                if len(title) < 15:
                    continue
                seen_links.add(href)
                items.append({"id": mk_id("html:" + href), "title": title[:250], "link": href,
                              "source": s["name"], "domain": domain_of(href), "published": None,
                              "summary": "", "undated_ok": True})
        elif s["kind"] == "telegram":
            r = requests.get(f"https://t.me/s/{s['name']}", headers=UA, timeout=20)
            r.raise_for_status()
            soup = BeautifulSoup(r.text, "html.parser")
            for m in soup.select("div.tgme_widget_message"):
                post = m.get("data-post", "")
                txt = m.select_one(".tgme_widget_message_text")
                if not post or not txt:
                    continue
                t = txt.get_text(" ").strip()
                tm = m.select_one("time")
                pub = None
                if tm and tm.get("datetime"):
                    try:
                        pub = datetime.fromisoformat(tm["datetime"]).astimezone(timezone.utc)
                    except Exception:
                        pub = None
                items.append({"id": mk_id("tg:" + post), "title": t[:280], "link": f"https://t.me/{post}",
                              "source": f"Telegram @{s['name']}", "domain": f"t.me/{s['name']}",
                              "published": pub, "summary": t[280:600]})
        elif s["kind"] == "bluesky":
            r = requests.get("https://public.api.bsky.app/xrpc/app.bsky.feed.getAuthorFeed",
                             params={"actor": s["handle"], "limit": 20, "filter": "posts_no_replies"},
                             headers=UA, timeout=20)
            r.raise_for_status()
            for f in r.json().get("feed", []):
                p = f.get("post", {})
                rec = p.get("record", {})
                rkey = p.get("uri", "").split("/")[-1]
                try:
                    pub = datetime.fromisoformat(rec.get("createdAt", "").replace("Z", "+00:00"))
                except Exception:
                    pub = None
                items.append({"id": mk_id("bsky:" + p.get("uri", "")), "title": rec.get("text", "")[:280],
                              "link": f"https://bsky.app/profile/{s['handle']}/post/{rkey}",
                              "source": f"Bluesky @{s['handle']}", "domain": f"bsky:{s['handle']}",
                              "published": pub, "summary": ""})
    except Exception as ex:
        return s, None, str(ex)
    for it in items:
        it.update({"origin": s["origin"], "lang": s["lang"], "player": s.get("player"),
                   "forced_trust": s.get("trust"), "label": s["label"], "foreign": s.get("foreign", False),
                   "all_relevant": s.get("all_relevant", False), "speed": s.get("speed", "fast")})
    return s, items, None

def collect(cfg, check=False, speeds=None, verbose=False):
    sources = [x for x in build_sources(cfg) if speeds is None or x.get("speed") in speeds]
    results, items = [], []
    with ThreadPoolExecutor(max_workers=8) as ex:
        for s, its, err in ex.map(fetch_source, sources):
            results.append((s, its, err))
            if its:
                items.extend(its)
    if check:
        now = now_utc()
        lines = []
        for s, its, err in results:
            if its is None:
                lines.append(f"✘ {s['label']} : ERREUR {str(err)[:60]}")
            elif not its:
                lines.append(f"⚪ {s['label']} : 0 article")
            else:
                dates = [i["published"] for i in its if i["published"]]
                age = f", dernier il y a {int((now - max(dates)).total_seconds() // 60)} min" if dates else ", sans dates"
                lines.append(f"✔ {s['label']} : {len(its)} articles{age}")
        ok = sum(1 for _, i, e in results if i)
        report = [f"🩺 Diagnostic : {ok}/{len(results)} sources OK"] + sorted(lines)
        if check == "telegram":
            buf = ""
            for l in report:
                if len(buf) + len(l) > 3500:
                    Sender(False).send("actu", html.escape(buf), silent=True); buf = ""
                buf += l + "\n"
            if buf:
                Sender(False).send("actu", html.escape(buf), silent=True)
            print(f"diagnostic envoyé sur Telegram ({ok}/{len(results)} OK)")
        else:
            print("\n".join(report))
        return []
    errs = [(s["label"], e) for s, i, e in results if e]
    if errs:   # en dépôt public les journaux sont visibles : on n'affiche que le nombre
        print(f"⚠ {len(errs)} source(s) en erreur (ignorées)"
              + (" : " + "; ".join(l for l, _ in errs[:10]) if verbose else ""), file=sys.stderr)
    return items

# ----------------------------------------------------------------- classification

class Rules:
    def __init__(self, cfg):
        k = cfg["keywords"]
        self.mercato = Matcher(k["mercato"]); self.urgent = Matcher(k["urgent"])
        self.interview = Matcher(k["interview"]); self.life = Matcher(k["life"])
        self.selection = Matcher(k.get("selection", []))
        self.critical = Matcher(k["critical_outside_hours"])
        self.strong = Matcher(cfg.get("strong_terms", []))
        self.weak = Matcher(cfg.get("weak_terms", []))
        self.football = Matcher(cfg.get("football_context", []))
        self.exclude = Matcher(cfg.get("exclude_terms", []))
        names = []
        for p in cfg.get("players", []) + cfg.get("targets", []):
            names += [p["name"]] + p.get("aliases", []) + p.get("search_aliases", [])
        names += cfg.get("academy", [])
        for p in cfg.get("staff", []):
            names += [p["name"]] + p.get("aliases", [])
        self.names = Matcher(names)
        self.cfg = cfg
    def tier(self, it):
        if it.get("forced_trust"):
            return it["forced_trust"]
        d = it["domain"]; c = self.cfg
        if in_list(d, c.get("competitor_domains", [])): return "competitor"
        if in_list(d, c.get("official_domains", [])): return "official"
        if in_list(d, c.get("trusted_domains", [])): return "trusted"
        return "other"
    def relevant(self, it):
        """Garde un article seulement s'il concerne le sujet suivi (voir config)."""
        title = it["title"]
        t = norm(title)
        if self.exclude.has(t):
            return False
        if it.get("all_relevant"):
            return True
        raw_t = title
        cs = self.cfg.get("case_sensitive_terms", [])
        def cs_in(txt):
            return any(re.search(r"\b" + re.escape(x) + r"\b", txt) for x in cs)
        if it.get("foreign"):   # presse étrangère : le nom (ou le club) doit être DANS LE TITRE
            return cs_in(raw_t) or self.strong.has(t) or self.names.has(t)
        full = norm(title + " " + it.get("summary", "")[:600])
        if cs_in(title + " " + it.get("summary", "")[:600]) or self.strong.has(full) or self.names.has(full):
            return True
        if self.weak.has(t):   # mot ambigu (ex. nom de ville) : seulement dans le titre
            if in_list(it["domain"], self.cfg.get("generalist_domains", [])):
                return self.football.has(full)
            return True
        return False
    def matched_name(self, it):
        t = norm(it["title"] + " " + it.get("summary", "")[:600])
        for p in self.cfg.get("players", []) + self.cfg.get("targets", []) + self.cfg.get("staff", []):
            for n in [p["name"]] + p.get("aliases", []) + p.get("search_aliases", []):
                if Matcher([n]).has(t):
                    return p["name"]
        return None
    def classify(self, it):
        text = norm(it["title"] + " " + it["summary"])
        tier = it["tier"]
        mercato, urgent = self.mercato.has(text), self.urgent.has(text)
        if tier == "competitor": cat = "veille"
        elif mercato: cat = "mercato"
        elif it.get("foreign") or self.selection.has(text) or self.interview.has(text) or self.life.has(text):
            cat = "joueurs"
        else: cat = "actu"
        level = "urgent" if (urgent and tier in ("official", "trusted") and cat != "veille") else "normal"
        critical = level == "urgent" and self.critical.has(text)
        return cat, level, critical

# ----------------------------------------------------------------- envoi Telegram

class Sender:
    def __init__(self, dry):
        self.dry, self.count = dry, 0
    def send(self, cat, text, silent):
        if self.dry:
            print(f"--- [{cat}] {'(silencieux)' if silent else '(SONNE)'}\n{re.sub('<[^>]+>', '', html.unescape(text))}\n")
            return True
        token = os.environ.get("TELEGRAM_BOT_TOKEN")
        chat = os.environ.get(f"TELEGRAM_CHAT_{cat.upper()}") or os.environ.get("TELEGRAM_CHAT_ID")
        if not token or not chat:
            print("⚠ TELEGRAM_BOT_TOKEN / TELEGRAM_CHAT_ID manquant", file=sys.stderr)
            return False
        payload = {"chat_id": chat, "text": text[:4000], "parse_mode": "HTML",
                   "disable_notification": silent, "disable_web_page_preview": False}
        thread = os.environ.get(f"TELEGRAM_THREAD_{cat.upper()}")
        if thread:
            payload["message_thread_id"] = int(thread)
        try:
            r = requests.post(f"https://api.telegram.org/bot{token}/sendMessage", json=payload, timeout=20)
            if not r.ok:
                print("⚠ Telegram:", r.text[:200], file=sys.stderr)
            time.sleep(1.1)
            return r.ok
        except Exception as ex:
            print("⚠ Telegram:", ex, file=sys.stderr)
            return False

CFG_LABELS = {}
BADGE = {"official": "✅ officiel", "trusted": "🟢 source fiable", "competitor": "🏁 concurrent", "other": "⚠️ à recouper"}

def translate(text, lang, cfg):
    if lang == "fr" or not cfg.get("translate_to_french") or not text:
        return None
    text = text[:400]
    try:   # point d'accès public de Google Traduction
        r = requests.get("https://translate.googleapis.com/translate_a/single",
                         params={"client": "gtx", "sl": "auto", "tl": "fr", "dt": "t", "q": text},
                         headers=UA, timeout=10)
        out = "".join(part[0] for part in r.json()[0] if part and part[0])
        if out.strip() and out.strip().lower() != text.strip().lower():
            return out.strip()
    except Exception:
        pass
    try:   # secours : MyMemory
        r = requests.get("https://api.mymemory.translated.net/get",
                         params={"q": text, "langpair": f"{lang}|fr"}, timeout=10)
        out = r.json().get("responseData", {}).get("translatedText", "")
        if out.strip() and out.strip().lower() != text.strip().lower():
            return html.unescape(out.strip())
    except Exception:
        pass
    return None

def fmt_alert(it, cat, level, kind, tz, extra=""):
    CAT_LABEL.update(CFG_LABELS)
    esc = html.escape
    head = {"urgent": "🔴 URGENT", "normal": "🔔"}.get(level, "•")
    if kind == "confirmed":
        head = "🟣 CONFIRMÉ"
    t = it["published"].astimezone(tz).strftime("%H:%M") if it.get("published") else "?"
    lines = [f"{head} · {CAT_EMOJI[cat]} {CAT_LABEL[cat]}"]
    if it.get("fr"):
        lines += [f"<b>{esc(it['fr'])}</b>", f"<i>VO : {esc(it['title'])}</i>"]
    else:
        lines.append(f"<b>{esc(it['title'])}</b>")
    lines.append(f"🗞 {esc(it['source'])} · {BADGE[it['tier']]} · 🕐 {t} · 🌐 {it['lang']}")
    if it.get("player"):
        lines.append(f"👤 {esc(it['player'])}")
    if extra:
        lines.append(extra)
    lines.append(f"🔗 {it['link']}")
    return "\n".join(lines)

def queue_entry(it, cat, tz):
    t = it["published"].astimezone(tz).strftime("%H:%M") if it.get("published") else "?"
    return {"cat": cat, "title": it.get("fr") or it["title"], "source": it["source"], "tier": it["tier"],
            "time": t, "link": it["link"], "lang": it["lang"]}

def send_digest(state, sender, label, silent=False):
    q = state["queue"]
    if not q:
        return
    order = ["mercato", "joueurs", "actu", "veille"]
    parts, cur = [], f"☀️ <b>{html.escape(label)}</b> ({len(q)} infos)\n"
    for cat in order:
        rows = [e for e in q if e["cat"] == cat]
        if not rows:
            continue
        block = f"\n{CAT_EMOJI[cat]} <b>{CAT_LABEL[cat]}</b>\n"
        for e in rows[:40]:
            block += (f"• {html.escape(e['title'][:160])} — {html.escape(e['source'])} "
                      f"{BADGE[e['tier']].split()[0]} {e['time']}\n{e['link']}\n")
        if len(cur) + len(block) > 3800:
            parts.append(cur); cur = ""
        cur += block
    parts.append(cur)
    for p in parts:
        sender.send("actu", p, silent=silent)
    state["queue"] = []

# ----------------------------------------------------------------- moteur

def process(items, cfg, state, now, sender, bootstrap):
    tz = ZoneInfo(cfg["timezone"])
    local = now.astimezone(tz)
    wh = cfg["work_hours"]
    in_hours = wh["start"] <= local.hour < wh["end"]
    rules = Rules(cfg)
    fresh_cut = now - timedelta(hours=cfg["freshness_hours"])
    win = timedelta(minutes=cfg["confirm_window_minutes"])
    state["clusters"] = [c for c in state["clusters"]
                         if datetime.fromisoformat(c["first"]) > now - timedelta(hours=6)]
    items.sort(key=lambda i: i["published"] or now)
    sent = 0
    for it in items:
        if it["id"] in state["seen"]:
            continue
        if sent >= cfg["max_alerts_per_run"]:
            break                      # pas marqué "vu" : partira au passage suivant
        state["seen"][it["id"]] = time.time()
        if bootstrap:
            continue
        if it["published"] is None and it.get("undated_ok"):
            it["published"] = now      # page web : détecté maintenant
        if it["published"] is None and not it.get("undated_ok"):
            continue                   # pas de date fiable : on ignore (évite les vieux articles)
        if it["published"] and it["published"] < fresh_cut:
            continue                   # plus de 3 h : trop vieux, jamais envoyé
        fm = cfg.get("freshness_minutes", {}).get(it.get("speed", "fast"))
        late = bool(fm and it["published"] and it["published"] < now - timedelta(minutes=fm))
        it["late_min"] = int((now - it["published"]).total_seconds() // 60) if late else 0
        mdate = re.search(r"(20\d\d)[/-](\d\d)[/-](\d\d)", it["link"])
        if mdate:
            try:
                if datetime(int(mdate[1]), int(mdate[2]), int(mdate[3]), tzinfo=timezone.utc) < now - timedelta(days=2):
                    continue
            except ValueError:
                pass
        it["tier"] = rules.tier(it)
        if in_list(it["domain"], cfg.get("own_domains", [])):
            continue
        if it["tier"] == "other" and not cfg.get("allow_unknown_sources", False):
            continue                   # uniquement les médias sérieux listés
        if not rules.relevant(it):
            continue                   # hors sujet
        tk = tokens(it["title"])
        cl = next((c for c in state["clusters"]
                   if jaccard(tk, set(c["tokens"])) >= 0.5 and now - datetime.fromisoformat(c["first"]) < win * 4), None)
        if cl:
            if it["domain"] not in cl["sources"]:
                cl["sources"].append(it["domain"]); cl["names"].append(it["source"])
            if (len(cl["sources"]) >= cfg["confirm_sources"] and not cl["confirmed"]
                    and cl["cat"] in ("mercato", "actu")):
                cl["confirmed"] = True
                extra = f"🟣 Repris par {len(cl['sources'])} médias : " + html.escape(", ".join(cl["names"][:6]))
                it["fr"] = translate(it["title"], it["lang"], cfg)
                sender.send(cl["cat"], fmt_alert(it, cl["cat"], "urgent", "confirmed", tz, extra), silent=not in_hours)
                sent += 1
            continue
        cat, level, critical = rules.classify(it)
        it["player"] = it.get("player") or rules.matched_name(it)
        state["clusters"].append({"tokens": sorted(tk), "first": now.isoformat(), "sources": [it["domain"]],
                                  "names": [it["source"]], "confirmed": False, "cat": cat})
        it["fr"] = translate(it["title"], it["lang"], cfg)
        if in_hours:
            silent = cat == "veille"
        else:
            silent = not critical      # la nuit : tout arrive, mais ne sonne que si c'est critique
        extra = ""
        if it.get("late_min"):         # reçu en retard (lenteur de la source) : envoyé quand même, sans son
            silent = True
            extra = f"⏳ Publié il y a {it['late_min']} min (source lente)"
        sender.send(cat, fmt_alert(it, cat, level, "alert", tz, extra), silent=silent)
        sent += 1
    return sent

# ----------------------------------------------------------------- main

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--no-bootstrap", action="store_true")
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--diag", action="store_true", help="diagnostic des sources envoyé sur Telegram")
    ap.add_argument("--test-telegram", action="store_true")
    ap.add_argument("--get-chat-id", action="store_true")
    ap.add_argument("--loop", type=float, default=0, help="tourner en boucle pendant N minutes")
    ap.add_argument("--verbose", action="store_true")
    ap.add_argument("--interval", type=int, default=30, help="secondes entre deux passages en boucle")
    a = ap.parse_args()
    cfg = load_config()
    CFG_LABELS.update(cfg.get("labels", {}))
    if a.get_chat_id:
        tok = os.environ.get("TELEGRAM_BOT_TOKEN")
        r = requests.get(f"https://api.telegram.org/bot{tok}/getUpdates", timeout=20).json()
        seen = {(u.get("message") or u.get("channel_post") or {}).get("chat", {}).get("id") for u in r.get("result", [])}
        print("chat_id trouvés :", [s for s in seen if s] or "aucun (écris d'abord un message au bot)")
        return
    if a.test_telegram:
        ok = Sender(False).send("actu", "✅ Connexion Telegram OK.", silent=False)
        print("OK" if ok else "Échec"); return
    if a.check or a.diag:
        collect(cfg, check="telegram" if a.diag else True); return
    deadline = time.time() + a.loop * 60
    while True:
        state = load_state()
        bootstrap = (not state["seen"]) and not a.no_bootstrap
        t = time.time()
        fast_due = bootstrap or t - state.get("last_fast", 0) >= cfg.get("google_fast_minutes", 2) * 60
        slow_due = bootstrap or t - state.get("last_slow", 0) >= cfg.get("slow_sources_minutes", 30) * 60
        speeds = {"direct"} | ({"fast"} if fast_due else set()) | ({"slow"} if slow_due else set())
        items = collect(cfg, speeds=speeds, verbose=a.verbose)
        if fast_due: state["last_fast"] = t
        if slow_due: state["last_slow"] = t
        sender = Sender(a.dry_run)
        n = process(items, cfg, state, now_utc(), sender, bootstrap)
        print(f"{datetime.now().strftime('%H:%M:%S')} : {len(items)} articles lus"
              f"{' [+google]' if fast_due else ''}{' [+étranger]' if slow_due else ''}, {n} alertes envoyées"
              + (" (premier lancement : état initialisé, rien envoyé)" if bootstrap else ""), flush=True)
        if not a.dry_run:
            save_state(state)
        if a.loop <= 0 or time.time() + a.interval > deadline:
            break
        time.sleep(a.interval)

if __name__ == "__main__":
    main()
