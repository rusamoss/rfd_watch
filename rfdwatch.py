#!/usr/bin/env python3
"""
rfdwatch.py

Tracks individual RfD nominations per subscribed editor. Reads the opt-in list at SUBSCRIBERS_PAGE, then for
each registered username reads/writes User:<username>/RfD subscriptions.

Detection order per section:
  - closed: the standard XfD-close boilerplate ("...xfd-closed..." class,
    inserted by tools like XFDcloser) is a permanent, reliable marker --
    once seen, the result is extracted and the entry is left alone for
    good (still expires normally, just never re-checked).
  - relisted: a "'''Relisted''', see [[NewLogPage#NewHeading]]" pointer
    moves tracking to the new section and drops the old one. Reported as "relisted" until the
    section it lands on picks up a real edit.
  - otherwise: every wiki-signature timestamp in the section is found directly (no state to
    persist), and the newest one is compared against what's already on record -- catching a
    real edit regardless of what tool made it, since some (e.g. XfD vote-listing scripts)
    don't produce MediaWiki's usual "/* Heading */" auto-summary that a comment-based check
    alone would depend on. Reported as "updated", timestamped from that marker when the
    responsible edit happens to have one, else from the signature itself. A section with no
    prior record and only one signature is reported as "created" from it instead (more than
    one means real activity already exists beyond the nomination, so it's "updated" even the
    first time); with no signature at all, it's "added" from now.

The page is sorted newest-change-first.

Subscriptions expire when their log page is more than EXPIRY_DAYS old.
Twinkle's own nomination log is a permanent record keyed to each
nomination's *original* location, so self-nom rediscovery matches by title
rather than by that original key -- otherwise a relisted nomination (whose
key moves) would look "new" again every run and get endlessly re-relisted.
"""

import os
import re
import sys
import traceback
from datetime import datetime, timedelta, timezone
from typing import Dict, List, Optional, Tuple

# Must happen before importing pywikibot: without this, config resolution
# falls back to the invoking process's cwd (unpredictable under cron),
# which could pick up a different project's user-config.py/credentials
# (e.g. scripts/'s, logged in as a different account entirely).
os.environ["PYWIKIBOT_DIR"] = os.path.dirname(os.path.abspath(__file__))

import pywikibot  # noqa: E402 -- see PYWIKIBOT_DIR comment above

BOT_USERNAME = "Rusabot"
CONTACT_URL = f"https://en.wikipedia.org/wiki/User:{BOT_USERNAME}"
READ_THROTTLE_SECONDS = 0.5

SUBSCRIBERS_PAGE = "User:Rusabot/RfD subscribers"
EXPIRY_DAYS = 49  # don't exceed action=query's 50 titles= limit
MAX_RELIST_HOPS = 10

MONTH_NAMES = [
    "January", "February", "March", "April", "May", "June",
    "July", "August", "September", "October", "November", "December",
]

# One line looks like: * [[User:Alice]]
SUBSCRIBER_RE = re.compile(r"^\*+\s*\[\[\s*[Uu]ser\s*:\s*([^\]|#]+?)\s*[\]|]", re.MULTILINE)

# Matches one Twinkle XfD-log line for an RfD nomination, e.g.:
# # [[:'Two Suns of Japan']]: [[Wikipedia:Redirects for discussion/Log/2025 March 27#'Two Suns of Japan'|nominated]] at [[WP:RFD|RfD]]; ...
# A bundled nomination lists more targets before the colon, e.g. "[[:A]]; [[:B]]: [[...|nominated]]..."
# -- group 1 (used as the display title) is just the first one, since they share one log_page/anchor.
SELF_NOM_RE = re.compile(
    r"^#\s*\[\[:([^\]|]+)(?:\|[^\]]*)?\]\](?:;\s*\[\[:[^\]|]+(?:\|[^\]]*)?\]\])*:\s*"
    r"\[\[(Wikipedia:Redirects for discussion/Log/[^#\]|]+)#([^\]|]+)\|nominated\]\]\s*at\s*\[\[WP:RFD\|RfD\]\]",
    re.MULTILINE,
)

# A wiki-signature timestamp, e.g. "04:25, 6 September 2026 (UTC)" -- Twinkle appends one to
# its own log line as the real nomination time; searched separately so a missing one is harmless.
WIKI_SIGNATURE_TIME_RE = re.compile(r"(\d{1,2}):(\d{2}), (\d{1,2}) ([A-Za-z]+) (\d{4}) \(UTC\)")

# The standard XfD-close boilerplate's CSS class (shared across venues, inserted
# by {{Rfd top}} and equivalents) -- permanent once present, so this alone means closed.
CLOSE_RE = re.compile(r"xfd-closed")
# The template inserts markup (e.g. </noinclude>) between "was" and the bold
# result -- DOTALL lets .*? skip past it to the nearest bold text.
CLOSE_RESULT_RE = re.compile(r"result of the discussion was.*?'''([^']*)'''", re.IGNORECASE | re.DOTALL)

# Matches a relist pointer, e.g. '''Relisted''', see [[LogPage#Heading]] -- the delimiter is
# sometimes "#" and sometimes "%23" (seen in practice), normalized before splitting. No DOTALL,
# so an earlier "Relisted" mention can't match a later line's unrelated link.
RELIST_RE = re.compile(r"'''Relisted'''.*?\[\[([^\]|]+)\]\]")

# One resolved subscription line looks like:
# * [[LogPage#Anchor|Title]] — updated 02:56, 6 September 2026 (UTC)<!--last:2026-09-06T02:56:53Z|updated-->
# An unresolved (never-yet-checked) subscription is just the bare link.
SUB_LINE_RE = re.compile(r"^\*\s*\[\[([^\]#]+)#([^\]|]+)\|([^\]]+)\]\](?:.*<!--last:([^|>]*)\|([^>]*)-->)?\s*$")

HEADING_RE = re.compile(r"^====\s*(.+?)\s*====\s*$")
STOP_RE = re.compile(r"^(===|====)")


def now_iso() -> str:
    """Matches JS's `new Date().toISOString()` format (millisecond precision)."""
    return datetime.now(timezone.utc).isoformat(timespec="milliseconds").replace("+00:00", "Z")


def parse_subscribers(wikitext: Optional[str]) -> List[str]:
    if not wikitext:
        return []
    return [m.group(1) for m in SUBSCRIBER_RE.finditer(wikitext)]


def find_signature_times(text: str) -> List[str]:
    """Every wiki-signature timestamp in text, in document order (oldest first, since replies
    are appended below earlier ones per standard discussion convention), as ISO 8601. Locale-
    independent like parse_log_date -- wiki signatures are always English regardless of locale."""
    times = []
    for m in WIKI_SIGNATURE_TIME_RE.finditer(text):
        hour, minute, day, month_str, year = m.groups()
        try:
            month = MONTH_NAMES.index(month_str) + 1
            dt = datetime(int(year), month, int(day), int(hour), int(minute), tzinfo=timezone.utc)
        except ValueError:
            continue
        times.append(dt.strftime("%Y-%m-%dT%H:%M:%SZ"))
    return times


def parse_wiki_timestamp(text: str) -> Optional[str]:
    """The first wiki-signature timestamp in text (e.g. Twinkle's own log-line signature), or None."""
    times = find_signature_times(text)
    return times[0] if times else None


def parse_self_noms(wikitext: str) -> List[Dict[str, str]]:
    noms = []
    for m in SELF_NOM_RE.finditer(wikitext):
        line_end = wikitext.find("\n", m.end())
        rest_of_line = wikitext[m.end():line_end if line_end != -1 else len(wikitext)]
        noms.append({
            "title": m.group(1),
            "log_page": m.group(2),
            "anchor": m.group(3),
            "logged_at": parse_wiki_timestamp(rest_of_line) or "",
        })
    return noms


def find_close_result(section_text: str) -> Optional[str]:
    if not CLOSE_RE.search(section_text):
        return None
    m = CLOSE_RESULT_RE.search(section_text)
    result = m.group(1).strip() if m else ""
    # '>' would break the <!--last:...|...--> comment's own [^>]* field on
    # the next parse, silently dropping the subscription line entirely.
    result = result.replace(">", "")
    return result or "closed"


def find_relist_target(section_text: str) -> Optional[Tuple[str, str]]:
    m = RELIST_RE.search(section_text)
    if not m:
        return None
    target = re.sub(r"%23", "#", m.group(1), flags=re.IGNORECASE)
    hash_index = target.find("#")
    if hash_index == -1:
        return None
    return target[:hash_index], target[hash_index + 1:]


def parse_log_date(log_page: str) -> Optional[datetime]:
    """"Wikipedia:Redirects for discussion/Log/2025 March 27" -> datetime, or None."""
    date_str = log_page.rsplit("/", 1)[-1]
    parts = date_str.split(" ")
    if len(parts) != 3:
        return None
    year_str, month_str, day_str = parts
    try:
        month = MONTH_NAMES.index(month_str) + 1
        return datetime(int(year_str), month, int(day_str), tzinfo=timezone.utc)
    except ValueError:
        return None


def is_expired(log_page: str) -> bool:
    d = parse_log_date(log_page)
    if d is None:  # unparseable date: don't drop something we can't judge the age of
        return False
    return datetime.now(timezone.utc) - d > timedelta(days=EXPIRY_DAYS)


def is_closed(sub: Dict[str, str]) -> bool:
    return sub["last_kind"].startswith("closed:")


def extract_section(wikitext: str, heading: str) -> Optional[str]:
    """Extracts one level-4 (====) section's full text by exact heading text, stopping at the next level-3 or level-4 heading."""
    lines = wikitext.split("\n")
    start = None
    for i, line in enumerate(lines):
        m = HEADING_RE.match(line)
        if m and m.group(1) == heading:
            start = i
            break
    if start is None:
        return None
    end = len(lines)
    for j in range(start + 1, len(lines)):
        if STOP_RE.match(lines[j]):
            end = j
            break
    return "\n".join(lines[start:end])


def sub_key(log_page: str, anchor: str) -> str:
    return f"{log_page}#{anchor}"


def format_human_time(iso: str) -> str:
    """"02:56, 6 September 2026 (UTC)" -- matches the standard wiki-signature timestamp format."""
    dt = datetime.fromisoformat(iso.replace("Z", "+00:00"))
    return f"{dt:%H:%M}, {dt.day} {MONTH_NAMES[dt.month - 1]} {dt.year} (UTC)"


def phrase_for_kind(kind: str) -> str:
    if kind == "relisted":
        return "relisted"
    if kind == "created":
        return "created"
    if kind == "added":
        return "added"
    if kind.startswith("closed:"):
        return "closed as " + kind[len("closed:"):]
    return "updated"


def parse_subscriptions(wikitext: Optional[str]) -> Dict[str, Dict[str, str]]:
    subs: Dict[str, Dict[str, str]] = {}
    if not wikitext:
        return subs
    for line in wikitext.split("\n"):
        m = SUB_LINE_RE.match(line)
        if not m:
            continue
        log_page, anchor, title, last_change, last_kind = m.groups()
        subs[sub_key(log_page, anchor)] = {
            "log_page": log_page,
            "anchor": anchor,
            "title": title,
            "last_change": last_change or "",
            "last_kind": last_kind or "",
        }
    return subs


def serialize_subscriptions(subs: Dict[str, Dict[str, str]]) -> str:
    """Sorted newest-change-first for a chronological feed -- sorting here (not nudging a
    changed entry in the dict) keeps that true even when many entries change in one run."""
    lines = []
    for s in sorted(subs.values(), key=lambda s: s["last_change"], reverse=True):
        link = f"[[{s['log_page']}#{s['anchor']}|{s['title']}]]"
        if not s["last_change"]:
            lines.append(f"* {link}")
        else:
            phrase = phrase_for_kind(s["last_kind"])
            human = format_human_time(s["last_change"])
            lines.append(f"* {link} — {phrase} {human}<!--last:{s['last_change']}|{s['last_kind']}-->")
    return "\n".join(lines) + "\n"


def discover_self_noms(subs: Dict[str, Dict[str, str]], xfd_log_wikitext: Optional[str]) -> bool:
    """Returns True if anything was added."""
    if not xfd_log_wikitext:
        return False
    added = False
    tracked_titles = {s["title"] for s in subs.values()}
    for n in parse_self_noms(xfd_log_wikitext):
        key = sub_key(n["log_page"], n["anchor"])
        if key not in subs and n["title"] not in tracked_titles and not is_expired(n["log_page"]):
            subs[key] = {
                "title": n["title"],
                "log_page": n["log_page"],
                "anchor": n["anchor"],
                "last_change": n["logged_at"],
                "last_kind": "created" if n["logged_at"] else "",
            }
            tracked_titles.add(n["title"])
            added = True
    return added


def prune_expired(subs: Dict[str, Dict[str, str]]) -> bool:
    """Returns True if anything was removed."""
    expired_keys = [key for key, s in subs.items() if is_expired(s["log_page"])]
    for key in expired_keys:
        del subs[key]
    return bool(expired_keys)


def find_last_change_for_anchor(history: List[Dict[str, str]], anchor: str) -> Optional[str]:
    """Newest revision (history is newest-first) whose edit summary carries MediaWiki's auto-generated "/* Heading */" section marker."""
    marker = f"/* {anchor} */"
    for rev in history:
        comment = rev.get("comment")
        if comment and marker in comment:
            return rev["timestamp"]
    return None


def get_wikitext_batch(site: "pywikibot.site.APISite", titles: List[str]) -> Dict[str, Optional[str]]:
    """Current content for many titles at once, via preloadpages -- keyed by the input string itself
    (not pywikibot's possibly-normalized Page.title()), matching what callers parsed from wikitext."""
    pages = {title: pywikibot.Page(site, title) for title in titles}
    for _ in site.preloadpages(list(pages.values())):
        pass  # preloadpages mutates the Page objects in place
    return {title: (page.text if page.exists() else None) for title, page in pages.items()}


def get_history(site: "pywikibot.site.APISite", title: str) -> List[Dict[str, str]]:
    """Newest-first revision history (timestamp + comment, no content), capped like the JS original's
    rvlimit=max -- only the newest few revisions are ever needed for a section's last change."""
    page = pywikibot.Page(site, title)
    if not page.exists():
        return []
    return [
        {"timestamp": rev.timestamp.strftime("%Y-%m-%dT%H:%M:%SZ"), "comment": rev.comment or ""}
        for rev in page.revisions(content=False, total=500)
    ]


def resolve_relist_chain(
    site: "pywikibot.site.APISite",
    by_content: Dict[str, Optional[str]],
    by_history: Dict[str, List[Dict[str, str]]],
    log_page: str,
    anchor: str,
    section_text: str,
) -> Tuple[str, str, str, bool, Optional[str]]:
    """Follows '''Relisted''' pointers to a section's current location. A discussion can hop log
    pages several times between runs (each hop leaves a pointer at the old page and moves the
    discussion to the new one); walking the whole chain here avoids getting stuck one hop behind.
    Each hop's content/history is fetched on demand and cached into by_content/by_history for
    reuse by other subs this run. Returns (log_page, anchor, section_text, was_relisted,
    last_relist_time) for wherever the chain ends -- last_relist_time is the on-wiki time of
    the final hop taken.
    """
    was_relisted = False
    last_relist_time = None
    for _ in range(MAX_RELIST_HOPS):
        relist_target = find_relist_target(section_text)
        if not relist_target:
            break
        new_log_page, new_anchor = relist_target
        if (new_log_page, new_anchor) == (log_page, anchor):
            break  # self-referential pointer -- nowhere to go

        if new_log_page not in by_content:
            by_content[new_log_page] = get_wikitext_batch(site, [new_log_page]).get(new_log_page)
        new_wikitext = by_content[new_log_page]
        if not new_wikitext:
            break  # target page unreadable this run -- stop where we are

        new_section_text = extract_section(new_wikitext, new_anchor)
        if new_section_text is None:
            break  # target section not found this run -- stop where we are

        last_relist_time = find_last_change_for_anchor(by_history.get(log_page, []), anchor) or last_relist_time
        was_relisted = True
        if new_log_page not in by_history:
            by_history[new_log_page] = get_history(site, new_log_page)

        log_page, anchor, section_text = new_log_page, new_anchor, new_section_text

    return log_page, anchor, section_text, was_relisted, last_relist_time


def check_for_updates(site: "pywikibot.site.APISite", subs: Dict[str, Dict[str, str]]) -> Tuple[bool, bool]:
    """Mutates `subs` in place. Returns (changed, notable) -- safe to mutate directly since
    there's only one page and one edit per user, so it either fully lands or fully doesn't.
    "notable" is False when the only changes were "created"/"added" states: the subscriber
    already knows about those (they made the nom or subscribed themselves), so callers can
    use it to mark a save minor when nothing worth seeing on a watchlist actually happened."""
    keys = [key for key, s in subs.items() if not is_closed(s)]
    if not keys:
        return False, False

    log_pages = list(dict.fromkeys(subs[key]["log_page"] for key in keys))  # unique, order-preserving
    by_content = get_wikitext_batch(site, log_pages)
    by_history = {page: get_history(site, page) for page in log_pages}

    changed = False
    notable = False
    for key in keys:
        sub = subs[key]
        wikitext = by_content.get(sub["log_page"])
        if not wikitext:
            continue  # page unreadable this run -- leave alone

        section_text = extract_section(wikitext, sub["anchor"])
        if section_text is None:
            continue  # section not found this run -- leave alone

        log_page, anchor, section_text, was_relisted, last_relist_time = resolve_relist_chain(
            site, by_content, by_history, sub["log_page"], sub["anchor"], section_text
        )
        new_key = sub_key(log_page, anchor)
        if new_key != key and new_key in subs:
            # Another of this user's subs already resolved to the same current
            # location -- keep both entries rather than clobbering one.
            print(f"[warn] {new_key} already tracked; leaving {key} as-is", file=sys.stderr)
            continue

        # The actual on-wiki edit time -- closing is itself a section edit, so this is the
        # real event time, not just when this script happens to run.
        event_time = find_last_change_for_anchor(by_history.get(log_page, []), anchor)
        close_result = find_close_result(section_text)

        if new_key != key:
            del subs[key]
            sub["log_page"], sub["anchor"] = log_page, anchor

        if close_result:
            sub["last_change"] = event_time or last_relist_time or now_iso()
            sub["last_kind"] = f"closed:{close_result}"
            subs[new_key] = sub
            changed = True
            notable = True
            continue

        if was_relisted:
            # Landed on a new section this run -- report the relist itself; a real edit since
            # then surfaces as "updated" on a later run, once tracked under this key.
            sub["last_change"] = last_relist_time or now_iso()
            sub["last_kind"] = "relisted"
            subs[new_key] = sub
            changed = True
            notable = True
            continue

        signatures = find_signature_times(section_text)

        if not sub["last_kind"]:
            # Never resolved yet. More than one signature already present (e.g. subscribed via
            # the button to an already-active discussion) means real activity beyond the
            # nomination -- report "updated", using the latest one, rather than "created".
            if len(signatures) > 1:
                sub["last_change"] = event_time or signatures[-1]
                sub["last_kind"] = "updated"
            elif signatures:
                sub["last_change"] = signatures[0]
                sub["last_kind"] = "created"
            else:
                sub["last_change"] = now_iso()
                sub["last_kind"] = "added"
            changed = True
        elif signatures:
            latest = signatures[-1]
            # Compare at minute precision: history-derived timestamps (event_time,
            # last_relist_time) carry seconds a wiki signature never can, so exact string
            # equality would look like a fresh change every time right after a relist or close.
            if latest[:16] != (sub["last_change"] or "")[:16]:
                # A newer signature exists -- some tool (e.g. an XfD vote-listing script)
                # may not produce MediaWiki's auto section-comment marker for event_time to
                # find, so this is what actually catches the change; event_time just gives a
                # more precise timestamp for it when the responsible edit happens to have one.
                sub["last_change"] = event_time or latest
                sub["last_kind"] = "updated"
                changed = True
                notable = True

    return changed, notable


def process_user(site: "pywikibot.site.APISite", username: str, retries_left: int = 1) -> None:
    xfd_log_page = pywikibot.Page(site, f"User:{username}/XfD log")
    subscriptions_page = pywikibot.Page(site, f"User:{username}/RfD subscriptions")

    subs = parse_subscriptions(subscriptions_page.text if subscriptions_page.exists() else None)

    added = discover_self_noms(subs, xfd_log_page.text if xfd_log_page.exists() else None)
    pruned = prune_expired(subs)
    changed, notable = check_for_updates(site, subs)

    if not (added or pruned or changed):
        print(f"[info] {username}: nothing to update", file=sys.stderr)
        return

    # subscriptions_page.text was already read above (to parse `subs`), so
    # pywikibot has the revision it's based on and passes that as
    # basetimestamp automatically -- a concurrent edit (e.g. the subscriber
    # hand-editing their own list) raises EditConflictError instead of
    # being silently overwritten.
    subscriptions_page.text = serialize_subscriptions(subs)
    # Minor unless something notable happened (relist/close/reply) -- a new self-nom or an
    # expired prune isn't news to the subscriber, so it's minor-hideable from their watchlist.
    try:
        subscriptions_page.save(
            summary="Updating RfD subscriptions ([[Wikipedia:Bots/Requests for approval/Rusabot 2|BRFA]])",
            bot=True,
            minor=not notable,
            apply_cosmetic_changes=False,
        )
    except pywikibot.exceptions.EditConflictError:
        if retries_left > 0:
            process_user(site, username, retries_left - 1)
        else:
            print(f"[warn] {username}: edit conflict, giving up after retry", file=sys.stderr)
        return
    print(f"[info] {username}: updated", file=sys.stderr)


def main() -> None:
    pywikibot.config.user_agent_description = f"RfDWatch; {CONTACT_URL}"
    site = pywikibot.Site("en", "wikipedia")
    site.throttle.set_delays(delay=READ_THROTTLE_SECONDS)
    site.login()

    subscribers_page = pywikibot.Page(site, SUBSCRIBERS_PAGE)
    usernames = parse_subscribers(subscribers_page.text if subscribers_page.exists() else None)
    if not usernames:
        print(f"[warn] no subscribers found on {SUBSCRIBERS_PAGE}", file=sys.stderr)
        return

    for username in usernames:
        try:
            process_user(site, username)
        except Exception:  # one subscriber's failure must not stop the rest
            print(f"[error] {username}:\n{traceback.format_exc()}", file=sys.stderr)


if __name__ == "__main__":
    main()
