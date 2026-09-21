#!/usr/bin/env python3
"""
Lincolnwood SD74 lunch menu fetcher
====================================

Pulls the school lunch (and optionally breakfast) menus from MealViewer and
writes them to menu.json, then refreshes the offline copy baked into
index.html so the page is never blank.

Where the data comes from
--------------------------
schools.mealviewer.com is a JavaScript app -- its page HTML is an empty
shell, so there's nothing useful to scrape from it. The app is fed by a
public, unauthenticated JSON API:

    https://api.mealviewer.com/api/v4/school/<schoolKey>/<MM-DD-YYYY>/<MM-DD-YYYY>/

This script uses that endpoint directly. JSON with explicit dates is far more
reliable than scraping rendered text.

A note on parsing
------------------
MealViewer's response shape is undocumented and has varied between districts
and versions, so the extractor below walks the structure by *looking for*
date fields and food-item fields rather than assuming one fixed set of key
names. If it still can't find anything, it prints a structural dump of what
it actually received so the problem can be diagnosed from the log instead of
guessed at.

Run locally:
    pip install requests
    python3 fetch_menu.py
"""

import json
import os
import re
import sys
import time
from datetime import date, datetime, timedelta, timezone

import requests

# --- Configuration ---------------------------------------------------------

# The key in the MealViewer URL. From
# schools.mealviewer.com/school/LincolnwoodSchoolDistrict74
# If the district later splits menus per building, add those keys here and
# each will appear as its own tab on the page.
SCHOOL_KEYS = ["LincolnwoodSchoolDistrict74"]

API = "https://api.mealviewer.com/api/v4/school/{key}/{start}/{end}/"

DAYS_BEHIND = 7      # keep a little history so "today" always has context
DAYS_AHEAD = 70      # far enough to cover all of next month

# Meal periods to keep, in display order. Add "Breakfast" if wanted.
MEALS = ["Lunch", "Breakfast"]

# Food categories worth showing, in order. Anything not listed still appears,
# just after these. Condiments are dropped -- they're noise on a menu board.
TYPE_ORDER = ["Entree", "Entrees", "Main", "Side", "Sides", "Vegetable",
              "Vegetables", "Fruit", "Fruits", "Grain", "Milk"]
SKIP_TYPES = {"condiment", "condiments"}

HEADERS = {
    "User-Agent": "SD74LunchMenuBot/1.0 (parent-run menu sync)",
    "Accept": "application/json",
}
TIMEOUT = 25
ATTEMPTS = 3
RETRY_WAIT = 2

INDEX_FILE = "index.html"
URL_REGION_RE = re.compile(r'(/\*URL_START\*/).*?(/\*URL_END\*/)', re.DOTALL)
FALLBACK_REGION_RE = re.compile(r'(/\*FALLBACK_START\*/).*?(/\*FALLBACK_END\*/)', re.DOTALL)


# --- Networking ------------------------------------------------------------

def fetch_json(url):
    last = None
    for attempt in range(1, ATTEMPTS + 1):
        try:
            r = requests.get(url, headers=HEADERS, timeout=TIMEOUT)
            r.raise_for_status()
            return r.json()
        except Exception as e:
            last = e
            if attempt < ATTEMPTS:
                print(f"    (attempt {attempt} failed: {e} -- retrying)", file=sys.stderr)
                time.sleep(RETRY_WAIT)
    raise last


# --- Tolerant extraction ---------------------------------------------------

DATE_KEYS = ("dateFull", "date_full", "date", "menuDate", "servingDate")
NAME_KEYS = ("item_Name", "itemName", "name", "menuItemDescription", "description")
TYPE_KEYS = ("item_Type", "itemType", "type", "category", "menuCategory")
BLOCK_NAME_KEYS = ("blockName", "block_Name", "mealPeriod", "name", "menuBlockName")

DATE_PATTERNS = (
    "%m/%d/%Y", "%Y-%m-%d", "%m-%d-%Y",
    "%m/%d/%Y %I:%M:%S %p", "%Y-%m-%dT%H:%M:%S",
)


def first_key(d, keys):
    for k in keys:
        if isinstance(d, dict) and d.get(k) not in (None, ""):
            return d[k]
    return None


def parse_any_date(value):
    if not isinstance(value, str):
        return None
    v = value.strip()
    for p in DATE_PATTERNS:
        try:
            return datetime.strptime(v[:len(datetime.now().strftime(p)) + 4], p).date()
        except ValueError:
            continue
    m = re.search(r'(\d{4})-(\d{2})-(\d{2})', v)
    if m:
        try:
            return date(int(m.group(1)), int(m.group(2)), int(m.group(3)))
        except ValueError:
            pass
    m = re.search(r'(\d{1,2})/(\d{1,2})/(\d{4})', v)
    if m:
        try:
            return date(int(m.group(3)), int(m.group(1)), int(m.group(2)))
        except ValueError:
            pass
    return None


def iter_dicts(node):
    """Every dict anywhere inside a nested JSON structure."""
    if isinstance(node, dict):
        yield node
        for v in node.values():
            yield from iter_dicts(v)
    elif isinstance(node, list):
        for v in node:
            yield from iter_dicts(v)


# Nutrition facts and allergen entries are shaped just like food items --
# they're objects with a "name" -- so they have to be excluded deliberately
# or the menu fills up with "Calcium (mg)", "Wheat", "No Known Allergens".

# 1. Never descend into a branch whose key says it holds nutrition/allergens.
SKIP_BRANCH_RE = re.compile(r'nutrient|nutrition|allergen|vitamin|mineral', re.IGNORECASE)

# 2. Reject names that are obviously a measurement or an allergen label.
NUTRIENT_NAME_RE = re.compile(
    r'^\s*(calories|calorie|protein|sodium|sugars?|fiber|fibre|cholesterol|'
    r'potassium|calcium|iron|carbohydrates?|total\s+carbs?|total\s+fat|'
    r'sat\.?\s*fat|saturated\s+fat|trans\s*fat|vitamin\s+\w+|serving\s+size)'
    r'\b|\((?:mg|g|iu|mcg|kcal)\)\s*$', re.IGNORECASE)

ALLERGEN_NAME_RE = re.compile(
    r'^\s*(no known allergens|contains|may contain|wheat|soy|soybeans?|milk|egg|eggs|'
    r'peanuts?|tree\s*nuts?|fish|shellfish|sesame|gluten|dairy)\s*$', re.IGNORECASE)


def looks_like_food(name, itype):
    """Filter out nutrition/allergen rows that share the food-item shape."""
    if NUTRIENT_NAME_RE.search(name):
        return False
    # "Milk" and "Egg" are real allergen labels but also real menu items --
    # so only reject them when they arrive with no food category attached.
    if not itype and ALLERGEN_NAME_RE.match(name):
        return False
    if itype.lower() in SKIP_TYPES:
        return False
    return True


def collect_items(node, _key_path=""):
    """Food items under this node, skipping nutrition and allergen branches."""
    out = []

    def walk(n, key_name=""):
        if SKIP_BRANCH_RE.search(key_name or ""):
            return                          # don't descend at all
        if isinstance(n, dict):
            name = first_key(n, NAME_KEYS)
            itype = first_key(n, TYPE_KEYS)
            itype = itype.strip() if isinstance(itype, str) else ""
            if isinstance(name, str):
                nm = name.strip()
                # A container (a line or block) also has a name; a real item
                # is a leaf -- it holds no further non-nutrition collections.
                has_children = any(
                    isinstance(v, (list, dict)) and v
                    for k, v in n.items() if not SKIP_BRANCH_RE.search(k))
                if nm and len(nm) <= 120 and not has_children \
                        and looks_like_food(nm, itype):
                    out.append({"name": nm, "type": itype})
            for k, v in n.items():
                walk(v, k)
        elif isinstance(n, list):
            for v in n:
                walk(v, key_name)

    walk(node, _key_path)

    # If anything arrived with a real category, trust those and drop the
    # untyped leftovers -- stray metadata almost never carries a type.
    typed = [it for it in out if it["type"]]
    if typed:
        out = typed

    seen, uniq = set(), []
    for it in out:
        k = it["name"].lower()
        if k in seen:
            continue
        seen.add(k)
        uniq.append(it)
    return uniq


def type_rank(itype):
    """Position of a food category in TYPE_ORDER, matching loosely so
    variants like "Main Dish" or "Entrees" rank with "Entree"."""
    t = (itype or "").strip().lower()
    if not t:
        return len(TYPE_ORDER)
    for i, known in enumerate(TYPE_ORDER):
        k = known.lower()
        if t == k or t.startswith(k) or k.startswith(t):
            return i
    if re.search(r'entr|main|hot\s*food|featured', t):
        return 0          # any other way of saying "entree" still leads
    return len(TYPE_ORDER)


def sort_items(items):
    return sorted(items, key=lambda it: (type_rank(it["type"]), it["name"].lower()))


def extract_days(payload):
    """{ 'YYYY-MM-DD': { 'Lunch': [items], ... } } from a MealViewer response."""
    days = {}

    # Prefer an explicit schedule list if one is present; otherwise scan the
    # whole payload for dict nodes that carry a date.
    candidates = None
    for k in ("menuSchedules", "menuSchedule", "menus", "days"):
        v = payload.get(k) if isinstance(payload, dict) else None
        if isinstance(v, list) and v:
            candidates = v
            break
    if candidates is None:
        candidates = [d for d in iter_dicts(payload)
                      if parse_any_date(first_key(d, DATE_KEYS) or "")]

    for day_node in candidates:
        if not isinstance(day_node, dict):
            continue
        day = None
        for d in iter_dicts(day_node):
            day = parse_any_date(first_key(d, DATE_KEYS) or "")
            if day:
                break
        if not day:
            continue

        # Find meal blocks under this day, if the structure has them.
        blocks = []
        for k in ("menuBlocks", "menuBlock", "meals", "blocks"):
            v = day_node.get(k)
            if isinstance(v, list) and v:
                blocks = v
                break

        if blocks:
            for b in blocks:
                if not isinstance(b, dict):
                    continue
                bname = first_key(b, BLOCK_NAME_KEYS) or "Lunch"
                bname = str(bname).strip().title()
                if MEALS and not any(m.lower() in bname.lower() for m in MEALS):
                    continue
                items = sort_items(collect_items(b))
                if items:
                    days.setdefault(day.isoformat(), {}).setdefault(bname, []).extend(items)
        else:
            items = sort_items(collect_items(day_node))
            if items:
                days.setdefault(day.isoformat(), {}).setdefault("Lunch", []).extend(items)

    # Tidy: drop duplicate items that arrived via several paths
    for day, meals in days.items():
        for meal, items in meals.items():
            seen, uniq = set(), []
            for it in items:
                k = it["name"].lower()
                if k in seen:
                    continue
                seen.add(k)
                uniq.append(it)
            meals[meal] = uniq
    return days


# --- Picking each day's real lunch ------------------------------------------
#
# Most menus include the same fallback choices every day ("Bagel Option",
# "Chef Salad Option"). They're categorised as entrees and would otherwise
# headline every single day. The day's actual lunch is the entree that
# CHANGES from day to day, so alternates are identified two ways:
#   - the word "option"/"alternate" in the name, and
#   - appearing on most of the days in the data.
ALT_NAME_RE = re.compile(r'\b(option|alternate|alt\.?|grab\s*(?:&|and)\s*go|daily)\b',
                         re.IGNORECASE)
RECURRING_SHARE = 0.6        # on >= 60% of days counts as a daily staple
MIN_DAYS_FOR_RECURRENCE = 3  # need a few days before recurrence means anything


def _norm(name):
    return re.sub(r'[^a-z0-9]+', '', name.lower())


def mark_featured(days):
    """Flag each day's headline item and its daily alternates, and reorder so
    the headline comes first and alternates last."""
    for meal in {m for d in days.values() for m in d}:
        meal_days = [d[meal] for d in days.values() if d.get(meal)]
        counts = {}
        for items in meal_days:
            for n in {_norm(i["name"]) for i in items}:
                counts[n] = counts.get(n, 0) + 1
        n_days = len(meal_days)

        side_rank = type_rank("Side")

        def is_alt(item):
            if ALT_NAME_RE.search(item["name"]):
                return True
            # Recurrence only marks an *entree* as a daily alternate. Fruit,
            # milk and sides legitimately show up most days -- that's just
            # a normal side, not an alternative lunch.
            if type_rank(item["type"]) >= side_rank:
                return False
            if n_days >= MIN_DAYS_FOR_RECURRENCE:
                return counts.get(_norm(item["name"]), 0) / n_days >= RECURRING_SHARE
            return False

        for day in days.values():
            items = day.get(meal)
            if not items:
                continue
            side_rank = type_rank("Side")
            for it in items:
                it["alt"] = is_alt(it)
                it.pop("featured", None)

            entrees = [i for i in items if type_rank(i["type"]) < side_rank]
            # Priority: a real (non-alternate) entree, then any entree --
            # even an "option" beats headlining a piece of fruit -- then
            # anything non-alternate, then whatever's there.
            pool = [i for i in entrees if not i["alt"]] \
                or entrees \
                or [i for i in items if not i["alt"]] \
                or items
            pool[0]["featured"] = True

            head = [i for i in items if i.get("featured")]
            rest = [i for i in items if not i.get("featured") and not i["alt"]]
            alts = [i for i in items if not i.get("featured") and i["alt"]]
            day[meal] = head + rest + alts
    return days


def school_name(payload):
    for key in ("schoolName", "name", "physicalLocationName"):
        for d in iter_dicts(payload):
            v = d.get(key)
            if isinstance(v, str) and v.strip() and len(v) < 90:
                return v.strip()
    return None


def dump_structure(payload, limit=60):
    """Print the shape of an unexpected response so it can be diagnosed."""
    print("--- RESPONSE STRUCTURE DUMP START ---", file=sys.stderr)
    if isinstance(payload, dict):
        print(f"top-level keys: {list(payload.keys())}", file=sys.stderr)
    text = json.dumps(payload)[:4000]
    print(f"first 4000 chars of JSON:\n{text}", file=sys.stderr)
    print("--- RESPONSE STRUCTURE DUMP END ---", file=sys.stderr)
    print("Copy everything between DUMP START and DUMP END and send it to "
          "Claude to adjust the parser.", file=sys.stderr)


# --- Keeping index.html in sync -------------------------------------------

def update_index(menu_payload):
    if not os.path.exists(INDEX_FILE):
        print(f"(no {INDEX_FILE} beside the script -- skipping page sync)")
        return
    html = open(INDEX_FILE, encoding="utf-8").read()
    before, notes = html, []

    repo = os.environ.get("GITHUB_REPOSITORY", "").strip()
    if repo and URL_REGION_RE.search(html):
        url = f"https://cdn.jsdelivr.net/gh/{repo}@main/menu.json"
        html = URL_REGION_RE.sub(lambda m: f"{m.group(1)}'{url}'{m.group(2)}", html, count=1)
        notes.append(f"data URL -> {url}")
    elif not repo:
        notes.append("data URL left alone (not running in GitHub Actions)")

    if FALLBACK_REGION_RE.search(html):
        payload = json.dumps(menu_payload, indent=2, sort_keys=True).replace("</", "<\\/")
        html = FALLBACK_REGION_RE.sub(lambda m: f"{m.group(1)}{payload}{m.group(2)}", html, count=1)
        notes.append("offline copy refreshed")
    else:
        notes.append("WARNING: no FALLBACK markers found in index.html")

    if html != before:
        open(INDEX_FILE, "w", encoding="utf-8").write(html)
        print("Updated index.html: " + "; ".join(notes))
    else:
        print("index.html unchanged: " + "; ".join(notes))


# --- Main ------------------------------------------------------------------

def main():
    today = date.today()
    # Start at whichever is earlier: a week back, or the 1st of this month,
    # so the month view always has the full current month.
    start = min(today - timedelta(days=DAYS_BEHIND), today.replace(day=1))
    end = today + timedelta(days=DAYS_AHEAD)
    fmt = "%m-%d-%Y"
    print(f"Window: {start.isoformat()} .. {end.isoformat()}")

    schools, failures, raw_for_dump = {}, [], None

    for key in SCHOOL_KEYS:
        url = API.format(key=key, start=start.strftime(fmt), end=end.strftime(fmt))
        print(f"\nFetching {key}\n  {url}")
        try:
            payload = fetch_json(url)
        except Exception as e:
            print(f"  ERROR: {e}", file=sys.stderr)
            failures.append(key)
            continue

        if raw_for_dump is None:
            raw_for_dump = payload

        name = school_name(payload) or key
        days = mark_featured(extract_days(payload))
        meals = sorted({m for d in days.values() for m in d})
        total = sum(len(items) for d in days.values() for items in d.values())
        print(f"  school: {name}")
        print(f"  {len(days)} day(s), meal periods: {meals or '(none)'}, {total} item(s)")

        if days:
            schools[name] = days
        else:
            print(f"  WARNING: no menu days parsed for {key}", file=sys.stderr)

    if not schools:
        print("\nERROR: no menu data parsed from any school.", file=sys.stderr)
        if raw_for_dump is not None:
            dump_structure(raw_for_dump)
        if os.path.exists("menu.json"):
            print("Keeping the existing menu.json rather than emptying it.", file=sys.stderr)
            # Still fill in index.html from the last good menu. Otherwise a
            # freshly uploaded page (blank saved copy, no live-data link)
            # would stay blank until a fetch next succeeds.
            try:
                update_index(json.load(open("menu.json")))
            except Exception as e:
                print(f"Could not refresh index.html from menu.json: {e}", file=sys.stderr)
            sys.exit(1)

    payload = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "source": "MealViewer (api.mealviewer.com)",
        "schools": schools,
    }
    with open("menu.json", "w") as f:
        json.dump(payload, f, indent=2, sort_keys=True)

    all_days = sorted({d for s in schools.values() for d in s})
    print(f"\nWrote menu.json: {len(schools)} school(s), {len(all_days)} day(s)")
    if all_days:
        print(f"Date range in data: {all_days[0]} .. {all_days[-1]}")
    if failures:
        print(f"WARNING: {len(failures)} school key(s) failed: {failures}", file=sys.stderr)

    update_index(payload)


if __name__ == "__main__":
    main()
