#!/usr/bin/env python3
"""Post news from RSS/Atom feeds to Discord channels, translated to Arabic.

Every channel in feeds.json has its own Discord webhook, read from the
environment variable named by its "webhook_secret", and its own list of feeds.
Each run fetches the feeds and posts every new item as its own message: a new
post in a forum channel (the webhook "thread_name" field), or a normal message
in a text channel. At most "limit" items per feed are posted per run, newest
first; older new items are skipped, not queued for later.

Titles and summaries are machine translated to Arabic with the free MyMemory
API (MYMEMORY_EMAIL raises its daily quota); the original English title is kept
in the card footer. When translation fails the card stays in English.

A source can also be a GitHub search ("kind": "github_search"): new
repositories with given topics (agent skills, Claude Code plugins, MCP
servers...) that passed a number of stars within a few days of being created.

What was already seen is remembered in state.json, per feed. Only the Python
standard library is used.

Usage:
  python notifier.py                       normal run
  python notifier.py --dry-run             print what would be posted, post nothing
  python notifier.py --dry-run --latest 1  preview the newest item of every feed
  python notifier.py --latest 1            post the newest item of every feed (webhook test)
  python notifier.py --channel research    only the channels with these keys (comma separated)

The first real run (and the first run after a feed is added) only records what
the feed already holds and posts nothing, unless --latest is given.
"""

from __future__ import annotations

import argparse
import email.utils
import gzip
import hashlib
import html
import html.entities
import json
import logging
import os
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from html.parser import HTMLParser
from pathlib import Path

MYMEMORY_URL = "https://api.mymemory.translated.net/get"
# Some sites refuse requests without a browser-like User-Agent.
USER_AGENT = "Mozilla/5.0 (compatible; learning-news-notifier/1.0)"
HERE = Path(__file__).resolve().parent

DEFAULT_LIMIT = 3
# Only the newest SCAN items of a feed are looked at. arXiv lists over a
# thousand papers a day; the rest are never considered and never stored.
SCAN = 50
# How many item keys to remember per feed (must stay well above SCAN).
KEEP_SEEN = 200
# An unseen item more than this much older than the newest item already seen
# in its feed is old backlog (for example after a site changed its links).
LOOKBACK = timedelta(days=7)
SUMMARY_CHARS = 300
THREAD_NAME_CHARS = 100  # Discord's limit for a thread (forum post) name
POST_DELAY = 2.0  # seconds between Discord messages
MAX_FEED_BYTES = 10_000_000
MAX_PAGE_BYTES = 400_000

COLOR_RELEASE = 0xD29922
COLOR_REPO = 0x8250DF
GITHUB_API = "https://api.github.com"

WEBHOOK_RE = re.compile(
    r"^https://(?:(?:ptb|canary)\.)?discord(?:app)?\.com/api/(?:v\d+/)?webhooks/\d+/[\w-]+"
)
SECRET_NAME_RE = re.compile(r"^[A-Z][A-Z0-9_]*$")
# Pre-release tags of release feeds: 1.2.0-alpha.3, v0.40.5-rc1, v0.32.0rc2, v0.65.0-nightly.2026...
PRERELEASE_RE = re.compile(
    r"(?i)\b(?:alpha|beta|rc|pre|preview|nightly|canary|dev|snapshot)\d*\b|\d(?:a|b|rc)\d"
)
# GitHub's Atom feeds of a repository: releases, tags and the commits of a branch.
GITHUB_FEED_RE = re.compile(r"^https://github\.com/([\w.-]+)/([\w.-]+)/(?:releases|tags|commits/[\w./-]+)\.atom$")

log = logging.getLogger("learning-news")


class NotifierError(Exception):
    pass


# --------------------------------------------------------------------------
# Configuration (feeds.json)
# --------------------------------------------------------------------------

@dataclass
class Feed:
    name: str
    url: str
    limit: int
    kind: str = "news"  # "news" | "release" | "github_search"
    skip_title: re.Pattern | None = None
    skip_text: re.Pattern | None = None
    page_image: bool = False
    page_summary: bool = False
    show_authors: bool = False
    icon: str | None = None
    color: int | None = None
    heading: str | None = None  # first line of every card from this feed
    # github_search: repositories with any of these topics (or matching query),
    # created in the last `days` days, with at least `min_stars` stars.
    topics: list[str] = field(default_factory=list)
    query: str = ""
    min_stars: int = 100
    days: int = 14


@dataclass
class Channel:
    key: str
    name: str
    type: str  # "forum" | "text"
    webhook_secret: str
    color: int
    feeds: list[Feed]
    applied_tags: list[str] = field(default_factory=list)


def parse_color(value, where: str) -> int:
    if isinstance(value, int):
        return value
    if isinstance(value, str) and re.fullmatch(r"#?[0-9A-Fa-f]{6}", value):
        return int(value.lstrip("#"), 16)
    raise NotifierError(f"{where}: color must look like \"#5865F2\"")


def compile_regex(value, where: str) -> re.Pattern | None:
    if not value:
        return None
    try:
        return re.compile(value)
    except re.error as error:
        raise NotifierError(f"{where}: bad regular expression: {error}") from None


def load_config(path: Path) -> list[Channel]:
    try:
        data = json.loads(path.read_text(encoding="utf-8-sig"))
    except OSError as error:
        raise NotifierError(f"Could not read {path.name}: {error}") from None
    except ValueError as error:
        raise NotifierError(f"{path.name} is not valid JSON: {error}") from None
    default_limit = data.get("limit", DEFAULT_LIMIT)
    channels: list[Channel] = []
    keys: set[str] = set()
    urls: set[str] = set()
    for index, raw in enumerate(data.get("channels") or []):
        where = f"{path.name} channel {raw.get('key') or index + 1}"
        key = str(raw.get("key") or "").strip()
        if not re.fullmatch(r"[a-z0-9_-]+", key) or key in keys:
            raise NotifierError(f"{where}: \"key\" must be a unique lowercase word")
        keys.add(key)
        kind = raw.get("type", "forum")
        if kind not in ("forum", "text"):
            raise NotifierError(f"{where}: \"type\" must be \"forum\" or \"text\"")
        secret = str(raw.get("webhook_secret") or "")
        if not SECRET_NAME_RE.match(secret):
            raise NotifierError(f"{where}: \"webhook_secret\" must be a name like DISCORD_WEBHOOK_AI")
        channel_limit = raw.get("limit", default_limit)
        feeds = []
        for raw_feed in raw.get("feeds") or []:
            feed_kind = raw_feed.get("kind", "news")
            feed_where = f"{where} feed {raw_feed.get('url') or raw_feed.get('name')}"
            if feed_kind not in ("news", "release", "github_search"):
                raise NotifierError(f"{feed_where}: \"kind\" must be \"news\", \"release\" or \"github_search\"")
            topics = [str(topic).strip() for topic in raw_feed.get("topics") or [] if str(topic).strip()]
            query = str(raw_feed.get("query") or "").strip()
            if feed_kind == "github_search":
                if not topics and not query:
                    raise NotifierError(f"{feed_where}: a github_search needs \"topics\" or \"query\"")
                for name in ("min_stars", "days"):
                    if not isinstance(raw_feed.get(name, 1), int) or raw_feed.get(name, 1) < 1:
                        raise NotifierError(f"{feed_where}: \"{name}\" must be a whole number, 1 or more")
                # The search page on github.com: what state.json remembers this source by.
                terms = " ".join([f"topic:{topic}" for topic in topics] + ([query] if query else []))
                url = "https://github.com/search?type=repositories&q=" + urllib.parse.quote(terms)
            else:
                url = str(raw_feed.get("url") or "").strip()
            if not url.startswith(("https://", "http://")):
                raise NotifierError(f"{feed_where}: \"url\" must start with https://")
            if url in urls:
                raise NotifierError(f"{feed_where}: the same feed is listed twice")
            urls.add(url)
            limit = raw_feed.get("limit", channel_limit)
            if not isinstance(limit, int) or limit < 0:
                raise NotifierError(f"{feed_where}: \"limit\" must be a whole number, 0 or more")
            skip_title = raw_feed.get("skip_title")
            if feed_kind == "release" and not raw_feed.get("prereleases") and not skip_title:
                skip_title = PRERELEASE_RE.pattern
            feeds.append(Feed(
                name=str(raw_feed.get("name") or urllib.parse.urlsplit(url).hostname),
                url=url,
                limit=limit,
                kind=feed_kind,
                skip_title=compile_regex(skip_title, feed_where),
                skip_text=compile_regex(raw_feed.get("skip_text"), feed_where),
                page_image=bool(raw_feed.get("page_image")),
                page_summary=bool(raw_feed.get("page_summary")),
                show_authors=bool(raw_feed.get("show_authors")),
                icon=raw_feed.get("icon") or None,
                color=parse_color(raw_feed["color"], feed_where) if raw_feed.get("color") else None,
                heading=str(raw_feed.get("heading") or "").strip() or None,
                topics=topics,
                query=query,
                min_stars=raw_feed.get("min_stars", 100),
                days=raw_feed.get("days", 14),
            ))
        if not feeds:
            raise NotifierError(f"{where}: no feeds")
        tags = [str(tag) for tag in raw.get("applied_tags") or []]
        channels.append(Channel(
            key=key,
            name=str(raw.get("name") or key),
            type=kind,
            webhook_secret=secret,
            color=parse_color(raw.get("color", "#5865F2"), where),
            feeds=feeds,
            applied_tags=tags[:5],
        ))
    if not channels:
        raise NotifierError(f"{path.name} has no channels")
    return channels


# --------------------------------------------------------------------------
# Fetching
# --------------------------------------------------------------------------

def http_get(url: str, accept: str, limit: int, timeout: float = 30, partial: bool = False,
             extra_headers: dict | None = None) -> bytes:
    """GET a URL; one retry on network errors and server errors."""
    headers = {"User-Agent": USER_AGENT, "Accept": accept, "Accept-Language": "en", **(extra_headers or {})}
    for attempt in range(2):
        request = urllib.request.Request(url, headers=headers)
        try:
            with urllib.request.urlopen(request, timeout=timeout) as response:
                data = response.read(limit + 1)
                if response.headers.get("Content-Encoding", "").lower() == "gzip":
                    data = gzip.decompress(data)
        except urllib.error.HTTPError as error:
            if error.code >= 500 and attempt == 0:
                time.sleep(3)
                continue
            raise NotifierError(f"HTTP {error.code}") from None
        except (urllib.error.URLError, TimeoutError, OSError, EOFError) as error:
            if attempt == 0:
                time.sleep(3)
                continue
            raise NotifierError(f"request failed: {getattr(error, 'reason', error)}") from None
        if len(data) > limit:
            if not partial:
                raise NotifierError(f"larger than {limit // 1_000_000} MB")
            data = data[:limit]
        return data
    raise AssertionError("unreachable")


def fetch_feed(url: str) -> bytes:
    return http_get(url, "application/rss+xml, application/atom+xml, application/xml;q=0.9, */*;q=0.8",
                    MAX_FEED_BYTES)


def fetch_page(url: str) -> str:
    data = http_get(url, "text/html, */*;q=0.8", MAX_PAGE_BYTES, timeout=15, partial=True)
    return data.decode("utf-8", "replace")


def github_search_page(query: str) -> dict:
    """One page of GitHub's repository search, most starred first."""
    headers = {"X-GitHub-Api-Version": "2022-11-28"}
    token = os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN")
    if token:
        headers["Authorization"] = f"Bearer {token}"
    params = urllib.parse.urlencode({"q": query, "sort": "stars", "order": "desc", "per_page": SCAN})
    data = http_get(f"{GITHUB_API}/search/repositories?{params}", "application/vnd.github+json",
                    MAX_FEED_BYTES, extra_headers=headers)
    try:
        return json.loads(data)
    except ValueError:
        raise NotifierError("GitHub search returned something that is not JSON") from None


def search_github(feed: Feed, now: datetime) -> ParsedFeed:
    """Repositories of the feed's topics created in its last `days` days, most starred first."""
    since = (now - timedelta(days=feed.days)).date().isoformat()
    filters = f"created:>={since} stars:>={feed.min_stars}"
    queries = [f"topic:{topic} {feed.query} {filters}" for topic in feed.topics] or [f"{feed.query} {filters}"]
    repos: dict[str, dict] = {}
    for query in queries:
        for repo in github_search_page(" ".join(query.split())).get("items") or []:
            # One repository often has several of the topics: it is kept once.
            if repo.get("full_name") and repo.get("description") and not repo.get("fork") and not repo.get("archived"):
                repos.setdefault(repo["full_name"], repo)
    ordered = sorted(repos.values(), key=lambda repo: repo.get("stargazers_count") or 0, reverse=True)
    return ParsedFeed("GitHub", None, [repo_item(repo, position) for position, repo in enumerate(ordered)])


def repo_item(repo: dict, position: int) -> Item:
    owner = repo.get("owner") or {}
    description = " ".join(str(repo["description"]).split())
    return Item(
        key=hashlib.sha1(f"github:{repo['full_name'].lower()}".encode("utf-8")).hexdigest()[:12],
        title=repo.get("name") or repo["full_name"],
        link=repo["html_url"],
        # No date: a repository is new to us when it first passes the star
        # threshold, which can be days after it was created.
        date=None,
        summary_html=html.escape(description),
        content_html="",
        # GitHub's social card: name, description and stars as a picture.
        image=f"https://opengraph.githubassets.com/1/{repo['full_name']}",
        author=owner.get("login") or "",
        comments=None,
        position=position,
        extra={
            "repo": repo["full_name"],
            "description": description,
            "stars": repo.get("stargazers_count") or 0,
            "created": (repo.get("created_at") or "")[:10],
            "topics": list(repo.get("topics") or [])[:6],
            "owner_url": owner.get("html_url"),
            "owner_avatar": owner.get("avatar_url"),
        },
    )


# --------------------------------------------------------------------------
# Feed parsing (RSS 2.0, RSS 1.0 and Atom)
# --------------------------------------------------------------------------

MEDIA_NS = "{http://search.yahoo.com/mrss/}"
XML_ENTITIES = {"amp", "lt", "gt", "quot", "apos"}


@dataclass
class Item:
    key: str
    title: str
    link: str
    date: datetime | None
    summary_html: str
    content_html: str
    image: str | None
    author: str
    comments: str | None
    position: int
    extra: dict = field(default_factory=dict)  # github_search: stars, topics...


@dataclass
class ParsedFeed:
    title: str
    icon: str | None
    items: list[Item]


def local(tag) -> str:
    return tag.rsplit("}", 1)[-1] if isinstance(tag, str) else ""


def child(node, *names):
    """First child with one of these local names, ignoring Media RSS elements."""
    for element in node:
        if isinstance(element.tag, str) and not element.tag.startswith(MEDIA_NS) and local(element.tag) in names:
            return element
    return None


def text_of(node) -> str:
    return "".join(node.itertext()).strip() if node is not None else ""


def markup_of(node) -> str:
    """The HTML held by an element: escaped text, CDATA, or inline XHTML."""
    if node is None:
        return ""
    if node.get("type") == "xhtml" or len(node):
        return "".join(ET.tostring(element, encoding="unicode") for element in node) + (node.text or "")
    return node.text or ""


def parse_xml(data: bytes):
    try:
        return ET.fromstring(data)
    except ET.ParseError:
        pass
    # Repair what feeds commonly get wrong: leading junk, HTML entities, bare "&".
    text = data.decode("utf-8", "replace").lstrip("\ufeff \t\r\n")

    def entity(match):
        name = match.group(1)
        if name in XML_ENTITIES:
            return match.group(0)
        code = html.entities.name2codepoint.get(name)
        return f"&#{code};" if code else ""

    text = re.sub(r"&([A-Za-z][A-Za-z0-9]*);", entity, text)
    text = re.sub(r"&(?!(?:[A-Za-z][A-Za-z0-9]*|#\d+|#x[0-9A-Fa-f]+);)", "&amp;", text)
    try:
        return ET.fromstring(text)
    except ET.ParseError as error:
        raise NotifierError(f"not a valid RSS/Atom feed: {error}") from None


def parse_date(value: str) -> datetime | None:
    value = (value or "").strip()
    if not value:
        return None
    try:
        parsed = email.utils.parsedate_to_datetime(value)
    except (TypeError, ValueError, IndexError):
        try:
            parsed = datetime.fromisoformat(value.replace("Z", "+00:00"))
        except ValueError:
            return None
    if parsed.tzinfo is None:
        parsed = parsed.replace(tzinfo=timezone.utc)
    return parsed.astimezone(timezone.utc)


def item_link(node) -> str:
    first = ""
    for element in node:
        if local(element.tag) != "link" or element.tag.startswith(MEDIA_NS):
            continue
        href = element.get("href")
        if href:
            if element.get("rel", "alternate") == "alternate":
                return href.strip()
            first = first or href.strip()
        elif (element.text or "").strip():
            return element.text.strip()
    if first:
        return first
    guid = child(node, "guid")
    if guid is not None and text_of(guid).startswith("http"):
        return text_of(guid)
    return ""


IMG_RE = re.compile(r"<img\b[^>]*>", re.I)
ATTR_RE = re.compile(r"""([\w:-]+)\s*=\s*(?:"([^"]*)"|'([^']*)'|([^\s>]+))""")


def attributes(tag: str) -> dict[str, str]:
    return {name.lower(): html.unescape(a or b or c) for name, a, b, c in ATTR_RE.findall(tag)}


def too_small(attrs) -> bool:
    for name in ("width", "height"):
        value = re.match(r"\d+", str(attrs.get(name) or ""))
        if value and int(value.group(0)) < 100:
            return True
    return False


def html_image(markup: str, base: str) -> str | None:
    for tag in IMG_RE.findall(markup or ""):
        attrs = attributes(tag)
        src = attrs.get("src") or attrs.get("data-src") or ""
        if not src or src.startswith("data:") or too_small(attrs):
            continue
        if re.search(r"(?i)feedburner|/pixel|gravatar|emoji|\.gif(?:\?|$)", src):
            continue
        url = urllib.parse.urljoin(base, src)
        if url.startswith("http"):
            return url
    return None


def item_image(node, link: str, *markups: str) -> str | None:
    """The item's picture: Media RSS, an image enclosure, or the first <img> in its HTML."""
    found: dict[str, str] = {}
    for element in node.iter():
        tag = element.tag if isinstance(element.tag, str) else ""
        url = (element.get("url") or "").strip()
        if not url.startswith("http") or too_small(element.attrib):
            continue
        name = local(tag)
        image_type = (element.get("type") or "").startswith("image/")
        if tag.startswith(MEDIA_NS) and name == "content":
            if element.get("medium") == "image" or image_type or (
                not element.get("medium") and not element.get("type")
                and re.search(r"(?i)\.(?:jpe?g|png|webp)(?:\?|$)", url)
            ):
                found.setdefault("content", url)
        elif tag.startswith(MEDIA_NS) and name == "thumbnail":
            found.setdefault("thumbnail", url)
        elif name == "enclosure" and image_type:
            found.setdefault("enclosure", url)
    for kind in ("content", "enclosure", "thumbnail"):
        if kind in found:
            return found[kind]
    for markup in markups:
        image = html_image(markup, link)
        if image:
            return image
    return None


def parse_item(node, position: int) -> Item | None:
    title = html_to_text(markup_of(child(node, "title"))).replace("\n", " ").strip()
    link = item_link(node)
    guid = text_of(child(node, "guid", "id")) or link or title
    if not guid or not (title or link):
        return None
    date = None
    for name in ("published", "pubDate", "issued", "date", "updated", "modified"):
        date = parse_date(text_of(child(node, name)))
        if date:
            break
    summary = markup_of(child(node, "description", "summary"))
    content = markup_of(child(node, "encoded", "content"))
    if title.endswith("…"):
        # GitHub cuts long commit titles short; the whole message is in the content.
        whole = html.unescape(re.sub(r"<[^>]+>", "", content or summary)).strip()
        first_line = whole.splitlines()[0].strip() if whole else ""
        if first_line.startswith(title[:-1].rstrip()):
            title = first_line
    author = text_of(child(node, "creator"))
    if not author:
        authors = [text_of(child(element, "name")) for element in node if local(element.tag) == "author"]
        author = ", ".join(name for name in authors if name)
    comments = text_of(child(node, "comments"))
    return Item(
        key=hashlib.sha1(guid.encode("utf-8")).hexdigest()[:12],
        title=title or link,
        link=link,
        date=date,
        summary_html=summary,
        content_html=content,
        image=item_image(node, link, summary, content),
        author=" ".join(author.split()),
        comments=comments if comments.startswith("http") else None,
        position=position,
    )


def parse_feed(data: bytes) -> ParsedFeed:
    root = parse_xml(data)
    channel = child(root, "channel")
    head = channel if channel is not None else root
    image = child(head, "image")
    icon = text_of(child(image, "url")) if image is not None else ""
    icon = icon or text_of(child(head, "icon")) or text_of(child(head, "logo"))
    items = []
    for node in root.iter():
        if local(node.tag) in ("item", "entry"):
            item = parse_item(node, len(items))
            if item:
                items.append(item)
    if not items and local(root.tag) not in ("rss", "feed", "RDF"):
        raise NotifierError(f"not an RSS/Atom feed (root element <{local(root.tag)}>)")
    return ParsedFeed(text_of(child(head, "title")), icon if icon.startswith("http") else None, items)


# --------------------------------------------------------------------------
# HTML to text, summaries
# --------------------------------------------------------------------------

class TextExtractor(HTMLParser):
    BLOCK = {"p", "div", "br", "ul", "ol", "blockquote", "tr", "section", "article", "header",
             "footer", "figure", "table", "hr", "dd", "dt", "details", "summary"}
    SKIP = {"script", "style", "figcaption", "pre", "noscript", "iframe", "svg", "button",
            "h1", "h2", "h3", "h4", "h5", "h6", "template"}

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.parts: list[str] = []
        self.skipping = 0

    def handle_starttag(self, tag, attrs):
        if tag in self.SKIP:
            self.skipping += 1
        elif tag == "li":
            self.parts.append("\n• ")
        elif tag in self.BLOCK:
            self.parts.append("\n")

    def handle_startendtag(self, tag, attrs):
        if tag in ("br", "hr"):
            self.parts.append("\n")

    def handle_endtag(self, tag):
        if tag in self.SKIP:
            self.skipping = max(0, self.skipping - 1)
        elif tag in self.BLOCK or tag == "li":
            self.parts.append("\n")

    def handle_data(self, data):
        if not self.skipping:
            self.parts.append(data)


def html_to_text(markup: str) -> str:
    if not markup:
        return ""
    if "<" not in markup:
        text = html.unescape(markup)
    else:
        parser = TextExtractor()
        parser.feed(markup)
        parser.close()
        text = "".join(parser.parts)
    lines = [" ".join(line.split()) for line in text.splitlines()]
    return "\n".join(line for line in lines if line and line != "•")


JUNK_LINE_RE = re.compile(
    r"^(?:Article URL|Comments URL|Points|# Comments):"
    r"|^arXiv:\S+\s+Announce Type:"
    r"|^The post .+ (?:appeared first|first appeared) on .+$"
    r"|^(?:Read more|Continue reading|Read the full)\b"
    r"|^Links?: "
    r"|^(?:•\s*)?https?://\S+$",
    re.I,
)


def clean_text(text: str) -> str:
    lines = []
    for line in text.splitlines():
        line = re.sub(r"\[\s*(?:\.\.\.|…)\s*\]|\s*(?:Read more|Continue reading)\s*(?:»|…|\.\.\.)\s*$", "", line).strip()
        line = re.sub(r"^Abstract:\s*", "", line)
        # GitHub's generated release notes: "Fix X by @someone in #123"
        line = re.sub(r"\s+by @[\w-]+(?:\[bot\])? in (?:#\d+|https://\S+)$", "", line)
        if line and not JUNK_LINE_RE.search(line):
            lines.append(line)
    return "\n".join(lines)


def cut(text: str, limit: int) -> str:
    """Shorten one paragraph, at a sentence end when there is one late enough."""
    if len(text) <= limit:
        return text
    window = text[:limit]
    ends = [match.end() for match in re.finditer(r"[.!?](?=\s)", window)]
    if ends and ends[-1] >= limit * 0.5:
        return window[: ends[-1]]
    return window.rsplit(None, 1)[0].rstrip(",;:-") + " …"


def excerpt(text: str, limit: int = SUMMARY_CHARS) -> str:
    """First lines of a text, up to about limit characters."""
    lines = text.splitlines()
    picked: list[str] = []
    size = 0
    for line in lines:
        if picked and size + len(line) > limit:
            break
        picked.append(cut(line, limit - size) if not picked else line)
        size += len(picked[-1]) + 1
    return "\n".join(picked)


# "v3.24.0: Qoder CLI support", "v2.11.37 — Copywriting reads the ledger"
RELEASE_TITLE_RE = re.compile(r"^(?:Release:?\s+)?(.*?\bv?\d+(?:\.\d+)+[\w.+-]*)\s*(?::|—|–|\s-)\s+(.+)$")


def split_release_title(title: str) -> tuple[str, str]:
    """(version, what the release title says besides the version)."""
    match = RELEASE_TITLE_RE.match(title)
    if match:
        return match.group(1).strip(), match.group(2).strip()
    return re.sub(r"^Release:?\s+", "", title).strip(), ""


def item_summary(item: Item, feed: Feed) -> str:
    sources = [item.content_html, item.summary_html] if feed.kind == "release" else [
        item.summary_html, item.content_html]
    text = ""
    for source in sources:
        candidate = clean_text(html_to_text(source))
        if len(candidate) >= 40:
            text = candidate
            break
        text = text or candidate
    if feed.kind == "release":
        headline = split_release_title(item.title)[1]
        # Often the notes open with the same sentence as the title.
        if headline and headline.rstrip(".…").lower()[:40] not in text[:300].lower():
            text = f"{headline}\n{text}" if text else headline
    if text and text.strip().lower() == item.title.strip().lower():
        return ""
    return excerpt(text)


# --------------------------------------------------------------------------
# Translation (free MyMemory API)
# --------------------------------------------------------------------------

# Parts of a text that must not be translated: links, code, versions and
# names. They are swapped for ZQ<n> placeholders, which the translator leaves
# alone, and put back afterwards. Some terms get a fixed Arabic wording the
# same way.
PROTECT_PATTERNS = [
    r"https?://\S+",
    r"`[^`]+`",
    r"^[a-z]+(?:\([^)]*\))?!?:(?=\s)",  # "fix(scope):" of commit-style release notes
    r"(?<![\w/])/[a-z][\w-]*",  # slash commands such as /config
    r"\bCVE-\d{4}-\d+\b",
    r"\b(?:RCE|XSS|CSRF|SQLi|DDoS|VPN|SDK|CLI|GPU|CPU|MCP|MIT)\b",
    r"\b[A-Z][A-Za-z0-9]*(?:-[A-Za-z0-9]+)+\b",  # GPT-Rosalind, C-RADIO, LLM-Referenced
    r"\b[a-z0-9]+(?:-[a-z0-9]+)+(?= (?:skill|plugin|server|agent|extension|hook)s?\b)",  # the claude-api skill
    r"\bClaude(?: (?:Code|Opus|Sonnet|Haiku))?(?: \d+(?:\.\d+)*)?\b",
    r"\b(?:Hugging Face|Hacker News|The Verge|Quanta Magazine|Krebs on Security|Google DeepMind|DeepMind"
    r"|OpenAI|Anthropic|Gemini|Gemma|Llama|Ollama|Mistral|DeepSeek|Qwen|Codex|Copilot|ChatGPT|Sora|Grok"
    r"|Apple|Meta|Windows|Rust|Swift|Chrome|Chromium|Edge|Firefox|Safari|Android|iOS|macOS|Linux|Docker"
    r"|Kubernetes|Python|Cloudflare|WordPress|Nextcloud|arXiv|Diffusers|Transformers|Open WebUI)\b",
    r"\b\w*_\w+\b",  # snake_case and SNAKE_CASE
    r"\b[\w/-]+\.(?:py|js|ts|json|ya?ml|md|exe|dll|sh|toml)\b",
    r"\b\w+\(\)",  # function()
    r"(?<![\w-])--?[A-Za-z][\w-]*",  # command line options
    r"\bv?\d+(?:\.\d+){1,3}(?:[-+][\w.]+)?\b",  # version numbers
    r"\b[A-Za-z]+[-.]?\d[\w.]*\b",  # GPT-5, Qwen3, H100, FLUX.3
    r"\b[A-Za-z]*[a-z][A-Z]\w*\b",  # camelCase and PascalCase: GitHub, iPhone
    r"\b[A-Z]{2,}[a-z]\w*\b",  # LLaMA-like mixed capitals
    r"#\d+",
]
# Only terms the translator gets wrong: it reads "LLM" as a law degree, for one.
GLOSSARY = [
    (r"\bLLMs\b(?!-)", "النماذج اللغوية الكبيرة"),
    (r"\bLLM\b(?!-)", "النموذج اللغوي الكبير"),
    (r"(?i:\blarge language models\b)", "النماذج اللغوية الكبيرة"),
    (r"(?i:\blarge language model\b)", "النموذج اللغوي الكبير"),
    (r"(?i:\bopen[- ]source\b)", "مفتوح المصدر"),
    (r"(?i:\bopen[- ]weights?\b)", "مفتوح الأوزان"),
    (r"(?i:\bzero[- ]days?\b)", "ثغرة يوم الصفر"),
    (r"(?i:\bransomware\b)", "برمجيات الفدية"),
    (r"(?i:\bphishing\b)", "التصيّد الاحتيالي"),
    (r"\bpull requests\b|\bPRs\b", "طلبات الدمج"),
    (r"\bpull request\b|\bPR\b", "طلب الدمج"),
]
PLACEHOLDER_RE = re.compile(r"ZQ\s?(\d+)")


def protect(text: str, keep: tuple[str, ...] = ()) -> tuple[str, list[str]]:
    """Swap what must not be translated for placeholders; `keep` adds names such as claude-mem."""
    tokens: list[str] = []

    def swap(pattern: str, replacement: str | None) -> None:
        nonlocal text

        def repl(match):
            if PLACEHOLDER_RE.fullmatch(match.group(0)):
                return match.group(0)
            tokens.append(match.group(0) if replacement is None else replacement)
            return f"ZQ{len(tokens) - 1}"

        text = re.sub(pattern, repl, text)

    for pattern in PROTECT_PATTERNS[:2]:  # links and code before anything else
        swap(pattern, None)
    for word in keep:
        if re.search(r"[A-Za-z]", word):
            swap(rf"(?i)(?<![\w-]){re.escape(word)}(?![\w-])", None)
    for pattern, arabic in GLOSSARY:
        swap(pattern, arabic)
    for pattern in PROTECT_PATTERNS[2:]:
        swap(pattern, None)
    return text, tokens


def tidy(translated: str, original: str) -> str:
    """Undo the translator's habits: "GPT - 5" for "GPT-5", and a space before "؟"."""
    for word in set(re.findall(r"[\w.]+(?:-[\w.]+)+", original)):
        translated = translated.replace(word.replace("-", " - "), word)
    return re.sub(r"\s+([؟،؛])", r"\1", translated)


def restore(text: str, tokens: list[str]) -> str | None:
    """Put the protected parts back; None when the translator lost one."""
    seen = set()

    def repl(match):
        index = int(match.group(1))
        if index >= len(tokens):
            return match.group(0)
        seen.add(index)
        return tokens[index]

    result = PLACEHOLDER_RE.sub(repl, text)
    return result if len(seen) == len(tokens) else None


class Translator:
    """English to Arabic with MyMemory.

    When MyMemory fails (network, daily quota) translation is off for the rest
    of the run and cards fall back to English.
    """

    def __init__(self, enabled: bool, email: str | None):
        self.enabled = enabled
        self.email = email
        self.cache: dict[tuple, str | None] = {}
        self.calls = 0
        self.chars = 0

    @property
    def status(self) -> str:
        return "MyMemory" + (" (email quota)" if self.email else "") if self.enabled else "off"

    def __call__(self, text: str, keep: tuple[str, ...] = ()) -> str | None:
        text = " ".join(text.split())
        if not self.enabled or not text:
            return None
        key = (text, keep)
        if key in self.cache:
            return self.cache[key]
        protected, tokens = protect(text, keep)
        if not re.search(r"[A-Za-z]{2,}", PLACEHOLDER_RE.sub("", protected)):
            return text  # only names, code and numbers: nothing to translate
        try:
            result = restore(self.fetch(protected), tokens)
            if result is None:
                # The translator lost a placeholder: translate the plain text instead.
                log.info("Translation dropped a protected word, retrying without protection: %s", text[:80])
                result = self.fetch(text)
        except NotifierError as error:
            log.warning("Translation is off for the rest of this run: %s", error)
            self.enabled = False
            return None
        result = tidy(" ".join(result.split()), text) if result else None
        if result and not re.search(r"[\u0600-\u06FF]", result):
            result = None  # came back untranslated
        self.cache[key] = result
        return result

    def fetch(self, text: str) -> str:
        if len(text.encode("utf-8")) > 500:  # MyMemory's limit per request
            text = text.encode("utf-8")[:490].decode("utf-8", "ignore").rsplit(" ", 1)[0]
        params = {"q": text, "langpair": "en|ar"}
        if self.email:
            params["de"] = self.email
        request = urllib.request.Request(
            f"{MYMEMORY_URL}?{urllib.parse.urlencode(params)}", headers={"User-Agent": USER_AGENT}
        )
        self.calls += 1
        self.chars += len(text)
        for attempt in range(2):
            try:
                with urllib.request.urlopen(request, timeout=20) as response:
                    data = json.load(response)
                break
            except urllib.error.HTTPError as error:
                raise NotifierError(f"MyMemory HTTP {error.code}") from None
            except (urllib.error.URLError, TimeoutError, OSError, ValueError) as error:
                if attempt == 0:
                    time.sleep(2)
                    continue
                raise NotifierError(f"MyMemory request failed: {error}") from None
        translated = (data.get("responseData") or {}).get("translatedText") or ""
        if str(data.get("responseStatus")) != "200" or data.get("quotaFinished") or "MYMEMORY WARNING" in translated:
            raise NotifierError(f"MyMemory refused ({data.get('responseStatus')}): {translated[:160]}")
        return html.unescape(translated)


def translate_block(text: str, translate: Translator, keep: tuple[str, ...] = ()) -> str | None:
    """Translate line by line, keeping "• " bullets; None unless every line worked."""
    out = []
    for line in text.splitlines():
        bullet = line.startswith("• ")
        body = line[2:] if bullet else line
        trailing = " …" if body.endswith(" …") else ""
        translated = translate(body[: -len(trailing)] if trailing else body, keep)
        if not translated:
            return None
        out.append(("• " if bullet else "") + translated + trailing)
    return "\n".join(out)


# --------------------------------------------------------------------------
# Selecting new items, state
# --------------------------------------------------------------------------

@dataclass
class Post:
    channel: Channel
    feed: Feed
    item: Item
    icon: str | None = None
    title_ar: str | None = None
    summary: str = ""
    summary_ar: str | None = None
    payload: dict | None = None

    @property
    def label(self) -> str:
        return f"{self.feed.name}: {self.item.title[:70]}"


def wanted(item: Item, feed: Feed) -> bool:
    if feed.skip_title and feed.skip_title.search(item.title):
        return False
    if feed.skip_text and feed.skip_text.search(item.summary_html + "\n" + item.content_html):
        return False
    return True


def newest_first(items: list[Item]) -> list[Item]:
    """Newest first by date; the feed's own order breaks ties and covers undated items."""
    if any(item.date is None for item in items):
        return list(items)
    return sorted(items, key=lambda item: item.date, reverse=True)


def format_time(value: datetime) -> str:
    return value.astimezone(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def select_items(items: list[Item], feed: Feed, fstate: dict | None, latest: int,
                 now: datetime) -> tuple[list[Item], list[Item], dict]:
    """Return (to post, to mark seen now, new feed state).

    A feed without state is seeded: everything it holds now counts as seen.
    Otherwise the newest unseen items are posted, at most feed.limit of them,
    and the other unseen ones are marked seen so they are never posted later.
    With latest > 0 the newest `latest` items are posted as well, seen or not.
    """
    window = newest_first([item for item in items if wanted(item, feed)])[:SCAN]
    new_state = {"seen": list((fstate or {}).get("seen") or []), "newest": (fstate or {}).get("newest")}
    dates = [item.date for item in window if item.date and item.date <= now + timedelta(days=1)]
    newest = parse_iso(new_state["newest"])
    if dates and (newest is None or max(dates) > newest):
        new_state["newest"] = format_time(max(dates))

    if fstate is None:
        to_post = window[:latest] if latest else []
        return to_post, window, new_state

    seen = set(new_state["seen"])
    cutoff = newest - LOOKBACK if newest else None
    fresh = [item for item in window
             if item.key not in seen and not (cutoff and item.date and item.date < cutoff)]
    to_post = fresh[: feed.limit]
    for item in window[:latest]:
        if item not in to_post:
            to_post.append(item)
    skipped = [item for item in fresh if item not in to_post]
    return to_post, skipped, new_state


def parse_iso(value: str | None) -> datetime | None:
    if not value:
        return None
    try:
        return datetime.fromisoformat(value.replace("Z", "+00:00"))
    except ValueError:
        return None


def mark_seen(fstate: dict, items: list[Item]) -> None:
    seen = fstate["seen"]
    known = set(seen)
    # Oldest first, so the newest keys are the last to be trimmed.
    for item in reversed(newest_first(items)):
        if item.key not in known:
            seen.append(item.key)
            known.add(item.key)


def load_state(path: Path) -> dict:
    if not path.exists():
        return {"feeds": {}}
    try:
        state = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as error:
        raise NotifierError(f"Could not read {path.name}: {error}") from None
    state.setdefault("feeds", {})
    return state


def save_state(path: Path, state: dict) -> None:
    for fstate in state["feeds"].values():
        fstate["seen"] = fstate["seen"][-KEEP_SEEN:]
    temp = path.with_suffix(".tmp")
    temp.write_text(json.dumps(state, indent=1, ensure_ascii=False, sort_keys=True) + "\n", encoding="utf-8")
    os.replace(temp, path)


# --------------------------------------------------------------------------
# Discord messages
# --------------------------------------------------------------------------

def truncate(text: str, limit: int) -> str:
    return text if len(text) <= limit else text[: limit - 1].rstrip() + "…"


def escape_markdown(text: str) -> str:
    text = re.sub(r"([\\*_~`|])", r"\\\1", text)
    return re.sub(r"(?m)^([#>-])", r"\\\1", text)


def link_url(url: str) -> str:
    return url.replace("(", "%28").replace(")", "%29").replace(" ", "%20")


def release_title(post: Post) -> str:
    title = split_release_title(post.item.title)[0]
    if post.feed.name.lower() not in title.lower():
        title = f"{post.feed.name} {title}"
    return title


def feed_author(post: Post) -> dict:
    if post.feed.kind == "github_search":
        extra = post.item.extra
        author = {"name": truncate(post.item.author or extra["repo"].split("/")[0], 256)}
        if extra.get("owner_url"):
            author["url"] = extra["owner_url"]
        if extra.get("owner_avatar"):
            author["icon_url"] = extra["owner_avatar"]
        return author
    author = {"name": truncate(post.feed.name, 256)}
    match = GITHUB_FEED_RE.match(post.feed.url)
    if match:
        author["url"] = f"https://github.com/{match.group(1)}/{match.group(2)}"
    icon = post.feed.icon or post.icon
    if not icon and match:
        icon = f"https://github.com/{match.group(1)}.png"
    if icon:
        author["icon_url"] = icon
    return author


def build_message(post: Post) -> tuple[dict, str]:
    """The Discord embed of a post and the name of its forum thread."""
    feed, item = post.feed, post.item
    release = feed.kind == "release"
    repo = feed.kind == "github_search"
    summary = post.summary_ar or post.summary
    lines = [feed.heading] if feed.heading else []
    if release:
        title = release_title(post)
        lines = lines or [f"🆕 **إصدار جديد من {escape_markdown(feed.name)}**"]
        thread_name = f"🆕 {title}"
        match = GITHUB_FEED_RE.match(feed.url)
        footer = f"{match.group(1)}/{match.group(2)} · {item.title}" if match else f"{feed.name} · {item.title}"
    elif repo:
        extra = item.extra
        title = extra["repo"]
        lines = lines or ["🧩 **إضافة جديدة رائجة**"]
        lines.append(f"⭐ {extra['stars']:,} نجمة · 📅 أُنشئت في {extra['created']}")
        # The forum list shows only the post's name: put what it does there too.
        thread_name = f"🧩 {item.title}: {summary}" if summary else f"🧩 {item.title}"
        footer = extra["description"] if post.summary_ar else extra["repo"]
    else:
        title = post.title_ar or item.title
        thread_name = title
        footer = item.title if post.title_ar else feed.name
    if summary:
        if lines:
            lines.append("")
        lines.append(escape_markdown(summary))
    if repo and item.extra.get("topics"):
        lines += ["", "🏷️ " + " ".join(f"`{topic}`" for topic in item.extra["topics"])]
    if feed.show_authors and item.author:
        lines += ["", f"✍️ {escape_markdown(truncate(item.author, 200))}"]
    # Aggregators such as Hacker News link to someone else's article and keep
    # the discussion on their own site; a blog's own comment section is not shown.
    host = urllib.parse.urlsplit(item.link).hostname
    discussion = item.comments if item.comments and urllib.parse.urlsplit(item.comments).hostname != host else None
    if release:
        label = "ملاحظات الإصدار"
    elif repo:
        label = "المستودع على GitHub"
    elif discussion:
        label = "اقرأ المقال"
    else:
        label = f"اقرأ على {feed.name}"
    links = [f"🔗 [{label}]({link_url(item.link)})"]
    if discussion:
        links.append(f"💬 [النقاش على {feed.name}]({link_url(discussion)})")
    lines += ["", " · ".join(links)]
    embed = {
        "author": feed_author(post),
        "title": truncate(title, 256),
        "url": item.link,
        "description": truncate("\n".join(lines).strip(), 4000),
        "color": feed.color if feed.color is not None else (
            COLOR_RELEASE if release else COLOR_REPO if repo else post.channel.color),
        "footer": {"text": truncate(footer, 2048)},
    }
    if item.date:
        embed["timestamp"] = item.date.isoformat()
    if item.image and not release:
        embed["image"] = {"url": item.image}
    return embed, truncate(" ".join(thread_name.split()), THREAD_NAME_CHARS) or "خبر جديد"


def message_payload(channel: Channel, embed: dict, thread_name: str) -> dict:
    # allowed_mentions stops "@everyone" in a title from pinging the server.
    payload: dict = {"embeds": [embed], "allowed_mentions": {"parse": []}}
    if channel.type == "forum":
        # Webhooks of forum channels must name the new post (thread) to create.
        payload["thread_name"] = thread_name
        if channel.applied_tags:
            payload["applied_tags"] = channel.applied_tags
    return payload


def post_discord(webhook: str, payload: dict) -> None:
    data = json.dumps(payload).encode("utf-8")
    url = webhook + ("&" if "?" in webhook else "?") + "wait=true"
    for _ in range(5):
        request = urllib.request.Request(
            url, data=data, method="POST",
            headers={"Content-Type": "application/json", "User-Agent": USER_AGENT},
        )
        try:
            with urllib.request.urlopen(request, timeout=30):
                return
        except urllib.error.HTTPError as error:
            body = error.read().decode("utf-8", "replace")
            if error.code == 429:
                try:
                    retry_after = float(json.loads(body).get("retry_after", 2))
                except (ValueError, AttributeError):
                    retry_after = 2.0
                log.info("Discord rate limit, waiting %.1fs", retry_after)
                time.sleep(min(retry_after, 60) + 0.5)
                continue
            # Never include the webhook URL in errors: it is a secret.
            raise NotifierError(f"Discord rejected the message: HTTP {error.code}: {body[:300]}") from None
        except (urllib.error.URLError, TimeoutError, OSError) as error:
            raise NotifierError(f"Could not reach Discord: {getattr(error, 'reason', error)}") from None
    raise NotifierError("Discord kept rate limiting the webhook; giving up for this run.")


# --------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------

def load_webhook(channel: Channel) -> str:
    webhook = os.environ.get(channel.webhook_secret, "").strip()
    if not webhook:
        raise NotifierError(
            f"{channel.webhook_secret} is not set (a repository secret in GitHub Actions), "
            f"so channel \"{channel.key}\" is skipped. Use --dry-run to test without webhooks."
        )
    if not WEBHOOK_RE.match(webhook):
        raise NotifierError(f"{channel.webhook_secret} does not look like "
                            "https://discord.com/api/webhooks/<id>/<token>; channel skipped.")
    return webhook


def env_flag(name: str, default: bool) -> bool:
    value = os.environ.get(name, "").strip().lower()
    return default if not value else value not in ("0", "false", "no", "off")


def parse_args(argv):
    parser = argparse.ArgumentParser(description="Post RSS/Atom news to Discord channels, in Arabic.")
    parser.add_argument("--dry-run", action="store_true",
                        help="print the Discord payloads instead of posting them; state is not changed")
    parser.add_argument("--latest", type=int, default=0, metavar="N",
                        help="also post the newest N items of every feed, even if already seen (test)")
    parser.add_argument("--channel", default=os.environ.get("CHANNEL", ""), metavar="KEYS",
                        help="only these channels (keys from feeds.json, comma separated)")
    parser.add_argument("--config", type=Path, default=HERE / "feeds.json", help="(default: feeds.json)")
    parser.add_argument("--state", type=Path, default=HERE / "state.json", help="(default: state.json)")
    parser.add_argument("--no-translate", dest="translate", action="store_false",
                        default=env_flag("TRANSLATE", True), help="keep everything in English (env TRANSLATE=0)")
    return parser.parse_args(argv)


def setup_logging() -> None:
    for stream in (sys.stdout, sys.stderr):
        if stream is not None and hasattr(stream, "reconfigure"):
            stream.reconfigure(encoding="utf-8", errors="replace")
    if log.handlers:
        return
    handler = logging.StreamHandler(sys.stderr)
    handler.setFormatter(logging.Formatter("%(asctime)s %(levelname)s %(message)s", "%H:%M:%S"))
    log.addHandler(handler)
    log.setLevel(logging.INFO)


def warn(message: str) -> None:
    log.warning("%s", message)
    if os.environ.get("GITHUB_ACTIONS") == "true":
        print(f"::warning::{message}", flush=True)  # shown on the run's summary page


def fetch_all(feeds: list[Feed], now: datetime) -> dict[str, ParsedFeed | NotifierError]:
    def one(feed: Feed):
        try:
            if feed.kind == "github_search":
                return search_github(feed, now)
            return parse_feed(fetch_feed(feed.url))
        except NotifierError as error:
            return error

    with ThreadPoolExecutor(max_workers=8) as pool:
        return dict(zip([feed.url for feed in feeds], pool.map(one, feeds)))


def add_page_details(posts: list[Post]) -> None:
    """Fill a missing picture or summary from the article page (og:image, og:description)."""
    def one(post: Post) -> None:
        need_image = post.feed.page_image and not post.item.image
        need_summary = post.feed.page_summary and not post.summary
        if not (need_image or need_summary) or not post.item.link.startswith("http"):
            return
        try:
            page = fetch_page(post.item.link)
        except NotifierError as error:
            log.info("No page details for %s: %s", post.item.link, error)
            return
        head = page.split("</head>", 1)[0]
        meta = {}
        for tag in re.findall(r"<meta\b[^>]*>", head, re.I):
            attrs = attributes(tag)
            name = (attrs.get("property") or attrs.get("name") or "").lower()
            if name and attrs.get("content") and name not in meta:
                meta[name] = attrs["content"].strip()
        if need_image:
            image = meta.get("og:image") or meta.get("twitter:image")
            if image:
                post.item.image = urllib.parse.urljoin(post.item.link, image)
        if need_summary:
            post.summary = excerpt(clean_text(meta.get("og:description") or meta.get("description") or ""))

    with ThreadPoolExecutor(max_workers=6) as pool:
        list(pool.map(one, posts))


def run(args) -> int:
    configured = load_config(args.config)
    channels = list(configured)
    if args.channel:
        wanted_keys = {key.strip() for key in args.channel.split(",") if key.strip()}
        unknown = wanted_keys - {channel.key for channel in channels}
        if unknown:
            raise NotifierError(f"Unknown channel(s): {', '.join(sorted(unknown))}; "
                                f"feeds.json has: {', '.join(channel.key for channel in channels)}")
        channels = [channel for channel in channels if channel.key in wanted_keys]

    failures: list[str] = []
    webhooks: dict[str, str] = {}
    if not args.dry_run:
        for channel in list(channels):
            try:
                webhooks[channel.key] = load_webhook(channel)
            except NotifierError as error:
                log.error("%s", error)
                failures.append(channel.key)
                channels.remove(channel)

    state = load_state(args.state)
    before = json.dumps(state, sort_keys=True)
    feeds = [feed for channel in channels for feed in channel.feeds]
    now = datetime.now(timezone.utc)
    results = fetch_all(feeds, now)

    plans: dict[str, list[Post]] = {}
    new_states: dict[str, dict] = {}
    seeded = []
    for channel in channels:
        posts: list[Post] = []
        for feed in channel.feeds:
            result = results[feed.url]
            if isinstance(result, NotifierError):
                warn(f"[{channel.key}] {feed.name}: {result} ({feed.url})")
                continue
            fstate = state["feeds"].get(feed.url)
            to_post, to_skip, new_state = select_items(result.items, feed, fstate, args.latest, now)
            mark_seen(new_state, to_skip)
            new_states[feed.url] = new_state
            if fstate is None:
                seeded.append(feed.name)
            log.info("[%s] %s: %d items, %d to post, %d skipped as backlog%s",
                     channel.key, feed.name, len(result.items), len(to_post),
                     len(to_skip) if fstate else 0, " (first run: recorded as seen)" if fstate is None else "")
            posts += [Post(channel, feed, item, icon=result.icon) for item in to_post]
        # Oldest first, so the newest item ends up on top of a forum and at the bottom of a chat.
        posts.sort(key=lambda post: (post.item.date or now, -post.item.position))
        plans[channel.key] = posts

    all_posts = [post for channel in channels for post in plans[channel.key]]
    for post in all_posts:
        post.summary = item_summary(post.item, post.feed)
    add_page_details(all_posts)
    translate = Translator(args.translate, os.environ.get("MYMEMORY_EMAIL", "").strip() or None)
    # Titles first: when the daily quota runs out, the titles are what matters most.
    for post in all_posts:
        if post.feed.kind == "news":  # release versions and repository names stay as they are
            translated = translate(post.item.title, (post.feed.name,))
            post.title_ar = translated if translated != " ".join(post.item.title.split()) else None
    for post in all_posts:
        if post.summary:
            # The source's own name (claude-mem, a repository) is not a word to translate.
            keep = (post.feed.name, post.item.title) if post.feed.kind == "github_search" else (post.feed.name,)
            post.summary_ar = translate_block(post.summary, translate, keep)
    for post in all_posts:
        embed, thread_name = build_message(post)
        post.payload = message_payload(post.channel, embed, thread_name)
    log.info("%d post(s) in %d channel(s); translation: %s, %d request(s), %d characters",
             len(all_posts), len(channels), translate.status, translate.calls, translate.chars)

    if args.dry_run:
        if seeded and not args.latest:
            log.info("A real run would record the current items of %d new feed(s) and post nothing "
                     "from them. Add --latest N to preview messages.", len(seeded))
        for channel in channels:
            posts = plans[channel.key]
            for index, post in enumerate(posts, 1):
                print(f"===== [{channel.key}] {channel.name} ({channel.type}) {index}/{len(posts)}: "
                      f"{post.label} =====")
                print(json.dumps(post.payload, indent=2, ensure_ascii=False))
        log.info("Dry run: nothing was posted and %s was not changed.", args.state.name)
        return 0

    # Feeds that were read get their new state now; posted items are added as they go out.
    for url, new_state in new_states.items():
        state["feeds"][url] = new_state
    first = True
    for channel in channels:
        for post in plans[channel.key]:
            if not first:
                time.sleep(POST_DELAY)
            first = False
            try:
                post_discord(webhooks[channel.key], post.payload)
            except NotifierError as error:
                log.error("[%s] %s", channel.key, error)
                failures.append(channel.key)
                break
            mark_seen(state["feeds"][post.feed.url], [post.item])
            log.info("[%s] Posted %s", channel.key, post.label)

    if not args.channel:
        urls = {feed.url for channel in configured for feed in channel.feeds}
        for url in [url for url in state["feeds"] if url not in urls]:
            del state["feeds"][url]  # a feed removed from feeds.json
    for fstate in state["feeds"].values():
        fstate["seen"] = fstate["seen"][-KEEP_SEEN:]
    if json.dumps(state, sort_keys=True) != before:
        save_state(args.state, state)
        log.info("Saved %s", args.state.name)
    if failures:
        raise NotifierError(f"Failed channel(s): {', '.join(dict.fromkeys(failures))}")
    if not all_posts:
        log.info("Nothing new.")
    return 0


def main(argv=None) -> int:
    args = parse_args(argv)
    setup_logging()
    try:
        return run(args)
    except NotifierError as error:
        log.error("%s", error)
        return 1


if __name__ == "__main__":
    sys.exit(main())
