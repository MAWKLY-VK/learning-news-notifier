"""Offline tests: no network, fake feeds, a fake Discord and a fake translator.

Run from the project folder:  python -m unittest discover -s tests -v
"""

import contextlib
import io
import json
import os
import sys
import tempfile
import unittest
from datetime import datetime, timedelta, timezone
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import notifier  # noqa: E402

FAKE_HOOK = "https://discord.com/api/webhooks/1/fake-token-for-tests"
NEWS_URL = "https://example.com/news.xml"
RELEASES_URL = "https://github.com/acme/tool/releases.atom"
PAPERS_URL = "https://example.org/papers.xml"
BASE = datetime(2026, 9, 1, 12, 0, tzinfo=timezone.utc)


def rss_date(hours: float) -> str:
    return (BASE + timedelta(hours=hours)).strftime("%a, %d %b %Y %H:%M:%S +0000")


def rss(items, extra_ns="") -> bytes:
    """items: (guid, title, hours after BASE, extra XML inside <item>)"""
    body = "".join(
        f"<item><title>{title}</title><link>https://example.com/{guid}</link>"
        f"<guid>{guid}</guid><pubDate>{rss_date(hours)}</pubDate>{extra}</item>"
        for guid, title, hours, extra in items
    )
    return (f'<?xml version="1.0"?><rss version="2.0" xmlns:media="http://search.yahoo.com/mrss/" '
            f'xmlns:dc="http://purl.org/dc/elements/1.1/" '
            f'xmlns:content="http://purl.org/rss/1.0/modules/content/" {extra_ns}>'
            f"<channel><title>Example</title>{body}</channel></rss>").encode("utf-8")


def atom_releases(tags) -> bytes:
    """tags: (tag, hours after BASE)"""
    entries = "".join(
        f"<entry><id>tag:github.com,2008:Repository/1/{tag}</id>"
        f"<updated>{(BASE + timedelta(hours=hours)).isoformat()}</updated>"
        f'<link rel="alternate" type="text/html" href="https://github.com/acme/tool/releases/tag/{tag}"/>'
        f"<title>{tag}</title>"
        f'<content type="html">&lt;h2&gt;What&#39;s changed&lt;/h2&gt;&lt;ul&gt;'
        f"&lt;li&gt;Added the {tag} feature by @someone in #12&lt;/li&gt;&lt;/ul&gt;</content>"
        f'<media:thumbnail height="30" width="30" url="https://avatars.example/u/1"/></entry>'
        for tag, hours in tags
    )
    return ('<?xml version="1.0" encoding="UTF-8"?><feed xmlns="http://www.w3.org/2005/Atom" '
            'xmlns:media="http://search.yahoo.com/mrss/"><title>Release notes</title>'
            f"{entries}</feed>").encode("utf-8")


CONFIG = {
    "limit": 3,
    "channels": [
        {"key": "news", "name": "أخبار", "type": "forum", "webhook_secret": "HOOK_NEWS",
         "color": "#10A37F", "applied_tags": ["111"],
         "feeds": [{"name": "Example", "url": NEWS_URL},
                   {"name": "Tool", "url": RELEASES_URL, "kind": "release"}]},
        {"key": "papers", "name": "أبحاث", "type": "text", "webhook_secret": "HOOK_PAPERS",
         "feeds": [{"name": "Papers", "url": PAPERS_URL, "limit": 1,
                    "skip_text": "Announce Type: replace", "show_authors": True}]},
    ],
}


class FakeWorld:
    """Feeds served from memory and a Discord that records what it gets."""

    def __init__(self):
        self.feeds = {
            NEWS_URL: rss([("n1", "First news", 1, ""), ("n2", "Second news", 2, "")]),
            RELEASES_URL: atom_releases([("v1.0.0", 1)]),
            PAPERS_URL: rss([("p1", "Old paper", 0, "<description>Announce Type: new Abstract: A.</description>")]),
        }
        self.posted = []  # (webhook, payload)
        self.fail_after = None

    def fetch_feed(self, url):
        if url not in self.feeds:
            raise notifier.NotifierError("HTTP 404")
        return self.feeds[url]

    def post(self, webhook, payload):
        if self.fail_after is not None and len(self.posted) >= self.fail_after:
            raise notifier.NotifierError("Discord rejected the message: HTTP 500")
        self.posted.append((webhook, payload))


def fake_mymemory(self, text):
    self.calls += 1
    return "عربي " + text


class NotifierTestCase(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.dir = Path(self.tmp.name)
        self.config = self.dir / "feeds.json"
        self.config.write_text(json.dumps(CONFIG, ensure_ascii=False), encoding="utf-8")
        self.state = self.dir / "state.json"
        self.world = FakeWorld()
        patches = [
            mock.patch.object(notifier, "fetch_feed", self.world.fetch_feed),
            mock.patch.object(notifier, "fetch_page", side_effect=notifier.NotifierError("offline")),
            mock.patch.object(notifier, "post_discord", self.world.post),
            mock.patch.object(notifier, "POST_DELAY", 0),
            mock.patch.object(notifier.Translator, "fetch", fake_mymemory),
            mock.patch.dict(os.environ, {"HOOK_NEWS": FAKE_HOOK, "HOOK_PAPERS": FAKE_HOOK + "2",
                                         "MYMEMORY_EMAIL": "", "TRANSLATE": "", "CHANNEL": ""}),
        ]
        for patch in patches:
            patch.start()
            self.addCleanup(patch.stop)
        self.addCleanup(self.tmp.cleanup)
        notifier.setup_logging()
        notifier.log.setLevel("CRITICAL")

    def run_notifier(self, *args):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = notifier.main(["--config", str(self.config), "--state", str(self.state), *args])
        return code, out.getvalue()

    def read_state(self):
        return json.loads(self.state.read_text(encoding="utf-8"))

    def titles(self, start=0):
        return [payload["embeds"][0]["footer"]["text"] for _, payload in self.world.posted[start:]]


class SeedingAndDedupe(NotifierTestCase):
    def test_first_run_seeds_silently(self):
        code, _ = self.run_notifier()
        self.assertEqual(code, 0)
        self.assertEqual(self.world.posted, [])
        state = self.read_state()
        self.assertEqual(set(state["feeds"]), {NEWS_URL, RELEASES_URL, PAPERS_URL})
        self.assertEqual(len(state["feeds"][NEWS_URL]["seen"]), 2)

    def test_quiet_run_does_not_rewrite_state(self):
        self.run_notifier()
        before = self.state.read_bytes()
        os.utime(self.state, (0, 0))
        self.run_notifier()
        self.assertEqual(self.world.posted, [])
        self.assertEqual(self.state.read_bytes(), before)
        self.assertEqual(self.state.stat().st_mtime, 0)

    def test_newest_three_posted_oldest_first_and_backlog_skipped(self):
        self.run_notifier()
        self.world.feeds[NEWS_URL] = rss(
            [(f"x{n}", f"New {n}", 10 + n, "") for n in range(5, 0, -1)]
            + [("n1", "First news", 1, ""), ("n2", "Second news", 2, "")]
        )
        code, _ = self.run_notifier()
        self.assertEqual(code, 0)
        self.assertEqual(self.titles(), ["New 3", "New 4", "New 5"])
        seen = self.read_state()["feeds"][NEWS_URL]["seen"]
        self.assertEqual(len(seen), 7)  # New 1 and New 2 are skipped for good, not queued

        self.run_notifier()
        self.assertEqual(len(self.world.posted), 3)

    def test_item_posted_once_even_if_it_moves(self):
        self.run_notifier()
        self.world.feeds[NEWS_URL] = rss([("n3", "Third", 3, ""), ("n1", "First news", 1, ""),
                                          ("n2", "Second news", 2, "")])
        self.run_notifier()
        self.world.feeds[NEWS_URL] = rss([("n2", "Second news", 2, ""), ("n3", "Third (edited)", 3, ""),
                                          ("n1", "First news", 1, "")])
        self.run_notifier()
        self.assertEqual(self.titles(), ["Third"])

    def test_per_feed_limit_override(self):
        self.run_notifier()
        self.world.feeds[PAPERS_URL] = rss([(f"p{n}", f"Paper {n}", 5 + n, "") for n in range(4)])
        self.run_notifier()
        self.assertEqual(self.titles(), ["Paper 3"])  # limit 1 for this feed

    def test_old_unseen_item_is_ignored(self):
        self.run_notifier()
        self.world.feeds[NEWS_URL] = rss([("n2", "Second news", 2, ""), ("n1", "First news", 1, ""),
                                          ("ancient", "Ancient", -24 * 30, "")])
        self.run_notifier()
        self.assertEqual(self.world.posted, [])

    def test_failed_post_is_retried_next_run(self):
        self.run_notifier()
        self.world.feeds[NEWS_URL] = rss([("a", "Item A", 10, ""), ("b", "Item B", 11, "")])
        self.world.fail_after = 1
        code, _ = self.run_notifier()
        self.assertEqual(code, 1)
        self.assertEqual(self.titles(), ["Item A"])
        self.world.fail_after = None
        code, _ = self.run_notifier()
        self.assertEqual(code, 0)
        self.assertEqual(self.titles(), ["Item A", "Item B"])

    def test_seen_list_is_bounded(self):
        with mock.patch.object(notifier, "SCAN", 3), mock.patch.object(notifier, "KEEP_SEEN", 5):
            for run in range(6):
                self.world.feeds[NEWS_URL] = rss([(f"r{run}-{n}", f"R{run} {n}", 10 * run + n, "")
                                                  for n in range(3)])
                self.run_notifier()
        self.assertLessEqual(len(self.read_state()["feeds"][NEWS_URL]["seen"]), 5)

    def test_removed_feed_is_forgotten(self):
        self.run_notifier()
        config = json.loads(json.dumps(CONFIG))
        config["channels"][0]["feeds"].pop()  # drop the release feed
        self.config.write_text(json.dumps(config, ensure_ascii=False), encoding="utf-8")
        self.run_notifier()
        self.assertNotIn(RELEASES_URL, self.read_state()["feeds"])

    def test_broken_feed_keeps_its_state(self):
        self.run_notifier()
        self.world.feeds[NEWS_URL] = b"<html>not a feed"
        code, _ = self.run_notifier()
        self.assertEqual(code, 0)
        self.assertEqual(len(self.read_state()["feeds"][NEWS_URL]["seen"]), 2)


class Filters(NotifierTestCase):
    def test_prereleases_are_skipped(self):
        self.run_notifier()
        self.world.feeds[RELEASES_URL] = atom_releases(
            [("v1.2.0-rc1", 30), ("v1.1.0", 20), ("v1.1.0-alpha.3", 15), ("v1.0.0", 1)])
        self.run_notifier()
        self.assertEqual(len(self.world.posted), 1)
        embed = self.world.posted[0][1]["embeds"][0]
        self.assertEqual(embed["title"], "Tool v1.1.0")
        self.assertEqual(self.world.posted[0][1]["thread_name"], "🆕 Tool v1.1.0")
        self.assertIn("Added the v1.1.0 feature", embed["description"])
        self.assertNotIn("@someone", embed["description"])
        self.assertNotIn("image", embed)  # the 30px avatar is not a picture

    def test_skip_text(self):
        self.run_notifier()
        self.world.feeds[PAPERS_URL] = rss([
            ("p2", "Replaced", 9, "<description>Announce Type: replace Abstract: B.</description>"),
            ("p3", "Brand new", 8, "<description>Announce Type: new Abstract: C.</description>"),
        ])
        self.run_notifier()
        self.assertEqual(self.titles(), ["Brand new"])


class Payloads(NotifierTestCase):
    def test_forum_and_text_payloads(self):
        long_title = "Very long headline " * 10
        self.world.feeds[NEWS_URL] = rss([("n1", long_title, 1, "")])
        self.world.feeds[PAPERS_URL] = rss([("p1", "A paper", 1,
                                             "<dc:creator>Ada Lovelace</dc:creator>"
                                             "<description>arXiv:1 Announce Type: new\nAbstract: We study.</description>")])
        code, _ = self.run_notifier("--latest", "1")
        self.assertEqual(code, 0)
        by_hook = {}
        for hook, payload in self.world.posted:
            by_hook.setdefault(hook, []).append(payload)
        forum = next(p for p in by_hook[FAKE_HOOK] if not p["thread_name"].startswith("🆕"))
        self.assertLessEqual(len(forum["thread_name"]), 100)
        self.assertTrue(forum["thread_name"].startswith("عربي"))
        self.assertEqual(forum["applied_tags"], ["111"])
        self.assertEqual(forum["allowed_mentions"], {"parse": []})
        self.assertEqual(forum["embeds"][0]["footer"]["text"], " ".join(long_title.split()))
        text = by_hook[FAKE_HOOK + "2"][0]
        self.assertNotIn("thread_name", text)
        self.assertNotIn("applied_tags", text)
        description = text["embeds"][0]["description"]
        self.assertIn("Ada Lovelace", description)
        self.assertIn("عربي We study.", description)
        self.assertNotIn("Announce Type", description)

    def test_translation_failure_falls_back_to_english(self):
        def broken(self, text):
            raise notifier.NotifierError("quota")

        self.world.feeds[NEWS_URL] = rss([("n1", "Plain English", 1, "<description>Summary here.</description>")])
        with mock.patch.object(notifier.Translator, "fetch", broken):
            self.run_notifier("--latest", "1", "--channel", "news")
        payload = self.world.posted[0][1]
        embed = payload["embeds"][0]
        self.assertEqual(payload["thread_name"], "Plain English")
        self.assertEqual(embed["title"], "Plain English")
        self.assertEqual(embed["footer"]["text"], "Example")
        self.assertIn("Summary here.", embed["description"])

    def test_dry_run_posts_nothing_and_keeps_state(self):
        code, out = self.run_notifier("--dry-run", "--latest", "1")
        self.assertEqual(code, 0)
        self.assertEqual(self.world.posted, [])
        self.assertFalse(self.state.exists())
        self.assertIn('"thread_name"', out)
        self.assertEqual(out.count("====="), 2 * 3)  # one header per feed

    def test_missing_webhook_skips_only_that_channel(self):
        with mock.patch.dict(os.environ, {"HOOK_PAPERS": ""}):
            code, _ = self.run_notifier("--latest", "1")
        self.assertEqual(code, 1)
        self.assertTrue(self.world.posted)
        self.assertTrue(all(hook == FAKE_HOOK for hook, _ in self.world.posted))
        self.assertNotIn(PAPERS_URL, self.read_state()["feeds"])

    def test_mentions_and_markdown_are_neutralised(self):
        self.world.feeds[NEWS_URL] = rss([("n1", "Ping", 1, "<description># @everyone *bold*</description>")])
        self.run_notifier("--latest", "1", "--channel", "news", "--no-translate")
        payload = self.world.posted[0][1]
        self.assertEqual(payload["allowed_mentions"], {"parse": []})
        self.assertTrue(payload["embeds"][0]["description"].startswith("\\# @everyone \\*bold\\*"))


class Parsing(unittest.TestCase):
    def test_rss_images_authors_and_repairs(self):
        data = rss([
            ("a", "With media &amp; more", 1,
             '<media:content url="https://img.example/a.jpg" medium="image"/><dc:creator>Jane</dc:creator>'
             "<comments>https://news.example/item?id=1</comments>"),
            ("b", "With enclosure", 2, '<enclosure url="https://img.example/b.png" type="image/png" length="1"/>'),
            ("c", "With html", 3,
             '<content:encoded><![CDATA[<p>Hi&nbsp;there</p><img src="/pixel.gif" width="1">'
             '<img src="/big.jpg">]]></content:encoded>'),
        ])
        # An HTML entity outside CDATA is invalid XML; the parser repairs it.
        data = data.replace(b"<title>With enclosure</title>", b"<title>With&nbsp;enclosure</title>")
        by_title = {item.title: item for item in notifier.parse_feed(data).items}
        self.assertEqual(by_title["With media & more"].image, "https://img.example/a.jpg")
        self.assertEqual(by_title["With media & more"].author, "Jane")
        self.assertEqual(by_title["With media & more"].comments, "https://news.example/item?id=1")
        self.assertEqual(by_title["With enclosure"].image, "https://img.example/b.png")
        self.assertEqual(by_title["With html"].image, "https://example.com/big.jpg")
        self.assertEqual(by_title["With html"].date, BASE + timedelta(hours=3))

    def test_atom_links_and_dates(self):
        data = (b'<feed xmlns="http://www.w3.org/2005/Atom"><title>T</title><entry><id>urn:1</id>'
                b'<title type="html">&lt;b&gt;Bold&lt;/b&gt; title</title>'
                b'<link rel="self" href="https://x.example/self"/>'
                b'<link rel="alternate" href="https://x.example/post"/>'
                b"<published>2026-09-01T10:00:00-04:00</published><updated>2026-09-03T00:00:00Z</updated>"
                b"<author><name>Sam</name></author>"
                b'<summary type="html">&lt;p&gt;Short &lt;a href="#"&gt;summary&lt;/a&gt;.&lt;/p&gt;</summary>'
                b"</entry></feed>")
        item = notifier.parse_feed(data).items[0]
        self.assertEqual(item.title, "Bold title")
        self.assertEqual(item.link, "https://x.example/post")
        self.assertEqual(item.date, datetime(2026, 9, 1, 14, 0, tzinfo=timezone.utc))
        self.assertEqual(item.author, "Sam")
        self.assertEqual(notifier.html_to_text(item.summary_html), "Short summary.")

    def test_excerpt_cuts_at_sentence(self):
        text = "First sentence is here. " * 20
        result = notifier.excerpt(text.strip(), 100)
        self.assertLessEqual(len(result), 100)
        self.assertTrue(result.endswith("."))

    def test_protect_and_restore(self):
        text = "Claude Code v2.1.3 fixes CVE-2026-1234 in `foo_bar` for LLMs on GitHub"
        protected, tokens = notifier.protect(text)
        self.assertNotIn("CVE", protected)
        self.assertNotIn("GitHub", protected)
        self.assertIn("النماذج اللغوية الكبيرة", tokens)
        self.assertIsNotNone(notifier.restore(protected, tokens))
        self.assertIsNone(notifier.restore(protected.replace("ZQ0", ""), tokens))

        protected, tokens = notifier.protect("fix(acp): open /config for an LLM-Referenced C-test")
        self.assertEqual(tokens, ["fix(acp):", "/config", "LLM-Referenced", "C-test"])
        self.assertEqual(notifier.tidy("جلب GPT - Rosalind ؟", "Bringing GPT-Rosalind?"), "جلب GPT-Rosalind؟")

    def test_bad_config_is_reported(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "feeds.json"
            config = json.loads(json.dumps(CONFIG))
            config["channels"][1]["type"] = "voice"
            path.write_text(json.dumps(config), encoding="utf-8")
            with self.assertRaises(notifier.NotifierError):
                notifier.load_config(path)

    def test_shipped_config_is_valid(self):
        channels = notifier.load_config(notifier.HERE / "feeds.json")
        self.assertEqual({channel.key: channel.type for channel in channels},
                         {"ai": "forum", "programming": "forum", "security": "forum", "research": "text"})
        self.assertEqual({channel.webhook_secret for channel in channels},
                         {"DISCORD_WEBHOOK_AI", "DISCORD_WEBHOOK_PROGRAMMING",
                          "DISCORD_WEBHOOK_SECURITY", "DISCORD_WEBHOOK_RESEARCH"})


if __name__ == "__main__":
    unittest.main()
