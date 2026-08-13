#!/usr/bin/env python3
"""
H14 -- PreToolUse hook blocking destructive git ops in Bash tool calls
without explicit `git ok` consent in the latest user message.

Reads PreToolUse JSON on stdin. If the tool is Bash and the command contains
a destructive git verb, the hook reads `transcript_path` from the payload
and inspects the latest user message for the literal phrase `git ok`
(case-insensitive). If absent -> exit 2; the tool call is blocked.

Destructive verbs (matched after `git `):
  commit, push, stash, revert, reset, checkout, restore, clean,
  rm, mv, pull, merge, rebase, cherry-pick
Plus: branch -D / -d / --delete

Read-only verbs (status, log, diff, show, grep, blame, fetch, ls-*, rev-*,
config when reading, remote when listing) are unmatched and pass through.

Fails open if transcript_path is missing or unreadable -- never blocks
legitimately-needed work due to a hook bug.

CLAUDE.md source: '⛔ Editing and git' section.
"""

HOOK_EVENT = "PreToolUse"
HOOK_MATCHER = "Bash"   # None = all calls for this event

import json
import re
import sys

DESTRUCTIVE_GIT_RE = re.compile(
    r"\bgit\s+("
    r"commit|push|stash|revert|reset|checkout|restore|clean"
    r"|rm|mv|pull|merge|rebase|cherry-pick"
    r")\b"
)
BRANCH_DELETE_RE = re.compile(r"\bgit\s+branch\s+(-D|-d|--delete)\b")

CONSENT_RE = re.compile(r"\bgit\s+ok\b", re.IGNORECASE)

def find_match(command):
    m = DESTRUCTIVE_GIT_RE.search(command)
    if m:
        return f"git {m.group(1)}"
    m = BRANCH_DELETE_RE.search(command)
    if m:
        return f"git branch {m.group(1)}"
    return None

def read_latest_user_message(transcript_path):
    if not transcript_path:
        return None
    try:
        with open(transcript_path, "r", encoding="utf-8") as f:
            lines = f.readlines()
    except (FileNotFoundError, OSError):
        return None
    for line in reversed(lines):
        line = line.strip()
        if not line:
            continue
        try:
            event = json.loads(line)
        except Exception:
            continue
        content = None
        # Variant 1: flat {role, content}
        if event.get("role") == "user":
            content = event.get("content", "")
        # Variant 2: nested {message: {role, content}}
        msg = event.get("message")
        if content is None and isinstance(msg, dict) and msg.get("role") == "user":
            content = msg.get("content", "")
        # Variant 3: type field
        if content is None and event.get("type") == "user":
            content = event.get("content", "") or event.get("text", "")
        if content is None:
            continue
        # Skip tool_result events (Anthropic protocol carries tool results
        # as role=user, but they're not real user prompts).
        if _is_tool_result_only(content):
            continue
        return _extract_text(content)
    return None

def _is_tool_result_only(content):
    """True if `content` is a list whose every element is a tool_result block.
    Such events are tool plumbing, not user prompts."""
    if not isinstance(content, list) or not content:
        return False
    for c in content:
        if not isinstance(c, dict):
            return False
        if c.get("type") != "tool_result":
            return False
    return True

def _extract_text(content):
    if isinstance(content, str):
        return content
    if isinstance(content, list):
        return "".join(
            (c.get("text", "") if isinstance(c, dict) else str(c))
            for c in content
        )
    return str(content)

def main():
    try:
        payload = json.load(sys.stdin)
    except Exception:
        return 0
    if payload.get("tool_name", "") != "Bash":
        return 0
    cmd = payload.get("tool_input", {}).get("command", "")
    matched = find_match(cmd)
    if not matched:
        return 0
    transcript_path = payload.get("transcript_path", "")
    latest = read_latest_user_message(transcript_path)
    if latest is None:
        return 0  # fail-open
    if CONSENT_RE.search(latest):
        return 0
    # Block
    print(f"hol4-hook H14: refused destructive git op: {matched!r}", file=sys.stderr)
    print("", file=sys.stderr)
    print("CLAUDE.md '⛔ Editing and git':", file=sys.stderr)
    print("  No git command that modifies working-tree or repo state runs", file=sys.stderr)
    print("  without an explicit, in-context user request for THAT command.", file=sys.stderr)
    print("", file=sys.stderr)
    print("Latest user message does not contain consent token `git ok`.", file=sys.stderr)
    print("To grant consent, include the literal phrase `git ok` somewhere in", file=sys.stderr)
    print("your next message.", file=sys.stderr)
    return 2

if __name__ == "__main__":
    sys.exit(main())
