#!/usr/bin/env python3
"""
H19 -- PreToolUse hook blocking mcp__hol4__hol_restart without explicit
`restart ok` consent in the latest user message.

Reads PreToolUse JSON on stdin. If the tool is mcp__hol4__hol_restart, the
hook reads `transcript_path` from the payload and inspects the latest user
message for the literal phrase `restart ok` (case-insensitive). If absent
-> exit 2; the tool call is blocked.

Rationale: hol4-proving skill RULE J / 'HOL4 -- iteration loop': hol_restart is
effectively never needed. A broken/weird replay is a proof or navigation
error to re-diagnose and fix -- NOT stale state / cache / corruption (which
is essentially never the cause). Restarting wipes session state and masks
the real bug. Consent must be explicit, per-request, like `git ok` (H14).

Fails open if transcript_path is missing or unreadable -- never blocks
legitimately-needed work due to a hook bug.
"""

HOOK_EVENT = "PreToolUse"
HOOK_MATCHER = "mcp__hol4__hol_restart"   # None = all calls for this event

import json
import re
import sys

CONSENT_RE = re.compile(r"\brestart\s+ok\b", re.IGNORECASE)

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
        # Skip tool_result events (carried as role=user but not real prompts).
        if _is_tool_result_only(content):
            continue
        return _extract_text(content)
    return None

def _is_tool_result_only(content):
    """True if `content` is a list whose every element is a tool_result block."""
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
    if payload.get("tool_name", "") != "mcp__hol4__hol_restart":
        return 0
    transcript_path = payload.get("transcript_path", "")
    latest = read_latest_user_message(transcript_path)
    if latest is None:
        return 0  # fail-open
    if CONSENT_RE.search(latest):
        return 0
    # Block
    print("hol4-hook H19: refused hol_restart without consent.", file=sys.stderr)
    print("", file=sys.stderr)
    print("hol4-proving skill RULE J / 'HOL4 -- iteration loop':", file=sys.stderr)
    print("  hol_restart is effectively never needed. A broken/weird replay", file=sys.stderr)
    print("  is a proof or navigation error to re-diagnose and fix -- NOT", file=sys.stderr)
    print("  stale state / cache / corruption (essentially never the cause).", file=sys.stderr)
    print("", file=sys.stderr)
    print("Latest user message does not contain consent token `restart ok`.", file=sys.stderr)
    print("To grant consent, include the literal phrase `restart ok` somewhere", file=sys.stderr)
    print("in your next message.", file=sys.stderr)
    return 2

if __name__ == "__main__":
    sys.exit(main())
