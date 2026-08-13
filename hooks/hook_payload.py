#!/usr/bin/env python3
"""
Payload helpers shared by the hooks in this directory.

Not itself a hook: `install_hooks.py` discovers only files named
`h<N>_<name>.py`, so this module is never wired into settings.json.

Two things every hook needs and none should reimplement:

- `output_text(payload)` — a PostToolUse tool result as searchable text. The
  MCP result schema is not canonical, so several field names are tried and
  every string leaf is collected. Strings are kept RAW: escaping non-ASCII
  would hide the goal-display markers hooks match on (H16's `⅋ᵣ`), and
  re-encoding a dict as JSON would turn its newlines into `\\n`, breaking
  line-anchored patterns.
- `latest_user_message(payload)` — the text of the newest real user turn in
  the session transcript, for the consent-gated PreToolUse hooks. Tool
  results ride the transcript as `role=user`; those are plumbing, not
  prompts, and are skipped.
"""
import json

RESULT_KEYS = ("tool_output", "tool_response", "tool_result",
               "result", "output", "response")


def _strings(v):
    """Every string leaf of a JSON-shaped value, in order."""
    if v is None:
        return []
    if isinstance(v, str):
        return [v]
    if isinstance(v, dict):
        return [s for x in v.values() for s in _strings(x)]
    if isinstance(v, (list, tuple)):
        return [s for x in v for s in _strings(x)]
    return [str(v)]


def output_text(payload):
    """A PostToolUse tool result flattened to one searchable string."""
    return "\n".join(s for key in RESULT_KEYS for s in _strings(payload.get(key)))


def _is_tool_result_only(content):
    """True if `content` is a list whose every element is a tool_result block.
    Such events are tool plumbing, not user prompts."""
    if not isinstance(content, list) or not content:
        return False
    return all(isinstance(c, dict) and c.get("type") == "tool_result"
               for c in content)


def _text_of(content):
    if isinstance(content, str):
        return content
    if isinstance(content, list):
        return "".join((c.get("text", "") if isinstance(c, dict) else str(c))
                       for c in content)
    return str(content)


def latest_user_message(payload):
    """Text of the newest real user turn, or None if unreadable (fail open)."""
    path = payload.get("transcript_path", "")
    if not path:
        return None
    try:
        with open(path, "r", encoding="utf-8") as f:
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
        if event.get("role") == "user":                       # flat
            content = event.get("content", "")
        msg = event.get("message")
        if content is None and isinstance(msg, dict) and msg.get("role") == "user":
            content = msg.get("content", "")                  # nested
        if content is None and event.get("type") == "user":   # type field
            content = event.get("content", "") or event.get("text", "")
        if content is None or _is_tool_result_only(content):
            continue
        return _text_of(content)
    return None
