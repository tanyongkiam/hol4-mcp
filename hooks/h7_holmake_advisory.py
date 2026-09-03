#!/usr/bin/env python3
"""
H7 -- PostToolUse hook injecting a RULE A reminder after a holmake call that
fits the edit-then-rebuild loop.

Advisory only, never blocks. Keyed on repeats per session (state under
~/.claude/hook-state/<session_id>/h7_builds.json): the first build of a
(workdir, target) is silent, and so is a rebuild with no *Script.sml in the
workdir modified since the previous build (a retry). A rebuild within 30
minutes AFTER a script edit is the signature of using holmake to check an
edit -- that one gets the reminder, worded for that loop.

Rule source: hol4-proving skill '⛔ RULE A' / 'HOL4 - iteration loop'.
"""

HOOK_EVENT = "PostToolUse"
HOOK_MATCHER = "mcp__hol4__holmake"   # None = all calls for this event

import glob
import json
import os
import sys
import time

STATE = os.path.expanduser("~/.claude/hook-state")
WINDOW_S = 30 * 60

REMINDER_TEMPLATE = """\
hol4-hook H7: Holmake ran again on {target}, {mins} min after the previous
build, with a *Script.sml edited in between -- the edit-then-rebuild loop.

Per hol4-proving skill RULE A: holmake is the FILE-BUILD GATE, not the way to
check an edit. Read the edit with hol_state_at (it auto-detects the change)
and confirm the theorem with hol_check_proof; rebuild ONCE when the file is
done. A theorem with surviving Resume blocks also needs its `Finalise <thm>;`
(skill Gate 2) -- without it the theorem stays cheated even when every
Resume body is OK."""


def describe_target(tool_input):
    workdir = tool_input.get("workdir", "")
    target = tool_input.get("target", "")
    if workdir and target:
        return f"{workdir} (target={target})"
    return workdir or target or "<unknown target>"


def state_file(payload):
    return os.path.join(STATE, payload.get("session_id") or "nosession",
                        "h7_builds.json")


def load_state(path):
    try:
        with open(path, encoding="utf-8") as fh:
            return json.load(fh)
    except Exception:
        return {}


def save_state(path, state):
    try:
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w", encoding="utf-8") as fh:
            json.dump(state, fh)
    except OSError:
        pass


def newest_script_mtime(workdir):
    newest = 0.0
    for p in glob.glob(os.path.join(workdir, "*Script.sml")):
        try:
            newest = max(newest, os.path.getmtime(p))
        except OSError:
            pass
    return newest


def main():
    try:
        payload = json.load(sys.stdin)
    except Exception:
        return 0
    if payload.get("tool_name", "") != "mcp__hol4__holmake":
        return 0
    ti = payload.get("tool_input", {})
    workdir = os.path.abspath(ti.get("workdir") or payload.get("cwd") or ".")
    key = f"{workdir}::{ti.get('target') or ''}"
    path = state_file(payload)
    state = load_state(path)
    prev = state.get(key)
    now = time.time()
    state[key] = {"ts": now}
    save_state(path, state)
    if not prev:
        return 0
    age = now - float(prev.get("ts", 0))
    if not (0 <= age < WINDOW_S):
        return 0
    if newest_script_mtime(workdir) <= float(prev.get("ts", 0)):
        return 0
    print(json.dumps({
        "hookSpecificOutput": {
            "hookEventName": "PostToolUse",
            "additionalContext": REMINDER_TEMPLATE.format(
                target=describe_target(ti), mins=int(age // 60)),
        }
    }))
    return 0

if __name__ == "__main__":
    sys.exit(main())
