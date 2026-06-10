#!/usr/bin/env python3
"""
H22 -- SessionStart hook injecting a directive to load the hol4-proving skill
when the session starts in a HOL4 project directory.

Detection: cwd (or up to 3 ancestors) contains a Holmakefile or .holpath, or
cwd itself contains *Script.sml files. Stateless, advisory only, never blocks;
silent (exit 0, no output) outside HOL4 directories and on any error.

The HOL4 ruleset lives in ~/.claude/skills/hol4-proving/SKILL.md; the global
CLAUDE.md only carries a pointer. This hook is the mechanical safety net that
makes the skill load on the FIRST attempt rather than after a violation.
"""
import glob
import json
import os
import sys

DIRECTIVE = """\
hol4-hook H22: HOL4 project detected (Holmakefile/.holpath/*Script.sml).
Before ANY proof work this session -- writing a tactic, editing a *Script.sml,
calling a hol_*/holmake MCP tool, or writing a HOL proof plan -- load the HOL4
ruleset: invoke the hol4-proving skill (Skill tool), or Read
~/.claude/skills/hol4-proving/SKILL.md. The rules apply on the FIRST attempt."""

MARKERS = ("Holmakefile", ".holpath")
ANCESTOR_LEVELS = 3

def is_hol4_dir(cwd):
    d = cwd
    for _ in range(ANCESTOR_LEVELS + 1):
        for m in MARKERS:
            if os.path.exists(os.path.join(d, m)):
                return True
        parent = os.path.dirname(d)
        if parent == d:
            break
        d = parent
    return bool(glob.glob(os.path.join(cwd, "*Script.sml")))

def main():
    try:
        payload = json.load(sys.stdin)
        cwd = payload.get("cwd") or os.getcwd()
        if not is_hol4_dir(cwd):
            return 0
        print(json.dumps({
            "hookSpecificOutput": {
                "hookEventName": "SessionStart",
                "additionalContext": DIRECTIVE,
            }
        }))
    except Exception:
        return 0
    return 0

if __name__ == "__main__":
    sys.exit(main())
