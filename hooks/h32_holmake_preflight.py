#!/usr/bin/env python3
"""
H32 -- PreToolUse hook on mcp__hol4__holmake: a build must name its target,
and a target whose stale ancestors live in ANOTHER directory needs the
user's `build ok`.

Two build shapes the rules reserve for the user (hol4-proving RULE A, build
ownership):
  - an UNTARGETED build (no `target`): Holmake builds every theory in the
    directory, including ones nobody is working on;
  - a targeted build whose ancestor closure has stale theories OUTSIDE the
    workdir: Holmake follows INCLUDES and rebuilds those directories too, so
    the call quietly becomes a build of someone else's theory.
An in-workdir target with fresh (or merely in-workdir-stale) ancestors passes
silently. Staleness is H30's make-style check over the target's ancestor
closure (imported from h30_stale_ancestors), so the two hooks agree.

Fails open on anything unexpected: no repo, unknown target script, closure
too large, unreadable transcript. Escape hatch: literal phrase `build ok` in
the latest user message.
"""

HOOK_EVENT = "PreToolUse"
HOOK_MATCHER = "mcp__hol4__holmake"

import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import h30_stale_ancestors as h30  # noqa: E402
from hook_payload import latest_user_message  # noqa: E402

CONSENT_RE = re.compile(r"\bbuild\s+ok\b", re.IGNORECASE)
MAX_SHOWN = 4


def target_script(workdir, target):
    """The Script.sml a holmake target names, or None if it is not a theory
    of this workdir (`fooTheory`, `fooTheory.dat`, `fooTheory.uo`, `foo`)."""
    name = re.sub(r"Theory(?:\.\w+)?$", "", os.path.basename(target))
    path = os.path.join(workdir, name + "Script.sml")
    return path if os.path.exists(path) else None


def refuse(lines):
    for ln in lines:
        print(ln, file=sys.stderr)
    print("", file=sys.stderr)
    print("If the user wants this build, ask them to include the literal phrase",
          file=sys.stderr)
    print("`build ok` in their next message.", file=sys.stderr)
    return 2


def main():
    try:
        payload = json.load(sys.stdin)
    except Exception:
        return 0
    if payload.get("tool_name", "") != "mcp__hol4__holmake":
        return 0
    ti = payload.get("tool_input", {})
    workdir = ti.get("workdir") or payload.get("cwd") or "."
    if not os.path.isabs(workdir):
        workdir = os.path.abspath(os.path.join(payload.get("cwd", "."), workdir))
    target = ti.get("target")

    latest = latest_user_message(payload)
    if latest is None:
        return 0  # fail-open
    if CONSENT_RE.search(latest):
        return 0

    if not target:
        return refuse([
            f"hol4-hook H32: refused holmake with no target in {workdir}.",
            "",
            "An untargeted Holmake builds EVERY theory in the directory, not the",
            "one you are working on. Name it: holmake(workdir=..., target=<thy>Theory).",
        ])

    try:
        script = target_script(workdir, target)
        if not script:
            return 0
        root = h30.repo_root(script)
        if not root:
            return 0
        res = h30.check_closure(script, root)
        if not res:
            return 0
        roots, _n_down, _direct = res
        wd = os.path.abspath(workdir) + os.sep
        outside = [(p, why) for p, why in roots
                   if not os.path.abspath(p).startswith(wd)]
    except Exception:
        return 0
    if not outside:
        return 0
    lines = [f"hol4-hook H32: refused holmake target={target} in {workdir} -- "
             f"it would rebuild theories OUTSIDE this directory:"]
    for p, why in outside[:MAX_SHOWN]:
        lines.append(f"  {p}")
        lines.append(f"    {why}")
    if len(outside) > MAX_SHOWN:
        lines.append(f"  ... and {len(outside) - MAX_SHOWN} more")
    lines += ["",
              "Holmake follows INCLUDES, so this call is also a build of those",
              "directories' theories -- someone else's work, possibly mid-edit.",
              "Build ownership is the user's call (RULE A)."]
    return refuse(lines)


if __name__ == "__main__":
    sys.exit(main())
