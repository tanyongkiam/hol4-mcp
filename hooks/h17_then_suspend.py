#!/usr/bin/env python3
"""
H17 -- PreToolUse hook on Edit/Write/MultiEdit that blocks the THEN-suspend
footgun in all its surface forms: `>>`, `\\\\`, and the word `THEN`,
each followed by `suspend "..."`.

Rationale: THEN (whichever surface form -- `>>`, `\\\\`, or the literal word
`THEN`) distributes its right operand across ALL remaining goals.
`suspend "L"` is a single-goal tactic. Writing `THEN suspend "L"` causes
N goals to be tagged with the same label, which the suspend framework merges
via `resconj` into one unprovable bundled goal at the corresponding Resume
body. Even with one goal, the file-replay engine refuses to commit the
suspension under THEN-form (treated as a banned bundled-suspend); use
THEN1 (`>-`) instead. This is the same failure mode H16 catches at
runtime; H17 catches it at edit time so it never reaches the live state.

Correct forms:
  - `>- suspend "L"`              (single-goal, the canonical form)
  - `>- (tac1 >> tac2 >> suspend "L")`  (chain on first goal, ending in suspend)
  - `>~ [pat] >- suspend "L"`     (pattern-guided dispatch)

Block fires on any `(>>|\\\\|THEN)\\s+suspend\\s*"..."` in the
Edit/Write/MultiEdit new content. Stateless, no transcript read.

CLAUDE.md source: 'HOL4 - suspend/Resume/Finalise' / 'One label = one goal'.
"""
import json
import re
import sys

# Match THEN (in any of its surface forms: `>>`, `\\`, or the word `THEN`)
# followed by `suspend "..."` separated only by whitespace (including
# newlines).
#
# - `>>` negative lookahead on `~` excludes `>>~`/`>>~-` (different combinators).
# - `\\` in CakeML's preamble is bound to THEN; identical hazard.
# - `THEN` as a word: word boundary on each side, and a negative lookahead
#   on `1`/`L`/`_` excludes `THEN1` (= `>-`), `THENL`, `THEN_LT`, etc.
BAD_THEN_SUSPEND_RE = re.compile(
    r'(?:>>(?!~)|\\\\|\bTHEN(?![1L_]))\s*suspend\s*"([^"]+)"',
    re.MULTILINE,
)

REMINDER = """\
hol4-hook H17: refused edit -- the literal pattern THEN+suspend
distributes the suspend across ALL remaining goals under ONE label,
bundling them via `resconj` into an unprovable merged goal at the
Resume body.

CLAUDE.md 'HOL4 - suspend/Resume/Finalise' / 'One label = one goal':
ALWAYS THEN1 (i.e. `>-`) immediately before every `suspend`, even
inside parentheses. THEN in ANY of its surface forms -- `>>`, `\\\\`
(CakeML synonym), or the literal word `THEN` -- followed by `suspend`
is rejected anywhere in the edit text, including chains like
`tac1 \\\\ tac2 \\\\ suspend "L"` and parenthesised bodies like
`>- (... >> suspend "L")`.

Correct forms:
  `>- suspend "L"`                          (canonical, single residual goal)
  `>- suspend "L1" >- suspend "L2"`         (N sequential dispatches)
  `tac1 >> tac2 >> tac3 >- suspend "L"`     (chain on single goal: THEN
                                             for the transforming steps,
                                             THEN1 only at the suspend
                                             boundary)
  `>~ [pat] >- suspend "L"`                 (pattern-guided)

For multiple residual goals into N distinct labels, chain with `>-`:
  `>- suspend "L1" >- suspend "L2" >- suspend "L3"`."""


def extract_edits(payload):
    """Return list of (file_path, new_text) candidates from tool_input.
    Only HOL4 proof scripts (*Script.sml) are scanned; other paths bypass."""
    ti = payload.get("tool_input", {}) or {}
    tool = payload.get("tool_name", "")
    path = ti.get("file_path", "")
    if not path.endswith("Script.sml"):
        return []
    out = []
    if tool == "Edit":
        out.append((path, ti.get("new_string", "")))
    elif tool == "Write":
        out.append((path, ti.get("content", "")))
    elif tool == "MultiEdit":
        for e in ti.get("edits", []) or []:
            out.append((path, e.get("new_string", "")))
    return out


def main():
    try:
        payload = json.load(sys.stdin)
    except Exception:
        return 0
    if payload.get("tool_name", "") not in {"Edit", "Write", "MultiEdit"}:
        return 0
    offenders = []
    for path, text in extract_edits(payload):
        if not text:
            continue
        for m in BAD_THEN_SUSPEND_RE.finditer(text):
            offenders.append((path, m.group(1), m.group(0)))
    if not offenders:
        return 0
    print(REMINDER, file=sys.stderr)
    print("", file=sys.stderr)
    print("Offending occurrences in this edit:", file=sys.stderr)
    for path, label, snippet in offenders:
        print(f"  {path}: {snippet!r}  (label {label!r})", file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main())
