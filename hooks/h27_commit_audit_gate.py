#!/usr/bin/env python3
"""
H27 -- PreToolUse gate that runs the post-discharge audit against a `git commit`
touching `*Script.sml`, and blocks on what it finds.

The skill's audit gates fire "when you feel done" -- self-reported, so nothing
fires when the feeling doesn't arrive. Scaffolded proofs pass `hol_check_proof`
AND `holmake`, so no other signal catches them either. This moves the gate to a
mechanical moment: when proof code leaves your hands.

DIFF-SCOPED. Only what this commit introduces is judged:
  - a theorem is swept for composition defects only if the commit touches it;
  - banned tactics, `cheat` and `[local]` helpers count only on ADDED lines.
Pre-existing debris in untouched theorems is tolerated until that theorem is
restructured, exactly as Gate 5 says.

Checks (skill audit gates 1, 2, 3, 5, 6 + the composition sweep):
  Gate 1  a Resume block added -- name the (a)/(b) justification or inline it
  Gate 2  a theorem left with Resume but no Finalise
  Gate 3  `cheat` added
  Gate 5  banned tactics added
  Gate 6  a `[local]` helper added that is used once
  sweep   proof_sweep.py over each touched theorem

Override: put `wip ok` in the message alongside `git ok`. Deliberate WIP commits
are legitimate; silently unenforceable gates are not.

Fails OPEN on anything unexpected (not a repo, git error, unreadable file) --
never block real work because of a gate bug.
"""

HOOK_EVENT = "PreToolUse"
HOOK_MATCHER = "Bash"   # None = all calls for this event

import json
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import proof_sweep  # noqa: E402
from hook_payload import latest_user_message  # noqa: E402

# Same option-consuming shape as H14: `git -C dir commit`, `git --no-pager commit`.
_OPT = (r"(?:(?:-C|-c|--git-dir|--work-tree|--namespace|--exec-path)"
        r"(?:=\S+|\s+\S+)|--?[A-Za-z][\w-]*)\s+")
COMMIT_RE = re.compile(r"\bgit\s+(?:" + _OPT + r")*commit\b")
WORKDIR_RE = re.compile(r"\bgit\s+(?:-C|--git-dir=?)\s*(\S+)")
# A leading `cd <dir> && ... git commit` retargets the repo just as `git -C` does;
# without this the gate audits the session's cwd and judges the wrong repository.
CD_RE = re.compile(r"(?:^|[;&|]|&&)\s*cd\s+(?!-)(\S+)")
OVERRIDE_RE = re.compile(r"\bwip\s+ok\b", re.IGNORECASE)

BANNED = [(re.compile(r"\bTRY\b"), "TRY"), (re.compile(r"\bORELSE\b"), "ORELSE"),
          (re.compile(r"\bFIRST\b"), "FIRST"), (re.compile(r"\bTHENL\b"), "THENL"),
          (re.compile(r">\|", ), ">|")]
BLOCK_START = re.compile(r"^(Theorem|Definition|Triviality|Resume)\s+([A-Za-z0-9_']+)")
BLOCK_END = re.compile(r"^(QED|End)\b")
LOCAL_DEF = re.compile(r"^Theorem\s+([A-Za-z0-9_']+)\s*\[[^\]]*\blocal\b")
COMMENT = re.compile(r"\(\*.*?\*\)", re.DOTALL)
MAX_SHOWN = 12
# Calibrated so a reviewed, cleaned proof script reports NOTHING. Gate 1 keeps a
# per-case Resume ladder, so only a short one reads as the deferred tail it calls
# junk; below this it is flagged, at or above it is the sanctioned form.
LADDER_MIN = 2

# Gate 6 (single-use `[local]` helpers) is deliberately NOT enforced here. Its
# keeper case — a small, intent-documenting named fact — is the common, correct
# idiom, and no mechanical test separates it from a one-shot nav-helper: on a
# reviewed script this check fired on `clean_prog_CONS`, `in_cc_eq_state_cc` and
# five siblings, all of which should stay. It remains a judgement prompt in the
# skill's audit, where a human is doing the judging.


def git(args, cwd):
    try:
        p = subprocess.run(["git"] + args, cwd=cwd, capture_output=True,
                           text=True, timeout=10)
        return p.stdout if p.returncode == 0 else None
    except Exception:
        return None


def diff_base(command):
    """What this commit will actually record, approximately."""
    if re.search(r"--amend\b", command):
        return ["HEAD~1"]          # the commit being replaced, plus current work
    if re.search(r"(?:^|\s)-[a-zA-Z]*a|--all\b", command):
        return ["HEAD"]            # -a stages tracked edits at commit time
    return ["--cached"]


def added_lines(path, base, cwd):
    """{new-file line number: text} for lines this commit adds."""
    out = git(["diff", "-U0"] + base + ["--", path], cwd)
    if out is None:
        return None
    added, ln = {}, 0
    for line in out.split("\n"):
        m = re.match(r"@@ -\S+ \+(\d+)(?:,\d+)? @@", line)
        if m:
            ln = int(m.group(1))
            continue
        if line.startswith("+") and not line.startswith("+++"):
            added[ln] = line[1:]
            ln += 1
        elif not line.startswith("-"):
            ln += 1
    return added


def blocks(text):
    """[(name, kind, first, last)] for every Theorem/Definition/Resume block."""
    out, cur = [], None
    for i, line in enumerate(text.split("\n"), 1):
        m = BLOCK_START.match(line)
        if m and cur is None:
            cur = (m.group(2), m.group(1), i)
        elif cur and BLOCK_END.match(line):
            out.append((cur[0], cur[1], cur[2], i))
            cur = None
    return out


def audit(path, base, cwd):
    added = added_lines(path, base, cwd)
    if not added:
        return []
    try:
        text = open(os.path.join(cwd, path), encoding="utf-8", errors="replace").read()
    except OSError:
        return []
    # Strip comments for token checks; keep line structure so numbers stay real.
    bare = {n: COMMENT.sub("", t) for n, t in added.items()}
    found, blks = [], blocks(text)
    ladders = {}
    for line in text.split("\n"):
        m = re.match(r"^Resume\s+([A-Za-z0-9_']+)", line)
        if m:
            ladders[m.group(1)] = ladders.get(m.group(1), 0) + 1

    for n, t in sorted(bare.items()):
        for rx, name in BANNED:
            if rx.search(t):
                found.append((n, f"Gate 5: banned tactic `{name}` on an added line"))
        if re.search(r"\bcheat\b", t):
            found.append((n, "Gate 3: `cheat` added — a committed cheat blocks the "
                             "pipeline theorem via check_thm"))
        m = re.match(r"^Resume\s+([A-Za-z0-9_']+)", t.strip())
        # Gate 1 keeper (a) is a multi-case induction "or a similarly large
        # multi-arm split" kept as one Resume per case, so a LADDER is the
        # sanctioned form and only a small number of Resumes reads as the
        # "single deferred tail" the gate calls junk.
        if m and ladders.get(m.group(1), 0) <= LADDER_MIN:
            found.append((n, f"Gate 1: `{m.group(1)}` has {ladders.get(m.group(1), 0)} "
                             f"Resume block(s) — too few to be the per-case ladder of an "
                             f"induction, so this reads as a deferred tail. Inline it, or "
                             f"say why it is a keeper"))

    # Gate 2: a theorem with a Resume in the file and no Finalise after it.
    for name in {m.group(1) for t in bare.values()
                 for m in [re.match(r"^Resume\s+([A-Za-z0-9_']+)", t.strip())] if m}:
        if not re.search(r"^Finalise\s+" + re.escape(name) + r"\s*;", text, re.M):
            found.append((0, f"Gate 2: `Resume {name}` present with no `Finalise "
                             f"{name};` — the theorem stays cheated"))

    # Composition sweep, only over theorems this commit touches.
    for name, kind, first, last in blks:
        if kind == "Definition" or not any(first <= n <= last for n in added):
            continue
        for ln, msg in proof_sweep.sweep(text, first, last):
            found.append((ln, f"{name}: {msg}"))
    return found


def main():
    try:
        payload = json.load(sys.stdin)
    except Exception:
        return 0
    if payload.get("tool_name", "") != "Bash":
        return 0
    command = payload.get("tool_input", {}).get("command", "")
    if not COMMIT_RE.search(command):
        return 0

    latest = latest_user_message(payload)
    if latest and OVERRIDE_RE.search(latest):
        return 0

    m = WORKDIR_RE.search(command) or CD_RE.search(command)
    cwd = m.group(1) if m else payload.get("cwd") or os.getcwd()
    if git(["rev-parse", "--git-dir"], cwd) is None:
        return 0                                   # not a repo: fail open

    base = diff_base(command)
    names = git(["diff", "--name-only"] + base, cwd)
    if names is None:
        return 0
    scripts = [f for f in names.split("\n") if f.endswith("Script.sml")]
    if not scripts:
        return 0

    findings = []
    for f in scripts:
        try:
            findings += [(f, ln, msg) for ln, msg in audit(f, base, cwd)]
        except Exception:
            continue                               # one bad file must not block
    if not findings:
        return 0

    print(f"hol4-hook H27: refused the commit — the audit gates flag "
          f"{len(findings)} thing(s) in the proof code it would record.",
          file=sys.stderr)
    print("", file=sys.stderr)
    for f, ln, msg in findings[:MAX_SHOWN]:
        where = f"{f}:{ln}" if ln else f
        print(f"  {where}: {msg}", file=sys.stderr)
    if len(findings) > MAX_SHOWN:
        print(f"  ... and {len(findings) - MAX_SHOWN} more", file=sys.stderr)
    print("", file=sys.stderr)
    print("Only theorems this commit TOUCHES were judged. Each sweep item is a "
          "PROMPT TO CHECK, not a proven defect — simplification is not "
          "confluent, so verify per theorem before collapsing anything.",
          file=sys.stderr)
    print("If this is a deliberate work-in-progress commit, say `wip ok`.",
          file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main())
