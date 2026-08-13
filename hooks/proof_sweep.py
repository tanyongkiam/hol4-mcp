#!/usr/bin/env python3
"""
Sweep finished HOL4 proof text for composition defects.

Every check is a PROMPT TO CHECK, never a proven defect: simplification is not
confluent, so no collapse is safe by inspection. Each trigger below is narrowed
to a shape that is rare in ordinary HOL4 (measured against a large proof
directory) -- the un-narrowed version of most of them flags common idiom.

Usage (standalone):
    ./proof_sweep.py FILE [FIRST_LINE LAST_LINE]

Used by h25_proof_text_sweep.py, which runs it on the theorem a successful
hol_check_proof just confirmed.
"""
import difflib
import re
import sys

# --- lexical vocabulary -----------------------------------------------------

NORM_STRENGTH = {"rveq": 0, "simp": 1, "srw_tac": 1, "rw": 2, "fs": 3, "rfs": 3,
                 "asm_simp_tac": 3, "full_simp_tac": 3, "gs": 4, "gvs": 5}
NORM = "|".join(sorted(NORM_STRENGTH, key=len, reverse=True))
# singular -> n-ary, derived from bossLib.sig/Q.sig by type shape
# (`α quotation -> tactic` / `α quotation list -> tactic`); the continuation-taking
# qspec_then / qx_choose_then are correctly excluded.
NARY = {"qexists_tac": "qexistsl_tac", "qexists": "qexistsl",
        "qx_gen_tac": "qx_genl_tac", "qid_spec_tac": "qid_specl_tac",
        "qrefine": "qrefinel", "qunabbrev_tac": "qunabbrevl_tac"}
SPLITTER = r"conj_tac|strip_tac|gen_tac"

LEAD = r"(?:>>|>-|\\\\|THEN1|THEN)?\s*"
RE_NORM = re.compile(r"^\s*(>>|>-|\\\\|THEN1|THEN)?\s*(" + NORM + r")\b\s*(\[[^\]]*\])?\s*$")
RE_NARY = re.compile(r"^\s*" + LEAD + r"(" + "|".join(NARY) + r")\b\s*(.*)$")
RE_DISP = re.compile(r"^\s*(>-|>>|\\\\)")
RE_BODY = re.compile(r"^(Proof|Resume\b)")
RE_IMPL = re.compile(r"\b(impl_tac|impl_keep_tac)\b")
RE_LAMBDA = re.compile(r"\(fn\s+(\w+)\s*=>\s*(?:" + NORM +
                       r"|once_rewrite_tac|rewrite_tac|assume_tac)\s*\[\s*\1\s*\]\s*\)")
COMMENT = re.compile(r"\(\*.*?\*\)", re.DOTALL)
STRING = re.compile(r'"(?:\\.|[^"\\])*"')


def indent(s):
    return len(s) - len(s.lstrip())


def _blank(m):
    """Erase content but keep line structure, so reported line numbers are real."""
    return "\n" * m.group(0).count("\n")


def clean(text):
    return STRING.sub(lambda m: _blank(m) or '""', COMMENT.sub(_blank, text))


# --- checks -----------------------------------------------------------------

def _norm_at(line):
    """(lead, tactic, args) for a line that is exactly one normaliser call."""
    m = RE_NORM.match(line)
    return (m.group(1) or "", m.group(2), (m.group(3) or "").strip()) if m else None


def check_normaliser_runs(lines, base):
    """B1: adjacent normalisers, only the classes with no load-bearing shape."""
    out, prev = [], None
    for k, l in enumerate(lines):
        cur = _norm_at(l)
        # Only a real run if both calls act on the SAME goal: the second must
        # continue the chain (`>>`), and the first must not have been a `>-` arm
        # -- in `tac >- A >> B`, A and B are on different goals.
        if cur and prev and cur[0] in (">>", "\\\\", "THEN") and prev[0] not in (">-", "THEN1"):
            (_, a, aa), (_, b, bb) = prev, cur
            bare = aa in ("", "[]") and bb in ("", "[]")
            same = aa == bb and aa not in ("", "[]")
            stronger = NORM_STRENGTH[b] > NORM_STRENGTH[a] and aa in ("", "[]")
            if bare or same or stronger:
                why = "both bare" if bare else ("identical lists" if same
                                                else f"{b} subsumes a bare {a}")
                out.append((base + k, f"adjacent normalisers `{a} >> {b}` ({why}) "
                                      f"-- one call with the union?"))
        prev = cur
    return out


def check_impl(lines, base):
    """B3: impl_tac >- <normaliser> >> <normaliser>."""
    out = []
    for k in range(len(lines) - 1):
        if not RE_IMPL.search(lines[k]):
            continue
        window = " ".join(x.strip() for x in lines[k:k + 3])
        if re.search(r"(impl_tac|impl_keep_tac)\s*(?:>-|THEN1)\s*\(?\s*(" + NORM +
                     r")\b[^)]*\)?\s*(?:>>|\\\\)\s*(" + NORM + r")\b", window):
            out.append((base + k, "`impl_tac >- <normaliser> >> <normaliser>` -- one "
                                  "assumption-using normaliser does both, if the arm "
                                  "actually closes the antecedent"))
    return out


def _arms(lines, base):
    """(line, indent, body, seq) per `>-` arm. `seq` is its position in the
    dispatcher sequence, so callers can require two arms be ADJACENT siblings --
    `tac >- A >> B >- C` does not make A and C siblings."""
    disp = [k for k, l in enumerate(lines) if l.strip() and RE_DISP.match(l)]
    pos = {k: i for i, k in enumerate(disp)}
    out = []
    for k in disp:
        if not lines[k].strip().startswith(">-"):
            continue
        d, j = indent(lines[k]), k + 1
        while j < len(lines) and not (lines[j].strip() and indent(lines[j]) <= d
                                      and RE_DISP.match(lines[j])):
            j += 1
        body = "\n".join(x.strip() for x in lines[k:j])
        out.append((base + k, d, body, pos[k]))
    return out


def _is_dispatcher_arm(body):
    """A `>- suspend "X"` arm of a multi-case induction dispatcher: the sanctioned
    flat-ladder form (skill Gate 1(a)). Never a duplication defect."""
    return re.fullmatch(r'>-\s*suspend\s*"[^"]*"', body.strip()) is not None


def check_dispatchers(lines, base):
    """B4/B5: `>-` that does not mark a sibling subgoal."""
    disp = [(base + k, indent(l), RE_DISP.match(l).group(1))
            for k, l in enumerate(lines) if l.strip() and RE_DISP.match(l)]
    out = []
    for i, (ln, d, kind) in enumerate(disp):
        if kind != ">-":
            continue
        def side(seq):
            acc = []
            for _, dd, kk in seq:
                if dd < d:
                    break
                if dd == d:
                    acc.append(kk)
            return acc
        before, after = side(disp[:i][::-1]), side(disp[i + 1:])
        if not before and not after:
            out.append((ln, "`>-` is the only dispatcher at its level, so the previous "
                            "tactic left one goal -- `>>`"))
        elif ">-" in before and not after:
            out.append((ln, "trailing `>-`: the last goal is usually the main line, not "
                            "a sibling -- `>>`, unless these really are sibling arms "
                            "(induction cases, constructor arms)"))
    return out


def check_sibling_arms(lines, base):
    """B6/B7, escalating to B9 at >=3."""
    arms = [a for a in _arms(lines, base) if not _is_dispatcher_arm(a[2])]
    out, k = [], 0
    while k < len(arms):
        m = k
        while (m + 1 < len(arms) and arms[m + 1][1] == arms[k][1]
               and arms[m + 1][3] == arms[m][3] + 1          # adjacent siblings only
               and len(arms[k][2]) > 4
               and difflib.SequenceMatcher(None, arms[k][2], arms[m + 1][2]).ratio() > 0.90):
            m += 1
        n = m - k + 1
        if n >= 3:
            out.append((arms[k][0], f"{n} near-identical sibling arms -- the split is "
                                    f"~{n}x coarser than the argument needs; name the "
                                    f"split (`gvs [AllCaseEqs()]`, or split the actual "
                                    f"scrutinee) rather than compressing the arms"))
        elif n == 2:
            out.append((arms[k][0], "two near-identical sibling arms -- `>>` if they "
                                    "close the same way, or one tail with `first_x_assum "
                                    "drule_all` if they differ only in which hypothesis "
                                    "they use (verify: same text != same goal)"))
        k = m + 1
    return out


def check_nested_ladder(lines, base):
    """B8: a right-nested ladder of one splitter with normaliser leaves."""
    out = []
    for ln, d, body, _ in _arms(lines, base):
        head = body.split("\n")[0]
        m = re.search(r"\b(" + SPLITTER + r")\b\s*(?:>-|THEN1)", head)
        if not m:
            continue
        rest = "\n".join(body.split("\n")[1:])
        if re.search(r"\b" + m.group(1) + r"\b\s*(?:>-|THEN1)", rest):
            leaves = re.findall(r"(?:>-|THEN1)\s*(" + NORM + r")\b", body)
            if len(leaves) >= 2:
                out.append((ln, f"nested `{m.group(1)}` ladder with normaliser leaves -- "
                                f"`rpt {m.group(1)} >> <strongest leaf>` IF the leaves are "
                                f"interchangeable; if they differ the ladder is carrying "
                                f"the structure (symptom: arms all succeed, one goal left "
                                f"over at the closing paren)"))
    return out


def check_nary(lines, base):
    """A2: a singular tactic applied consecutively where an n-ary form exists."""
    out, prev = [], None
    for k, l in enumerate(lines):
        m = RE_NARY.match(l)
        cur = m.group(1) if m else None
        if cur and prev == cur:
            out.append((base + k, f"`{cur}` twice in a row -- `{NARY[cur]} [...]` "
                                  f"(check argument order)"))
        prev = cur
    return out


def check_lambda(lines, base):
    """A3: a lambda that only re-feeds its own binder."""
    return [(base + k, "lambda that only re-feeds its own binder -- the "
                       "assumption-using normalisers already use the assumption")
            for k, l in enumerate(lines) if RE_LAMBDA.search(l)]


CHECKS = [check_normaliser_runs, check_impl, check_dispatchers,
          check_sibling_arms, check_nested_ladder, check_nary, check_lambda]


def sweep(text, first=None, last=None):
    """[(line, message)] for the given 1-based inclusive line range."""
    lines = clean(text).split("\n")
    lo = (first or 1) - 1
    hi = last if last else len(lines)
    window = lines[lo:hi]
    hits = []
    for chk in CHECKS:
        hits.extend(chk(window, lo + 1))
    return sorted(set(hits))


def main():
    if len(sys.argv) < 2:
        print(__doc__.strip())
        return 2
    text = open(sys.argv[1], encoding="utf-8", errors="replace").read()
    first = int(sys.argv[2]) if len(sys.argv) > 3 else None
    last = int(sys.argv[3]) if len(sys.argv) > 3 else None
    hits = sweep(text, first, last)
    for ln, msg in hits:
        print(f"{sys.argv[1]}:{ln}: {msg}")
    print(f"-- {len(hits)} item(s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
