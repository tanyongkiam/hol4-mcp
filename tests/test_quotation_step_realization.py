"""Tests for realizing operand-spanning atoms as tactics in the step plan.

`by` and `rename` are parsed by TacticParse into atoms whose span is only an
OPERAND (a term quotation / a quotation list), not a runnable tactic:

    `P` by tac        ->  Subgoal (span = `P`)          -- needs an `sg ` prefix
    >>~- ([pat], t)   ->  Group(false, pat, Rename pat) -- needs `Q.RENAME_TAC `

while the application forms already span a complete tactic and must be left
alone:

    sg `P` / subgoal `P`   ->  Group(true, <whole call>, Subgoal _)
    rename [pat]           ->  Group(true, <whole call>, Rename _)

`Group`'s first field is exactly that distinction (TacticParse `group tac a b`),
so it — not the first character of the span — decides whether a prefix is added.
Sniffing for an ASCII backtick misses `‘…’` / `“…”`, which is what CakeML and
most modern HOL4 sources use.
"""

import pytest
import json
from pathlib import Path

from hol4_mcp.hol_session import HOLSession, escape_sml_string
from hol4_mcp.hol_file_parser import parse_step_plan_output

FIXTURES_DIR = Path(__file__).parent / "fixtures"
SML_HELPERS_DIR = Path(__file__).parent.parent / "hol4_mcp" / "sml_helpers"


@pytest.fixture
async def hol_session():
    session = HOLSession(str(FIXTURES_DIR))
    await session.start()
    result = await session.send(
        f'use "{SML_HELPERS_DIR / "tactic_prefix.sml"}";', timeout=10)
    assert "error" not in result.lower()
    yield session
    await session.stop()


async def call_step_plan(session, tactic_str):
    escaped = escape_sml_string(tactic_str)
    result = await session.send(f'goalfrag_step_plan_json "{escaped}";', timeout=10)
    return parse_step_plan_output(result)


async def execute_steps(session, steps, goal):
    """Run a step plan on `goal`; -1 means a step raised (e.g. a type error)."""
    await session.send('drop_all();', timeout=5)
    await session.send(f'gf `{goal}`;', timeout=10)
    for step in steps:
        r = await session.send(step.cmd, timeout=10)
        if "Exception-" in r or "error:" in r or "poly:" in r or "Type error" in r:
            return -1
    r = await session.send('goals_json();', timeout=10)
    for line in r.strip().split('\n'):
        if line.startswith('{"ok":'):
            return len(json.loads(line)['ok'])
    return -1


def texts(steps):
    return [s.text for s in steps]


def unquote(t):
    """Normalise every term-quotation delimiter to the ASCII backtick."""
    for c in "‘’“”":
        t = t.replace(c, "`")
    return t


def bare_quotations(steps):
    """Steps that are nothing but a term quotation — not a runnable tactic."""
    out = []
    for t in texts(steps):
        s = unquote(t).strip()
        if len(s) >= 2 and s.startswith("`") and s.endswith("`"):
            out.append(t)
    return out


# ---------------------------------------------------------------------------
# `Q` by tac — the Subgoal atom spans only the quotation
# ---------------------------------------------------------------------------

ASCII_BY = "`T` by SIMP_TAC bool_ss []"
UNICODE_BY = "‘T’ by SIMP_TAC bool_ss []"

# The shape real sources use: mid-chain, with a parenthesised `by` body.
CHAIN_ASCII_BY = "rpt strip_tac \\\\ `T` by (ALL_TAC \\\\ SIMP_TAC bool_ss [])"
CHAIN_UNICODE_BY = "rpt strip_tac \\\\ ‘T’ by (ALL_TAC \\\\ SIMP_TAC bool_ss [])"


class TestSubgoalByRealization:
    async def test_ascii_by_merges_to_one_step(self, hol_session):
        """Control: the ASCII form is realized and merged into one atomic step."""
        steps = await call_step_plan(hol_session, ASCII_BY)
        assert texts(steps) == [ASCII_BY], texts(steps)

    async def test_unicode_by_merges_to_one_step(self, hol_session):
        """Unicode quotes must behave identically to the ASCII control."""
        steps = await call_step_plan(hol_session, UNICODE_BY)
        assert texts(steps) == [UNICODE_BY], texts(steps)

    async def test_no_bare_quotation_step(self, hol_session):
        """A bare term quotation is not a tactic: handing it to goalFrag.expand
        is a Poly/ML 'Type error in function application'."""
        steps = await call_step_plan(hol_session, UNICODE_BY)
        assert not bare_quotations(steps), texts(steps)

    async def test_unicode_by_executes(self, hol_session):
        steps = await call_step_plan(hol_session, UNICODE_BY + " \\\\ ASM_REWRITE_TAC []")
        assert await execute_steps(hol_session, steps, "T") == 0

    async def test_chain_quote_style_does_not_change_the_plan(self, hol_session):
        """The mid-chain, parenthesised-body shape real sources use. Quote
        style is not semantics: both plans must be identical."""
        ascii_steps = await call_step_plan(hol_session, CHAIN_ASCII_BY)
        uni_steps = await call_step_plan(hol_session, CHAIN_UNICODE_BY)
        assert [unquote(t) for t in texts(uni_steps)] == \
               [unquote(t) for t in texts(ascii_steps)]

    async def test_chain_unicode_by_has_no_bare_quotation(self, hol_session):
        steps = await call_step_plan(hol_session, CHAIN_UNICODE_BY)
        assert not bare_quotations(steps), texts(steps)

    async def test_chain_unicode_by_executes_like_ascii(self, hol_session):
        ascii_steps = await call_step_plan(hol_session, CHAIN_ASCII_BY)
        expected = await execute_steps(hol_session, ascii_steps, "T")
        assert expected >= 0, "ASCII control itself failed to execute"
        uni_steps = await call_step_plan(hol_session, CHAIN_UNICODE_BY)
        assert await execute_steps(hol_session, uni_steps, "T") == expected

    async def test_unicode_by_after_multi_goal_split(self, hol_session):
        """`Q` by tac must stay ONE atomic step so it distributes per goal.

        Decomposed as [sg Q, open_then1, tac, close] only the FIRST goal's
        subgoal is discharged; the rest stay open (see merge_by_steps)."""
        tac = "conj_tac \\\\ " + UNICODE_BY + " \\\\ ASM_REWRITE_TAC []"
        steps = await call_step_plan(hol_session, tac)
        assert await execute_steps(hol_session, steps, "T /\\ T") == 0


# ---------------------------------------------------------------------------
# rename [pat] — the Group spans the whole call, so it is ALREADY a tactic
# ---------------------------------------------------------------------------

RENAME_CALL = "rename [‘y = y’]"
SELECT_THEN = "conj_tac >>~- ([‘T’], SIMP_TAC bool_ss [])"


class TestRenameRealization:
    async def test_rename_call_kept_verbatim(self, hol_session):
        """`rename [pat]` is a complete tactic; prefixing it yields
        `Q.RENAME_TAC rename [pat]` — a function applied to a tactic."""
        steps = await call_step_plan(hol_session, RENAME_CALL)
        assert texts(steps) == [RENAME_CALL], texts(steps)

    async def test_renamed_tac_call_kept_verbatim(self, hol_session):
        call = "Q.RENAME_TAC [‘y = y’]"
        steps = await call_step_plan(hol_session, call)
        assert texts(steps) == [call], texts(steps)

    async def test_rename_call_executes(self, hol_session):
        steps = await call_step_plan(hol_session, RENAME_CALL + " \\\\ REFL_TAC")
        assert await execute_steps(hol_session, steps, "x = x") == 0

    async def test_select_arm_still_prefixed(self, hol_session):
        """Regression guard: in `>>~- ([pat], tac)` the span IS just the
        pattern, so it still needs the Q.RENAME_TAC prefix."""
        steps = await call_step_plan(hol_session, SELECT_THEN)
        prefixed = [t for t in texts(steps) if t.startswith("Q.RENAME_TAC ")]
        assert prefixed, texts(steps)
        assert prefixed[0] == "Q.RENAME_TAC [‘T’]", prefixed

    async def test_select_then_still_executes(self, hol_session):
        steps = await call_step_plan(hol_session, SELECT_THEN)
        assert await execute_steps(hol_session, steps, "T /\\ T") == 0
