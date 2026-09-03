"""Failure output tells the truth first: an opaque break names the step and
the sub-suspend recipe before anything else and withholds the entry goal; a
TIMEOUT attributes its budget to prefix vs target; an absurd timeout is
refused; a cheat-dependent state is flagged on line one; an undeclared name
in hol_send points at the parked position; a repeated break at one step is
called out as a loop."""
import re

import pytest

from hol4_mcp.hol_mcp_server import (
    _init_file_cursor,
    hol_check_proof,
    hol_send,
    hol_state_at,
    hol_stop,
)

OPAQUE_SCRIPT = """\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "opq";

Theorem opaque_fail:
  !x:num. x + 0 = x
Proof
  gen_tac >>
  (Induct_on `x` >>
   FAIL_TAC "inside")
QED

Theorem later_thm:
  T
Proof
  simp []
QED

val _ = export_theory();
"""
OPAQUE_QED_LINE = 11
OPAQUE_SPAN = "lines 9-10"

FAIL_DEP_SCRIPT = """\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "fdep";

Theorem fail_dep:
  T /\\ T
Proof
  FAIL_TAC "nope"
QED

Theorem uses_dep:
  T /\\ T
Proof
  ACCEPT_TAC fail_dep
QED

val _ = export_theory();
"""

SLEEP_SCRIPT = """\
open HolKernel Parse boolLib bossLib;

val _ = new_theory "slp";

Theorem quick:
  T
Proof
  simp []
QED

Theorem sleeper:
  T
Proof
  (fn g => (OS.Process.sleep (Time.fromSeconds 20); ALL_TAC g)) >>
  simp []
QED

val _ = export_theory();
"""


async def init(tmp_path, name, script, session):
    f = tmp_path / f"{name}Script.sml"
    f.write_text(script)
    r = await _init_file_cursor(file=str(f), session=session)
    assert "Theorems:" in r, r
    return f


def body(output):
    """Output lines after the `Theorem:` header."""
    lines = output.split("\n")
    assert lines[0].startswith("Theorem:"), output
    return lines[1:]


async def test_opaque_break_names_step_first_and_withholds_goal(tmp_path):
    session = "fo_opaque"
    try:
        await init(tmp_path, "opq", OPAQUE_SCRIPT, session)
        r = await hol_state_at(line=OPAQUE_QED_LINE, col=1, session=session)
        first = body(r)[0]
        assert first.startswith("PROOF BROKEN"), r
        m = re.search(r"opaque step (\d+) \(" + OPAQUE_SPAN + r"\)", first)
        assert m and "suspend" in first, r
        assert "=== Goal" not in r, r

        r2 = await hol_state_at(line=OPAQUE_QED_LINE, col=1, session=session,
                                show_partial=True)
        assert body(r2)[0].startswith("PROOF BROKEN"), r2
        assert "=== Goal" in r2 and "entering the opaque step" in r2, r2
    finally:
        await hol_stop(session)


async def test_timeout_attributes_prefix_and_target(tmp_path):
    session = "fo_timeout"
    try:
        f = await init(tmp_path, "slp", SLEEP_SCRIPT, session)
        r = await hol_state_at(line=15, col=3, session=session, timeout=8)
        assert r.startswith("ERROR: TIMEOUT") or "TIMEOUT" in r.split("\n")[0], r
        m = re.search(r"prefix=(\d+(?:\.\d+)?)s.*target=(\d+(?:\.\d+)?)s", r)
        assert m, r
        prefix, target = float(m.group(1)), float(m.group(2))
        assert target >= 0.5 and prefix < target, r
        assert "YOUR tactics" in r, r
    finally:
        await hol_stop(session)


async def test_absurd_timeout_is_refused(tmp_path):
    session = "fo_absurd"
    try:
        await init(tmp_path, "opq", OPAQUE_SCRIPT, session)
        r = await hol_state_at(line=16, col=3, session=session, timeout=20000)
        assert r.startswith("ERROR"), r
        assert "20000" in r and "3600" in r and "seconds" in r, r
    finally:
        await hol_stop(session)


async def test_cheat_dependence_marked_on_first_line(tmp_path):
    session = "fo_cheat"
    try:
        await init(tmp_path, "fdep", FAIL_DEP_SCRIPT, session)
        r = await hol_state_at(line=15, col=1, session=session)
        assert "⚠ depends on cheat" in r.split("\n")[0], r
        assert "[auto-cheated deps:" in r, r

        r2 = await hol_check_proof(theorem="uses_dep", session=session)
        assert "⚠ depends on cheat" in r2.split("\n")[0], r2
    finally:
        await hol_stop(session)


async def test_hol_send_undeclared_name_points_at_parked_position(tmp_path):
    session = "fo_send"
    try:
        f = await init(tmp_path, "opq", OPAQUE_SCRIPT, session)
        await hol_state_at(line=8, col=3, session=session)   # parked in opaque_fail
        r = await hol_send(command="later_thm;", session=session)
        assert "has not been declared" in r, r
        assert "later_thm" in r and "line 13" in r and "opaque_fail" in r, r
        assert "hol_state_at" in r, r
    finally:
        await hol_stop(session)


async def test_repeated_break_at_same_step_is_called_a_loop(tmp_path):
    session = "fo_loop"
    try:
        f = await init(tmp_path, "opq", OPAQUE_SCRIPT, session)
        outputs = []
        for i in range(4):
            text = f.read_text().replace(
                'FAIL_TAC "inside"', f'FAIL_TAC "inside{i}"')
            text = re.sub(r'FAIL_TAC "inside\d*"', f'FAIL_TAC "inside{i}"', text)
            f.write_text(text)
            outputs.append(await hol_state_at(line=OPAQUE_QED_LINE, col=1, session=session))
        assert all("PROOF BROKEN" in o for o in outputs), outputs[-1]
        assert not any("[Loop:" in o for o in outputs[:3]), outputs[2]
        loop = [ln for ln in outputs[3].split("\n") if ln.startswith("[Loop:")]
        assert loop, outputs[3]
        assert "4 edit" in loop[0] and "opaque_fail" in loop[0], loop[0]
        assert re.search(r"same step \d+", loop[0]), loop[0]
        assert "suspend" in loop[0] and "Resume" in loop[0] and "QED" in loop[0], loop[0]

        # A passing navigation resets the counter.
        f.write_text(f.read_text().replace('FAIL_TAC "inside3"', 'simp []'))
        ok = await hol_state_at(line=OPAQUE_QED_LINE, col=1, session=session)
        assert "PROOF BROKEN" not in ok, ok
        f.write_text(f.read_text().replace("   simp [])", '   FAIL_TAC "again")', 1))
        again = await hol_state_at(line=OPAQUE_QED_LINE, col=1, session=session)
        assert "PROOF BROKEN" in again and "[Loop:" not in again, again
    finally:
        await hol_stop(session)
