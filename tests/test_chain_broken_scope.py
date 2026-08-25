"""Scope regression for the broken-chain session-reinit gate.

``_reparse_if_changed`` forces a FULL session reinit (restart + replay of the
whole file prefix) when an edit lands in a suspend/Resume chain that is
currently broken. That is correct for the chain being edited — its suspension
store is stale, so children must re-register from a clean session.

The bug: both ``_suspension_chain_root_line`` and ``_affected_chain_is_broken``
scanned every theorem with ``proof_end_line >= start_line`` — the edited
theorem AND EVERYTHING AFTER IT. So a broken chain LATER in the file made every
edit to an EARLIER chain trigger the reinit, even though that later chain was
untouched by the edit and had not run. On a large script the reinit is a
multi-minute prefix reload, paid on every keystroke-sized edit.

These helpers are pure over the parsed file state, so no HOL session is needed.
"""

import pytest
from pathlib import Path

from hol4_mcp.hol_cursor import FileProofCursor


# Two INDEPENDENT chains: `early` (lines 5-19) and `late` (lines 21-31).
_TWO_CHAINS = (
    "open HolKernel Parse boolLib bossLib markerLib;\n"   # 1
    "\n"                                                   # 2
    'val _ = new_theory "twochains";\n'                   # 3
    "\n"                                                   # 4
    "Theorem early:\n"                                     # 5
    "  p /\\ (p ==> q) ==> p /\\ q\n"                      # 6
    "Proof\n"                                              # 7
    "  strip_tac >> conj_tac\n"                            # 8
    '  >- suspend "e1"\n'                                  # 9
    '  >- suspend "e2"\n'                                  # 10
    "QED\n"                                                # 11
    "\n"                                                   # 12
    "Resume early[e1]:\n"                                  # 13
    "  first_assum ACCEPT_TAC\n"                           # 14
    "QED\n"                                                # 15
    "\n"                                                   # 16
    "Resume early[e2]:\n"                                  # 17
    "  RES_TAC\n"                                          # 18
    "QED\n"                                                # 19
    "\n"                                                   # 20
    "Theorem late:\n"                                      # 21
    "  p ==> p\n"                                          # 22
    "Proof\n"                                              # 23
    '  suspend "L1"\n'                                     # 24
    "QED\n"                                                # 25
    "\n"                                                   # 26
    "Resume late[L1]:\n"                                   # 27
    "  strip_tac >> first_assum ACCEPT_TAC\n"              # 28
    "QED\n"                                                # 29
    "\n"                                                   # 30
    "Finalise late\n"                                      # 31
    "\n"                                                   # 32
    "val _ = export_theory();\n"                           # 33
)

EARLY_BODY_LINE = 14   # inside Resume early[e1]
LATE_BODY_LINE = 28    # inside Resume late[L1]


def _cursor(tmp_path: Path) -> FileProofCursor:
    script = tmp_path / "twochainsScript.sml"
    script.write_text(_TWO_CHAINS)
    cursor = FileProofCursor(script, session=None)
    cursor._reparse_if_changed()
    return cursor


def test_later_broken_chain_does_not_taint_edit_in_earlier_chain(tmp_path: Path):
    """An edit inside `early` must not be judged broken because `late` failed."""
    cursor = _cursor(tmp_path)
    cursor._failed_proofs = {"late[L1]": "auto-cheated"}

    assert not cursor._affected_chain_is_broken(EARLY_BODY_LINE), (
        "edit in the `early` chain was judged broken because an unrelated LATER "
        "chain (`late`) has a failed body — this forces a full session reinit "
        "and a multi-minute prefix reload on every edit"
    )


def test_broken_chain_containing_the_edit_still_triggers_reinit(tmp_path: Path):
    """The feature itself must survive: editing a chain that IS broken still
    reports broken, so its children re-register from a clean session."""
    cursor = _cursor(tmp_path)
    cursor._failed_proofs = {"early[e2]": "auto-cheated"}

    assert cursor._affected_chain_is_broken(EARLY_BODY_LINE), (
        "editing a chain with a failed body must still force the reinit"
    )


def test_edit_in_later_broken_chain_still_triggers_reinit(tmp_path: Path):
    """Editing the broken chain itself, from inside it, still reports broken."""
    cursor = _cursor(tmp_path)
    cursor._failed_proofs = {"late[L1]": "auto-cheated"}

    assert cursor._affected_chain_is_broken(LATE_BODY_LINE), (
        "editing the broken `late` chain must still force the reinit"
    )


def test_healthy_chains_never_trigger_reinit(tmp_path: Path):
    cursor = _cursor(tmp_path)
    cursor._failed_proofs = {}

    assert not cursor._affected_chain_is_broken(EARLY_BODY_LINE)
    assert not cursor._affected_chain_is_broken(LATE_BODY_LINE)
