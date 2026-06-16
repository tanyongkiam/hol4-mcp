"""Unit tests for auto-cheat reason classification and target-self-cheat
verdict (MCP Bug A).

These exercise pure module-level helpers, so they do NOT need a live HOL
session or the FastMCP tool wrappers — they validate the reporting logic in
isolation.
"""

from hol4_mcp.hol_cursor import (
    _error_reason,
    _line_is_error_marker,
    PER_THEOREM_TIMEOUT,
)
from hol4_mcp.hol_mcp_server import (
    _auto_cheated_deps_lines,
    _target_self_cheated_reason,
    _target_self_cheated_lines,
)


# --- _line_is_error_marker -------------------------------------------------

def test_marker_false_on_goal_terms_mentioning_error():
    # The exact fragment that misreported a slow proof as failed.
    assert not _line_is_error_marker("| (SOME (Rerr (Rabort Rtype_error)),s1) => T")
    assert not _line_is_error_marker("res <> SOME (Rerr (Rabort Rtype_error)) ∧")
    assert not _line_is_error_marker("no_ReturnException case in evaluate")
    # A bare goal conclusion that happens to mention error constructors.
    assert not _line_is_error_marker("⊢ evaluate (c,s) = (SOME (Rerr e), s')")


def test_marker_true_on_real_errors():
    assert _line_is_error_marker("Exception- HOL_ERR {message = ...} raised")
    assert _line_is_error_marker("HOL_ERR something")
    assert _line_is_error_marker("uncaught exception raised exception at top level")
    assert _line_is_error_marker("TIMEOUT after 120s - sent interrupt.")
    assert _line_is_error_marker("parse error at 12:5: unexpected token")
    assert _line_is_error_marker("Fail mk_thm: not allowed")


# --- _error_reason ---------------------------------------------------------

def test_error_reason_timeout():
    out = "TIMEOUT after 120s - sent interrupt.\nInitial goal:\n| (SOME (Rerr ...),s1) => T"
    r = _error_reason(out)
    assert r.upper().startswith("TIMEOUT")
    # Must NOT have grabbed the goal fragment.
    assert "Rerr" not in r


def test_error_reason_does_not_return_goal_fragment():
    # A failing proof prints its goal (mentioning Rerr/Rtype_error) BEFORE the
    # exception. The reason must NOT be that goal line.
    out = (
        "Initial goal:\n"
        "| (SOME (Rerr (Rabort Rtype_error)),s1) => T\n"
        "...lots of goal text...\n"
        "Exception- HOL_ERR {origin_function = \"DECIDE\"} raised\n"
    )
    r = _error_reason(out)
    assert "HOL_ERR" in r
    assert "Rtype_error" not in r


def test_error_reason_generic_when_no_marker():
    # Output with no recognizable error marker and only goal-ish text must
    # fall back to a generic 'could not validate', never a goal fragment.
    out = "| (SOME (Rerr (Rabort Rtype_error)),s1) => T\nsome other goal line\n"
    r = _error_reason(out)
    assert "Rtype_error" not in r
    assert "could not validate" in r


def test_error_reason_real_exception():
    out = "Exception- Fail \"oops\" raised\n"
    r = _error_reason(out)
    assert "error:" in r and ("Fail" in r or "Exception" in r)


# --- budget ----------------------------------------------------------------

def test_budget_raised():
    assert PER_THEOREM_TIMEOUT >= 120


# --- _auto_cheated_deps_lines / target self-cheat --------------------------

class _FakeCursor:
    def __init__(self, failed):
        self._failed_proofs = failed


def test_deps_excludes_target():
    cur = _FakeCursor({"thmA": "timeout >120s loading whole proof",
                       "thmB": "error: HOL_ERR ..."})
    lines = _auto_cheated_deps_lines(cur, target_name="thmA")
    rendered = "\n".join(lines)
    assert "thmA" not in rendered          # target excluded
    assert "thmB" in rendered              # genuine dep still named


def test_deps_empty_when_only_target_failed():
    cur = _FakeCursor({"thmA": "timeout >120s loading whole proof"})
    # The only failed proof IS the target — there are no real deps to name.
    assert _auto_cheated_deps_lines(cur, target_name="thmA") == []


def test_target_self_cheated_reason():
    cur = _FakeCursor({"thmA": "timeout >120s loading whole proof"})
    assert _target_self_cheated_reason(cur, "thmA") is not None
    assert _target_self_cheated_reason(cur, "thmB") is None
    assert _target_self_cheated_reason(cur, None) is None


def test_self_cheat_lines_timeout_never_mentions_holmake():
    lines = _target_self_cheated_lines("timeout >120s loading whole proof")
    blob = "\n".join(lines).lower()
    assert "not validated" in blob
    assert "suspend" in blob               # in-workflow remedy
    assert "holmake" not in blob           # MUST NOT point at the file gate


def test_self_cheat_lines_error_never_mentions_holmake():
    lines = _target_self_cheated_lines("error: HOL_ERR ...")
    blob = "\n".join(lines).lower()
    assert "not validated" in blob
    assert "holmake" not in blob
