"""Pointing the session at another script in the same workdir must not make HOL
export the partially replayed previous theory.

`Theory.new_theory` exports the current theory segment to disk before creating
the next one whenever the current segment is non-empty. A cursor that has
replayed part of `aaScript.sml` therefore leaves a truncated
`aaTheory.{dat,sig,sml}` in the workdir the moment `bbScript.sml`'s
`new_theory` runs in the same HOL process, and Holmake then treats that export
as an up-to-date build of `aaTheory`.
"""

from pathlib import Path

from hol4_mcp.hol_mcp_server import (
    _init_file_cursor,
    hol_state_at as _hol_state_at,
    hol_stop as _hol_stop,
)

hol_state_at = _hol_state_at
hol_stop = _hol_stop
hol_file_init = _init_file_cursor

COMPLETE_MARKER = "No goals (proof complete)"


def _script(theory: str, thm: str) -> str:
    return (
        "open HolKernel Parse boolLib bossLib;\n"   # 1
        "\n"                                        # 2
        f'val _ = new_theory "{theory}";\n'         # 3
        "\n"                                        # 4
        f"Theorem {thm}:\n"                         # 5
        "  T\n"                                     # 6
        "Proof\n"                                   # 7
        "  simp[]\n"                                # 8
        "QED\n"                                     # 9
        "\n"                                        # 10
        "val _ = export_theory();\n"                # 11
    )


_QED = 9


async def test_file_switch_does_not_export_partial_theory(tmp_path: Path):
    session = "file_switch_export"
    first = tmp_path / "aaScript.sml"
    second = tmp_path / "bbScript.sml"
    first.write_text(_script("aa", "first_thm"))
    second.write_text(_script("bb", "second_thm"))
    try:
        init = await hol_file_init(file=str(first), session=session)
        assert not init.startswith("ERROR"), init
        state = await hol_state_at(session=session, line=_QED, col=1)
        assert COMPLETE_MARKER in state, state

        init = await hol_file_init(file=str(second), session=session)
        assert not init.startswith("ERROR"), init
        state = await hol_state_at(session=session, line=_QED, col=1)
        assert COMPLETE_MARKER in state, state

        exported = sorted(
            str(p.relative_to(tmp_path)) for p in tmp_path.rglob("aaTheory.*")
        )
        assert exported == [], (
            f"switching files exported the partially replayed theory: {exported}"
        )
    finally:
        await hol_stop(session=session)
