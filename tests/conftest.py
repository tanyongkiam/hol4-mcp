"""Pytest fixtures for HOL4 tests."""

import pytest
import asyncio
from pathlib import Path

from hol4_mcp.hol_session import HOLSession
from hol4_mcp.hol_cursor import FileProofCursor


FIXTURES_DIR = Path(__file__).parent / "fixtures"
SML_HELPERS_DIR = Path(__file__).parent.parent / "hol4_mcp" / "sml_helpers"


@pytest.fixture
async def hol_session():
    """Fixture that provides a HOL session with tactic_prefix loaded."""
    session = HOLSession(str(FIXTURES_DIR))
    await session.start()
    # Load tactic_prefix.sml which defines timing functions
    result = await session.send(f'use "{SML_HELPERS_DIR / "tactic_prefix.sml"}";', timeout=30)
    assert "error" not in result.lower(), f"Failed to load tactic_prefix.sml: {result}"
    yield session
    await session.stop()


@pytest.fixture
def temp_script(tmp_path: Path) -> Path:
    """Fixture that provides a temporary SML script file."""
    script = tmp_path / "testScript.sml"
    script.write_text("""
(* Test script for proof timing *)

Theorem test_trivial:
  T
Proof
  rw[]
QED
""")
    return script