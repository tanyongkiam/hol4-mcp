"""Test step_plan_json consistency - single source of truth for O(1) navigation."""

import pytest
from pathlib import Path

from hol4_mcp.hol_file_parser import parse_step_plan_output
from hol4_mcp.hol_session import HOLSession, escape_sml_string

FIXTURES_DIR = Path(__file__).parent / "fixtures"
SML_HELPERS_DIR = Path(__file__).parent.parent / "hol4_mcp" / "sml_helpers"


@pytest.fixture
async def hol_session():
    """Fixture that provides a HOL session with tactic_prefix loaded."""
    session = HOLSession(str(FIXTURES_DIR))
    await session.start()
    result = await session.send(f'use "{SML_HELPERS_DIR / "tactic_prefix.sml"}";', timeout=10)
    assert "error" not in result.lower(), f"Failed to load tactic_prefix.sml: {result}"
    yield session
    await session.stop()


class TestStepPlan:
    """Test step_plan_json returns consistent step boundaries with commands."""

    async def test_step_plan_single_tactic(self, hol_session):
        """Single tactic returns one step."""
        tactic = "strip_tac"
        escaped = escape_sml_string(tactic)
        result = await hol_session.send(f'step_plan_json "{escaped}";', timeout=10)
        plan = parse_step_plan_output(result)
        
        assert len(plan) == 1
        assert plan[0].end == 9  # len("strip_tac")
        assert "e(strip_tac)" in plan[0].cmd

    async def test_step_plan_then_chain_is_one_step(self, hol_session):
        """THEN chain (>>) is treated as single step."""
        tactic = "strip_tac >> rw[] >> fs[]"
        escaped = escape_sml_string(tactic)
        result = await hol_session.send(f'step_plan_json "{escaped}";', timeout=10)
        plan = parse_step_plan_output(result)
        
        # THEN chain is one step with end at the final fragment
        assert len(plan) == 1
        assert plan[0].end == len(tactic)
        assert plan[0].cmd.count("e(") == 1

    async def test_step_plan_thenl_is_one_step(self, hol_session):
        """THENL (>-) with arms is treated as single step."""
        tactic = "conj_tac >- simp[] >- fs[]"
        escaped = escape_sml_string(tactic)
        result = await hol_session.send(f'step_plan_json "{escaped}";', timeout=10)
        plan = parse_step_plan_output(result)
        
        # THENL is one step
        assert len(plan) == 1
        assert plan[0].end == len(tactic)
        assert plan[0].cmd.count("e(") == 1

    async def test_step_plan_thenl_bracket_is_one_step(self, hol_session):
        """THENL with bracket (>|) is treated as single step."""
        tactic = "conj_tac >| [simp[], rw[]]"
        escaped = escape_sml_string(tactic)
        result = await hol_session.send(f'step_plan_json "{escaped}";', timeout=10)
        plan = parse_step_plan_output(result)
        
        assert len(plan) == 1
        assert plan[0].end == len(tactic)

    async def test_step_plan_ends_are_monotonic(self, hol_session):
        """Step ends should be monotonically increasing."""
        tactic = "strip_tac >> rw[]"
        escaped = escape_sml_string(tactic)
        result = await hol_session.send(f'step_plan_json "{escaped}";', timeout=10)
        plan = parse_step_plan_output(result)
        
        for i in range(1, len(plan)):
            assert plan[i].end >= plan[i-1].end

    async def test_step_plan_commands_are_executable(self, hol_session):
        """Step commands should be valid e() calls."""
        tactic = "conj_tac >- simp[] >- fs[]"
        escaped = escape_sml_string(tactic)
        result = await hol_session.send(f'step_plan_json "{escaped}";', timeout=10)
        plan = parse_step_plan_output(result)
        
        for step in plan:
            assert step.cmd.strip().startswith("e(")
            assert step.cmd.strip().endswith(");")
