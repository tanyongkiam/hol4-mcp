import json
import os
from pathlib import Path
import subprocess
import sys

import pytest


ROOT = Path(__file__).resolve().parents[2]
CODEX = ROOT / "integrations" / "codex"
ADAPTER = CODEX / "hook_adapter.py"


@pytest.fixture
def run_codex_hook(tmp_path):
    plugin_data = tmp_path / "plugin-data"
    real_home = tmp_path / "real-home"
    real_home.mkdir()

    def run(script, payload, *args, env=None):
        environment = os.environ.copy()
        environment.update({
            "PLUGIN_ROOT": str(ROOT),
            "PLUGIN_DATA": str(plugin_data),
            "HOME": str(real_home),
            "PYTHONDONTWRITEBYTECODE": "1",
        })
        if env:
            environment.update(env)
        return subprocess.run(
            [sys.executable, str(script), *args],
            input=json.dumps(payload), text=True, capture_output=True,
            env=environment, timeout=60, check=False,
        )

    run.plugin_data = plugin_data
    run.real_home = real_home
    return run


def payload(tmp_path, tool_name, tool_input, event="PreToolUse", session="codex-test"):
    return {
        "session_id": session,
        "turn_id": "turn-1",
        "transcript_path": None,
        "cwd": str(tmp_path),
        "hook_event_name": event,
        "tool_name": tool_name,
        "tool_input": tool_input,
    }


def test_apply_patch_is_previewed_and_banned_tactic_blocks_without_editing(run_codex_hook, tmp_path):
    script = tmp_path / "fooScript.sml"
    before = "Theorem foo:\n  T\nProof\n  simp []\nQED\n"
    script.write_text(before)
    patch = """*** Begin Patch
*** Update File: fooScript.sml
@@
 Proof
-  simp []
+  TRY (simp [])
 QED
*** End Patch"""
    result = run_codex_hook(
        ADAPTER, payload(tmp_path, "apply_patch", {"command": patch}),
        "h1_banned_tactics.py",
    )
    assert result.returncode == 2
    assert "H1" in result.stderr and "TRY" in result.stderr
    assert script.read_text() == before


def test_apply_patch_advisory_is_returned_as_valid_codex_json(run_codex_hook, tmp_path):
    script = tmp_path / "fooScript.sml"
    script.write_text("Theorem foo:\n  T\nProof\n  cheat\nQED\n")
    patch = """*** Begin Patch
*** Update File: fooScript.sml
@@
 QED
+Resume foo[left]:
+  cheat
+QED
*** End Patch"""
    result = run_codex_hook(
        ADAPTER, payload(tmp_path, "apply_patch", {"command": patch}),
        "h10_resume_needs_finalise.py",
    )
    assert result.returncode == 0, result.stderr
    context = json.loads(result.stdout)["hookSpecificOutput"]["additionalContext"]
    assert "Finalise foo;" in context


def test_apply_patch_add_file_is_checked(run_codex_hook, tmp_path):
    patch = """*** Begin Patch
*** Add File: newScript.sml
+Theorem foo:
+  T
+Proof
+  FIRST [simp []]
+QED
*** End Patch"""
    result = run_codex_hook(
        ADAPTER, payload(tmp_path, "apply_patch", {"command": patch}),
        "h1_banned_tactics.py",
    )
    assert result.returncode == 2
    assert "FIRST" in result.stderr
    assert not (tmp_path / "newScript.sml").exists()


def test_apply_patch_fallback_does_not_depend_on_codex_internal_binary(run_codex_hook, tmp_path):
    script = tmp_path / "fooScript.sml"
    script.write_text("Theorem foo:\n  T\nProof\n  simp []\nQED\n")
    patch = """*** Begin Patch
*** Update File: fooScript.sml
@@
 Proof
-  simp []
+  ORELSE (simp []) (cheat)
 QED
*** End Patch"""
    result = run_codex_hook(
        ADAPTER, payload(tmp_path, "apply_patch", {"command": patch}),
        "h1_banned_tactics.py", env={"PATH": ""},
    )
    assert result.returncode == 2
    assert "ORELSE" in result.stderr


def test_post_tool_result_reaches_existing_advisory(run_codex_hook, tmp_path):
    call = payload(
        tmp_path,
        "mcp__hol4__hol_state_at",
        {"file": str(tmp_path / "fooScript.sml"), "line": 10},
        event="PostToolUse",
    )
    call["tool_response"] = (
        "goal state\n[Timing: total=31000ms, replay=30001ms, "
        "startup=999ms, method=replay]"
    )
    result = run_codex_hook(ADAPTER, call, "h8_state_at_replay_cost.py")
    assert result.returncode == 0, result.stderr
    context = json.loads(result.stdout)["hookSpecificOutput"]["additionalContext"]
    assert "30.0s" in context and "replay" in context


def test_prompt_capture_supplies_stable_pregrant_history(run_codex_hook, tmp_path):
    prompt = {
        "session_id": "consent-session",
        "turn_id": "turn-1",
        "cwd": str(tmp_path),
        "hook_event_name": "UserPromptSubmit",
        "prompt": "skip prefix ok for this investigation",
    }
    captured = run_codex_hook(CODEX / "prompt_capture.py", prompt)
    assert captured.returncode == 0
    call = payload(
        tmp_path, "mcp__hol4__hol_state_at",
        {"file": str(tmp_path / "fooScript.sml"), "line": 10, "skip_prefix": True},
        session="consent-session",
    )
    result = run_codex_hook(ADAPTER, call, "h31_skip_prefix_consent.py")
    assert result.returncode == 0, result.stderr
    assert "pre-granted" in json.loads(result.stdout)["hookSpecificOutput"]["additionalContext"]


def test_hook_state_is_redirected_away_from_real_claude_home(run_codex_hook, tmp_path):
    call = payload(
        tmp_path, "mcp__hol4__hol_state_at",
        {"file": str(tmp_path / "fooScript.sml"), "line": 10, "skip_prefix": True},
        session="isolated-session",
    )
    result = run_codex_hook(ADAPTER, call, "h31_skip_prefix_consent.py")
    assert result.returncode == 2
    assert not (run_codex_hook.real_home / ".claude").exists()
    isolated = run_codex_hook.plugin_data / "runtime-home" / ".claude" / "hook-state"
    assert isolated.is_dir()


def test_session_context_is_codex_native(run_codex_hook, tmp_path):
    (tmp_path / "Holmakefile").write_text("")
    start = {
        "session_id": "start-session",
        "cwd": str(tmp_path),
        "hook_event_name": "SessionStart",
        "source": "startup",
    }
    result = run_codex_hook(CODEX / "session_context.py", start)
    assert result.returncode == 0
    context = json.loads(result.stdout)["hookSpecificOutput"]["additionalContext"]
    assert "hol4-proving" in context
    assert "Claude" not in context and "settings.json" not in context


def test_plugin_files_reference_only_existing_codex_components():
    manifest = json.loads((ROOT / ".codex-plugin" / "plugin.json").read_text())
    hooks = json.loads((ROOT / "hooks" / "hooks.json").read_text())
    assert manifest["skills"] == "./skills/"
    assert manifest["mcpServers"]["hol4"]["tool_timeout_sec"] >= 600
    assert not (ROOT / ".mcp.json").exists()
    commands = [
        handler["command"]
        for groups in hooks["hooks"].values()
        for group in groups
        for handler in group["hooks"]
    ]
    assert all("${PLUGIN_ROOT}" in command for command in commands)
    assert not any("h14_git_destructive_consent.py" in command for command in commands)
    assert not any("h22_hol4_context.py" in command for command in commands)
