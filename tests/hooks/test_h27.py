"""H27 (audit gates at commit time) must judge only what the commit introduces:
an `--amend` that changes a statement line is not a proof edit, a lone `>-`
is H25's advisory and not a blocker, while a body edit adding `cheat` is."""
import subprocess
import importlib.util
import re
from pathlib import Path

import pytest

_spec = importlib.util.spec_from_file_location(
    "git_commit_snapshot", Path(__file__).resolve().parents[2] / "hooks/git_commit_snapshot.py")
_snapshot_module = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_snapshot_module)


SCRIPT = """\
open HolKernel boolLib bossLib;

val _ = new_theory "foo";

Theorem foo_one:
  !x. x + 0 = x
Proof
  rw [] >> TRY (simp [])
  >> simp []
  >> fs []
QED

Theorem foo_two:
  !x. 0 + x = x
Proof
  rw [] >> strip_tac
  >- metis_tac []
QED

val _ = export_theory();
"""


def git(repo, *args):
    subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@t", *args],
                   cwd=repo, check=True, capture_output=True, text=True)


@pytest.fixture
def repo(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    git(repo, "init", "-q")
    (repo / "README").write_text("foo\n")
    git(repo, "add", "README")
    git(repo, "commit", "-q", "-m", "init")
    (repo / "fooScript.sml").write_text(SCRIPT)
    git(repo, "add", "fooScript.sml")
    git(repo, "commit", "-q", "-m", "A")
    return repo


def stage(repo, old, new):
    p = repo / "fooScript.sml"
    text = p.read_text()
    assert old in text
    p.write_text(text.replace(old, new))
    git(repo, "add", "fooScript.sml")


def run(run_hook, repo, command="git commit --amend --no-edit"):
    return run_hook("h27_commit_audit_gate.py", "Bash", {"command": command}, cwd=repo)


def test_amend_with_statement_only_retype_passes(run_hook, repo):
    stage(repo, "!x. x + 0 = x", "!y. y + 0 = y")
    code, err, _ = run(run_hook, repo)
    assert code == 0, err


def test_lone_dispatcher_is_not_a_blocker(run_hook, repo):
    stage(repo, "rw [] >> strip_tac\n  >- metis_tac []", "rw [ADD] >> strip_tac\n  >- metis_tac []")
    code, err, _ = run(run_hook, repo, "git commit -m 'retouch foo_two'")
    assert code == 0, err


def test_amend_body_edit_adding_cheat_is_refused(run_hook, repo):
    stage(repo, "  >- metis_tac []", "  >- cheat")
    code, err, _ = run(run_hook, repo)
    assert code == 2
    assert "Gate 3" in err


def test_amend_judges_only_the_touched_theorem(run_hook, repo):
    stage(repo, "  >- metis_tac []", "  >- cheat")
    code, err, _ = run(run_hook, repo)
    assert code == 2
    assert "foo_one" not in err, "untouched theorem must not be judged"


def test_body_edit_in_touched_theorem_is_swept(run_hook, repo):
    stage(repo, "  rw [] >> TRY (simp [])", "  rw [ADD] >> TRY (simp [])")
    code, err, _ = run(run_hook, repo, "git commit -m 'x'")
    assert code == 2
    assert "Gate 5" in err
    assert "adjacent normalisers" not in err, "unchanged inherited findings are not new defects"
    assert "foo_two" not in err


def test_inherited_style_in_touched_theorem_passes(run_hook, repo):
    stage(repo, "  >> fs []", "  >> fs []\n  >> ALL_TAC")
    code, err, _ = run(run_hook, repo)
    assert code == 0, err


def test_staged_cheat_not_hidden_by_unstaged_cleanup(run_hook, repo):
    stage(repo, "  >- metis_tac []", "  >- cheat")
    (repo / "fooScript.sml").write_text(SCRIPT)
    code, err, _ = run(run_hook, repo)
    assert code == 2 and "Gate 3" in err


def test_unstaged_cheat_not_audited_for_index_commit(run_hook, repo):
    stage(repo, "!x. 0 + x = x", "!y. 0 + y = y")
    p = repo / "fooScript.sml"
    p.write_text(p.read_text().replace("  >- metis_tac []", "  >- cheat"))
    assert run(run_hook, repo)[0] == 0
    code, err, _ = run(run_hook, repo, "git commit -am 'checkpoint'")
    assert code == 2 and "Gate 3" in err


@pytest.mark.parametrize("flags", ["--only", ""])
def test_path_commit_excludes_other_staged_files(run_hook, repo, flags):
    stage(repo, "  >- metis_tac []", "  >- cheat")
    (repo / "README").write_text("changed\n")
    code, err, _ = run(run_hook, repo, f"git commit {flags} -m note -- README")
    assert code == 0, err
    assert run(run_hook, repo, "git commit --include -m note -- README")[0] == 2


def test_only_reads_selected_worktree_content(run_hook, repo):
    p = repo / "fooScript.sml"
    p.write_text(SCRIPT.replace("  >- metis_tac []", "  >- cheat"))
    code, err, _ = run(run_hook, repo, "git commit -m x -- fooScript.sml")
    assert code == 2 and "Gate 3" in err


def test_message_is_not_parsed_as_flags(run_hook, repo):
    (repo / "fooScript.sml").write_text(SCRIPT.replace("  >- metis_tac []", "  >- cheat"))
    assert run(run_hook, repo, "git commit -m 'document --all and -a'")[0] == 0


def test_quoted_repo_path(run_hook, repo):
    stage(repo, "  >- metis_tac []", "  >- cheat")
    spaced = repo.with_name("repo with spaces")
    repo.rename(spaced)
    code, err, _ = run(run_hook, spaced, f"git -C '{spaced}' commit -m x")
    assert code == 2 and "Gate 3" in err


def test_staging_and_commit_must_be_separate_calls(run_hook, repo):
    code, err, _ = run(run_hook, repo, "git add fooScript.sml && git commit -m x")
    assert code == 2 and "separate tool calls" in err


@pytest.mark.parametrize("command", [
    "bash -c 'git commit -m x'", "env git commit -m x",
    'git commit -m "$(git add fooScript.sml)"',
])
def test_unmodelled_shell_commit_cannot_silently_bypass_audit(run_hook, repo, command):
    stage(repo, "  >- metis_tac []", "  >- cheat")
    code, err, _ = run(run_hook, repo, command)
    assert code == 2 and "cannot determine the proposed commit" in err


def test_literal_commit_prose_is_not_a_commit_or_substitution(run_hook, repo):
    stage(repo, "  >- metis_tac []", "  >- cheat")
    assert run(run_hook, repo, "echo 'git commit -m x'")[0] == 0
    assert run(run_hook, repo, "git log --grep='git commit'")[0] == 0


def test_scoped_wip_approval_survives_status_but_not_new_contents(run_hook, repo):
    stage(repo, "  >- metis_tac []", "  >- cheat")
    command = "git commit -m checkpoint"
    code, err, _ = run(run_hook, repo, command)
    assert code == 2
    review = re.search(r"Review ([0-9a-f]{12}):", err).group(1)
    approval = f"Approve the incomplete-proof checkpoint for review {review}"

    def call(message, history=(), tool="Bash"):
        return run_hook("h27_commit_audit_gate.py", tool, {"command": command},
                        cwd=repo, user_msg=message, history=history)

    code, err, out = call(approval, [""])
    assert code == 0 and "does not grant Git permission" in out, (err, out)
    state = run_hook.home / ".claude/hook-state/test-session/audit_approvals.json"
    before = state.read_bytes()
    assert call("status?", ["", approval], "mcp__hol4__hol_build_status")[0] == 0
    assert state.read_bytes() == before
    assert call("status?", ["", approval])[0] == 0
    stage(repo, "  >- cheat", "  >- (cheat)")
    code, err, _ = call("keep going", ["", approval, "status?"])
    assert code == 2 and f"Review {review}:" not in err


def test_style_approval_does_not_permit_admission(run_hook, repo):
    stage(repo, "  >- metis_tac []", "  >- cheat")
    command = "git commit -m checkpoint"
    _, err, _ = run(run_hook, repo, command)
    review = re.search(r"Review ([0-9a-f]{12}):", err).group(1)
    code, err, _ = run_hook("h27_commit_audit_gate.py", "Bash", {"command": command},
        cwd=repo, user_msg=f"Approve style exceptions for review {review}", history=[""])
    assert code == 2 and "Gate 3" in err


def test_old_wip_phrase_cannot_bypass_content_resolution(run_hook, repo):
    code, err, _ = run_hook("h27_commit_audit_gate.py", "Bash",
        {"command": "bash -c 'git commit -m x'"}, cwd=repo, user_msg="git ok wip ok")
    assert code == 2 and "cannot determine" in err


def test_deleted_finalise_is_blocked(run_hook, repo):
    p = repo / "fooScript.sml"
    p.write_text('Theorem t:\n T\nProof\n suspend "a"\nQED\n'
                 'Resume t[a]:\n simp[]\nQED\nFinalise t;\n')
    git(repo, "add", "fooScript.sml")
    git(repo, "commit", "-qm", "fixture")
    p.write_text(p.read_text().replace("Finalise t;\n", ""))
    git(repo, "add", "fooScript.sml")
    code, err, _ = run(run_hook, repo)
    assert code == 2 and "Gate 2" in err


@pytest.mark.parametrize("args", [
    ["-m", "x"], ["-am", "x"], ["--amend", "--no-edit"],
    ["--only", "-m", "x", "--", "README"],
    ["--include", "-m", "x", "--", "README"],
    ["-m", "x", "--", "fooScript.sml"],
])
def test_snapshot_matches_real_git_commit_without_changing_index(repo, args):
    import shlex
    stage(repo, "  >- metis_tac []", "  >- cheat")
    source = repo / "fooScript.sml"
    source.write_text(source.read_text().replace("  >- cheat", "  >- simp[]"))
    (repo / "README").write_text("changed\n")
    index = (repo / ".git/index").read_bytes()
    _, files = _snapshot_module.snapshot(shlex.join(["git", "commit", *args]), str(repo))
    assert (repo / ".git/index").read_bytes() == index
    git(repo, "commit", *args)
    actual = subprocess.run(["git", "show", "HEAD:fooScript.sml"], cwd=repo,
                            check=True, capture_output=True, text=True).stdout
    expected = files.get("fooScript.sml", (SCRIPT, SCRIPT))[1]
    assert actual == expected
