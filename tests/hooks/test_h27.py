"""H27 (audit gates at commit time) must judge only what the commit introduces:
an `--amend` that changes a statement line is not a proof edit, a lone `>-`
is H25's advisory and not a blocker, while a body edit adding `cheat` is."""
import subprocess

import pytest


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
    assert "adjacent normalisers" in err
    assert "foo_two" not in err
