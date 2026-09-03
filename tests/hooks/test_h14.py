"""H14 (destructive git ops need `git ok`): read-only subcommands that share a
prefix with a destructive verb, dry runs, and git verbs quoted inside prose
must pass; the destructive forms must keep blocking."""
import pytest


PASS_CASES = [
    pytest.param("git merge-base --is-ancestor abc123 HEAD", id="merge-base"),
    pytest.param("git stash list", id="stash-list"),
    pytest.param("git stash show --stat stash@{0}", id="stash-show"),
    pytest.param("git clean -n", id="clean-dry-n"),
    pytest.param("git clean --dry-run", id="clean-dry-run"),
    pytest.param('echo "state after the fix (git checkout, buildable) is recorded"',
                 id="quoted-prose"),
    pytest.param("git status --short && git diff --stat", id="status-diff"),
    pytest.param("git log --oneline -5 -- fooScript.sml", id="log"),
]

BLOCK_CASES = [
    pytest.param("git merge x", id="merge"),
    pytest.param("git stash", id="stash"),
    pytest.param("git stash pop", id="stash-pop"),
    pytest.param("git clean -fd", id="clean-fd"),
    pytest.param("git checkout -- f", id="checkout-file"),
    pytest.param("git -C d commit -m 'x'", id="C-commit"),
    pytest.param("git branch -D x", id="branch-D"),
    pytest.param("bash -c 'git push origin HEAD'", id="bash-c-push"),
    pytest.param('echo "$(git stash)"', id="stash-in-subst"),
]


@pytest.mark.parametrize("cmd", PASS_CASES)
def test_allows(run_hook, cmd):
    code, err, _ = run_hook("h14_git_destructive_consent.py", "Bash", {"command": cmd})
    assert code == 0, err


@pytest.mark.parametrize("cmd", BLOCK_CASES)
def test_blocks(run_hook, cmd):
    code, err, _ = run_hook("h14_git_destructive_consent.py", "Bash", {"command": cmd})
    assert code == 2
    assert "H14" in err


def test_consent_allows(run_hook):
    code, _, _ = run_hook("h14_git_destructive_consent.py", "Bash",
                          {"command": "git commit -m x"}, user_msg="git ok, commit it")
    assert code == 0
