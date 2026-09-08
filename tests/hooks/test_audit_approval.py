"""Scoped approvals do not become broad WIP or Git pregrants."""
import importlib.util
from pathlib import Path


def load_policy(monkeypatch):
    hooks = Path(__file__).resolve().parents[2] / "hooks"
    monkeypatch.syspath_prepend(str(hooks))
    spec = importlib.util.spec_from_file_location("audit_approval", hooks / "audit_approval.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_approval_is_scoped_persistent_and_expires(monkeypatch):
    policy = load_policy(monkeypatch)
    key, other = "123456789abc", "abcdef123456"
    messages, state = ["please commit completed work"], {}
    assert not policy.apply_reviews(state, messages, key, 0)
    messages += [f"I approve the style exceptions for review {key}."]
    assert policy.apply_reviews(state, messages, key, 1) == {"style"}
    messages += ["what is the status?", "<codex_internal_context>keep going</codex_internal_context>"]
    assert policy.apply_reviews(state, messages, key, 2) == {"style"}
    assert not policy.apply_reviews(state, messages, other, 3)
    assert not policy.apply_reviews(state, messages, key, policy.WINDOW + 2)


def test_admission_approval_is_separate_and_revocable(monkeypatch):
    policy = load_policy(monkeypatch)
    key, messages, state = "123456789abc", ["git ok wip ok"], {}
    assert not policy.apply_reviews(state, messages, key, 0)
    messages += [f"Approve the incomplete-proof checkpoint for review {key}"]
    assert policy.apply_reviews(state, messages, key, 1) == {"incomplete-proof"}
    messages += [f"Revoke review {key}", "what now?"]
    assert not policy.apply_reviews(state, messages, key, 2)
    assert policy.finding_class("Gate 3: cheat added") == "incomplete-proof"
    assert policy.finding_class("Gate 5: banned tactic") == "style"


def test_unreviewed_quoted_negated_or_historical_text_is_not_consent(monkeypatch):
    policy = load_policy(monkeypatch)
    key, state = "123456789abc", {}
    messages = [f"Approve style exceptions for review {key}"]
    assert not policy.apply_reviews(state, messages, key, 0)
    messages += [f"Do not approve style exceptions for review {key}",
                 f"> Approve style exceptions for review {key}"]
    assert not policy.apply_reviews(state, messages, key, 1)


def test_approving_one_class_does_not_renew_another(monkeypatch):
    policy = load_policy(monkeypatch)
    key, messages, state = "123456789abc", ["review this"], {}
    policy.apply_reviews(state, messages, key, 0)
    messages += [f"Approve style exceptions for review {key}"]
    policy.apply_reviews(state, messages, key, 1)
    messages += [f"Approve incomplete-proof checkpoint for review {key}"]
    assert policy.apply_reviews(state, messages, key, 1700) == {"style", "incomplete-proof"}
    assert policy.apply_reviews(state, messages, key, 1802) == {"incomplete-proof"}


def test_scope_changes_on_proof_command_repository_or_finding_change(monkeypatch):
    policy = load_policy(monkeypatch)
    args = ["/repo", "git commit -m x", {"aScript.sml": ["old", "new"]}, [["a", None, 2, "Gate 3: cheat"]]]
    original = policy.review_id(*args)
    for index, replacement in enumerate(["/other", "git commit --amend --no-edit",
                                         {"aScript.sml": ["old", "changed"]}, []]):
        changed = list(args)
        changed[index] = replacement
        assert policy.review_id(*changed) != original


def test_rolling_prompt_window_accepts_post_disclosure_approval(monkeypatch):
    policy = load_policy(monkeypatch)
    key, state = "123456789abc", {}
    messages = [f"earlier prompt {n}" for n in range(64)]
    assert not policy.apply_reviews(state, messages, key, 0)
    # Codex retains 64 prompts: the new approval still has list index 63.
    messages = messages[1:] + [f"I approve the style exceptions for review {key}."]
    assert policy.apply_reviews(state, messages, key, 1) == {"style"}
    messages = messages[1:] + ["status?"]
    assert policy.apply_reviews(state, messages, key, 2) == {"style"}
    assert state["grants"][key]["classes"]["style"] == 1
    messages = messages[1:] + [f"Revoke review {key}"]
    assert not policy.apply_reviews(state, messages, key, 3)
    messages = messages[1:] + ["continue"]
    assert not policy.apply_reviews(state, messages, key, 4)


def test_rolling_history_does_not_turn_preapproval_into_consent(monkeypatch):
    policy = load_policy(monkeypatch)
    key, state = "123456789abc", {}
    messages = [f"prompt {n}" for n in range(63)] + [
        f"Approve style exceptions for review {key}"]
    assert not policy.apply_reviews(state, messages, key, 0)
    messages = messages[1:] + ["status?"]
    assert not policy.apply_reviews(state, messages, key, 1)


def test_missing_history_boundary_requires_redisclosure(monkeypatch):
    policy = load_policy(monkeypatch)
    key = "123456789abc"
    for state in ({"pending": {key: {"created": 0, "after_user_count": 64}}},
                  {}):
        policy.apply_reviews(state, ["old context"], key, 1)
        messages = [f"Approve style exceptions for review {key}"]
        assert not policy.apply_reviews(state, messages, key, 2)
        messages += [f"I approve the style exceptions for review {key}."]
        assert policy.apply_reviews(state, messages, key, 3) == {"style"}


def test_rolling_history_does_not_renew_expired_approval(monkeypatch):
    policy = load_policy(monkeypatch)
    key, state, messages = "123456789abc", {}, ["review", "context"]
    policy.apply_reviews(state, messages, key, 0)
    messages = messages[1:] + [f"Approve style exceptions for review {key}"]
    assert policy.apply_reviews(state, messages, key, 1) == {"style"}
    messages = messages[1:] + ["status?"]
    assert not policy.apply_reviews(state, messages, key, policy.WINDOW + 2)
