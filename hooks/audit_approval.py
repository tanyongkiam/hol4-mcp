"""Content-scoped audit exceptions shared by both hook integrations.

This is audit policy only, never permission to execute Git. State is isolated
by the existing client/session contract. Nothing here runs on proof steps or
status polls.
"""
import hashlib
import json
import os
import re
import time

from hook_payload import session_state_dir, user_messages

WINDOW = 30 * 60
APPROVE = re.compile(
    r"(?:I\s+)?(?:approve|allow)\s+(?:the\s+)?"
    r"(style exceptions|incomplete[- ]proof checkpoint|style exceptions and incomplete[- ]proof checkpoint)"
    r"\s+(?:for\s+)?(?:review\s+)?([0-9a-f]{12})[.!]?", re.I)
REVOKE = re.compile(r"revoke\s+(?:review\s+)?([0-9a-f]{12}|all audit approvals)[.!]?", re.I)


def finding_class(message):
    return "incomplete-proof" if message.startswith(("Gate 2:", "Gate 3:")) else "style"


def review_id(root, command, files, findings):
    scope = {"repository": os.path.realpath(root), "operation": "git commit",
             "command": command, "proof_files": files, "findings": findings}
    return hashlib.sha256(json.dumps(scope, sort_keys=True).encode()).hexdigest()[:12]


def history_position(state, messages):
    """Track a monotone position across append-only or rolling transcripts.

    Keep hashes, not prompt text. Without an overlapping history boundary we
    cannot prove an approval followed disclosure, so pending reviews must be
    disclosed again. Existing, unexpired grants retain their original scope.
    """
    current = [hashlib.sha256(text.encode()).hexdigest() for text in messages]
    previous = state.get("history")
    offset = state.get("history_offset", 0)
    if previous is None:
        continuous = not state.get("pending")  # legacy state has no boundary
    else:
        overlap = next((n for n in range(min(len(previous), len(current)), 0, -1)
                        if previous[-n:] == current[:n]), 0)
        continuous = bool(overlap) or not previous
        offset += len(previous) - overlap
    state["history"] = current
    state["history_offset"] = offset
    return offset, continuous


def apply_reviews(state, messages, review, now):
    """Pure transition; approval must follow disclosure of this exact review."""
    offset, continuous = history_position(state, messages)
    pending = state.setdefault("pending", {})
    if not continuous:
        pending.clear()
    grants = state.setdefault("grants", {})
    seen = set(state.get("seen", []))
    for key in list(pending):
        if not 0 <= now - pending[key]["created"] < WINDOW:
            pending.pop(key)
    for key in list(grants):
        classes = grants[key]["classes"]
        for kind in list(classes):
            if not 0 <= now - classes[kind] < WINDOW:
                classes.pop(kind)
        if not classes:
            grants.pop(key)
    if review not in pending:
        pending[review] = {"created": now, "after_user_count": offset + len(messages)}
    for index, text in enumerate(messages):
        index += offset
        text = text.strip()
        approval, revocation = APPROVE.fullmatch(text), REVOKE.fullmatch(text)
        if not approval and not revocation:
            continue
        event = hashlib.sha256(json.dumps([index, text]).encode()).hexdigest()
        if event in seen:
            continue
        seen.add(event)
        if revocation:
            key = revocation[1].lower()
            if key == "all audit approvals":
                grants.clear()
            else:
                grants.pop(key, None)
            continue
        kind, key = approval[1].lower(), approval[2].lower()
        proposal = pending.get(key)
        if proposal is None or index < proposal["after_user_count"]:
            continue
        classes = []
        if "style exceptions" in kind:
            classes.append("style")
        if "checkpoint" in kind:
            classes.append("incomplete-proof")
        # Approving one class must not renew a different class's expiry.
        existing = grants.setdefault(key, {"classes": {}})["classes"]
        existing.update({kind: now for kind in classes})
    state["seen"] = sorted(seen)
    return set(grants.get(review, {}).get("classes", []))


def approved_classes(payload, review):
    messages = user_messages(payload)
    if messages is None or not payload.get("session_id"):
        return set()  # unknown user/session provenance cannot grant exceptions
    directory = session_state_dir(payload)
    try:
        import fcntl
        os.makedirs(directory, exist_ok=True)
        with open(os.path.join(directory, "audit_approvals.lock"), "a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            path = os.path.join(directory, "audit_approvals.json")
            try:
                with open(path, encoding="utf-8") as stream:
                    state = json.load(stream)
            except (OSError, ValueError):
                state = {}
            result = apply_reviews(state, messages, review, time.time())
            with open(path, "w", encoding="utf-8") as stream:
                json.dump(state, stream)
            return result
    except (ImportError, OSError, TypeError, KeyError, ValueError, AttributeError):
        return set()  # never waive an audit because its state cannot be read/saved
