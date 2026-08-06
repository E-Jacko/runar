"""Testing-gap remediation Phase A5 (Python tier): machine-checked gate on the
always-ack ``MockProvider`` escape hatches (``MockProvider.always_ack``,
``disable_broadcast_validation()``, ``enable_broadcast_validation(False)``).

A test file may only use one of those escape hatches if it has a matching entry
in ``always_ack_allowlist.json``. Enforced in BOTH directions: it fails on
unlisted always-ack usage (someone quietly re-disabling the fund-safety net)
AND on stale entries (a file that no longer needs always-ack, or that was
deleted) — so the list can only shrink.

Mirrors ``packages/runar-sdk/src/__tests__/always-ack-allowlist.test.ts``,
``packages/runar-go/always_ack_allowlist_test.go``,
``packages/runar-rs/tests/always_ack_allowlist.rs`` and
``packages/runar-rb/spec/sdk/always_ack_allowlist_spec.rb``.
"""

from __future__ import annotations

import json
import re
from pathlib import Path

PACKAGE_ROOT = Path(__file__).resolve().parents[1]
ALLOWLIST_PATH = PACKAGE_ROOT / 'always_ack_allowlist.json'
SELF_REL = 'tests/test_always_ack_allowlist.py'
VALID_CATEGORIES = {'structure-only', 'negative-api', 'fixture-shape', 'pending-a3'}

# Call-site patterns only. The DEFINITIONS live in runar/sdk/provider.py, which
# is outside the scanned tree (tests/ only), so the provider is never
# self-referentially allowlisted.
ALWAYS_ACK_PATTERN = re.compile(
    r'MockProvider\.always_ack'
    r'|\.disable_broadcast_validation\(\)'
    r'|\.enable_broadcast_validation\(\s*False\s*\)'
)


def _allowlist() -> list[dict]:
    return json.loads(ALLOWLIST_PATH.read_text())['entries']


def _files_using_always_ack() -> set[str]:
    found = set()
    for path in sorted((PACKAGE_ROOT / 'tests').rglob('*.py')):
        rel = path.relative_to(PACKAGE_ROOT).as_posix()
        if rel == SELF_REL:
            continue
        if ALWAYS_ACK_PATTERN.search(path.read_text()):
            found.add(rel)
    return found


def test_allowlist_entries_are_well_formed():
    for e in _allowlist():
        assert e.get('file', '').strip(), f'allowlist entry with an empty file: {e}'
        assert e.get('reason', '').strip(), f"allowlist entry {e['file']} has no reason"
        assert e.get('category') in VALID_CATEGORIES, (
            f"allowlist entry {e['file']} has invalid category {e.get('category')!r} "
            f'(want one of {sorted(VALID_CATEGORIES)})'
        )


def test_every_allowlist_entry_names_an_existing_file():
    missing = [e['file'] for e in _allowlist() if not (PACKAGE_ROOT / e['file']).exists()]
    assert missing == [], (
        'always_ack_allowlist.json names files that no longer exist; remove them: '
        f'{missing}'
    )


def test_no_stale_allowlist_entries():
    usage = _files_using_always_ack()
    stale = [
        e['file']
        for e in _allowlist()
        if (PACKAGE_ROOT / e['file']).exists() and e['file'] not in usage
    ]
    assert stale == [], (
        'always_ack_allowlist.json has entries for files that no longer use '
        'MockProvider.always_ack / disable_broadcast_validation / '
        'enable_broadcast_validation(False) — remove them (the allowlist must only '
        f'shrink): {stale}'
    )


def test_no_ungoverned_always_ack_usage():
    listed = {e['file'] for e in _allowlist()}
    unlisted = sorted(_files_using_always_ack() - listed)
    assert unlisted == [], (
        'Unlisted always-ack MockProvider usage:\n  - ' + '\n  - '.join(unlisted) + '\n'
        'Add an entry to always_ack_allowlist.json with a file, reason and category '
        f'({" | ".join(sorted(VALID_CATEGORIES))}), or fix the test to run under the '
        'default validating provider instead.'
    )
