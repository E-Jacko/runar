"""``@sighash`` directive parsing (issue #123).

A public method may carry a ``/** @sighash <FLAGS> */`` comment directive that
declares which BIP-143 sighash type its auto-injected covenant (and the
SDK-built preimage) commits to. ``<FLAGS>`` is a ``|``-separated set of SigHash
names, e.g. ``SINGLE|FORKID``, ``ALL|ANYONECANPAY|FORKID``, ``NONE|FORKID``.

The default (no directive) is ``ALL|FORKID`` (0x41) — byte-identical to the
historically-pinned mode, so existing fixtures see ZERO change.

Reuses the exact two-surface directive shape #109 established for
``@embedAlways`` (JSDoc block + leading trivia); the *detection* lives in the
parser, this module owns the *flag grammar* (name → value, combo validity).

Port of packages/runar-compiler/src/passes/sighash-directive.ts.
"""

from __future__ import annotations

import re
from dataclasses import dataclass

# Numeric value of each sighash flag name.
_FLAG_VALUES: dict[str, int] = {
    "ALL": 0x01,
    "NONE": 0x02,
    "SINGLE": 0x03,
    "FORKID": 0x40,
    "ANYONECANPAY": 0x80,
}

# The base-type names. Exactly one MUST appear in a directive.
_BASE_TYPE_NAMES = frozenset({"ALL", "NONE", "SINGLE"})

# SIGHASH_ALL | SIGHASH_FORKID — the default when no directive is present.
SIGHASH_DEFAULT = 0x41

# Base-type mask. ``sig_hash_type & BASE_TYPE_MASK`` recovers 1/2/3
# (ALL/NONE/SINGLE) after the FORKID/ANYONECANPAY high bits are stripped.
BASE_TYPE_MASK = 0x1F
BASE_ALL = 0x01
BASE_NONE = 0x02
BASE_SINGLE = 0x03
FLAG_FORKID = 0x40
FLAG_ANYONECANPAY = 0x80


@dataclass
class SighashParseResult:
    """Discriminated result: exactly one of ``value`` / ``error`` is set."""
    value: int | None = None
    error: str | None = None


def parse_sighash_flags(flags_text: str) -> SighashParseResult:
    """Parse the flag list of an ``@sighash`` directive.

    ``flags_text`` is the raw text following ``@sighash`` (e.g. ``"SINGLE|FORKID"``),
    with any trailing comment punctuation already stripped by the caller.

    Validation (security-relevant — a mis-declared mode is an exploit class):
      - every name must be a known flag (reject typos like ``FORKD``)
      - EXACTLY ONE base type (ALL/NONE/SINGLE) — reject zero, and reject
        nonsensical combos such as ``ALL|NONE``. This is checked on NAMES, not on
        the OR-ed numeric value, because ``ALL|NONE`` (0x01|0x02) collides with
        the numeric value of SINGLE (0x03) — a silent, dangerous aliasing a
        purely numeric check would miss.
      - reject a duplicated flag name (signals a copy/paste error).
      - FORKID is mandatory on BSV (the whole OP_PUSH_TX / BIP-143 machinery is
        FORKID-only) — reject a FORKID-less flag set (deploy-to-brick).
    """
    raw = flags_text.strip()
    if raw == "":
        return SighashParseResult(
            error="@sighash directive requires at least one flag "
                  "(e.g. `@sighash ALL|FORKID`)"
        )

    names = [n.strip() for n in raw.split("|")]
    seen: set[str] = set()
    base_types: list[str] = []
    value = 0

    for name in names:
        if name == "":
            return SighashParseResult(
                error=f'@sighash directive has an empty flag in "{raw}"'
            )
        if name not in _FLAG_VALUES:
            return SighashParseResult(
                error=f'@sighash: unknown flag "{name}" '
                      f"(valid: ALL, NONE, SINGLE, FORKID, ANYONECANPAY)"
            )
        if name in seen:
            return SighashParseResult(
                error=f'@sighash: duplicate flag "{name}" in "{raw}"'
            )
        seen.add(name)
        if name in _BASE_TYPE_NAMES:
            base_types.append(name)
        value |= _FLAG_VALUES[name]

    if len(base_types) == 0:
        return SighashParseResult(
            error=f"@sighash: must specify exactly one base type "
                  f'(ALL, NONE, or SINGLE); got "{raw}"'
        )
    if len(base_types) > 1:
        return SighashParseResult(
            error=f"@sighash: cannot combine base types ({'|'.join(base_types)}) "
                  f"— pick exactly one of ALL/NONE/SINGLE"
        )

    # FORKID is mandatory on BSV: the entire OP_PUSH_TX / BIP-143 preimage
    # machinery is FORKID-only, so a FORKID-less flag set deploys a covenant
    # whose derived signature can never verify (deploy-to-brick). Reject it up
    # front rather than let a spendable-looking script ship.
    if (value & _FLAG_VALUES["FORKID"]) == 0:
        return SighashParseResult(
            error=f"@sighash: FORKID is mandatory on BSV; write e.g. "
                  f'@sighash {base_types[0]}|FORKID (got "{raw}")'
        )

    return SighashParseResult(value=value)


# Extract the flag list following ``@sighash`` in a block of comment text.
_SIGHASH_RE = re.compile(r"@sighash\s+([A-Za-z0-9_|\s]*?)(?:\*/|\n|\r|$)")


def extract_sighash_directive(comment_text: str) -> SighashParseResult | None:
    """Extract and parse an ``@sighash`` directive from a block of comment text.

    Returns ``None`` when no ``@sighash`` token is present, otherwise the parse
    result (value or error). Used by the parser after it has collected a
    method's JSDoc / leading-comment trivia.
    """
    m = _SIGHASH_RE.search(comment_text)
    if m is None:
        return None
    return parse_sighash_flags(m.group(1) or "")


def describe_sighash(value: int) -> str:
    """Human-readable rendering of a sighash value (for diagnostics)."""
    parts: list[str] = []
    base = value & BASE_TYPE_MASK
    if base == BASE_ALL:
        parts.append("ALL")
    elif base == BASE_NONE:
        parts.append("NONE")
    elif base == BASE_SINGLE:
        parts.append("SINGLE")
    else:
        parts.append(f"0x{base:x}")
    if value & FLAG_ANYONECANPAY:
        parts.append("ANYONECANPAY")
    if value & FLAG_FORKID:
        parts.append("FORKID")
    return "|".join(parts)
