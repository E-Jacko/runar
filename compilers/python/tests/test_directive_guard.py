"""Fail-closed guard for the ``@sighash`` comment directive (#123) that only
the TypeScript compiler implements. The Python compiler must reject it rather
than silently drop it. (``@embedAlways`` (#109) is now supported by the Python
TS-surface parser and is no longer guarded.)
"""

from __future__ import annotations

from runar_compiler.frontend.parser_dispatch import parse_source


def test_parse_source_rejects_sighash_directive():
    source = """
class Counter extends SmartContract {
    readonly x: bigint;
    constructor(x: bigint) { super(x); }
    /** @sighash SINGLE|FORKID */
    public unlock() {}
}
"""
    result = parse_source(source, "Counter.runar.ts")
    assert result.errors, "expected fail-closed error for @sighash directive"
    joined = "\n".join(result.error_strings())
    assert "@sighash" in joined and "#123" in joined, joined


def test_parse_source_allows_non_directive_identifier():
    # A field named `sighashType` must NOT trip the word-boundary guard.
    source = """
class Counter extends SmartContract {
    readonly sighashType: bigint;
    constructor(sighashType: bigint) { super(sighashType); }
    public unlock() {}
}
"""
    result = parse_source(source, "Counter.runar.ts")
    assert not any("not yet supported" in m for m in result.error_strings()), \
        result.error_strings()
