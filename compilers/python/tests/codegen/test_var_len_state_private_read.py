"""Regression: a var-length state read inside a PRIVATE helper still needs _codePart.

Deep-review finding C18 (P1 funds-safety). ``_method_reads_var_len_state`` used
to walk only the public method's own bindings (plus if/loop bodies), while its
sibling ``_method_uses_check_preimage`` already recursed through private
``method_call`` targets. Private methods are INLINED into the caller's stack
context, so a public method whose only read of a mutable variable-length
(ByteString) state field happens inside a private helper computed
``uses_code_part = False``. ``_codePart`` was then never pushed as the implicit
stack parameter, ``_lower_deserialize_state`` took its "terminal method, skip
deserialization" shortcut, and the later ``load_prop`` fell through to the
DEPLOY-TIME constructor placeholder instead of the live on-chain state.

The lock: the helper variant must compile byte-identically to the control
variant that reads ``len(this.tag)`` directly.
"""

from __future__ import annotations

from runar_compiler.compiler import compile_from_source_str_with_result


HELPER_SRC = """
class VarLenPrivateRead extends StatefulSmartContract {
  tag: ByteString;
  constructor(tag: ByteString) { super(tag); this.tag = tag; }
  private tagLen(): bigint { return len(this.tag); }
  public check(expected: bigint) { assert(this.tagLen() == expected); }
}
"""

# Same contract, but `check` reads the var-length state field directly.
CONTROL_SRC = """
class VarLenPrivateRead extends StatefulSmartContract {
  tag: ByteString;
  constructor(tag: ByteString) { super(tag); this.tag = tag; }
  public check(expected: bigint) { assert(len(this.tag) == expected); }
}
"""

# Private helper calling another private helper — the recursion must be
# transitive, and the cycle guard must not hang on mutual recursion.
NESTED_SRC = """
class VarLenPrivateRead extends StatefulSmartContract {
  tag: ByteString;
  constructor(tag: ByteString) { super(tag); this.tag = tag; }
  private inner(): bigint { return len(this.tag); }
  private outer(): bigint { return this.inner(); }
  public check(expected: bigint) { assert(this.outer() == expected); }
}
"""


def _compile(src: str):
    r = compile_from_source_str_with_result(
        src, "VarLenPrivateRead.runar.ts", disable_constant_folding=True
    )
    assert r.success, [d.message for d in r.diagnostics]
    return r


def _uses_code_part(result) -> bool:
    for m in result.artifact.abi.methods:
        if m.name == "check":
            return bool(m.uses_code_part)
    raise AssertionError("method 'check' not found in ABI")


class TestVarLenStateReadThroughPrivateMethod:
    def test_helper_variant_matches_direct_read(self):
        helper = _compile(HELPER_SRC)
        control = _compile(CONTROL_SRC)
        assert helper.script_hex == control.script_hex

    def test_helper_variant_uses_code_part(self):
        assert _uses_code_part(_compile(HELPER_SRC)) is True

    def test_nested_private_helpers_match_direct_read(self):
        nested = _compile(NESTED_SRC)
        control = _compile(CONTROL_SRC)
        assert nested.script_hex == control.script_hex
        assert _uses_code_part(nested) is True
