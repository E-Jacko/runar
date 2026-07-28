# frozen_string_literal: true

require_relative "../test_helper"
require_relative "codegen_helper"

# ---------------------------------------------------------------------------
# C18 (P1 funds-safety): a var-length state read inside a PRIVATE helper still
# needs _codePart.
#
# `method_reads_var_len_state?` used to walk only the public method's own
# bindings (plus if/loop bodies), while its sibling
# `method_uses_check_preimage?` already recursed through private `method_call`
# targets. Private methods are INLINED into the caller's stack context, so a
# public method whose only read of a mutable variable-length (ByteString) state
# field happens inside a private helper computed `uses_code_part = false`.
# `_codePart` was then never pushed as the implicit stack parameter,
# `_lower_deserialize_state` took its "terminal method, skip deserialization"
# shortcut, and the later `load_prop` fell through to the DEPLOY-TIME
# constructor placeholder instead of the live on-chain state.
#
# The lock: the helper variant must compile byte-identically to the control
# variant that reads `len(this.tag)` directly.
# ---------------------------------------------------------------------------

class TestVarLenStatePrivateRead < Minitest::Test
  include CodegenTestHelpers

  HELPER_SRC = <<~TS
    class VarLenPrivateRead extends StatefulSmartContract {
      tag: ByteString;
      constructor(tag: ByteString) { super(tag); this.tag = tag; }
      private tagLen(): bigint { return len(this.tag); }
      public check(expected: bigint) { assert(this.tagLen() == expected); }
    }
  TS

  # Same contract, but `check` reads the var-length state field directly.
  CONTROL_SRC = <<~TS
    class VarLenPrivateRead extends StatefulSmartContract {
      tag: ByteString;
      constructor(tag: ByteString) { super(tag); this.tag = tag; }
      public check(expected: bigint) { assert(len(this.tag) == expected); }
    }
  TS

  # Private helper calling another private helper -- the recursion must be
  # transitive, and the cycle guard must not hang on nested helpers.
  NESTED_SRC = <<~TS
    class VarLenPrivateRead extends StatefulSmartContract {
      tag: ByteString;
      constructor(tag: ByteString) { super(tag); this.tag = tag; }
      private inner(): bigint { return len(this.tag); }
      private outer(): bigint { return this.inner(); }
      public check(expected: bigint) { assert(this.outer() == expected); }
    }
  TS

  def compile(src)
    compile_ts_source(src, "VarLenPrivateRead.runar.ts")
  end

  def uses_code_part(artifact)
    m = artifact.abi.methods.find { |x| x.name == "check" }
    refute_nil m, "method 'check' not found in ABI"
    m.uses_code_part
  end

  def test_helper_variant_matches_direct_read
    assert_equal compile(CONTROL_SRC).script, compile(HELPER_SRC).script
  end

  def test_helper_variant_uses_code_part
    assert_equal true, uses_code_part(compile(HELPER_SRC))
  end

  def test_nested_private_helpers_match_direct_read
    nested = compile(NESTED_SRC)
    assert_equal compile(CONTROL_SRC).script, nested.script
    assert_equal true, uses_code_part(nested)
  end
end
