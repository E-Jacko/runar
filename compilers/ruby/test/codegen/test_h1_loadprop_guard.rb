# frozen_string_literal: true

require_relative "../test_helper"
require "runar_compiler/ir/types"
require "runar_compiler/codegen/stack"

# ---------------------------------------------------------------------------
# H1 (#119 tail): _lower_load_prop must NOT silently coerce an unknown property
# onto constructor slot 0.
#
# A `load_prop` binding whose name is not a declared constructor-param property
# used to fall through to a placeholder for constructor slot 0 (or, in the Ruby
# tier, the count of non-initialized props) -- an UNRELATED argument's
# deploy-time bytes -- with no diagnostic. That is a silent-wrong-code path: the
# produced locking script splices the wrong value at that position.
#
# The hardened behaviour is a HARD ERROR with a clear diagnostic and the
# binding's source location, instead of the silent placeholder.
# ---------------------------------------------------------------------------

class TestH1LoadPropGuard < Minitest::Test
  include RunarCompiler::IR

  # Minimal ANF program with a real readonly constructor-param property `pk`
  # (constructor slot 0) plus a public method that loads a property `ghost`
  # that is NOT declared on the contract. `ghost` therefore reaches the
  # placeholder fallback with no matching constructor slot.
  def program_with_unknown_load_prop
    load_ghost = ANFValue.new(kind: "load_prop")
    load_ghost.name = "ghost"

    assert_val = ANFValue.new(kind: "assert")
    assert_val.value_ref = "t0"

    ANFProgram.new(
      contract_name: "Ghost",
      properties: [ANFProperty.new(name: "pk", type: "PubKey", readonly: true)],
      methods: [
        ANFMethod.new(
          name: "spend",
          params: [],
          is_public: true,
          body: [
            ANFBinding.new(
              name: "t0",
              value: load_ghost,
              source_loc: SourceLocation.new(file: "Ghost.runar.ts", line: 7, column: 4)
            ),
            ANFBinding.new(name: "t1", value: assert_val)
          ]
        )
      ]
    )
  end

  def test_raises_on_load_prop_with_no_constructor_slot
    err = assert_raises(RuntimeError) do
      RunarCompiler::Codegen.lower_to_stack(program_with_unknown_load_prop)
    end
    assert_includes err.message, "ghost",
                    "diagnostic should name the offending ghost property"
  end

  def test_diagnostic_includes_prop_name_source_location_and_known_props
    err = assert_raises(RuntimeError) do
      RunarCompiler::Codegen.lower_to_stack(program_with_unknown_load_prop)
    end
    assert_includes err.message, "ghost"
    assert_includes err.message, "Ghost.runar.ts"
    assert_includes err.message, "7"
    assert_includes err.message, "constructor parameter"
    # The list of known constructor-param property names is included.
    assert_includes err.message, "pk"
  end

  def test_real_ctor_param_prop_lowers_without_error
    load_pk = ANFValue.new(kind: "load_prop")
    load_pk.name = "pk"

    assert_val = ANFValue.new(kind: "assert")
    assert_val.value_ref = "t0"

    program = ANFProgram.new(
      contract_name: "Ok",
      properties: [ANFProperty.new(name: "pk", type: "PubKey", readonly: true)],
      methods: [
        ANFMethod.new(
          name: "spend",
          params: [],
          is_public: true,
          body: [
            ANFBinding.new(name: "t0", value: load_pk),
            ANFBinding.new(name: "t1", value: assert_val)
          ]
        )
      ]
    )

    # A legit readonly constructor-param property has a deploy-time slot, so it
    # lowers to a placeholder WITHOUT raising.
    methods = RunarCompiler::Codegen.lower_to_stack(program)
    refute_nil methods.find { |m| m[:name] == "spend" }
  end
end
