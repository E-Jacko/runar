# frozen_string_literal: true

# Repeated-operand consume bug (hand-written ANF via compile_from_ir / --ir).
#
# Mirrors packages/runar-compiler/src/__tests__/repeated-operand-consume.test.ts.
#
# A binding whose ANF value reads the SAME ref at more than one operand
# position used to make an independent last-use consume decision per load; a
# consume-mode bring_to_top of a ref already on top of the stack is a no-op,
# so `t := x + x` left a single stack slot for OP_ADD (underflow at runtime),
# or paired the opcode with the wrong slot when the ref was buried. Canonical
# rule: an operand load may consume (ROLL) its ref only when this binding is
# the ref's last use AND the ref occurs exactly once in the value's FULL
# operand list. Repeated refs copy (PICK / DUP) at every position.
# Unreachable from the frontend (every operand gets a fresh temp); reachable
# via hand-written IR.

require_relative "test_helper"
require "json"

class TestRepeatedOperandConsume < Minitest::Test
  def program_json(params, body)
    JSON.generate(
      "contractName" => "Repeat",
      "properties" => [{ "name" => "target", "type" => "bigint", "readonly" => true }],
      "methods" => [
        {
          "name" => "unlock",
          "params" => params.map { |p| { "name" => p, "type" => "bigint" } },
          "body" => body,
          "isPublic" => true
        }
      ]
    )
  end

  def compile_ir(json)
    RunarCompiler.compile_from_ir_bytes(json, disable_constant_folding: true)
  end

  def test_bin_op_same_ref_twice
    # unlock(x) { assert(x + x === target) }
    ir = program_json(["x"], [
      { "name" => "t0", "value" => { "kind" => "bin_op", "op" => "+", "left" => "x", "right" => "x" } },
      { "name" => "t1", "value" => { "kind" => "load_prop", "name" => "target" } },
      { "name" => "t2", "value" => { "kind" => "bin_op", "op" => "===", "left" => "t0", "right" => "t1" } },
      { "name" => "t3", "value" => { "kind" => "assert", "value" => "t2" } }
    ])
    artifact = compile_ir(ir)
    # Both loads of x must COPY: DUP DUP ADD <placeholder OP_0> NUMEQUAL NIP.
    # Cross-tier canonical hex, byte-identical with the TS tier.
    assert_equal "767693009c77", artifact.script
  end

  def test_call_same_ref_in_two_arg_positions
    # unlock(x) { assert(min(x, x) === target) }
    ir = program_json(["x"], [
      { "name" => "t0", "value" => { "kind" => "call", "func" => "min", "args" => %w[x x] } },
      { "name" => "t1", "value" => { "kind" => "load_prop", "name" => "target" } },
      { "name" => "t2", "value" => { "kind" => "bin_op", "op" => "===", "left" => "t0", "right" => "t1" } },
      { "name" => "t3", "value" => { "kind" => "assert", "value" => "t2" } }
    ])
    artifact = compile_ir(ir)
    # DUP DUP MIN <placeholder OP_0> NUMEQUAL NIP
    assert_equal "7676a3009c77", artifact.script
  end

  def test_repeated_ref_buried_below_live_slot
    # unlock(x, y) { assert(x + x + y === target) } -- at t0 the stack is
    # [x, y]: x sits at depth 1, so a naive rule pairs OP_ADD with the wrong
    # slot instead of copying x twice.
    ir = program_json(%w[x y], [
      { "name" => "t0", "value" => { "kind" => "bin_op", "op" => "+", "left" => "x", "right" => "x" } },
      { "name" => "t1", "value" => { "kind" => "bin_op", "op" => "+", "left" => "t0", "right" => "y" } },
      { "name" => "t2", "value" => { "kind" => "load_prop", "name" => "target" } },
      { "name" => "t3", "value" => { "kind" => "bin_op", "op" => "===", "left" => "t1", "right" => "t2" } },
      { "name" => "t4", "value" => { "kind" => "assert", "value" => "t3" } }
    ])
    artifact = compile_ir(ir)
    # OVER DUP ADD SWAP ADD OP_0 NUMEQUAL NIP -- byte-identical with TS.
    assert_equal "7876937c93009c77", artifact.script
  end

  def test_distinct_refs_unchanged
    # Frontend-shaped ANF (fresh temp per operand) must not shift bytes.
    ir = program_json(["x"], [
      { "name" => "t0", "value" => { "kind" => "load_param", "name" => "x" } },
      { "name" => "t1", "value" => { "kind" => "load_param", "name" => "x" } },
      { "name" => "t2", "value" => { "kind" => "bin_op", "op" => "+", "left" => "t0", "right" => "t1" } },
      { "name" => "t3", "value" => { "kind" => "load_prop", "name" => "target" } },
      { "name" => "t4", "value" => { "kind" => "bin_op", "op" => "===", "left" => "t2", "right" => "t3" } },
      { "name" => "t5", "value" => { "kind" => "assert", "value" => "t4" } }
    ])
    artifact = compile_ir(ir)
    # DUP SWAP ADD <placeholder OP_0> NUMEQUAL -- canonical frontend Dbl shape.
    assert_equal "767c93009c", artifact.script
  end
end
