# frozen_string_literal: true

require_relative "test_helper"

# Pull in frontend + codegen modules.
require "runar_compiler/frontend/ast_nodes"
require "runar_compiler/frontend/diagnostic"
require "runar_compiler/frontend/validator"
require "runar_compiler/frontend/typecheck"
require "runar_compiler/frontend/anf_lower"
require "runar_compiler/frontend/parser_ts"
require "runar_compiler/codegen/stack"

# Stack lowering across unrolled for-loops -- outer-scope refs (method params,
# pre-loop consts) must survive loop unrolling:
#
#  (a) a const defined before a loop and referenced inside it (including only
#      inside a nested if-branch) failed compilation with "Value 'X' not found
#      on stack" -- the first iteration consumed it;
#  (b) worse, a method PARAM referenced after an unrolled loop whose body also
#      references it was silently lowered to an empty push (OP_0): compilation
#      succeeded, the env-based interpreter passed, but the emitted Script
#      failed at runtime (silent interpreter<->Script divergence).
#
# The fix: _lower_loop collects outer refs deeply (nested branches included)
# and protects them in non-final iterations, and in the final iteration
# whenever the enclosing scope still references them after the loop. The old
# silent OP_0 fallbacks are now hard errors.
class TestLoopOuterRefs < Minitest::Test
  # V003 repro: multi-input tx walk -- param `data` used inside AND after the loop.
  LOOP_WALK_SOURCE = <<~TS
    class LoopWalk extends SmartContract {
      readonly pad00: ByteString = "00" as ByteString;

      constructor() {
        super();
      }

      public walk(data: ByteString) {
        let off = 5n;
        for (let i = 0n; i < 3n; i++) {
          if (i < bin2num(cat(substr(data, 4n, 1n), this.pad00))) {
            const sl = bin2num(cat(substr(data, off + 36n, 1n), this.pad00));
            assert(sl < 253n);
            off = off + 36n + 1n + sl + 4n;
          }
        }
        const tail = bin2num(cat(substr(data, off, 1n), this.pad00));
        assert(tail === 7n);
      }
    }
  TS

  # Symptom (a): const defined before the loop, referenced inside it.
  CONST_BEFORE_LOOP_SOURCE = <<~TS
    class ConstLoop extends SmartContract {
      readonly pad00: ByteString = "00" as ByteString;

      constructor() {
        super();
      }

      public probe(data: ByteString) {
        const base = 5n;
        let acc = 0n;
        for (let i = 0n; i < 3n; i++) {
          const b = bin2num(cat(substr(data, base + i, 1n), this.pad00));
          acc = acc + b;
        }
        assert(acc === 6n);
      }
    }
  TS

  def compile_source(source, file_name = "Test.runar.ts")
    parse_result = RunarCompiler.send(:_parse_source, source, file_name)
    assert_empty parse_result.errors.map(&:format_message), "unexpected parse errors"
    refute_nil parse_result.contract

    program = RunarCompiler::Frontend.lower_to_anf(parse_result.contract)
    RunarCompiler.compile_from_program(program, disable_constant_folding: true)
  end

  def test_param_referenced_after_loop_is_not_lowered_to_empty_push
    artifact = compile_source(LOOP_WALK_SOURCE, "LoopWalk.runar.ts")
    refute_nil artifact.script
    refute_empty artifact.script

    # The post-loop code (after the last OP_ENDIF) reads `data` via
    # substr(data, off, 1n). With the bug, `data` was emitted as OP_0 right
    # after the final OP_ENDIF; fixed code brings the real param up.
    asm = artifact.asm
    idx = asm.rindex("OP_ENDIF")
    refute_nil idx, "expected an OP_ENDIF in the loop-walk script"
    post_loop = asm[idx..]
    refute_includes post_loop.split(/\s+/), "OP_0",
                     "post-loop region silently lowered a live param to OP_0"
  end

  def test_const_defined_before_a_loop_and_referenced_inside_compiles
    # Previously: "Value 'base' not found on stack (...)".
    artifact = compile_source(CONST_BEFORE_LOOP_SOURCE, "ConstLoop.runar.ts")
    refute_nil artifact.script
    refute_empty artifact.script
  end

  def test_load_param_that_cannot_be_satisfied_is_a_loud_error_not_op0
    # Hand-written ANF referencing a parameter the method does not have --
    # the old code silently emitted OP_0 here.
    program = {
      "contractName" => "Broken",
      "properties" => [],
      "methods" => [
        {
          "name" => "run",
          "isPublic" => true,
          "params" => [{ "name" => "x", "type" => "bigint" }],
          "body" => [
            { "name" => "t0", "value" => { "kind" => "load_param", "name" => "ghost" } },
            { "name" => "t1", "value" => { "kind" => "assert", "valueRef" => "t0" } }
          ]
        }
      ]
    }

    err = assert_raises(RuntimeError) do
      RunarCompiler.compile_from_ir_bytes(JSON.dump(program))
    end
    assert_match(/Refusing to emit a silent OP_0/, err.message)
  end
end
