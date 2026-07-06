//! Stack lowering across unrolled for-loops — outer-scope refs (method
//! params, pre-loop consts) must survive loop unrolling. Port of the
//! TypeScript `loop-outer-refs.test.ts` (PR #113, fix 5).
//!
//!  (a) a const defined before a loop and referenced inside it (including
//!      only inside a nested if-branch) failed compilation with
//!      "value 'X' not found on stack" — the first iteration consumed it;
//!  (b) worse, a method PARAM referenced after an unrolled loop whose body
//!      also references it was silently lowered to an empty push (OP_0):
//!      compilation succeeded, the env-based interpreter passed, but the
//!      emitted Script failed at runtime (silent interpreter<->Script
//!      divergence).
//!
//! The fix: lower_loop collects outer refs deeply (nested branches included)
//! and protects them in non-final iterations, and in the final iteration
//! whenever the enclosing scope still references them after the loop. The
//! old silent OP_0 fallbacks are now hard errors.

use runar_compiler_rust::{
    compile_from_ir_str, compile_from_source_str_with_result, CompileOptions,
};

/// V003 repro: multi-input tx walk — param `data` used inside AND after the loop.
const LOOP_WALK_SOURCE: &str = r#"
import { SmartContract, assert, substr, cat, bin2num } from 'runar-lang';
import type { ByteString } from 'runar-lang';

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
"#;

/// Symptom (a): const defined before the loop, referenced inside it.
const CONST_BEFORE_LOOP_SOURCE: &str = r#"
import { SmartContract, assert, substr, cat, bin2num } from 'runar-lang';
import type { ByteString } from 'runar-lang';

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
"#;

#[test]
fn param_referenced_after_a_loop_is_not_lowered_to_an_empty_push() {
    let opts = CompileOptions::default();
    let result = compile_from_source_str_with_result(
        LOOP_WALK_SOURCE,
        Some("LoopWalk.runar.ts"),
        &opts,
    );
    assert!(
        result.success,
        "LoopWalk should compile; diagnostics: {:?}",
        result
            .diagnostics
            .iter()
            .map(|d| d.message.clone())
            .collect::<Vec<_>>()
    );

    // The post-loop code (after the last OP_ENDIF) reads `data` via
    // substr(data, off, 1n). With the bug, `data` was emitted as OP_0
    // right after the final OP_ENDIF; fixed code brings the real param up.
    let asm = result.script_asm.expect("compiled asm");
    let last_endif = asm.rfind("OP_ENDIF").expect("loop emits at least one OP_ENDIF");
    let post_loop = &asm[last_endif..];
    assert!(
        !post_loop.contains("OP_0"),
        "post-loop region must not contain a silent OP_0 placeholder; post-loop asm: {}",
        post_loop
    );
}

#[test]
fn const_defined_before_a_loop_and_referenced_inside_compiles() {
    let opts = CompileOptions::default();
    let result = compile_from_source_str_with_result(
        CONST_BEFORE_LOOP_SOURCE,
        Some("ConstLoop.runar.ts"),
        &opts,
    );
    // Previously: "value 'base' not found on stack (...)"
    assert!(
        result.success,
        "ConstLoop should compile; diagnostics: {:?}",
        result
            .diagnostics
            .iter()
            .map(|d| d.message.clone())
            .collect::<Vec<_>>()
    );
    assert!(result.script_hex.is_some(), "script hex should be present");
}

#[test]
fn a_load_param_that_cannot_be_satisfied_is_a_loud_error_not_op0() {
    // Hand-written ANF referencing a parameter the method does not have —
    // the old code silently emitted OP_0 here.
    let ir_json = r#"{
        "contractName": "Broken",
        "properties": [],
        "methods": [{
            "name": "run",
            "params": [{"name": "x", "type": "bigint"}],
            "body": [
                {"name": "t0", "value": {"kind": "load_param", "name": "ghost"}},
                {"name": "t1", "value": {"kind": "assert", "value": "t0"}}
            ],
            "isPublic": true
        }]
    }"#;

    // The hard error is raised inside stack lowering; lower_to_stack's
    // catch_unwind boundary converts it into a Result::Err (rather than
    // unwinding the whole process), so it surfaces here as an Err message.
    let err = compile_from_ir_str(ir_json).expect_err("unsatisfiable load_param must be rejected");
    assert!(
        err.contains("Refusing to emit a silent OP_0"),
        "error should be the loud stack-lowering diagnostic, got: {}",
        err
    );
}
