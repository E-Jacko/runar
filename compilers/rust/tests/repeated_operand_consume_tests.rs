//! Repeated-operand consume fix, ported from the TS tier
//! (packages/runar-compiler/src/__tests__/repeated-operand-consume.test.ts).
//!
//! A binding whose ANF value reads the SAME ref at more than one operand
//! position (e.g. `t := x + x`) used to make an independent last-use consume
//! decision per operand load. A consume-mode bring_to_top of a ref already on
//! top of the stack is a pure no-op, so a single stack slot ended up backing
//! two operand positions and the bare OP_ADD underflowed at runtime (or, with
//! the ref buried below other live slots, paired the wrong slot).
//!
//! Canonical rule (merged in TS, ported here): an operand load may consume
//! (ROLL / move) its ref only when this binding is the ref's last use AND the
//! ref occurs exactly once in the value's FULL operand list. Repeated refs
//! copy (PICK / DUP) at every position; the original lingers and is cleaned
//! by the existing method epilogue.
//!
//! Unreachable from the language frontend (ANF lowering gives every operand a
//! fresh temp); fully reachable via `compile_from_ir` / CLI `--ir`.
//!
//! Expected hex strings below are the TS-tier reference outputs for the same
//! ANF (fold-off, placeholder constructor slot) and must stay byte-identical
//! across all 7 tiers.

use runar_compiler_rust::{compile_from_ir_str_with_options, CompileOptions};

fn fold_off() -> CompileOptions {
    CompileOptions {
        disable_constant_folding: true,
        ..CompileOptions::default()
    }
}

#[test]
fn bin_op_same_ref_twice_copies_at_both_positions() {
    let ir_json = r#"{
  "contractName": "Repeat",
  "properties": [{ "name": "target", "type": "bigint", "readonly": true }],
  "methods": [
    {
      "name": "unlock",
      "params": [{ "name": "x", "type": "bigint" }],
      "body": [
        { "name": "t0", "value": { "kind": "bin_op", "op": "+", "left": "x", "right": "x" } },
        { "name": "t1", "value": { "kind": "load_prop", "name": "target" } },
        { "name": "t2", "value": { "kind": "bin_op", "op": "===", "left": "t0", "right": "t1" } },
        { "name": "t3", "value": { "kind": "assert", "value": "t2" } }
      ],
      "isPublic": true
    }
  ]
}"#;

    let artifact = compile_from_ir_str_with_options(ir_json, &fold_off())
        .expect("compile_from_ir_str failed");

    // DUP DUP ADD OP_0 NUMEQUAL NIP (TS-tier reference)
    assert_eq!(
        artifact.script, "767693009c77",
        "repeated-operand script mismatch, asm: {}",
        artifact.asm
    );
}

#[test]
fn call_same_ref_in_two_arg_positions() {
    let ir_json = r#"{
  "contractName": "Repeat",
  "properties": [{ "name": "target", "type": "bigint", "readonly": true }],
  "methods": [
    {
      "name": "unlock",
      "params": [{ "name": "x", "type": "bigint" }],
      "body": [
        { "name": "t0", "value": { "kind": "call", "func": "min", "args": ["x", "x"] } },
        { "name": "t1", "value": { "kind": "load_prop", "name": "target" } },
        { "name": "t2", "value": { "kind": "bin_op", "op": "===", "left": "t0", "right": "t1" } },
        { "name": "t3", "value": { "kind": "assert", "value": "t2" } }
      ],
      "isPublic": true
    }
  ]
}"#;

    let artifact = compile_from_ir_str_with_options(ir_json, &fold_off())
        .expect("compile_from_ir_str failed");

    // DUP DUP MIN OP_0 NUMEQUAL NIP (TS-tier reference)
    assert_eq!(
        artifact.script, "7676a3009c77",
        "repeated-operand min(x,x) script mismatch, asm: {}",
        artifact.asm
    );
}

#[test]
fn repeated_ref_buried_below_live_slot() {
    // At `t0 := x + x` the stack is [x, y] (y live on top): a naive "last
    // occurrence may still consume" rule pairs x with the wrong slot instead
    // of duplicating x.
    let ir_json = r#"{
  "contractName": "Repeat",
  "properties": [{ "name": "target", "type": "bigint", "readonly": true }],
  "methods": [
    {
      "name": "unlock",
      "params": [
        { "name": "x", "type": "bigint" },
        { "name": "y", "type": "bigint" }
      ],
      "body": [
        { "name": "t0", "value": { "kind": "bin_op", "op": "+", "left": "x", "right": "x" } },
        { "name": "t1", "value": { "kind": "bin_op", "op": "+", "left": "t0", "right": "y" } },
        { "name": "t2", "value": { "kind": "load_prop", "name": "target" } },
        { "name": "t3", "value": { "kind": "bin_op", "op": "===", "left": "t1", "right": "t2" } },
        { "name": "t4", "value": { "kind": "assert", "value": "t3" } }
      ],
      "isPublic": true
    }
  ]
}"#;

    let artifact = compile_from_ir_str_with_options(ir_json, &fold_off())
        .expect("compile_from_ir_str failed");

    // OVER DUP ADD SWAP ADD OP_0 NUMEQUAL NIP (TS-tier reference)
    assert_eq!(
        artifact.script, "7876937c93009c77",
        "repeated-operand buried-slot script mismatch, asm: {}",
        artifact.asm
    );
}
