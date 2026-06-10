package compiler

import "testing"

// TestRepeatedOperandConsume_BinOpSameRefTwice ports the repeated-operand
// consume fix from the TS tier (packages/runar-compiler/src/__tests__/
// repeated-operand-consume.test.ts).
//
// A binding whose ANF value reads the SAME ref at more than one operand
// position (e.g. `t := x + x`) used to make an independent last-use consume
// decision per operand load. A consume-mode bringToTop of a ref already on
// top of the stack is a pure no-op, so a single stack slot ended up backing
// two operand positions and the bare OP_ADD underflowed at runtime (or,
// with the ref buried below other live slots, paired the wrong slot).
//
// Canonical rule (merged in TS, ported here): an operand load may consume
// (ROLL / move) its ref only when this binding is the ref's last use AND the
// ref occurs exactly once in the value's FULL operand list. Repeated refs
// copy (PICK / DUP) at every position; the original lingers and is cleaned
// by the existing method epilogue.
//
// Unreachable from the language frontend (pass 04 gives every operand a
// fresh temp); fully reachable via CompileFromIR / CLI --ir.
//
// Expected hex (byte-identical with the TS tier for the same ANF, fold-off,
// placeholder constructor slot): 767693009c77
// = OP_DUP OP_DUP OP_ADD OP_0 OP_NUMEQUAL OP_NIP
func TestRepeatedOperandConsume_BinOpSameRefTwice(t *testing.T) {
	irJSON := []byte(`{
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
}`)

	artifact, err := CompileFromIRBytes(irJSON, CompileOptions{DisableConstantFolding: true})
	if err != nil {
		t.Fatalf("CompileFromIRBytes failed: %v", err)
	}

	const want = "767693009c77" // DUP DUP ADD OP_0 NUMEQUAL NIP (TS-tier reference)
	if artifact.Script != want {
		t.Errorf("repeated-operand script mismatch:\n  got:  %s\n  want: %s\n  asm:  %s",
			artifact.Script, want, artifact.ASM)
	}
}

// TestRepeatedOperandConsume_CallSameRefTwice covers the builtin-call arg
// loop: `t := min(x, x)` must copy x at both argument positions.
func TestRepeatedOperandConsume_CallSameRefTwice(t *testing.T) {
	irJSON := []byte(`{
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
}`)

	artifact, err := CompileFromIRBytes(irJSON, CompileOptions{DisableConstantFolding: true})
	if err != nil {
		t.Fatalf("CompileFromIRBytes failed: %v", err)
	}

	// DUP DUP MIN OP_0 NUMEQUAL NIP — same shape as the bin_op case with
	// OP_MIN (0xa3) in place of OP_ADD.
	const want = "7676a3009c77"
	if artifact.Script != want {
		t.Errorf("repeated-operand min(x,x) script mismatch:\n  got:  %s\n  want: %s\n  asm:  %s",
			artifact.Script, want, artifact.ASM)
	}
}

// TestRepeatedOperandConsume_BuriedBelowLiveSlot covers the wrong-slot
// pairing variant: at `t0 := x + x` the stack is [x, y] (y live on top), so
// a naive "last occurrence may still consume" rule pairs x with y instead of
// duplicating x.
func TestRepeatedOperandConsume_BuriedBelowLiveSlot(t *testing.T) {
	irJSON := []byte(`{
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
}`)

	artifact, err := CompileFromIRBytes(irJSON, CompileOptions{DisableConstantFolding: true})
	if err != nil {
		t.Fatalf("CompileFromIRBytes failed: %v", err)
	}

	// x at depth 1 is copied at both positions (OVER, then DUP of the
	// fresh copy), added, y is moved up for the second add, compared
	// against the placeholder target, and the lingering x is nipped by
	// the epilogue.
	// OVER DUP ADD SWAP ADD OP_0 NUMEQUAL NIP (TS-tier reference)
	const want = "7876937c93009c77"
	if artifact.Script != want {
		t.Errorf("repeated-operand buried-slot script mismatch:\n  got:  %s\n  want: %s\n  asm:  %s",
			artifact.Script, want, artifact.ASM)
	}
}
