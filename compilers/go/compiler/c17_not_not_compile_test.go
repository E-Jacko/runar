package compiler

import (
	"strings"
	"testing"
)

// C17 — end-to-end: `x !== 0n` must not be optimised down to `x`.
//
// The stack lowerer emits `!==` as [OP_NUMEQUAL, OP_NOT], so the method body
// lowers to `<x> ; PUSH 0 ; OP_NUMEQUAL ; OP_NOT`. The peephole rewrites
// `PUSH 0; OP_NUMEQUAL` into a fresh OP_NOT, and — before the C17 guard — the
// unguarded `OP_NOT OP_NOT -> []` rule then deleted the comparison outright,
// leaving the raw operand on the stack. Truthiness survived, the VALUE did
// not: for x = 5 the correct program leaves 1, the optimised one left 5, so
// `(x !== 0n) === true` flipped from accept to reject.
//
// 0x91 is OP_NOT; the surviving pair is the byte sequence 9191.
const c17NotCompositionSource = `
import { SmartContract, assert } from 'runar-lang';

export class NotComposition extends SmartContract {
  constructor() { super(); }
  public unlock(x: bigint): void {
    const nonZero: boolean = x !== 0n;
    assert(nonZero === true);
  }
}
`

func TestC17_NotEqualZero_KeepsNotPair(t *testing.T) {
	res := CompileFromSourceStrWithResult(
		c17NotCompositionSource,
		"NotComposition.runar.ts",
		CompileOptions{DisableConstantFolding: true},
	)
	if !res.Success {
		t.Fatalf("compilation failed: %v", res.Diagnostics)
	}
	if !strings.Contains(res.ScriptHex, "9191") {
		t.Errorf("`x !== 0n` lost its OP_NOT OP_NOT pair — the comparison was "+
			"optimised away and the raw operand survives instead.\n  hex: %s\n  asm: %s",
			res.ScriptHex, res.ScriptAsm)
	}
	t.Logf("`(x !== 0n) === true` locking script: hex=%s asm=%s", res.ScriptHex, res.ScriptAsm)
}
