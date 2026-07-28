package codegen

import (
	"fmt"
	"strings"
	"testing"
)

// ---------------------------------------------------------------------------
// C17 — `OP_NOT OP_NOT` is boolean NORMALISATION, not numeric identity.
//
// For a non-canonical operand (say 5) the pair yields 1, while deleting it
// leaves 5. Truthiness is preserved, the VALUE is not — and a downstream
// OP_EQUAL / OP_NUMEQUAL / state serialisation consumes the value, so the
// optimised and unoptimised programs disagree on accept/reject.
//
// The unguarded 2-op `not-not-elim` rule is unsound in composition with the
// sibling `PUSH 0; OP_NUMEQUAL -> OP_NOT` rule, which synthesises a fresh
// OP_NOT sitting on an ARBITRARY script number. The stack lowerer emits
// `!==` as [OP_NUMEQUAL, OP_NOT] (see stack.go binaryOpMap), so
//
//	x !== 0n   ==>   <x> ; PUSH 0 ; OP_NUMEQUAL ; OP_NOT
//
// becomes `<x> ; OP_NOT ; OP_NOT`, which the unguarded rule then deleted
// entirely — `x !== 0n` compiled to `x`.
//
// The fix widens the rule to a 3-op window that includes the PRODUCER of the
// negated value and only fires when that producer provably leaves a canonical
// boolean (0 or 1) behind.
// ---------------------------------------------------------------------------

// c17Signature renders a stack-op list as a compact, comparable string.
func c17Signature(ops []StackOp) string {
	parts := make([]string, len(ops))
	for i, op := range ops {
		switch op.Op {
		case "opcode":
			parts[i] = op.Code
		case "push":
			switch op.Value.Kind {
			case "bigint":
				parts[i] = fmt.Sprintf("PUSH(%s)", op.Value.BigInt.String())
			case "bool":
				parts[i] = fmt.Sprintf("PUSH(%t)", op.Value.Bool)
			default:
				parts[i] = fmt.Sprintf("PUSH(%x)", op.Value.Bytes)
			}
		default:
			parts[i] = strings.ToUpper(op.Op)
		}
	}
	return strings.Join(parts, " ")
}

func c17Check(t *testing.T, name string, in []StackOp, want string) {
	t.Helper()
	got := c17Signature(OptimizeStackOps(in))
	if got != want {
		t.Errorf("%s:\n  input:    %s\n  got:      %s\n  expected: %s",
			name, c17Signature(in), got, want)
	}
}

func c17PushBool(b bool) StackOp {
	return StackOp{Op: "push", Value: PushValue{Kind: "bool", Bool: b}}
}

// The whole point of C17: when the producer of the negated value is NOT
// provably a canonical boolean, the OP_NOT pair must SURVIVE.
func TestC17_NotNotElim_NonCanonicalProducer_PairSurvives(t *testing.T) {
	// `x !== 0n` where x comes off the witness stack via a pick.
	c17Check(t, "pick-produced operand (x !== 0n)",
		[]StackOp{
			{Op: "pick", Depth: 3},
			pushBigIntOp(0),
			opcodeOp("OP_NUMEQUAL"),
			opcodeOp("OP_NOT"),
		},
		"PICK OP_NOT OP_NOT")

	// Mirrored composition: `(!b) === false` lowers to OP_NOT; PUSH 0; OP_NUMEQUAL.
	c17Check(t, "mirrored composition ((!b) === false)",
		[]StackOp{
			{Op: "pick", Depth: 2},
			opcodeOp("OP_NOT"),
			pushBigIntOp(0),
			opcodeOp("OP_NUMEQUAL"),
		},
		"PICK OP_NOT OP_NOT")

	// Arbitrary numeric producers.
	c17Check(t, "OP_ADD producer",
		[]StackOp{opcodeOp("OP_ADD"), opcodeOp("OP_NOT"), opcodeOp("OP_NOT")},
		"OP_ADD OP_NOT OP_NOT")
	c17Check(t, "OP_SIZE producer",
		[]StackOp{opcodeOp("OP_SIZE"), opcodeOp("OP_NOT"), opcodeOp("OP_NOT")},
		"OP_SIZE OP_NOT OP_NOT")
	c17Check(t, "non-canonical literal producer",
		[]StackOp{pushBigIntOp(5), opcodeOp("OP_NOT"), opcodeOp("OP_NOT")},
		"PUSH(5) OP_NOT OP_NOT")

	// Stack-shuffling ops are DELIBERATELY excluded from the canonical set:
	// they forward a value whose provenance this local window cannot see.
	c17Check(t, "dup producer (provenance invisible)",
		[]StackOp{{Op: "dup"}, opcodeOp("OP_NOT"), opcodeOp("OP_NOT")},
		"DUP OP_NOT OP_NOT")
	c17Check(t, "roll producer (provenance invisible)",
		[]StackOp{{Op: "roll", Depth: 4}, opcodeOp("OP_NOT"), opcodeOp("OP_NOT")},
		"ROLL OP_NOT OP_NOT")

	// A bare pair with no visible producer must also survive — the operand
	// could be anything at all.
	c17Check(t, "bare pair, no producer in window",
		[]StackOp{opcodeOp("OP_NOT"), opcodeOp("OP_NOT")},
		"OP_NOT OP_NOT")
}

// NEGATIVE case: the guard must not make the rule dead. A genuinely canonical
// producer still gets the redundant pair removed.
func TestC17_NotNotElim_CanonicalProducer_StillElided(t *testing.T) {
	canonical := []string{
		"OP_EQUAL",
		"OP_NUMEQUAL",
		"OP_NUMNOTEQUAL",
		"OP_LESSTHAN",
		"OP_GREATERTHAN",
		"OP_LESSTHANOREQUAL",
		"OP_GREATERTHANOREQUAL",
		"OP_BOOLAND",
		"OP_BOOLOR",
		"OP_WITHIN",
		"OP_0NOTEQUAL",
		"OP_CHECKSIG",
		"OP_CHECKMULTISIG",
	}
	for _, code := range canonical {
		c17Check(t, code+" producer",
			[]StackOp{opcodeOp(code), opcodeOp("OP_NOT"), opcodeOp("OP_NOT")},
			code)
	}

	// OP_NOT itself is canonical: NOT NOT NOT collapses to a single NOT.
	c17Check(t, "OP_NOT producer (triple negation)",
		[]StackOp{opcodeOp("OP_NOT"), opcodeOp("OP_NOT"), opcodeOp("OP_NOT")},
		"OP_NOT")

	// Literal canonical booleans.
	c17Check(t, "PUSH 0 producer",
		[]StackOp{pushBigIntOp(0), opcodeOp("OP_NOT"), opcodeOp("OP_NOT")},
		"PUSH(0)")
	c17Check(t, "PUSH 1 producer",
		[]StackOp{pushBigIntOp(1), opcodeOp("OP_NOT"), opcodeOp("OP_NOT")},
		"PUSH(1)")
	c17Check(t, "PUSH true producer",
		[]StackOp{c17PushBool(true), opcodeOp("OP_NOT"), opcodeOp("OP_NOT")},
		"PUSH(true)")
	c17Check(t, "PUSH false producer",
		[]StackOp{c17PushBool(false), opcodeOp("OP_NOT"), opcodeOp("OP_NOT")},
		"PUSH(false)")
}

// The raw_bytes peephole barrier must keep holding for the widened window.
func TestC17_NotNotElim_RawBytesBarrier(t *testing.T) {
	c17Check(t, "raw_bytes inside the window",
		[]StackOp{
			opcodeOp("OP_NUMEQUAL"),
			{Op: "raw_bytes", RawBytes: []byte{0x51}, InArity: 0, OutArity: 1},
			opcodeOp("OP_NOT"),
			opcodeOp("OP_NOT"),
		},
		"OP_NUMEQUAL RAW_BYTES OP_NOT OP_NOT")
}
