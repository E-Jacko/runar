package runar

// ---------------------------------------------------------------------------
// anf_interpreter_nonminimal_unary_test.go
//
// The binary-op minimal-encoding gate (anf_interpreter_shift_bitwise_test.go)
// only sees a non-minimal value that reaches a BINARY numeric consumer. A
// shift result can also be consumed by a UNARY op or by a numeric BUILTIN
// without ever passing through one:
//
//	abs(n >> 1) === 0     // OP_ABS reads the operand as a script number
//	bool(n >> 1) === false // OP_0NOTEQUAL likewise
//	!(n >> 1)             // OP_NOT likewise
//	-(n >> 1)             // OP_NEGATE likewise
//
// All of those opcodes decode with fRequireMinimal=true and ABORT on the
// 1-byte [0x00] that `1 >> 1` leaves. Reading only the decoded value
// re-minimises it, reports a clean spend, and locks the UTXO.
//
// Mirrors the TS reference widening in
// packages/runar-testing/src/interpreter/interpreter.ts, which gates the two
// funnels (`toBigInt` / `toBool`) every numeric builtin and unary op reads its
// operand through.
// ---------------------------------------------------------------------------

import (
	"math/big"
	"strings"
	"testing"
)

// sbCall builds a builtin-call binding over the named argument bindings.
func sbCall(name, fn string, args ...string) ANFBinding {
	iargs := make([]interface{}, len(args))
	for i, a := range args {
		iargs[i] = a
	}
	return ANFBinding{Name: name, Value: map[string]interface{}{
		"kind": "call", "func": fn, "args": iargs,
	}}
}

// TestAnfInterpreter_NonMinimalUnaryAndBuiltinOperand_Aborts pins that a
// non-minimally-encoded shift result ABORTS when a UNARY op or a numeric
// BUILTIN consumes it, exactly as the deployed script does.
func TestAnfInterpreter_NonMinimalUnaryAndBuiltinOperand_Aborts(t *testing.T) {
	// Shared prefix: t2 = 1 >> 1 -> raw stack bytes [0x00] (non-minimal zero).
	prefix := []ANFBinding{
		sbConst("t0", "1"),
		sbConst("t1", "1"),
		sbBin("t2", ">>", "t0", "t1"),
		sbConst("t3", "0"),
		sbConst("t4", "1"),
	}

	cases := []struct {
		name string
		tail []ANFBinding
	}{
		{"abs(1>>1) -> ABORT (OP_ABS)", []ANFBinding{sbCall("t5", "abs", "t2")}},
		{"bool(1>>1) -> ABORT (OP_0NOTEQUAL)", []ANFBinding{sbCall("t5", "bool", "t2")}},
		{"sign(1>>1) -> ABORT", []ANFBinding{sbCall("t5", "sign", "t2")}},
		{"min(1>>1,1) -> ABORT (OP_MIN)", []ANFBinding{sbCall("t5", "min", "t2", "t4")}},
		{"min(1,1>>1) -> ABORT (second arg too)", []ANFBinding{sbCall("t5", "min", "t4", "t2")}},
		{"max(1>>1,1) -> ABORT (OP_MAX)", []ANFBinding{sbCall("t5", "max", "t2", "t4")}},
		{"within(1>>1,0,1) -> ABORT (OP_WITHIN)", []ANFBinding{sbCall("t5", "within", "t2", "t3", "t4")}},
		{"safediv(1>>1,1) -> ABORT", []ANFBinding{sbCall("t5", "safediv", "t2", "t4")}},
		{"clamp(1>>1,0,1) -> ABORT", []ANFBinding{sbCall("t5", "clamp", "t2", "t3", "t4")}},
		{"-(1>>1) -> ABORT (OP_NEGATE)", []ANFBinding{sbUn("t5", "-", "t2")}},
		{"!(1>>1) -> ABORT (OP_NOT)", []ANFBinding{sbUn("t5", "!", "t2")}},
	}

	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			body := append(append([]ANFBinding{}, prefix...), c.tail...)
			body = append(body, sbUpd("t6", "out", "t3"))
			_, err := ComputeNewState(
				sbProgram(body), "run",
				map[string]interface{}{"out": big.NewInt(0)},
				map[string]interface{}{}, nil,
			)
			if err == nil {
				t.Fatalf("expected a non-minimal-operand ABORT, got nil (spend wrongly reported valid)")
			}
			se, ok := err.(*ScriptOpcodeError)
			if !ok {
				t.Fatalf("expected *ScriptOpcodeError, got %T (%v)", err, err)
			}
			if !strings.Contains(se.Message, "non-minimally encoded") {
				t.Errorf("expected a non-minimal-encoding message, got %q", se.Message)
			}
		})
	}
}

// TestExecuteStrict_NonMinimalBuiltinOperand_GuardDoesNotSilentlyPass is the
// funds-locking scenario end to end: `assert(abs(n >> 1) === 0)` with n = 1.
// The deployed script aborts at OP_ABS, so strict mode must report a failure
// rather than a clean spend.
func TestExecuteStrict_NonMinimalBuiltinOperand_GuardDoesNotSilentlyPass(t *testing.T) {
	body := []ANFBinding{
		sbConst("t0", "1"),
		sbConst("t1", "1"),
		sbBin("t2", ">>", "t0", "t1"),
		sbCall("t3", "abs", "t2"),
		sbConst("t4", "0"),
		sbBin("t5", "===", "t3", "t4"),
		sbAssert("t6", "t5"),
		sbUpd("t7", "out", "t4"),
	}
	_, _, _, err := ExecuteStrict(
		sbProgram(body), "run",
		map[string]interface{}{"out": big.NewInt(0)},
		map[string]interface{}{}, nil,
	)
	if err == nil {
		t.Fatalf("assert(abs(1>>1)===0) was accepted off-chain; the deployed script aborts at OP_ABS (funds locked)")
	}
	if !strings.Contains(err.Error(), "non-minimally encoded") {
		t.Fatalf("expected a non-minimal-encoding abort, got %v", err)
	}
}

// TestAnfInterpreter_UnaryBuiltinControls_StayAccepted pins the spends that
// MUST keep working. Widening the gate to the unary/builtin funnels must not
// reject a minimal operand, and must not touch the byte-array ops at all.
func TestAnfInterpreter_UnaryBuiltinControls_StayAccepted(t *testing.T) {
	t.Run("abs(2>>1)==1 — minimal operand through a builtin", func(t *testing.T) {
		body := []ANFBinding{
			sbConst("t0", "2"),
			sbConst("t1", "1"),
			sbBin("t2", ">>", "t0", "t1"), // raw [0x01] — minimal
			sbCall("t3", "abs", "t2"),
			sbUpd("t4", "out", "t3"),
		}
		state, err := ComputeNewState(
			sbProgram(body), "run",
			map[string]interface{}{"out": big.NewInt(0)},
			map[string]interface{}{}, nil,
		)
		if err != nil {
			t.Fatalf("control regressed — expected a clean spend, got %v", err)
		}
		if got := anfToBigInt(state["out"]); got.Cmp(bi(1)) != 0 {
			t.Errorf("out = %s, want 1", got)
		}
	})

	t.Run("2>>1===1 — minimal shift result", func(t *testing.T) {
		body := []ANFBinding{
			sbConst("t0", "2"),
			sbConst("t1", "1"),
			sbBin("t2", ">>", "t0", "t1"),
			sbBin("t3", "===", "t2", "t1"),
			sbAssert("t4", "t3"),
			sbUpd("t5", "out", "t1"),
		}
		if _, _, _, err := ExecuteStrict(
			sbProgram(body), "run",
			map[string]interface{}{"out": big.NewInt(0)},
			map[string]interface{}{}, nil,
		); err != nil {
			t.Fatalf("control regressed — expected a clean spend, got %v", err)
		}
	})

	t.Run("~(2<<8)===-127 — OP_INVERT is a byte op, never gated", func(t *testing.T) {
		body := []ANFBinding{
			sbConst("t0", "2"),
			sbConst("t1", "8"),
			sbBin("t2", "<<", "t0", "t1"), // raw [0x00] — NON-minimal
			sbUn("t3", "~", "t2"),         // OP_INVERT on [0x00] -> [0xff] = -127
			sbConst("t4", "-127"),
			sbBin("t5", "===", "t3", "t4"),
			sbAssert("t6", "t5"),
			sbUpd("t7", "out", "t4"),
		}
		if _, _, _, err := ExecuteStrict(
			sbProgram(body), "run",
			map[string]interface{}{"out": big.NewInt(0)},
			map[string]interface{}{}, nil,
		); err != nil {
			t.Fatalf("control regressed — OP_INVERT must accept non-minimal bytes, got %v", err)
		}
	})

	t.Run("(2<<8)|5===5 — OP_OR takes non-minimal bytes", func(t *testing.T) {
		body := []ANFBinding{
			sbConst("t0", "2"),
			sbConst("t1", "8"),
			sbBin("t2", "<<", "t0", "t1"), // raw [0x00] — NON-minimal
			sbConst("t3", "5"),
			sbBin("t4", "|", "t2", "t3"),
			sbBin("t5", "===", "t4", "t3"),
			sbAssert("t6", "t5"),
			sbUpd("t7", "out", "t3"),
		}
		if _, _, _, err := ExecuteStrict(
			sbProgram(body), "run",
			map[string]interface{}{"out": big.NewInt(0)},
			map[string]interface{}{}, nil,
		); err != nil {
			t.Fatalf("control regressed — expected a clean spend, got %v", err)
		}
	})

	t.Run("(2<<8)|5===5 through a named-local alias", func(t *testing.T) {
		body := []ANFBinding{
			sbConst("t0", "2"),
			sbConst("t1", "8"),
			sbBin("t2", "<<", "t0", "t1"),
			sbAlias("s", "t2"),
			sbConst("t3", "5"),
			sbBin("t4", "|", "s", "t3"),
			sbBin("t5", "===", "t4", "t3"),
			sbAssert("t6", "t5"),
			sbUpd("t7", "out", "t3"),
		}
		if _, _, _, err := ExecuteStrict(
			sbProgram(body), "run",
			map[string]interface{}{"out": big.NewInt(0)},
			map[string]interface{}{}, nil,
		); err != nil {
			t.Fatalf("control regressed — expected a clean spend, got %v", err)
		}
	})
}
