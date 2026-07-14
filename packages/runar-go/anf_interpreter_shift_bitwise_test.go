package runar

// ---------------------------------------------------------------------------
// anf_interpreter_shift_bitwise_test.go
//
// Pins the ANF interpreter's `& | ^ ~ << >>` evaluation to Bitcoin Script's
// byte-array script-number semantics: OP_AND/OP_OR/OP_XOR/OP_INVERT/
// OP_LSHIFT/OP_RSHIFT operate on the operands' minimal script-number BYTES,
// not their bigint value. Truth table mirrors the TS reference
// (packages/runar-testing/src/__tests__/script-number-bitwise.test.ts and
// vm/utils.ts scriptNumberBitwise / scriptNumberInvert / scriptNumberShift).
// ---------------------------------------------------------------------------

import (
	"math/big"
	"strings"
	"testing"
)

func bi(n int64) *big.Int { return big.NewInt(n) }

func TestAnfEvalBinOp_ShiftBitwise_TruthTable(t *testing.T) {
	cases := []struct {
		name string
		op   string
		l, r int64
		want int64
	}{
		{"255<<1==254 not 510", "<<", 255, 1, 254},
		{"256<<1==512", "<<", 256, 1, 512},
		{"5<<3==40", "<<", 5, 3, 40},
		{"32>>3==4", ">>", 32, 3, 4},
		{"255>>1==-127 not 127", ">>", 255, 1, -127},
		{"5&3==1", "&", 5, 3, 1},
		{"-1&5==1 not 5", "&", -1, 5, 1},
	}

	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			got := anfEvalBinOp(c.op, bi(c.l), bi(c.r), "")
			gotBig, ok := got.(*big.Int)
			if !ok {
				t.Fatalf("expected *big.Int result, got %T (%v)", got, got)
			}
			if gotBig.Cmp(bi(c.want)) != 0 {
				t.Errorf("%d %s %d = %s, want %d", c.l, c.op, c.r, gotBig, c.want)
			}
		})
	}
}

func TestAnfEvalUnaryOp_Invert_TruthTable(t *testing.T) {
	cases := []struct {
		name string
		val  int64
		want int64
	}{
		{"~5==-122 not -6", 5, -122},
		{"~255==-32512", 255, -32512},
		{"~0==0", 0, 0},
	}

	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			got := anfEvalUnaryOp("~", bi(c.val), "")
			gotBig, ok := got.(*big.Int)
			if !ok {
				t.Fatalf("expected *big.Int result, got %T (%v)", got, got)
			}
			if gotBig.Cmp(bi(c.want)) != 0 {
				t.Errorf("~%d = %s, want %d", c.val, gotBig, c.want)
			}
		})
	}
}

func TestAnfEvalBinOp_ShiftBitwise_Aborts(t *testing.T) {
	cases := []struct {
		name string
		op   string
		l, r int64
	}{
		{"255&1 -> ABORT (len mismatch)", "&", 255, 1},
		{"7|0 -> ABORT (len mismatch)", "|", 7, 0},
		{"5<<(-1) -> ABORT (negative shift)", "<<", 5, -1},
	}

	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			defer func() {
				r := recover()
				if r == nil {
					t.Fatalf("expected panic (ABORT), got none")
				}
				if _, ok := r.(*ScriptOpcodeError); !ok {
					t.Fatalf("expected *ScriptOpcodeError, got %T (%v)", r, r)
				}
			}()
			anfEvalBinOp(c.op, bi(c.l), bi(c.r), "")
		})
	}
}

// TestExecuteStrict_ShiftBitwise_AbortSurfacesAsError confirms the panic
// unwinds through runMethod's recover and surfaces as a plain Go error from
// the public entry points (ExecuteStrict / ComputeNewState), not a raw
// runtime panic — mirroring the TS reference where scriptNumberBitwise /
// scriptNumberShift throw a catchable Error rather than crashing the
// process.
func TestExecuteStrict_ShiftBitwise_AbortSurfacesAsError(t *testing.T) {
	anf := &ANFProgram{
		ContractName: "ShiftAbort",
		Properties:   []ANFProperty{},
		Methods: []ANFMethod{
			{
				Name:     "run",
				IsPublic: true,
				Params:   []ANFParam{},
				Body: []ANFBinding{
					{
						Name: "t0",
						Value: map[string]interface{}{
							"kind":  "load_const",
							"value": "255",
						},
					},
					{
						Name: "t1",
						Value: map[string]interface{}{
							"kind":  "load_const",
							"value": "1",
						},
					},
					{
						Name: "t2",
						Value: map[string]interface{}{
							"kind":        "bin_op",
							"op":          "&",
							"left":        "t0",
							"right":       "t1",
							"result_type": "bigint",
						},
					},
				},
			},
		},
	}

	_, _, _, err := ExecuteStrict(anf, "run", map[string]interface{}{}, map[string]interface{}{}, nil)
	if err == nil {
		t.Fatalf("expected an error from ExecuteStrict on OP_AND length mismatch, got nil")
	}
	if _, ok := err.(*ScriptOpcodeError); !ok {
		t.Fatalf("expected *ScriptOpcodeError, got %T (%v)", err, err)
	}
}

// ---------------------------------------------------------------------------
// CHAINED byte-op semantics (issue: shift/bitwise results are fixed-length,
// possibly NON-minimal byte arrays on-chain; a chained length-sensitive op
// must see that real length, not the re-minimised numeric value).
//
// A single op on minimal operands was already correct (truth-table tests
// above). These pin the interpreter's per-binding side-map threading so a
// shift/bitwise RESULT feeding another `& | ^ << >> ~` matches the deployed
// script. Mirrors the TS reference (packages/runar-sdk/src/anf-interpreter.ts
// `scriptBytes` side map + packages/runar-testing/src/vm/utils.ts
// scriptNumber*Bytes helpers).
// ---------------------------------------------------------------------------

// sbConst builds a load_const binding whose value is the decimal string `val`.
func sbConst(name, val string) ANFBinding {
	return ANFBinding{Name: name, Value: map[string]interface{}{"kind": "load_const", "value": val}}
}

// sbBin builds a numeric bin_op binding (result_type "bigint").
func sbBin(name, op, left, right string) ANFBinding {
	return ANFBinding{Name: name, Value: map[string]interface{}{
		"kind": "bin_op", "op": op, "left": left, "right": right, "result_type": "bigint",
	}}
}

// sbUn builds a numeric unary_op binding (result_type "bigint").
func sbUn(name, op, operand string) ANFBinding {
	return ANFBinding{Name: name, Value: map[string]interface{}{
		"kind": "unary_op", "op": op, "operand": operand, "result_type": "bigint",
	}}
}

// sbUpd builds an update_prop binding writing binding `val` to property `prop`.
func sbUpd(name, prop, val string) ANFBinding {
	return ANFBinding{Name: name, Value: map[string]interface{}{
		"kind": "update_prop", "name": prop, "value": val,
	}}
}

// sbProgram wraps a method body around a single mutable property "out".
func sbProgram(body []ANFBinding) *ANFProgram {
	return &ANFProgram{
		ContractName: "Chained",
		Properties:   []ANFProperty{{Name: "out", Type: "bigint", Readonly: false}},
		Methods: []ANFMethod{{
			Name: "run", IsPublic: true, Params: []ANFParam{}, Body: body,
		}},
	}
}

// TestAnfInterpreter_ChainedByteOps_Values pins the value results of chained
// shift/bitwise expressions where an intermediate is a non-minimal byte array.
func TestAnfInterpreter_ChainedByteOps_Values(t *testing.T) {
	cases := []struct {
		name string
		body []ANFBinding
		want int64
	}{
		{
			// (2<<8)|5: 2<<8 leaves the 1-byte [0x00]; OP_OR([0x00],[0x05])=
			// [0x05] => 5. A re-minimising interpreter would OR empty|[0x05]
			// and abort on the length mismatch.
			name: "(2<<8)|5 == 5",
			body: []ANFBinding{
				sbConst("t0", "2"),
				sbConst("t1", "8"),
				sbBin("t2", "<<", "t0", "t1"),
				sbConst("t3", "5"),
				sbBin("t4", "|", "t2", "t3"),
				sbUpd("t5", "out", "t4"),
			},
			want: 5,
		},
		{
			// ~(2<<8): invert the 1-byte [0x00] -> [0xff] => -127 decoded.
			name: "~(2<<8) == -127",
			body: []ANFBinding{
				sbConst("t0", "2"),
				sbConst("t1", "8"),
				sbBin("t2", "<<", "t0", "t1"),
				sbUn("t3", "~", "t2"),
				sbUpd("t4", "out", "t3"),
			},
			want: -127,
		},
		{
			// (256<<8)&256: 256<<8 within 2 bytes = [0x01,0x00] (=1); AND with
			// encode(256)=[0x00,0x01] => [0x00,0x00] => 0. Both 2 bytes, so no
			// abort — but the numeric values (1 & 256) would give 0 too here;
			// the point is the byte path agrees and does NOT abort.
			name: "(256<<8)&256 == 0",
			body: []ANFBinding{
				sbConst("t0", "256"),
				sbConst("t1", "8"),
				sbBin("t2", "<<", "t0", "t1"),
				sbConst("t3", "256"),
				sbBin("t4", "&", "t2", "t3"),
				sbUpd("t5", "out", "t4"),
			},
			want: 0,
		},
	}

	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			state, err := ComputeNewState(
				sbProgram(c.body), "run",
				map[string]interface{}{"out": big.NewInt(0)},
				map[string]interface{}{}, nil,
			)
			if err != nil {
				t.Fatalf("unexpected error: %v", err)
			}
			got, ok := state["out"].(*big.Int)
			if !ok {
				t.Fatalf("expected *big.Int state[out], got %T (%v)", state["out"], state["out"])
			}
			if got.Cmp(bi(c.want)) != 0 {
				t.Errorf("%s = %s, want %d", c.name, got, c.want)
			}
		})
	}
}

// TestAnfInterpreter_ChainedByteOps_Abort pins the funds-loss case: on-chain
// `(1<<8)&0` is OP_AND([0x00], []) — a length mismatch that ABORTS. A buggy
// interpreter that re-minimises the shift result to 0 would compute `0 & 0 =
// 0` and report the spend as valid off-chain while the chain rejects it.
func TestAnfInterpreter_ChainedByteOps_Abort(t *testing.T) {
	body := []ANFBinding{
		sbConst("t0", "1"),
		sbConst("t1", "8"),
		sbBin("t2", "<<", "t0", "t1"),
		sbConst("t3", "0"),
		sbBin("t4", "&", "t2", "t3"),
		sbUpd("t5", "out", "t4"),
	}
	_, err := ComputeNewState(
		sbProgram(body), "run",
		map[string]interface{}{"out": big.NewInt(0)},
		map[string]interface{}{}, nil,
	)
	if err == nil {
		t.Fatalf("expected an ABORT error for (1<<8)&0 length mismatch, got nil")
	}
	se, ok := err.(*ScriptOpcodeError)
	if !ok {
		t.Fatalf("expected *ScriptOpcodeError, got %T (%v)", err, err)
	}
	if se.Opcode != "OP_AND" || !strings.Contains(se.Message, "same length") {
		t.Errorf("expected OP_AND same-length abort, got %q: %q", se.Opcode, se.Message)
	}
}
