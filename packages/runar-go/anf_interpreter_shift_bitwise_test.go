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
