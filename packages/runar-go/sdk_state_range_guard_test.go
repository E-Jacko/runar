package runar

import (
	"fmt"
	"math"
	"math/big"
	"strings"
	"testing"
)

// A bigint state value whose MAGNITUDE does not fit the fixed 8-byte
// little-endian sign-magnitude word must be REFUSED, not silently truncated.
//
// ---------------------------------------------------------------------------
// num2bin-le8 gives a bigint state field exactly 63 bits of magnitude (bytes
// 0..6 plus the low 7 bits of byte 7) and one sign bit (0x80 of byte 7).
// SerializeState wrote the low 8 bytes and dropped everything above, then
// OR-ed the sign bit in on top of whatever landed there. Measured in the TS
// reference before the guard:
//
//	value       bytes written       reads back as
//	2^63        0000000000000080    0    (negative zero)
//	2^63 + 5    0500000000000080    -5   (SIGN FLIP)
//	2^64        0000000000000000    0
//
// The Go tier corrupts EARLIER and more quietly still: toInt64 destroys the
// value before any encoder sees it — big.Int.Int64() sign-flips on overflow,
// and the strconv.ParseInt path returns 0 on ErrRange. So the guard has to
// live where the wide value is still intact.
//
// The deploy then succeeds and the UTXO is unspendable: the covenant rebuilds
// the continuation with the compiler's own OP_NUM2BIN 8, which cannot produce
// those bytes from that number, so hash256(outputs) never matches.
//
// Expected bytes below are derived BY HAND from the sign-magnitude rule, never
// read off the serializer.
// ---------------------------------------------------------------------------

func rangeGuardFields() []StateField {
	return []StateField{{Name: "count", Type: "bigint", Index: 0}}
}

// expectStatePanic runs SerializeState and asserts it panicked with a message
// containing every fragment in `want`.
func expectStatePanic(t *testing.T, what string, values map[string]interface{}, want ...string) {
	t.Helper()
	defer func() {
		r := recover()
		if r == nil {
			t.Fatalf("%s: SerializeState returned normally, expected a panic", what)
		}
		msg := fmt.Sprintf("%v", r)
		for _, frag := range want {
			if !strings.Contains(msg, frag) {
				t.Errorf("%s: panic message %q does not contain %q", what, msg, frag)
			}
		}
	}()
	_ = SerializeState(rangeGuardFields(), values)
}

func TestStateRangeGuard_RejectsTwoPow63_BigInt(t *testing.T) {
	two63 := new(big.Int).Lsh(big.NewInt(1), 63)
	expectStatePanic(t, "2^63 (*big.Int)",
		map[string]interface{}{"count": two63},
		"does not fit", "count", "9223372036854775808")
}

func TestStateRangeGuard_RejectsNegTwoPow63_BigInt(t *testing.T) {
	negTwo63 := new(big.Int).Neg(new(big.Int).Lsh(big.NewInt(1), 63))
	expectStatePanic(t, "-(2^63) (*big.Int)",
		map[string]interface{}{"count": negTwo63},
		"does not fit", "count", "-9223372036854775808")
}

func TestStateRangeGuard_RejectsTwoPow63Plus5_BigInt(t *testing.T) {
	// The sign-flip case: used to write 0500000000000080, which reads back
	// as -5 — a positive balance deserialising as a debt.
	v := new(big.Int).Add(new(big.Int).Lsh(big.NewInt(1), 63), big.NewInt(5))
	expectStatePanic(t, "2^63+5 (*big.Int)",
		map[string]interface{}{"count": v},
		"does not fit", "count", "9223372036854775813")
}

func TestStateRangeGuard_RejectsTwoPow64_BigInt(t *testing.T) {
	two64 := new(big.Int).Lsh(big.NewInt(1), 64)
	expectStatePanic(t, "2^64 (*big.Int)",
		map[string]interface{}{"count": two64},
		"does not fit", "count")
}

func TestStateRangeGuard_RejectsTwoPow70_BigInt(t *testing.T) {
	two70 := new(big.Int).Lsh(big.NewInt(1), 70)
	expectStatePanic(t, "2^70 (*big.Int)",
		map[string]interface{}{"count": two70},
		"does not fit", "count")
	expectStatePanic(t, "-(2^70) (*big.Int)",
		map[string]interface{}{"count": new(big.Int).Neg(two70)},
		"does not fit", "count")
}

func TestStateRangeGuard_RejectsMinInt64(t *testing.T) {
	// -2^63 IS representable as an int64 but its MAGNITUDE is 2^63, one past
	// the 63 magnitude bits. It used to encode as 0000000000000080 — negative
	// zero, which reads back as 0.
	expectStatePanic(t, "math.MinInt64 (int64)",
		map[string]interface{}{"count": int64(math.MinInt64)},
		"does not fit", "count", "-9223372036854775808")
}

func TestStateRangeGuard_RejectsOutOfRangeBigIntString(t *testing.T) {
	// strconv.ParseInt returns 0 + ErrRange here, so the value was already
	// destroyed before encodeNum2Bin ran.
	expectStatePanic(t, `"9223372036854775808n" (string)`,
		map[string]interface{}{"count": "9223372036854775808n"},
		"does not fit", "count", "9223372036854775808")
	expectStatePanic(t, `"-9223372036854775808n" (string)`,
		map[string]interface{}{"count": "-9223372036854775808n"},
		"does not fit", "count")
}

func TestStateRangeGuard_RejectsUint64AboveMaxInt64(t *testing.T) {
	// int64(uint64(1<<63)) wraps to math.MinInt64 — same negative-zero word.
	expectStatePanic(t, "uint64(1<<63)",
		map[string]interface{}{"count": uint64(1) << 63},
		"does not fit", "count")
}

func TestStateRangeGuard_RejectsOutOfRangeFixedArrayElement(t *testing.T) {
	fields := []StateField{{
		Name:  "Slots",
		Type:  "FixedArray<bigint, 2>",
		Index: 0,
		FixedArray: &ABIFixedArray{
			ElementType:    "bigint",
			Length:         2,
			SyntheticNames: []string{"Slots__0", "Slots__1"},
		},
	}}
	defer func() {
		r := recover()
		if r == nil {
			t.Fatal("fixed-array element 2^63: SerializeState returned normally, expected a panic")
		}
		if !strings.Contains(fmt.Sprintf("%v", r), "does not fit") {
			t.Errorf("unexpected panic: %v", r)
		}
	}()
	_ = SerializeState(fields, map[string]interface{}{
		"Slots": []interface{}{int64(1), new(big.Int).Lsh(big.NewInt(1), 63)},
	})
}

// ---------------------------------------------------------------------------
// Accepting controls — byte-exact, and they must stay byte-exact.
// ---------------------------------------------------------------------------

func TestStateRangeGuard_AcceptsBoundaryValues(t *testing.T) {
	maxMag := new(big.Int).Sub(new(big.Int).Lsh(big.NewInt(1), 63), big.NewInt(1))
	cases := []struct {
		name  string
		value interface{}
		want  string
	}{
		// magnitude bytes 0..6 all 0xff, byte 7 = 0x7f (seven magnitude bits
		// set, sign bit clear).
		{"2^63-1 (int64)", int64(math.MaxInt64), "ffffffffffffff7f"},
		{"2^63-1 (*big.Int)", maxMag, "ffffffffffffff7f"},
		{"2^63-1 (string)", "9223372036854775807n", "ffffffffffffff7f"},
		// same magnitude, sign bit set: 0x7f | 0x80 = 0xff.
		{"-(2^63-1) (int64)", int64(-math.MaxInt64), "ffffffffffffffff"},
		{"-(2^63-1) (*big.Int)", new(big.Int).Neg(maxMag), "ffffffffffffffff"},
		{"-(2^63-1) (string)", "-9223372036854775807n", "ffffffffffffffff"},
		{"0", int64(0), "0000000000000000"},
		{"1", int64(1), "0100000000000000"},
		{"-1", int64(-1), "0100000000000080"},
		{"127", int64(127), "7f00000000000000"},
		{"-127", int64(-127), "7f00000000000080"},
		{"128", int64(128), "8000000000000000"},
		{"-128", int64(-128), "8000000000000080"},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			got := SerializeState(rangeGuardFields(), map[string]interface{}{"count": tc.value})
			if got != tc.want {
				t.Errorf("expected %s, got %s", tc.want, got)
			}
		})
	}
}
