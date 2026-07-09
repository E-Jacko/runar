package runar

import (
	"strings"
	"testing"
)

// Issue #106 — EmptySig marker for OR-CHECKSIG branched auth (Go tier).
//
// The deliberately-failing branch of an OR-CHECKSIG method must push an empty
// signature (OP_0) or BIP146 NULLFAIL rejects the spend. EmptySig is the
// producer-side sentinel: encodeArg emits OP_0 for it, and the auto-sign
// collectors never sign it (it is not nil). Wire-byte parity with the TS SDK
// (contract.ts encodeArg emits "00").

func TestEmptySig_EncodeArgEmitsOP0(t *testing.T) {
	if got := encodeArg(EmptySig); got != "00" {
		t.Fatalf("encodeArg(EmptySig) = %q, want \"00\"", got)
	}
}

func TestEmptySig_IsEmptySigGuard(t *testing.T) {
	if !IsEmptySig(EmptySig) {
		t.Fatal("IsEmptySig(EmptySig) should be true")
	}
	if IsEmptySig(nil) {
		t.Fatal("IsEmptySig(nil) should be false — nil means auto-sign, not empty")
	}
	if IsEmptySig(strings.Repeat("aa", 72)) {
		t.Fatal("IsEmptySig on a hex string should be false")
	}
	// Not nil — so the auto-sign collector (args[i] == nil) skips it.
	if EmptySig == nil {
		t.Fatal("EmptySig must not be nil, or the auto-sign collector would treat it as auto-sign")
	}
}

// OR-CHECKSIG [realSigA, EmptySig] — the failing branch encodes OP_0 while the
// matching branch keeps its real signature push. Mirrors the TS wire output.
func TestEmptySig_OrChecksigWireBytes(t *testing.T) {
	artifact := makeArtifact("51", ABI{
		Constructor: ABIConstructor{Params: nil},
		Methods: []ABIMethod{
			{
				Name: "execute",
				Params: []ABIParam{
					{Name: "sigA", Type: "Sig"},
					{Name: "sigB", Type: "Sig"},
				},
				IsPublic: true,
			},
		},
	})
	c := NewRunarContract(artifact, nil)

	sigA := strings.Repeat("aa", 72)
	script := c.BuildUnlockingScript("execute", []interface{}{sigA, EmptySig})

	// 72 bytes = 0x48 direct push of sigA, then OP_0 (00) for the EmptySig slot.
	expected := "48" + sigA + "00"
	if script != expected {
		t.Fatalf("OR-CHECKSIG wire mismatch:\n got %s\nwant %s", script, expected)
	}
}
