package runar

import (
	"encoding/hex"
	"testing"
)

// Issue #123 — the SDK threads a method's declared @sighash mode through
// ComputeOpPushTx / preimage construction. The go-sdk's CalcInputPreimage does
// the BIP-143 field zeroing (hashPrevouts under ANYONECANPAY, hashSequence
// unless pure ALL, hashOutputs under NONE / same-index SINGLE) natively once the
// correct flag is passed.

// sighashTypeFromPreimage returns the trailing sighashType byte of a BIP-143
// preimage (the low byte of the final LE uint32 field).
func sighashTypeFromPreimage(preimage []byte) byte {
	// ...nLocktime(4) || sighashType(4). The declared flag is the first byte of
	// the sighashType uint32 (LE).
	return preimage[len(preimage)-4]
}

func TestSDKSighash_ComputeUnderDeclaredMode(t *testing.T) {
	f := loadBip143Fixture(t)
	s := f.Scenarios[0]

	// Default (0x41): byte-identical to the un-parameterised ComputeOpPushTx.
	derDefault, preDefault, err := ComputeOpPushTx(s.UnsignedTxHex, s.InputIndex, s.PrevScriptHex, s.PrevValueSats)
	if err != nil {
		t.Fatalf("default ComputeOpPushTx: %v", err)
	}
	derVia41, preVia41, err := ComputeOpPushTxWithSigHash(s.UnsignedTxHex, s.InputIndex, s.PrevScriptHex, s.PrevValueSats, -1, 0x41)
	if err != nil {
		t.Fatalf("0x41 ComputeOpPushTxWithSigHash: %v", err)
	}
	if hex.EncodeToString(derDefault) != hex.EncodeToString(derVia41) ||
		hex.EncodeToString(preDefault) != hex.EncodeToString(preVia41) {
		t.Fatal("explicit 0x41 must be byte-identical to the default ComputeOpPushTx")
	}
	if got := sighashTypeFromPreimage(preDefault); got != 0x41 {
		t.Fatalf("default preimage sighashType byte = 0x%02x, want 0x41", got)
	}
	if derDefault[len(derDefault)-1] != 0x41 {
		t.Fatalf("default DER trailing byte = 0x%02x, want 0x41", derDefault[len(derDefault)-1])
	}

	// SINGLE|FORKID (0x43) and ALL|ANYONECANPAY|FORKID (0xC1): the derived sig's
	// trailing byte AND the preimage's sighashType field must carry the flag, and
	// the preimage must diverge from the default (zeroed digest fields).
	for _, flag := range []int{0x43, 0xc1} {
		der, pre, err := ComputeOpPushTxWithSigHash(s.UnsignedTxHex, s.InputIndex, s.PrevScriptHex, s.PrevValueSats, -1, flag)
		if err != nil {
			t.Fatalf("mode 0x%02x: %v", flag, err)
		}
		if der[len(der)-1] != byte(flag) {
			t.Fatalf("mode 0x%02x: DER trailing byte = 0x%02x", flag, der[len(der)-1])
		}
		if got := sighashTypeFromPreimage(pre); got != byte(flag) {
			t.Fatalf("mode 0x%02x: preimage sighashType byte = 0x%02x", flag, got)
		}
		if hex.EncodeToString(pre) == hex.EncodeToString(preDefault) {
			t.Fatalf("mode 0x%02x: preimage must differ from ALL|FORKID (zeroed BIP-143 fields)", flag)
		}
	}
}

func TestSDKSighash_MethodSigHashTypeResolvesABI(t *testing.T) {
	mode43 := 0x43
	artifact := makeArtifact("51", ABI{
		Constructor: ABIConstructor{Params: nil},
		Methods: []ABIMethod{
			{Name: "bump", IsPublic: true, SigHashType: &mode43},
			{Name: "plain", IsPublic: true},
		},
	})
	c := NewRunarContract(artifact, nil)
	if got := c.methodSigHashType("bump"); got != 0x43 {
		t.Fatalf("bump sighash = 0x%02x, want 0x43", got)
	}
	if got := c.methodSigHashType("plain"); got != 0x41 {
		t.Fatalf("plain sighash = 0x%02x, want default 0x41", got)
	}
	if got := c.methodSigHashType("missing"); got != 0x41 {
		t.Fatalf("missing method sighash = 0x%02x, want default 0x41", got)
	}
}
