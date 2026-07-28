package runar

// ---------------------------------------------------------------------------
// sdk_null_bytestring_arg_test.go
//
// G6 — a nil arg for a ByteString param is only meaningful for the
// auto-computed `allPrevouts` slot. For any other ByteString param it is a
// caller mistake, and silently substituting the 36*n-zero-byte prevouts stub
// hands the contract prevouts bytes where it expected its own value — the tx
// broadcasts and then fails at script execution with an opaque error.
//
// nil for a Sig param (auto-sign) must keep working untouched.
// ---------------------------------------------------------------------------

import (
	"strings"
	"testing"
)

// makeArtifactWithByteStringParam builds a stateful artifact whose single
// public method takes (sig Sig, <byteStringParamName> ByteString).
func makeArtifactWithByteStringParam(byteStringParamName string) *RunarArtifact {
	abi := ABI{
		Constructor: ABIConstructor{Params: []ABIParam{{Name: "count", Type: "bigint"}}},
		Methods: []ABIMethod{
			{
				Name:     "move",
				IsPublic: true,
				Params: []ABIParam{
					{Name: "sig", Type: "Sig"},
					{Name: byteStringParamName, Type: "ByteString"},
					{Name: "_changePKH", Type: "Ripemd160"},
					{Name: "_changeAmount", Type: "bigint"},
					{Name: "txPreimage", Type: "SigHashPreimage"},
				},
			},
		},
	}
	return makeArtifact("51", abi, func(a *RunarArtifact) {
		a.ContractName = "NullByteStringArgTest"
		a.StateFields = []StateField{{Name: "count", Type: "bigint", Index: 0}}
		csi := 0
		a.CodeSeparatorIndex = &csi
	})
}

// A nil ByteString arg for an ordinary user param must fail loudly at build
// time, naming the parameter — not silently become the prevouts stub.
func TestNilByteStringArg_RejectedForNonPrevoutsParam(t *testing.T) {
	art := makeArtifactWithByteStringParam("memo")
	contract, provider, signer := setupContractAndDeploy(t, art)

	_, err := contract.PrepareCall("move", []interface{}{nil, nil}, provider, signer, nil)
	if err == nil {
		t.Fatal("expected PrepareCall to reject a nil ByteString arg for param 'memo'")
	}
	if !strings.Contains(err.Error(), "memo") {
		t.Errorf("error must name the offending parameter, got: %v", err)
	}
}

// The documented `allPrevouts` auto-compute path must keep working: nil there
// is the SDK's own sentinel, not a caller mistake.
func TestNilByteStringArg_AllPrevoutsStillAutoResolves(t *testing.T) {
	art := makeArtifactWithByteStringParam("allPrevouts")
	contract, provider, signer := setupContractAndDeploy(t, art)

	if _, err := contract.PrepareCall("move", []interface{}{nil, nil}, provider, signer, nil); err != nil {
		t.Fatalf("nil allPrevouts must still auto-resolve, got: %v", err)
	}
}

// nil for a Sig param is the auto-sign sentinel and must stay accepted.
func TestNilSigArg_StillAutoSigns(t *testing.T) {
	art := makeArtifactWithByteStringParam("memo")
	contract, provider, signer := setupContractAndDeploy(t, art)

	if _, err := contract.PrepareCall("move", []interface{}{nil, "deadbeef"}, provider, signer, nil); err != nil {
		t.Fatalf("nil Sig arg must still auto-sign, got: %v", err)
	}
}

// The same rule applies to the per-input args of additional contract inputs.
func TestNilByteStringArg_RejectedForAdditionalContractInputArgs(t *testing.T) {
	art := makeArtifactWithByteStringParam("memo")
	contract, provider, signer := setupContractAndDeploy(t, art)

	extra := UTXO{
		Txid:        strings.Repeat("cc", 32),
		OutputIndex: 0,
		Satoshis:    5000,
		Script:      contract.currentUtxo.Script,
	}
	opts := &CallOptions{
		AdditionalContractInputs:    []*UTXO{&extra},
		AdditionalContractInputArgs: [][]interface{}{{nil, nil}},
	}
	_, err := contract.PrepareCall("move", []interface{}{nil, "deadbeef"}, provider, signer, opts)
	if err == nil {
		t.Fatal("expected a nil ByteString arg in AdditionalContractInputArgs to be rejected")
	}
	if !strings.Contains(err.Error(), "memo") {
		t.Errorf("error must name the offending parameter, got: %v", err)
	}
}
