package runar

import (
	"strings"
	"testing"
)

// Issue #118: a true terminal method pays out the full contract balance, so
// fee == 0 and ARC rejects; the covenant asserts its exact output set, so no
// change output can absorb a fee. CallOptions.FeeUtxo adds a plain P2PKH input
// to the terminal tx BEFORE the OP_PUSH_TX preimage is computed (so hashPrevouts
// covers it), consumed entirely as fee with no change output.
func TestTerminalCall_FeeUtxoAddsFeeInput_Issue118(t *testing.T) {
	artifact := makeArtifact("51", ABI{
		Constructor: ABIConstructor{Params: nil},
		Methods:     []ABIMethod{{Name: "close", Params: nil, IsPublic: true}},
	})
	contract := NewRunarContract(artifact, nil)

	provider := NewMockProvider("testnet")
	mockAddr := strings.Repeat("00", 20)
	signer := NewMockSigner("", mockAddr)
	provider.AddUtxo(mockAddr, UTXO{Txid: strings.Repeat("aa", 32), OutputIndex: 0, Satoshis: 100000, Script: "76a914" + strings.Repeat("00", 20) + "88ac"})

	if _, _, err := contract.Deploy(provider, signer, DeployOptions{Satoshis: 50000}); err != nil {
		t.Fatalf("Deploy error: %v", err)
	}

	payout := "76a914" + strings.Repeat("bb", 20) + "88ac"
	feeUtxo := UTXO{Txid: strings.Repeat("cc", 32), OutputIndex: 0, Satoshis: 2000, Script: "76a914" + strings.Repeat("00", 20) + "88ac"}

	// Terminal method pays out the full 50000 balance; the fee is covered
	// entirely by the extra feeUtxo input.
	if _, _, err := contract.Call("close", nil, provider, signer, &CallOptions{
		TerminalOutputs: []TerminalOutput{{ScriptHex: payout, Satoshis: 50000}},
		FeeUtxo:         &feeUtxo,
	}); err != nil {
		t.Fatalf("Terminal call error: %v", err)
	}

	termHex := provider.GetBroadcastedTxs()[1]
	parsed := parseTxHex(termHex)

	// 1 contract input + 1 fee input = 2.
	if parsed.inputCount != 2 {
		t.Errorf("expected 2 inputs (contract + fee), got %d", parsed.inputCount)
	}
	// Exactly the terminal output, no change output.
	if parsed.outputCount != 1 {
		t.Errorf("expected 1 output (no change), got %d", parsed.outputCount)
	}
	// The fee input sits at index 1 and must be signed (non-empty scriptSig).
	if len(parsed.inputs) > 1 && parsed.inputs[1].script == "" {
		t.Errorf("fee input (index 1) must be signed")
	}
}

// Without a FeeUtxo, a terminal call keeps a single contract input.
func TestTerminalCall_NoFeeUtxo_SingleInput_Issue118(t *testing.T) {
	artifact := makeArtifact("51", ABI{
		Constructor: ABIConstructor{Params: nil},
		Methods:     []ABIMethod{{Name: "close", Params: nil, IsPublic: true}},
	})
	contract := NewRunarContract(artifact, nil)

	provider := NewMockProvider("testnet")
	mockAddr := strings.Repeat("00", 20)
	signer := NewMockSigner("", mockAddr)
	provider.AddUtxo(mockAddr, UTXO{Txid: strings.Repeat("aa", 32), OutputIndex: 0, Satoshis: 100000, Script: "76a914" + strings.Repeat("00", 20) + "88ac"})

	if _, _, err := contract.Deploy(provider, signer, DeployOptions{Satoshis: 50000}); err != nil {
		t.Fatalf("Deploy error: %v", err)
	}

	payout := "76a914" + strings.Repeat("bb", 20) + "88ac"
	if _, _, err := contract.Call("close", nil, provider, signer, &CallOptions{
		TerminalOutputs: []TerminalOutput{{ScriptHex: payout, Satoshis: 49000}},
	}); err != nil {
		t.Fatalf("Terminal call error: %v", err)
	}

	parsed := parseTxHex(provider.GetBroadcastedTxs()[1])
	if parsed.inputCount != 1 {
		t.Errorf("expected 1 input (contract only) without FeeUtxo, got %d", parsed.inputCount)
	}
}
