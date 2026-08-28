//go:build integration

package integration

import (
	"sync"
	"testing"

	"runar-integration/helpers"

	runar "github.com/icellan/runar/packages/runar-go"
)

var rawOutputArtifact *runar.RunarArtifact
var rawOutputOnce sync.Once

func getRawOutputArtifact(t *testing.T) *runar.RunarArtifact {
	t.Helper()
	rawOutputOnce.Do(func() {
		var err error
		rawOutputArtifact, err = helpers.CompileToSDKArtifact(
			"integration/contracts/outputs/RawOutput.runar.ts",
			map[string]interface{}{},
		)
		if err != nil {
			t.Fatalf("compile RawOutput: %v", err)
		}
	})
	return rawOutputArtifact
}

func TestRawOutput_SendToP2PKH(t *testing.T) {
	artifact := getRawOutputArtifact(t)
	contract := runar.NewRunarContract(artifact, []interface{}{int64(0)})

	wallet := helpers.NewWallet()
	helpers.RPCCall("importaddress", wallet.Address, "", false)
	if _, err := helpers.FundWallet(wallet, 1.0); err != nil {
		t.Fatalf("fund: %v", err)
	}
	provider := helpers.NewBatchRPCProvider()
	defer provider.MineAll()
	signer, err := helpers.SDKSignerFromWallet(wallet)
	if err != nil {
		t.Fatalf("signer: %v", err)
	}

	if _, _, err := contract.Deploy(provider, signer, runar.DeployOptions{Satoshis: 50_000}); err != nil {
		t.Fatalf("deploy: %v", err)
	}

	p2pkh := wallet.P2PKHScript()
	txid, _, err := contract.Call("sendToScript", []interface{}{p2pkh}, provider, signer, nil)
	if err != nil {
		t.Fatalf("call sendToScript: %v", err)
	}
	if len(txid) != 64 {
		t.Fatalf("txid length: %d", len(txid))
	}
	if stateBigInt(t, contract, "count") != 1 {
		t.Fatalf("count=%d, want 1", stateBigInt(t, contract, "count"))
	}

	// Output shape: [0]=raw 1000+p2pkh, [1]=state 2000
	rawHex, err := provider.GetRawTransaction(txid)
	if err != nil {
		t.Fatalf("getrawtransaction: %v", err)
	}
	outs, err := parseOutputsFromRawTxHex(rawHex)
	if err != nil {
		t.Fatalf("parse outputs: %v", err)
	}
	if len(outs) < 2 {
		t.Fatalf("expected >=2 outputs, got %d", len(outs))
	}
	if outs[0].satoshis != 1000 || outs[0].script != p2pkh {
		t.Fatalf("outputs[0] raw: sats=%d script=%s want 1000 / %s", outs[0].satoshis, outs[0].script, p2pkh)
	}
	if outs[1].satoshis != 2000 {
		t.Fatalf("outputs[1] state sats=%d want 2000", outs[1].satoshis)
	}
	if utxo := contract.GetCurrentUtxo(); utxo == nil || utxo.OutputIndex != 1 {
		t.Fatalf("currentUtxo.outputIndex want 1, got %#v", utxo)
	}

	// Re-spend continuation
	p2pkh2 := "76a914" + "abababababababababababababababababababab" + "88ac"
	if _, _, err := contract.Call("sendToScript", []interface{}{p2pkh2}, provider, signer, nil); err != nil {
		t.Fatalf("second sendToScript: %v", err)
	}
	if stateBigInt(t, contract, "count") != 2 {
		t.Fatalf("count after second call=%d want 2", stateBigInt(t, contract, "count"))
	}
}
