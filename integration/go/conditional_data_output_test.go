//go:build integration

package integration

import (
	"sync"
	"testing"

	"runar-integration/helpers"

	runar "github.com/icellan/runar/packages/runar-go"
)

var condDataArtifact *runar.RunarArtifact
var condDataOnce sync.Once

func getCondDataArtifact(t *testing.T) *runar.RunarArtifact {
	t.Helper()
	condDataOnce.Do(func() {
		var err error
		condDataArtifact, err = helpers.CompileToSDKArtifact(
			"integration/contracts/constructs/ConditionalDataOutput.runar.ts",
			map[string]interface{}{},
		)
		if err != nil {
			t.Fatalf("compile ConditionalDataOutput: %v", err)
		}
	})
	return condDataArtifact
}

func TestConditionalDataOutput_WithData(t *testing.T) {
	artifact := getCondDataArtifact(t)
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

	if _, _, err := contract.Deploy(provider, signer, runar.DeployOptions{Satoshis: 20_000}); err != nil {
		t.Fatalf("deploy: %v", err)
	}

	payload := "6a09" + "6273766d2d74657374"
	txid, _, err := contract.Call("pay", []interface{}{true, payload}, provider, signer, nil)
	if err != nil {
		t.Fatalf("call pay: %v", err)
	}
	if len(txid) != 64 {
		t.Fatalf("txid length: %d", len(txid))
	}
	if stateBigInt(t, contract, "amount") != 1 {
		t.Fatalf("amount=%d, want 1", stateBigInt(t, contract, "amount"))
	}

	rawHex, err := provider.GetRawTransaction(txid)
	if err != nil {
		t.Fatalf("getrawtransaction: %v", err)
	}
	outs, err := parseOutputsFromRawTxHex(rawHex)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}
	if len(outs) < 2 {
		t.Fatalf("expected >=2 outs, got %d", len(outs))
	}
	if outs[1].satoshis != 1 || outs[1].script != payload {
		t.Fatalf("outputs[1] data: sats=%d script=%s", outs[1].satoshis, outs[1].script)
	}
}

func TestConditionalDataOutput_NoData(t *testing.T) {
	artifact := getCondDataArtifact(t)
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

	if _, _, err := contract.Deploy(provider, signer, runar.DeployOptions{Satoshis: 20_000}); err != nil {
		t.Fatalf("deploy: %v", err)
	}

	payload := "6a04" + "6e6f6e65"
	txid, _, err := contract.Call("pay", []interface{}{false, payload}, provider, signer, nil)
	if err != nil {
		t.Fatalf("call pay: %v", err)
	}
	if stateBigInt(t, contract, "amount") != 1 {
		t.Fatalf("amount=%d, want 1", stateBigInt(t, contract, "amount"))
	}

	rawHex, err := provider.GetRawTransaction(txid)
	if err != nil {
		t.Fatalf("getrawtransaction: %v", err)
	}
	outs, err := parseOutputsFromRawTxHex(rawHex)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}
	for i, o := range outs {
		if o.script == payload {
			t.Fatalf("flag=false must not emit data payload at output[%d]", i)
		}
	}
}
