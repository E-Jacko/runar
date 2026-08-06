//go:build integration

package integration

import (
	"sync"
	"testing"

	"runar-integration/helpers"

	runar "github.com/icellan/runar/packages/runar-go"
)

var condWriteArtifact *runar.RunarArtifact
var condWriteOnce sync.Once

func getCondWriteArtifact(t *testing.T) *runar.RunarArtifact {
	t.Helper()
	condWriteOnce.Do(func() {
		var err error
		condWriteArtifact, err = helpers.CompileToSDKArtifact(
			"integration/contracts/constructs/CondWriteMultiField.runar.ts",
			map[string]interface{}{},
		)
		if err != nil {
			t.Fatalf("compile CondWriteMultiField: %v", err)
		}
	})
	return condWriteArtifact
}

func TestCondWriteMultiField_Bump(t *testing.T) {
	artifact := getCondWriteArtifact(t)
	contract := runar.NewRunarContract(artifact, []interface{}{int64(1), int64(2)})

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

	txid, _, err := contract.Call("bump", []interface{}{int64(1)}, provider, signer, nil)
	if err != nil {
		t.Fatalf("call bump: %v", err)
	}
	if a, b := stateBigInt(t, contract, "a"), stateBigInt(t, contract, "b"); a != 2 || b != 4 {
		t.Fatalf("post-state a=%d b=%d, want a=2 b=4", a, b)
	}
	if _, err := helpers.AssertOnChainState(artifact, txid, 0, map[string]interface{}{
		"a": int64(2), "b": int64(4),
	}); err != nil {
		t.Fatalf("on-chain state: %v", err)
	}
}

func TestCondWriteMultiField_NoBump(t *testing.T) {
	artifact := getCondWriteArtifact(t)
	contract := runar.NewRunarContract(artifact, []interface{}{int64(1), int64(2)})

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

	txid, _, err := contract.Call("bump", []interface{}{int64(0)}, provider, signer, nil)
	if err != nil {
		t.Fatalf("call bump: %v", err)
	}
	if a, b := stateBigInt(t, contract, "a"), stateBigInt(t, contract, "b"); a != 1 || b != 2 {
		t.Fatalf("post-state a=%d b=%d, want a=1 b=2", a, b)
	}
	if _, err := helpers.AssertOnChainState(artifact, txid, 0, map[string]interface{}{
		"a": int64(1), "b": int64(2),
	}); err != nil {
		t.Fatalf("on-chain state: %v", err)
	}
}
