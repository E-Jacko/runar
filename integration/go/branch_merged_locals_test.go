//go:build integration

package integration

import (
	"math/big"
	"sync"
	"testing"

	"runar-integration/helpers"

	runar "github.com/icellan/runar/packages/runar-go"
)

var branchMergedArtifact *runar.RunarArtifact
var branchMergedOnce sync.Once

func getBranchMergedArtifact(t *testing.T) *runar.RunarArtifact {
	t.Helper()
	branchMergedOnce.Do(func() {
		var err error
		branchMergedArtifact, err = helpers.CompileToSDKArtifact(
			"integration/contracts/constructs/BranchMergedLocals.runar.ts",
			map[string]interface{}{},
		)
		if err != nil {
			t.Fatalf("compile BranchMergedLocals: %v", err)
		}
	})
	return branchMergedArtifact
}

func stateBigInt(t *testing.T, c *runar.RunarContract, field string) int64 {
	t.Helper()
	st := c.GetState()
	v, ok := st[field]
	if !ok {
		t.Fatalf("state has no %q; got %#v", field, st)
	}
	switch n := v.(type) {
	case int64:
		return n
	case int:
		return int64(n)
	case float64:
		return int64(n)
	case *big.Int:
		return n.Int64()
	case big.Int:
		return n.Int64()
	default:
		t.Fatalf("state.%s is %T, expected integer; got %#v", field, v, v)
		return 0
	}
}

func TestBranchMergedLocals_ToFirst(t *testing.T) {
	artifact := getBranchMergedArtifact(t)
	contract := runar.NewRunarContract(artifact, []interface{}{int64(10), int64(20)})

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

	txid, _, err := contract.Call("bid", []interface{}{int64(99), int64(1)}, provider, signer, nil)
	if err != nil {
		t.Fatalf("call bid: %v", err)
	}
	if len(txid) != 64 {
		t.Fatalf("txid length: %d", len(txid))
	}
	if a, b := stateBigInt(t, contract, "a"), stateBigInt(t, contract, "b"); a != 99 || b != 20 {
		t.Fatalf("post-state a=%d b=%d, want a=99 b=20", a, b)
	}
	if _, err := helpers.AssertOnChainState(artifact, txid, 0, map[string]interface{}{
		"a": int64(99), "b": int64(20),
	}); err != nil {
		t.Fatalf("on-chain state: %v", err)
	}
}

func TestBranchMergedLocals_ToSecond(t *testing.T) {
	artifact := getBranchMergedArtifact(t)
	contract := runar.NewRunarContract(artifact, []interface{}{int64(10), int64(20)})

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

	txid, _, err := contract.Call("bid", []interface{}{int64(77), int64(0)}, provider, signer, nil)
	if err != nil {
		t.Fatalf("call bid: %v", err)
	}
	if len(txid) != 64 {
		t.Fatalf("txid length: %d", len(txid))
	}
	if a, b := stateBigInt(t, contract, "a"), stateBigInt(t, contract, "b"); a != 10 || b != 77 {
		t.Fatalf("post-state a=%d b=%d, want a=10 b=77", a, b)
	}
	if _, err := helpers.AssertOnChainState(artifact, txid, 0, map[string]interface{}{
		"a": int64(10), "b": int64(77),
	}); err != nil {
		t.Fatalf("on-chain state: %v", err)
	}
}
