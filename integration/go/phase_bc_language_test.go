//go:build integration

package integration

import (
	"testing"

	"runar-integration/helpers"

	runar "github.com/icellan/runar/packages/runar-go"
)

func deployCall(
	t *testing.T,
	source string,
	ctor []interface{},
	method string,
	args []interface{},
	sats int64,
) (string, *runar.RunarArtifact) {
	t.Helper()
	artifact, err := helpers.CompileToSDKArtifact(source, map[string]interface{}{})
	if err != nil {
		t.Fatalf("compile %s: %v", source, err)
	}
	contract := runar.NewRunarContract(artifact, ctor)
	wallet := helpers.NewWallet()
	helpers.RPCCall("importaddress", wallet.Address, "", false)
	if _, err := helpers.FundWallet(wallet, 1.0); err != nil {
		t.Fatalf("fund: %v", err)
	}
	provider := helpers.NewBatchRPCProvider()
	t.Cleanup(func() { provider.MineAll() })
	signer, err := helpers.SDKSignerFromWallet(wallet)
	if err != nil {
		t.Fatalf("signer: %v", err)
	}
	if _, _, err := contract.Deploy(provider, signer, runar.DeployOptions{Satoshis: sats}); err != nil {
		t.Fatalf("deploy: %v", err)
	}
	txid, _, err := contract.Call(method, args, provider, signer, nil)
	if err != nil {
		t.Fatalf("call %s: %v", method, err)
	}
	if len(txid) != 64 {
		t.Fatalf("txid length %d", len(txid))
	}
	return txid, artifact
}

func TestPhaseB_ArithmeticOps(t *testing.T) {
	deployCall(t, "integration/contracts/language/ArithmeticOps.runar.ts",
		[]interface{}{int64(45)}, "verify", []interface{}{int64(10), int64(2)}, 5000)
}

func TestPhaseB_BooleanLogic(t *testing.T) {
	deployCall(t, "integration/contracts/language/BooleanLogic.runar.ts",
		[]interface{}{int64(5)}, "verify", []interface{}{int64(10), int64(1), false}, 5000)
}

func TestPhaseB_BitwiseOps(t *testing.T) {
	deployCall(t, "integration/contracts/language/BitwiseOps.runar.ts",
		[]interface{}{int64(0x0f), int64(0x33)}, "testBitwise", nil, 5000)
	deployCall(t, "integration/contracts/language/BitwiseOps.runar.ts",
		[]interface{}{int64(0x0f), int64(0x33)}, "testShift", nil, 5000)
}

func TestPhaseB_BoundedLoop(t *testing.T) {
	deployCall(t, "integration/contracts/language/BoundedLoop.runar.ts",
		[]interface{}{int64(15)}, "verify", []interface{}{int64(1)}, 5000)
}

func TestPhaseB_ByteStringOps(t *testing.T) {
	deployCall(t, "integration/contracts/language/ByteStringOps.runar.ts",
		[]interface{}{"01020304"}, "verify", nil, 5000)
}

func TestPhaseB_IfElseSimple(t *testing.T) {
	deployCall(t, "integration/contracts/language/IfElseSimple.runar.ts",
		[]interface{}{int64(5)}, "check", []interface{}{int64(10), true}, 5000)
}

func TestPhaseB_TernaryOps(t *testing.T) {
	deployCall(t, "integration/contracts/language/TernaryOps.runar.ts",
		[]interface{}{int64(7)}, "verify", []interface{}{true, int64(7), int64(9)}, 5000)
}

func TestPhaseB_PropertyInitializers(t *testing.T) {
	txid, artifact := deployCall(t, "integration/contracts/constructs/PropertyInitializers.runar.ts",
		[]interface{}{int64(100)}, "increment", []interface{}{int64(5)}, 10_000)
	if _, err := helpers.AssertOnChainState(artifact, txid, 0, map[string]interface{}{
		"count": int64(5),
	}); err != nil {
		t.Fatalf("on-chain: %v", err)
	}
}

func TestPhaseC_AsmAnyone(t *testing.T) {
	deployCall(t, "integration/contracts/unsafe/AsmAnyone.runar.ts",
		nil, "unlock", nil, 5000)
}

func TestPhaseC_CurrentBlockHeight(t *testing.T) {
	txid, artifact := deployCall(t, "integration/contracts/intents/CurrentBlockHeight.runar.ts",
		[]interface{}{int64(2_000_000_000), int64(0)}, "spend", nil, 10_000)
	if _, err := helpers.AssertOnChainState(artifact, txid, 0, map[string]interface{}{
		"count": int64(1),
	}); err != nil {
		t.Fatalf("on-chain: %v", err)
	}
}

func TestPhaseC_PreimageExtractors(t *testing.T) {
	txid, artifact := deployCall(t, "integration/contracts/crypto/PreimageExtractors.runar.ts",
		[]interface{}{int64(0)}, "tick", nil, 10_000)
	if _, err := helpers.AssertOnChainState(artifact, txid, 0, map[string]interface{}{
		"count": int64(1),
	}); err != nil {
		t.Fatalf("on-chain: %v", err)
	}
}
