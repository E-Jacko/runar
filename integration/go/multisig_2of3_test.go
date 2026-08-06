//go:build integration

package integration

import (
	"encoding/hex"
	"sync"
	"testing"

	"runar-integration/helpers"

	runar "github.com/icellan/runar/packages/runar-go"
)

var multiSigArtifact *runar.RunarArtifact
var multiSigOnce sync.Once

func getMultiSigArtifact(t *testing.T) *runar.RunarArtifact {
	t.Helper()
	multiSigOnce.Do(func() {
		var err error
		multiSigArtifact, err = helpers.CompileToSDKArtifact(
			"integration/contracts/crypto/MultiSig2of3.runar.ts",
			map[string]interface{}{},
		)
		if err != nil {
			t.Fatalf("compile MultiSig2of3: %v", err)
		}
	})
	return multiSigArtifact
}

// spendMultiSig2of3SDK uses PrepareCall + FinalizeCall (Go SDK multi-Sig path)
// with two distinct key holders. Logs "SDK_CALL_PATH" so residual verification
// can grep for the SDK path (not raw hand-built unlock).
func spendMultiSig2of3SDK(
	t *testing.T,
	contract *runar.RunarContract,
	provider runar.Provider,
	fundingSigner runar.Signer,
	pk1, pk2 *helpers.Wallet,
) string {
	t.Helper()
	// nil,nil → two Sig placeholders in prepared.SigIndices
	prepared, err := contract.PrepareCall("unlock", []interface{}{nil, nil}, provider, fundingSigner, nil)
	if err != nil {
		t.Fatalf("PrepareCall unlock: %v", err)
	}
	if len(prepared.SigIndices) != 2 {
		t.Fatalf("expected 2 SigIndices, got %v", prepared.SigIndices)
	}
	t.Logf("SDK_CALL_PATH: PrepareCall unlock sigIndices=%v", prepared.SigIndices)

	s1, err := helpers.SDKSignerFromWallet(pk1)
	if err != nil {
		t.Fatalf("signer1: %v", err)
	}
	s2, err := helpers.SDKSignerFromWallet(pk2)
	if err != nil {
		t.Fatalf("signer2: %v", err)
	}
	utxo := contract.GetCurrentUtxo()
	if utxo == nil {
		t.Fatal("no current utxo")
	}
	sig0, err := s1.Sign(prepared.TxHex, 0, utxo.Script, utxo.Satoshis, nil)
	if err != nil {
		t.Fatalf("sign pk1: %v", err)
	}
	sig1, err := s2.Sign(prepared.TxHex, 0, utxo.Script, utxo.Satoshis, nil)
	if err != nil {
		t.Fatalf("sign pk2: %v", err)
	}
	txid, _, err := contract.FinalizeCall(prepared, map[int]string{
		prepared.SigIndices[0]: sig0,
		prepared.SigIndices[1]: sig1,
	}, provider)
	if err != nil {
		t.Fatalf("FinalizeCall: %v", err)
	}
	t.Logf("SDK_CALL_PATH: FinalizeCall txid=%s", txid)
	return txid
}

// spendMultiSig2of3Raw builds unlocking script <sig1> <sig2> without SDK Call.
func spendMultiSig2of3Raw(t *testing.T, contract *runar.RunarContract, signer1, signer2 *helpers.Wallet) string {
	t.Helper()
	utxo := helpers.SDKUtxoToHelper(contract.GetCurrentUtxo())
	receiverScript := signer1.P2PKHScript()
	spendTx, err := helpers.BuildSpendTx(utxo, receiverScript, 4500)
	if err != nil {
		t.Fatalf("build spend: %v", err)
	}

	sig1Hex, err := helpers.SignInput(spendTx, 0, signer1.PrivKey)
	if err != nil {
		t.Fatalf("sign1: %v", err)
	}
	sig1Bytes, _ := hex.DecodeString(sig1Hex)

	sig2Hex, err := helpers.SignInput(spendTx, 0, signer2.PrivKey)
	if err != nil {
		t.Fatalf("sign2: %v", err)
	}
	sig2Bytes, _ := hex.DecodeString(sig2Hex)

	unlockHex := helpers.EncodePushBytes(sig1Bytes) + helpers.EncodePushBytes(sig2Bytes)

	spendHex, err := helpers.SpendContract(utxo, unlockHex, receiverScript, 4500)
	if err != nil {
		t.Fatalf("spend: %v", err)
	}
	return spendHex
}

func TestMultiSig2of3_SDKCall_DistinctKeys(t *testing.T) {
	pk1 := helpers.NewWallet()
	pk2 := helpers.NewWallet()
	pk3 := helpers.NewWallet()
	funder := helpers.NewWallet()

	artifact := getMultiSigArtifact(t)
	// Sanity: multi-sig ASM should not be classified as OR-CHECKSIG soft-warn path
	if artifact.ASM != "" {
		t.Logf("artifact ASM contains CHECKMULTISIG: %v",
			containsFold(artifact.ASM, "OP_CHECKMULTISIG"))
	}

	contract := runar.NewRunarContract(artifact, []interface{}{
		pk1.PubKeyHex(), pk2.PubKeyHex(), pk3.PubKeyHex(),
	})

	helpers.RPCCall("importaddress", funder.Address, "", false)
	if _, err := helpers.FundWallet(funder, 1.0); err != nil {
		t.Fatalf("fund: %v", err)
	}
	provider := helpers.NewBatchRPCProvider()
	defer provider.MineAll()
	signer, err := helpers.SDKSignerFromWallet(funder)
	if err != nil {
		t.Fatalf("signer: %v", err)
	}

	if _, _, err := contract.Deploy(provider, signer, runar.DeployOptions{Satoshis: 5000}); err != nil {
		t.Fatalf("deploy: %v", err)
	}

	txid := spendMultiSig2of3SDK(t, contract, provider, signer, pk1, pk2)
	if len(txid) != 64 {
		t.Fatalf("txid length %d", len(txid))
	}
}

func TestMultiSig2of3_RawPath_Valid2of3(t *testing.T) {
	pk1 := helpers.NewWallet()
	pk2 := helpers.NewWallet()
	pk3 := helpers.NewWallet()
	funder := helpers.NewWallet()

	artifact := getMultiSigArtifact(t)
	contract := runar.NewRunarContract(artifact, []interface{}{
		pk1.PubKeyHex(), pk2.PubKeyHex(), pk3.PubKeyHex(),
	})

	helpers.RPCCall("importaddress", funder.Address, "", false)
	if _, err := helpers.FundWallet(funder, 1.0); err != nil {
		t.Fatalf("fund: %v", err)
	}
	provider := helpers.NewBatchRPCProvider()
	defer provider.MineAll()
	signer, err := helpers.SDKSignerFromWallet(funder)
	if err != nil {
		t.Fatalf("signer: %v", err)
	}

	if _, _, err := contract.Deploy(provider, signer, runar.DeployOptions{Satoshis: 5000}); err != nil {
		t.Fatalf("deploy: %v", err)
	}

	spendHex := spendMultiSig2of3Raw(t, contract, pk1, pk2)
	txid := helpers.AssertTxAccepted(t, spendHex)
	t.Logf("raw multisig spend accepted: %s", txid)
}

func TestMultiSig2of3_WrongKeys_Rejected(t *testing.T) {
	owner1 := helpers.NewWallet()
	owner2 := helpers.NewWallet()
	owner3 := helpers.NewWallet()
	attacker1 := helpers.NewWallet()
	attacker2 := helpers.NewWallet()
	funder := helpers.NewWallet()

	artifact := getMultiSigArtifact(t)
	contract := runar.NewRunarContract(artifact, []interface{}{
		owner1.PubKeyHex(), owner2.PubKeyHex(), owner3.PubKeyHex(),
	})

	helpers.RPCCall("importaddress", funder.Address, "", false)
	if _, err := helpers.FundWallet(funder, 1.0); err != nil {
		t.Fatalf("fund: %v", err)
	}
	provider := helpers.NewBatchRPCProvider()
	defer provider.MineAll()
	signer, err := helpers.SDKSignerFromWallet(funder)
	if err != nil {
		t.Fatalf("signer: %v", err)
	}

	if _, _, err := contract.Deploy(provider, signer, runar.DeployOptions{Satoshis: 5000}); err != nil {
		t.Fatalf("deploy: %v", err)
	}

	utxo := helpers.SDKUtxoToHelper(contract.GetCurrentUtxo())
	spendTx, err := helpers.BuildSpendTx(utxo, attacker1.P2PKHScript(), 4500)
	if err != nil {
		t.Fatalf("build: %v", err)
	}
	sig1Hex, err := helpers.SignInput(spendTx, 0, attacker1.PrivKey)
	if err != nil {
		t.Fatalf("sign1: %v", err)
	}
	sig2Hex, err := helpers.SignInput(spendTx, 0, attacker2.PrivKey)
	if err != nil {
		t.Fatalf("sign2: %v", err)
	}
	sig1, _ := hex.DecodeString(sig1Hex)
	sig2, _ := hex.DecodeString(sig2Hex)
	unlockHex := helpers.EncodePushBytes(sig1) + helpers.EncodePushBytes(sig2)
	spendHex, err := helpers.SpendContract(utxo, unlockHex, attacker1.P2PKHScript(), 4500)
	if err != nil {
		t.Fatalf("spend build: %v", err)
	}
	helpers.AssertTxRejected(t, spendHex)
}

func containsFold(s, sub string) bool {
	return len(s) >= len(sub) && (s == sub || len(sub) == 0 ||
		(func() bool {
			for i := 0; i+len(sub) <= len(s); i++ {
				match := true
				for j := 0; j < len(sub); j++ {
					a, b := s[i+j], sub[j]
					if a >= 'a' && a <= 'z' {
						a -= 32
					}
					if b >= 'a' && b <= 'z' {
						b -= 32
					}
					if a != b {
						match = false
						break
					}
				}
				if match {
					return true
				}
			}
			return false
		})())
}
