package runar

import (
	"strings"
	"testing"
)

// Issue #134: deploy() and the call funding loops signed every P2PKH funding
// input with the connected method signer and pushed that signer's pubkey, so
// funding coins owned by a different key failed OP_EQUALVERIFY. DeployOptions/
// CallOptions.FundingSigner lets the funding loops use fundingSigner ?? signer
// while the method's own Sig args keep the connected signer.

func TestDeploy_FundingSignerSignsFundingInputs_Issue134(t *testing.T) {
	methodSigner, _ := NewLocalSigner("0000000000000000000000000000000000000000000000000000000000000003")
	fundingSigner, _ := NewLocalSigner("0000000000000000000000000000000000000000000000000000000000000005")
	methodPub, _ := methodSigner.GetPublicKey()
	fundingPub, _ := fundingSigner.GetPublicKey()
	if methodPub == fundingPub {
		t.Fatal("test setup: method and funding pubkeys must differ")
	}

	artifact := makeArtifact("51", ABI{
		Constructor: ABIConstructor{Params: []ABIParam{}},
		Methods:     []ABIMethod{{Name: "spend", Params: nil, IsPublic: true}},
	})

	addr, _ := methodSigner.GetAddress()
	newProvider := func() *MockProvider {
		p := NewMockProvider("testnet")
		p.AddUtxo(addr, UTXO{Txid: strings.Repeat("a1", 32), OutputIndex: 0, Satoshis: 100000, Script: "76a914" + strings.Repeat("00", 20) + "88ac"})
		return p
	}

	// With FundingSigner: the deploy funding input's P2PKH unlock must push the
	// FUNDING signer's pubkey, not the connected method signer's.
	p := newProvider()
	c := NewRunarContract(artifact, []interface{}{})
	if _, _, err := c.Deploy(p, methodSigner, DeployOptions{Satoshis: 1000, FundingSigner: fundingSigner}); err != nil {
		t.Fatalf("deploy with fundingSigner: %v", err)
	}
	deployHex := p.GetBroadcastedTxs()[0]
	if !strings.Contains(deployHex, "21"+fundingPub) {
		t.Errorf("expected funding input to push the funding signer's pubkey (issue #134)")
	}
	if strings.Contains(deployHex, "21"+methodPub) {
		t.Errorf("funding input must NOT push the method signer's pubkey when FundingSigner is set")
	}

	// Back-compat: without FundingSigner, funding is signed by the connected signer.
	p2 := newProvider()
	c2 := NewRunarContract(artifact, []interface{}{})
	if _, _, err := c2.Deploy(p2, methodSigner, DeployOptions{Satoshis: 1000}); err != nil {
		t.Fatalf("deploy without fundingSigner: %v", err)
	}
	deployHex2 := p2.GetBroadcastedTxs()[0]
	if !strings.Contains(deployHex2, "21"+methodPub) {
		t.Errorf("without FundingSigner, funding input must push the connected signer's pubkey (back-compat)")
	}
}
