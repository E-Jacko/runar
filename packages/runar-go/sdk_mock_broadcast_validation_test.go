package runar

import (
	"encoding/json"
	"os"
	"os/exec"
	"strings"
	"testing"

	bsvscript "github.com/bsv-blockchain/go-sdk/script"
	"github.com/bsv-blockchain/go-sdk/transaction"
)

// Testing-gap remediation Phase A5 (Go tier): MockProvider.Broadcast is
// fail-CLOSED by default. It replays every input whose outpoint the provider
// knows through the go-sdk script interpreter (the same engine
// packages/runar-go/script_vm.go wraps), enforces value conservation, and
// refuses to hand back a fake txid for a transaction a real node would reject.
//
// The TypeScript reference (packages/runar-sdk/src/providers/mock.ts) has a
// fail-OPEN hole this port deliberately closes: a transaction none of whose
// inputs are known validated NOTHING and was accepted. Here that is an error
// ("validated 0 of N inputs") so a gate can never silently pass vacuously.

const mockValidationAnyoneCanSpendHex = "51" // OP_TRUE

// buildOneInputTx assembles a single-input transaction spending
// prevTxid:vout (whose locking script / value are given) with the supplied
// unlocking script and a single output.
func buildOneInputTx(t *testing.T, prevTxid string, vout uint32, prevScriptHex string, prevSats uint64,
	unlockingHex string, outSats uint64, outScriptHex string) *transaction.Transaction {
	t.Helper()
	tx := transaction.NewTransaction()
	if err := tx.AddInputFrom(prevTxid, vout, prevScriptHex, prevSats, nil); err != nil {
		t.Fatalf("AddInputFrom: %v", err)
	}
	unlocking, err := bsvscript.NewFromHex(unlockingHex)
	if err != nil {
		t.Fatalf("unlocking script: %v", err)
	}
	tx.Inputs[0].UnlockingScript = unlocking
	out, err := bsvscript.NewFromHex(outScriptHex)
	if err != nil {
		t.Fatalf("output script: %v", err)
	}
	tx.AddOutput(&transaction.TransactionOutput{Satoshis: outSats, LockingScript: out})
	return tx
}

// --- rejection: script-invalid spend -----------------------------------------

func TestMockProvider_Broadcast_RejectsScriptInvalidSpend(t *testing.T) {
	p := NewMockProvider("testnet")
	// A known outpoint locked with OP_RETURN-style always-false script
	// (OP_0: leaves a falsey top of stack).
	p.AddUtxo("addr", UTXO{
		Txid:        strings.Repeat("11", 32),
		OutputIndex: 0,
		Satoshis:    10_000,
		Script:      "00", // OP_0 -> falsey top of stack -> spend must fail
	})
	tx := buildOneInputTx(t, strings.Repeat("11", 32), 0, "00", 10_000,
		"", 1_000, mockValidationAnyoneCanSpendHex)

	if _, err := p.Broadcast(tx); err == nil {
		t.Fatalf("MockProvider accepted a script-INVALID transaction; broadcast validation is fail-open")
	} else if !strings.Contains(err.Error(), "input 0") {
		t.Fatalf("error should name the failing input, got: %v", err)
	}
}

// --- rejection: underfunded (outputs exceed known inputs) ---------------------

func TestMockProvider_Broadcast_RejectsUnderfundedTx(t *testing.T) {
	p := NewMockProvider("testnet")
	p.AddUtxo("addr", UTXO{
		Txid:        strings.Repeat("22", 32),
		OutputIndex: 0,
		Satoshis:    1_000,
		Script:      mockValidationAnyoneCanSpendHex,
	})
	tx := buildOneInputTx(t, strings.Repeat("22", 32), 0, mockValidationAnyoneCanSpendHex, 1_000,
		"", 5_000, mockValidationAnyoneCanSpendHex)

	_, err := p.Broadcast(tx)
	if err == nil {
		t.Fatalf("MockProvider accepted an UNDERFUNDED transaction (outputs 5000 > inputs 1000)")
	}
	if !strings.Contains(err.Error(), "underfunded") {
		t.Fatalf("expected an underfunded error, got: %v", err)
	}
}

// --- rejection: vacuous validation (zero inputs actually checked) -------------

func TestMockProvider_Broadcast_RejectsVacuousValidation(t *testing.T) {
	p := NewMockProvider("testnet")
	// Nothing added: the provider knows no outpoints, so it can validate
	// nothing. A gate that silently validates nothing is worse than no gate.
	tx := buildOneInputTx(t, strings.Repeat("33", 32), 0, mockValidationAnyoneCanSpendHex, 10_000,
		"", 1_000, mockValidationAnyoneCanSpendHex)

	_, err := p.Broadcast(tx)
	if err == nil {
		t.Fatalf("MockProvider accepted a transaction whose inputs are ALL unknown — " +
			"validation ran on zero inputs and passed vacuously")
	}
	if !strings.Contains(err.Error(), "validated 0 of 1") {
		t.Fatalf("expected a non-vacuity error naming the validated/total input counts, got: %v", err)
	}
}

// --- acceptance: a valid spend of a known outpoint ---------------------------

func TestMockProvider_Broadcast_AcceptsValidSpend(t *testing.T) {
	p := NewMockProvider("testnet")
	p.AddUtxo("addr", UTXO{
		Txid:        strings.Repeat("44", 32),
		OutputIndex: 0,
		Satoshis:    10_000,
		Script:      mockValidationAnyoneCanSpendHex,
	})
	tx := buildOneInputTx(t, strings.Repeat("44", 32), 0, mockValidationAnyoneCanSpendHex, 10_000,
		"", 9_000, mockValidationAnyoneCanSpendHex)

	txid, err := p.Broadcast(tx)
	if err != nil {
		t.Fatalf("MockProvider rejected a VALID spend: %v", err)
	}
	if len(txid) != 64 {
		t.Fatalf("expected a 64-char fake txid, got %q", txid)
	}
	if got := p.LastValidatedInputCount(); got != 1 {
		t.Fatalf("LastValidatedInputCount() = %d, want 1 (non-vacuity witness)", got)
	}
}

// --- acceptance: a real compiled contract's deploy + call --------------------

func TestMockProvider_Broadcast_AcceptsRealDeployAndCall(t *testing.T) {
	src := `import { StatefulSmartContract } from 'runar-lang';
class Counter extends StatefulSmartContract {
  count: bigint;
  constructor(count: bigint) { super(count); this.count = count; }
  public inc(): void {
    this.count = this.count + 1n;
  }
}`
	tmp := t.TempDir() + "/Counter.runar.ts"
	if err := os.WriteFile(tmp, []byte(src), 0o644); err != nil {
		t.Fatal(err)
	}
	out, err := exec.Command("go", "run", "../../compilers/go", "--source", tmp).Output()
	if err != nil {
		t.Fatalf("compile Counter: %v", err)
	}
	var art RunarArtifact
	if err := json.Unmarshal(out, &art); err != nil {
		t.Fatalf("unmarshal artifact: %v", err)
	}

	signer, err := NewLocalSigner("0000000000000000000000000000000000000000000000000000000000000003")
	if err != nil {
		t.Fatalf("signer: %v", err)
	}
	addr, _ := signer.GetAddress()
	p := NewMockProvider("testnet")
	// A REAL P2PKH funding script for this signer — a bogus one (e.g.
	// 76a914 <20 zero bytes> 88ac) is not spendable by the signer's key and
	// the interpreter now says so.
	p.AddUtxo(addr, UTXO{
		Txid:        strings.Repeat("aa", 32),
		OutputIndex: 0,
		Satoshis:    500_000,
		Script:      BuildP2PKHScript(addr),
	})

	c := NewRunarContract(&art, []interface{}{int64(5)})
	if _, _, err := c.Deploy(p, signer, DeployOptions{Satoshis: 1_000}); err != nil {
		t.Fatalf("deploy REJECTED by the validating MockProvider: %v", err)
	}
	if _, _, err := c.Call("inc", nil, p, signer, nil); err != nil {
		t.Fatalf("call REJECTED by the validating MockProvider: %v", err)
	}
	if got := len(p.GetBroadcastedTxs()); got != 2 {
		t.Fatalf("expected 2 broadcasts (deploy+call), got %d", got)
	}
	// Non-vacuity: the call tx spends the contract continuation + a funding
	// coin, both known to the provider — so BOTH inputs were really executed.
	if got := p.LastValidatedInputCount(); got < 2 {
		t.Fatalf("call broadcast validated only %d input(s); expected >= 2 (contract + funding)", got)
	}
}

// --- the governed opt-out ----------------------------------------------------

func TestNewAlwaysAckMockProvider_SkipsValidation(t *testing.T) {
	p := NewAlwaysAckMockProvider("testnet")
	// Same tx the vacuity test above rejects.
	tx := buildOneInputTx(t, strings.Repeat("33", 32), 0, mockValidationAnyoneCanSpendHex, 10_000,
		"", 1_000, mockValidationAnyoneCanSpendHex)
	if _, err := p.Broadcast(tx); err != nil {
		t.Fatalf("always-ack provider must not validate; got %v", err)
	}
}

func TestMockProvider_DisableAndReEnableBroadcastValidation(t *testing.T) {
	p := NewMockProvider("testnet")
	tx := buildOneInputTx(t, strings.Repeat("33", 32), 0, mockValidationAnyoneCanSpendHex, 10_000,
		"", 1_000, mockValidationAnyoneCanSpendHex)

	if _, err := p.Broadcast(tx); err == nil {
		t.Fatalf("default provider must validate")
	}
	p.DisableBroadcastValidation()
	if _, err := p.Broadcast(tx); err != nil {
		t.Fatalf("after DisableBroadcastValidation the provider must ack: %v", err)
	}
	p.EnableBroadcastValidation(true)
	if _, err := p.Broadcast(tx); err == nil {
		t.Fatalf("after EnableBroadcastValidation(true) the provider must validate again")
	}
}
