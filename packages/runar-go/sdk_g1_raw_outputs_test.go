package runar

import (
	"encoding/json"
	"os/exec"
	"strings"
	"testing"

	"github.com/bsv-blockchain/go-sdk/script/interpreter"
	"github.com/bsv-blockchain/go-sdk/transaction"
)

// Deep-review finding G1 (P1) — spending a method that calls
// this.addRawOutput(...) via the SDK must build a transaction whose outputs
// match the covenant's hashOutputs continuation, or input 0's OP_VERIFY fails
// and the funds are stuck.
//
// The shipped example RawOutputTest.sendToScript emits, in SOURCE order:
//
//	this.addRawOutput(1000, scriptBytes);  // raw output FIRST
//	this.count = this.count + 1;
//	this.addOutput(0, this.count);         // state continuation SECOND (0 sats)
//
// The compiler folds BOTH into the continuation hashOutputs in that order, so
// the on-chain output layout the covenant reconstructs is
// [raw(1000, scriptBytes)] [stateContinuation(0)] [change]. The SDK must emit
// exactly that ordering; emitting only the state continuation (the pre-fix
// behaviour) mismatches hashOutputs and the auto-injected state-check OP_VERIFY
// rejects.
//
// This test deploys + calls sendToScript via MockProvider, then replays input
// 0 through the go-sdk script interpreter WITH full transaction context (the
// same engine packages/runar-go/script_vm.go wraps) to PROVE the covenant
// verifies, and asserts the built tx's outputs are in the required order.
func TestG1_AddRawOutputSpendIsCovenantValidInSourceOrder(t *testing.T) {
	// Compile the shipped example to a full artifact via the Go compiler CLI
	// (same pattern as sdk_issue100_test.go).
	out, err := exec.Command("go", "run", "../../compilers/go", "--source",
		"../../examples/go/add-raw-output/RawOutputTest.runar.go").Output()
	if err != nil {
		t.Fatalf("compile RawOutputTest: %v", err)
	}
	var art RunarArtifact
	if err := json.Unmarshal(out, &art); err != nil {
		t.Fatalf("unmarshal artifact: %v", err)
	}

	// The caller-supplied raw locking script: a plain P2PKH (76a914 <20> 88ac).
	rawScript := "76a914" + strings.Repeat("ab", 20) + "88ac"

	signer, err := NewLocalSigner("0000000000000000000000000000000000000000000000000000000000000003")
	if err != nil {
		t.Fatalf("signer: %v", err)
	}
	addr, _ := signer.GetAddress()
	provider := NewMockProvider("testnet")
	provider.AddUtxo(addr, UTXO{
		Txid:        strings.Repeat("aa", 32),
		OutputIndex: 0,
		Satoshis:    500000,
		Script:      "76a914" + strings.Repeat("00", 20) + "88ac",
	})

	// Deploy with count = 0.
	c := NewRunarContract(&art, []interface{}{int64(0)})
	if _, _, err := c.Deploy(provider, signer, DeployOptions{Satoshis: 50000}); err != nil {
		t.Fatalf("deploy: %v", err)
	}

	// Call sendToScript(rawScript).
	if _, _, err := c.Call("sendToScript", []interface{}{rawScript}, provider, signer, nil); err != nil {
		t.Fatalf("call sendToScript: %v", err)
	}

	// State advanced 0 -> 1 (this.count = this.count + 1).
	if got := anfToBigInt(c.state["count"]).Int64(); got != 1 {
		t.Fatalf("state count = %d after sendToScript, want 1", got)
	}

	txs := provider.GetBroadcastedTxs()
	if len(txs) != 2 {
		t.Fatalf("expected 2 broadcasts (deploy+call), got %d", len(txs))
	}
	deployTx, err := transaction.NewTransactionFromHex(txs[0])
	if err != nil {
		t.Fatalf("parse deploy tx: %v", err)
	}
	callTx, err := transaction.NewTransactionFromHex(txs[1])
	if err != nil {
		t.Fatalf("parse call tx: %v", err)
	}

	// --- Output ordering: [0] raw(1000), [1] state(0), [2] change. ---
	if len(callTx.Outputs) != 3 {
		t.Fatalf("expected 3 outputs [raw][state][change], got %d", len(callTx.Outputs))
	}

	// [0] raw output: 1000 sats, script == the caller-supplied bytes.
	if got := callTx.Outputs[0].Satoshis; got != 1000 {
		t.Fatalf("output[0] (raw) satoshis = %d, want 1000", got)
	}
	if got := strings.ToLower(callTx.Outputs[0].LockingScript.String()); got != rawScript {
		t.Fatalf("output[0] (raw) script = %s, want %s", got, rawScript)
	}

	// [1] state continuation: 0 sats, codePart + OP_RETURN (6a) + serialized count.
	if got := callTx.Outputs[1].Satoshis; got != 0 {
		t.Fatalf("output[1] (state continuation) satoshis = %d, want 0", got)
	}
	stateScript := strings.ToLower(callTx.Outputs[1].LockingScript.String())
	if stateScript == rawScript {
		t.Fatalf("output[1] must be the state continuation, not the raw script")
	}
	if !strings.Contains(stateScript, "6a") {
		t.Fatalf("output[1] state continuation should carry an OP_RETURN (6a); got %s", stateScript)
	}

	// [2] change: a P2PKH output (76a9..88ac) carrying the remainder.
	changeScript := strings.ToLower(callTx.Outputs[2].LockingScript.String())
	if !strings.HasPrefix(changeScript, "76a914") || !strings.HasSuffix(changeScript, "88ac") {
		t.Fatalf("output[2] change not P2PKH: %s", changeScript)
	}
	if callTx.Outputs[2].Satoshis == 0 {
		t.Fatalf("output[2] change must be > 0")
	}

	// The SDK tracks the continuation UTXO at its REAL index (1, not 0 — the raw
	// output precedes it) and its real value (0).
	if c.currentUtxo == nil {
		t.Fatalf("currentUtxo not tracked after call")
	}
	if c.currentUtxo.OutputIndex != 1 {
		t.Fatalf("currentUtxo.OutputIndex = %d, want 1 (raw output precedes the continuation)", c.currentUtxo.OutputIndex)
	}
	if c.currentUtxo.Satoshis != 0 {
		t.Fatalf("currentUtxo.Satoshis = %d, want 0", c.currentUtxo.Satoshis)
	}
	if strings.ToLower(c.currentUtxo.Script) != stateScript {
		t.Fatalf("currentUtxo.Script does not match the continuation output[1]")
	}

	// --- The covenant proof. Replay input 0 through the go-sdk script
	// interpreter WITH full tx context. OP_CHECKSIG (OP_PUSH_TX) authenticates
	// the pushed preimage against the real spending sighash, and the state-check
	// OP_VERIFY reconstructs [raw(1000)][state(0)][change] and compares its hash
	// against the preimage's hashOutputs. Pre-fix (state continuation alone at
	// output 0) that hash mismatches and this Execute returns an error.
	prevOut := deployTx.Outputs[0]
	execErr := interpreter.NewEngine().Execute(
		interpreter.WithTx(callTx, 0, prevOut),
		interpreter.WithAfterGenesis(),
		interpreter.WithAfterChronicle(),
		interpreter.WithForkID(),
	)
	if execErr != nil {
		t.Fatalf("covenant spend REJECTED by go-sdk interpreter (finding G1 not fixed): %v", execErr)
	}
}
