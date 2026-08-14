package runar

import (
	"encoding/json"
	"os"
	"os/exec"
	"strings"
	"testing"

	"github.com/bsv-blockchain/go-sdk/script/interpreter"
	"github.com/bsv-blockchain/go-sdk/transaction"
)

// Deep-review follow-on (SDK funds bug, separate from the C20/C27 compiler
// cluster and finding G1): on the stateful CALL path, the SDK built the
// state-continuation output at the SPENT INPUT's satoshis, ignoring an
// explicit this.addOutput(<N>, ...) amount that the ANF interpreter already
// records. A stateful method whose continuation is e.g. addOutput(1000, ...)
// therefore built a 1-sat continuation (the input value) -> the covenant's
// hashOutputs binding rejects the spend -> funds stranded.
//
// Finding G1 (already merged) reads the ANF-recorded satoshis but ONLY on
// the raw-output-PRESENT branch. This test pins the fix that generalizes it
// to the no-raw single-continuation path: when the ANF interpreter's ordered
// outputs are EXACTLY ONE entry of kind "state" (a single addOutput, no raw
// outputs), the continuation must use ITS satoshis, not the input value.
func TestCall_ContinuationSatoshis_DerivedFromSingleAddOutput(t *testing.T) {
	src := `import { StatefulSmartContract } from 'runar-lang';
class SatCounter extends StatefulSmartContract {
  count: bigint;
  constructor(count: bigint) { super(count); this.count = count; }
  public inc(): void {
    this.count = this.count + 1n;
    this.addOutput(1000n, this.count);
  }
}`
	tmp := t.TempDir() + "/SatCounter.runar.ts"
	if err := os.WriteFile(tmp, []byte(src), 0o644); err != nil {
		t.Fatal(err)
	}
	out, err := exec.Command("go", "run", "../../compilers/go", "--source", tmp).Output()
	if err != nil {
		t.Fatalf("compile SatCounter: %v", err)
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
	provider := NewMockProvider("testnet")
	provider.AddUtxo(addr, UTXO{
		Txid:        strings.Repeat("aa", 32),
		OutputIndex: 0,
		Satoshis:    500000,
		Script:      BuildP2PKHScript(addr),
	})

	// Deploy with count = 5, at the default (1 sat) amount — the call's
	// addOutput(1000) must OVERRIDE this, not inherit it.
	c := NewRunarContract(&art, []interface{}{int64(5)})
	if _, _, err := c.Deploy(provider, signer, DeployOptions{Satoshis: 1}); err != nil {
		t.Fatalf("deploy: %v", err)
	}

	// Call inc() WITHOUT a satoshis option — the SDK must derive 1000 from the
	// contract's this.addOutput(1000, ...), not default to the 1-sat input value.
	if _, _, err := c.Call("inc", nil, provider, signer, nil); err != nil {
		t.Fatalf("call inc: %v", err)
	}
	if got := anfToBigInt(c.state["count"]).Int64(); got != 6 {
		t.Fatalf("state count = %d after inc, want 6", got)
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

	if len(callTx.Outputs) == 0 {
		t.Fatalf("call tx has no outputs")
	}
	if got := callTx.Outputs[0].Satoshis; got != 1000 {
		t.Fatalf("continuation output[0] satoshis = %d, want 1000 (must derive from "+
			"this.addOutput(1000, ...), not default to the 1-sat spent input)", got)
	}

	// The covenant proof. Replay input 0 through the go-sdk script interpreter
	// WITH full transaction context (the same engine packages/runar-go/script_vm.go
	// wraps). OP_PUSH_TX authenticates the preimage against the real spending
	// sighash, and the state-check OP_VERIFY reconstructs the continuation output
	// and compares its hash against the preimage's hashOutputs. Pre-fix (a 1-sat
	// continuation instead of 1000) that hash mismatches and Execute errors.
	prevOut := deployTx.Outputs[0]
	execErr := interpreter.NewEngine().Execute(
		interpreter.WithTx(callTx, 0, prevOut),
		interpreter.WithAfterGenesis(),
		interpreter.WithAfterChronicle(),
		interpreter.WithForkID(),
	)
	if execErr != nil {
		t.Fatalf("covenant spend REJECTED by go-sdk interpreter (continuation satoshis bug not fixed): %v", execErr)
	}
}
