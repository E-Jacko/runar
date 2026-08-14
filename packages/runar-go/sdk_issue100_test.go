package runar

import (
	"encoding/json"
	"os"
	"os/exec"
	"strings"
	"testing"

	"github.com/bsv-blockchain/go-sdk/transaction"
)

// Issue #100: terminal method reading variable-length (ByteString) state must
// receive _codePart in its unlocking script (the analogous TS bug dropped it in
// the finalize path). codePart is ~472 bytes → its push begins with PUSHDATA2
// (0x4d); without it the unlock would begin with the ~72-byte opSig push (0x48).
func TestIssue100_TerminalVarLenReadGetsCodePart(t *testing.T) {
	src := `import { StatefulSmartContract, assert, substr } from 'runar-lang';
import type { ByteString } from 'runar-lang';
class StateRead extends StatefulSmartContract {
  s: ByteString;
  constructor(s: ByteString) { super(s); this.s = s; }
  public update(ns: ByteString): void { this.s = ns; }
  public termCheck(expected: ByteString): void { assert(substr(this.s, 8n, 20n) === expected); }
}`
	tmp := t.TempDir() + "/StateRead.runar.ts"
	if err := os.WriteFile(tmp, []byte(src), 0o644); err != nil {
		t.Fatal(err)
	}
	out, err := exec.Command("go", "run", "../../compilers/go", "--source", tmp).Output()
	if err != nil {
		t.Fatalf("compile: %v", err)
	}
	var art RunarArtifact
	if err := json.Unmarshal(out, &art); err != nil {
		t.Fatalf("unmarshal: %v", err)
	}

	signer, _ := NewLocalSigner("0000000000000000000000000000000000000000000000000000000000000003")
	addr, _ := signer.GetAddress()
	provider := NewMockProvider("testnet")
	provider.AddUtxo(addr, UTXO{Txid: strings.Repeat("aa", 32), OutputIndex: 0, Satoshis: 500000, Script: BuildP2PKHScript(addr)})

	init := strings.Repeat("00", 8) + strings.Repeat("cc", 20)
	live := strings.Repeat("11", 8) + strings.Repeat("dd", 20)
	c := NewRunarContract(&art, []interface{}{init})
	if _, _, err := c.Deploy(provider, signer, DeployOptions{}); err != nil {
		t.Fatalf("deploy: %v", err)
	}
	if _, _, err := c.Call("update", []interface{}{live}, provider, signer, nil); err != nil {
		t.Fatalf("update: %v", err)
	}
	if _, _, err := c.Call("termCheck", []interface{}{strings.Repeat("dd", 20)}, provider, signer, nil); err != nil {
		t.Fatalf("termCheck: %v", err)
	}

	txs := provider.GetBroadcastedTxs()
	tx, err := transaction.NewTransactionFromHex(txs[len(txs)-1])
	if err != nil {
		t.Fatalf("parse tx: %v", err)
	}
	unlock := strings.ToLower(tx.Inputs[0].UnlockingScript.String())
	if !strings.HasPrefix(unlock, "4d") {
		t.Fatalf("termCheck unlock does not begin with PUSHDATA2 (codePart); got prefix %.6s — codePart was dropped (issue #100)", unlock)
	}
	t.Logf("termCheck unlock begins with codePart push (prefix %.6s) — #100 fixed", unlock)
}
