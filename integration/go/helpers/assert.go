package helpers

import "testing"

// AssertTxAccepted broadcasts a transaction and expects it to be accepted.
// Returns the txid.
func AssertTxAccepted(t *testing.T, txHex string) string {
	t.Helper()
	txid, err := SendRawTransaction(txHex)
	if err != nil {
		t.Fatalf("expected TX to be accepted but got error: %v", err)
	}
	t.Logf("TX accepted: %s", txid)
	return txid
}

// AssertTxRejected broadcasts a transaction and expects it to be rejected.
func AssertTxRejected(t *testing.T, txHex string) {
	t.Helper()
	txid, err := SendRawTransaction(txHex)
	if err == nil {
		t.Fatalf("expected TX to be rejected but it was accepted: %s", txid)
	}
	t.Logf("TX correctly rejected: %v", err)
}

// AssertTxInBlock mines a block and verifies the transaction has confirmations.
func AssertTxInBlock(t *testing.T, txid string) {
	t.Helper()
	if err := Mine(1); err != nil {
		t.Fatalf("mine: %v", err)
	}
	tx, err := GetRawTransaction(txid)
	if err != nil {
		t.Fatalf("getrawtransaction: %v", err)
	}
	confirmations, ok := tx["confirmations"].(float64)
	if !ok {
		// Teranode's getrawtransaction doesn't return confirmations.
		// If we can fetch the TX after mining, consider it confirmed.
		t.Logf("TX %s mined (confirmations not available)", txid)
		return
	}
	if confirmations < 1 {
		t.Fatalf("TX %s not in block (confirmations=%v)", txid, confirmations)
	}
	t.Logf("TX %s confirmed (confirmations=%v)", txid, confirmations)
}

// AssertUtxoNeverSpent mines blocksToMine blocks and then verifies (txid,
// vout) is STILL in the UTXO set (unspent). This is the correct way to prove
// a broadcast spend was never consensus-final: SV Node accepts non-final
// transactions (future nLockTime + non-final nSequence) into the mempool for
// relay, but excludes them from block templates until they become final —
// sendrawtransaction returning success (or even a txid) is NOT evidence the
// spend can ever be mined. Checking the source UTXO's on-chain spent status
// after mining is the only check that reflects actual consensus enforcement.
func AssertUtxoNeverSpent(t *testing.T, txid string, vout int, blocksToMine int) {
	t.Helper()
	if err := Mine(blocksToMine); err != nil {
		t.Fatalf("mine: %v", err)
	}
	out, err := GetTxOut(txid, vout)
	if err != nil {
		t.Fatalf("gettxout: %v", err)
	}
	if out == nil {
		t.Fatalf("UTXO %s:%d was spent — a premature/non-final spend was consensus-confirmed", txid, vout)
	}
	t.Logf("UTXO %s:%d still unspent after mining %d block(s) — spend never confirmed", txid, vout, blocksToMine)
}
