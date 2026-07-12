//go:build integration

package integration

import (
	"encoding/hex"
	"testing"

	"runar-integration/helpers"

	runar "github.com/icellan/runar/packages/runar-go"

	"github.com/bsv-blockchain/go-sdk/script"
	"github.com/bsv-blockchain/go-sdk/transaction"
)

// ---------------------------------------------------------------------------
// Audit finding #26 — missing consensus-finality negative coverage for the
// time-lock contract family.
//
// Every pre-existing Auction test (TestAuction_Close, TestAuction_WrongSigner_Rejected)
// deploys with deadline=0, which `extractLocktime(txPreimage) >= 0` always
// satisfies trivially — no test ever broadcasts a spend whose deadline is
// genuinely in the FUTURE relative to the live regtest chain tip and checks
// that the node's own consensus rules (not just the contract's script-level
// assert) actually reject it. The tests below close that gap.
//
// Background — issue #131 (now FIXED in the Go SDK as of this writing; see
// resolveInputSequence in packages/runar-go/sdk_calling.go / sdk_types.go):
// Bitcoin only enforces nLockTime against a transaction when at least one
// input's nSequence is non-final (< 0xffffffff). A transaction whose inputs
// are ALL final (0xffffffff) is accepted by IsFinalTx immediately, REGARDLESS
// of its nLockTime value — a contract's own
// `assert(extractLocktime(txPreimage) >= deadline)` is consensus-enforced
// ONLY when the spending tx also carries a non-final input sequence.
//
//   - TestAuction_CloseBeforeDeadline_FinalSequence_Accepted pins that raw
//     Bitcoin mechanism directly: a premature close with an all-final
//     sequence is accepted, proving the script-level assert alone is not a
//     time-lock.
//   - TestAuction_CloseBeforeDeadline_NonFinalSequence_Rejected is the
//     missing negative test itself: the SAME premature close, but with a
//     non-final input sequence, is correctly REJECTED by the node — proving
//     the auction contract's own locktime logic is sound when consensus
//     enforcement is actually engaged.
//   - TestAuction_CloseBeforeDeadline_SDKDefault_Rejected is the end-to-end
//     regression guard for issue #131's fix: RunarContract.Call with
//     CallOptions.Locktime set (Sequence left nil) must default to a
//     non-final input sequence, so a premature close through the SDK's own
//     default call path — the path every real caller uses — is rejected too.
// ---------------------------------------------------------------------------

// futureAuctionDeadline returns a deadline (block-height domain, far below
// the nLockTime UNIX-time threshold of 500_000_000) guaranteed to be ahead of
// the live regtest chain tip at the time this test runs.
func futureAuctionDeadline(t *testing.T) int64 {
	t.Helper()
	currentHeight, err := helpers.GetBlockCount()
	if err != nil {
		t.Fatalf("get block count: %v", err)
	}
	return int64(currentHeight) + 10_000
}

// buildRawCloseTx builds a raw (non-SDK) close() spend of a deployed auction
// UTXO, with the given nLockTime and input nSequence set BEFORE signing — so
// both the checkSig signature and the OP_PUSH_TX preimage commit to them.
// Returns the finished, signed transaction hex.
func buildRawCloseTx(t *testing.T, auctioneer *helpers.Wallet, utxo *helpers.UTXO, lockTime, sequence uint32) string {
	t.Helper()

	spendTx, err := helpers.BuildSpendTx(utxo, auctioneer.P2PKHScript(), 4500)
	if err != nil {
		t.Fatalf("build spend: %v", err)
	}
	spendTx.LockTime = lockTime
	spendTx.Inputs[0].SequenceNumber = sequence

	sigHex, err := helpers.SignInput(spendTx, 0, auctioneer.PrivKey)
	if err != nil {
		t.Fatalf("sign: %v", err)
	}
	sigBytes, _ := hex.DecodeString(sigHex)

	opPushTxSigHex, preimageHex, err := helpers.SignOpPushTx(spendTx, 0)
	if err != nil {
		t.Fatalf("op_push_tx: %v", err)
	}
	opPushTxSigBytes, _ := hex.DecodeString(opPushTxSigHex)
	preimageBytes, _ := hex.DecodeString(preimageHex)

	// Unlocking: <opPushTxSig> <sig> <txPreimage> <methodIndex=1> (close)
	unlockHex := helpers.EncodePushBytes(opPushTxSigBytes) +
		helpers.EncodePushBytes(sigBytes) +
		helpers.EncodePushBytes(preimageBytes) +
		helpers.EncodeMethodIndex(1)

	unlockScript, _ := script.NewFromHex(unlockHex)
	spendTx.Inputs[0].UnlockingScript = unlockScript

	return spendTx.Hex()
}

// TestAuction_CloseBeforeDeadline_FinalSequence_Accepted documents the raw
// Bitcoin consensus mechanism that made issue #131 dangerous: a close() spend
// whose nLockTime is set to a deadline that is genuinely in the future (far
// beyond the live regtest chain tip) is nonetheless ACCEPTED by the node when
// the input's nSequence is final (0xffffffff). The contract's own
// `assert(extractLocktime(preimage) >= deadline)` is satisfied (nLockTime ==
// deadline), so acceptance here is purely because an all-final sequence takes
// nLockTime out of consensus scope entirely — this is standard Bitcoin
// behavior, not itself a Rúnar bug, and it is why the auction's time-lock is
// only as strong as the sequence number on the spending transaction.
func TestAuction_CloseBeforeDeadline_FinalSequence_Accepted(t *testing.T) {
	auctioneer := helpers.NewWallet()
	bidder := helpers.NewWallet()

	deadline := futureAuctionDeadline(t)
	contract, _ := deployAuction(t, auctioneer, bidder, 1000, deadline)
	utxo := helpers.SDKUtxoToHelper(contract.GetCurrentUtxo())

	txHex := buildRawCloseTx(t, auctioneer, utxo, uint32(deadline), transaction.DefaultSequenceNumber)

	helpers.AssertTxAccepted(t, txHex)
}

// TestAuction_CloseBeforeDeadline_NonFinalSequence_Rejected is the missing
// negative test from audit finding #26. Same premature close as above (a
// deadline genuinely in the future, nLockTime == deadline), but with a
// non-final input sequence (0xfffffffe) so nLockTime is actually
// consensus-enforced. The node must REJECT it as non-final — the auction's
// time-lock holds when the transaction's sequence number actually engages
// Bitcoin's finality rule.
func TestAuction_CloseBeforeDeadline_NonFinalSequence_Rejected(t *testing.T) {
	auctioneer := helpers.NewWallet()
	bidder := helpers.NewWallet()

	deadline := futureAuctionDeadline(t)
	contract, _ := deployAuction(t, auctioneer, bidder, 1000, deadline)
	utxo := helpers.SDKUtxoToHelper(contract.GetCurrentUtxo())

	txHex := buildRawCloseTx(t, auctioneer, utxo, uint32(deadline), 0xfffffffe)

	helpers.AssertTxRejected(t, txHex)
}

// TestAuction_CloseBeforeDeadline_SDKDefault_Rejected is the end-to-end
// regression guard for issue #131's fix in the Go SDK. RunarContract.Call
// with CallOptions.Locktime set and Sequence left nil must default every
// input to a non-final sequence (see resolveInputSequence in
// packages/runar-go/sdk_calling.go), so a premature close (deadline still far
// in the future) submitted through the SDK's own default call path — the
// path every real caller uses, not just a hand-crafted raw tx — is rejected
// by the node. If this ever starts failing (txid returned, err == nil), the
// SDK has silently reverted to emitting all-final sequences and #131 is
// open again.
func TestAuction_CloseBeforeDeadline_SDKDefault_Rejected(t *testing.T) {
	auctioneer := helpers.NewWallet()
	bidder := helpers.NewWallet()

	deadline := futureAuctionDeadline(t)
	contract, _ := deployAuction(t, auctioneer, bidder, 1000, deadline)

	provider := helpers.NewBatchRPCProvider()
	defer provider.MineAll()
	signer, err := helpers.SDKSignerFromWallet(auctioneer)
	if err != nil {
		t.Fatalf("signer: %v", err)
	}

	lt := uint32(deadline)
	callOpts := &runar.CallOptions{
		Locktime: &lt,
		TerminalOutputs: []runar.TerminalOutput{
			{ScriptHex: auctioneer.P2PKHScript(), Satoshis: 4500},
		},
	}
	txid, _, err := contract.Call(
		"close",
		[]interface{}{nil}, // sig placeholder — auto-signed by SDK
		provider, signer, callOpts,
	)
	if err == nil {
		t.Fatalf("SECURITY REGRESSION (#131): premature close with a future deadline was ACCEPTED (txid=%s) via the SDK's default Call path — resolveInputSequence must default to a non-final nSequence whenever Locktime is set", txid)
	}
	t.Logf("SDK default call path correctly REJECTED premature close: %v", err)
}
