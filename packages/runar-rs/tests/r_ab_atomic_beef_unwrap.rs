//! R-AB regression — `hex_to_bsv_tx` detects AtomicBEEF and preserves the
//! source-transaction chain on each input.
//!
//! Uses only upstream-existing deps: `bsv-sdk = 0.1.72` (pinned via Cargo.lock,
//! shipped under crate name `bsv`).
//!
//! Strategy:
//!   1. Build a parent tx (P) and a child tx (C) that spends P.
//!   2. Wrap (P, C) in an AtomicBEEF envelope (Beef V1, with merkle path for P,
//!      atomic_txid = C.id()).
//!   3. Hex-encode and call `hex_to_bsv_tx`.
//!   4. Assert: the returned tx is C, and `C.inputs[0].source_transaction`
//!      is `Some(<parent>)`.
//!
//!   Sanity test: passing a raw tx hex (no BEEF magic) still parses via the
//!   legacy `BsvTransaction::from_hex` fallback.

use bsv::script::locking_script::LockingScript;
use bsv::script::unlocking_script::UnlockingScript;
use bsv::transaction::beef::{Beef, BEEF_V1};
use bsv::transaction::beef_tx::BeefTx;
use bsv::transaction::merkle_path::{MerklePath, MerklePathLeaf};
use bsv::transaction::transaction::Transaction as BsvTransaction;
use bsv::transaction::transaction_input::TransactionInput;
use bsv::transaction::transaction_output::TransactionOutput;

use runar_lang::sdk::contract::hex_to_bsv_tx;

fn make_parent() -> BsvTransaction {
    let mut tx = BsvTransaction::new();
    tx.outputs.push(TransactionOutput {
        satoshis: Some(10_000),
        locking_script: LockingScript::from_hex(&format!("76a914{}88ac", "00".repeat(20)))
            .unwrap(),
        change: false,
    });
    tx
}

fn make_child(parent_txid: &str) -> BsvTransaction {
    let mut tx = BsvTransaction::new();
    tx.inputs.push(TransactionInput {
        source_transaction: None,
        source_txid: Some(parent_txid.to_string()),
        source_output_index: 0,
        unlocking_script: Some(UnlockingScript::from_hex("00").unwrap()),
        sequence: 0xFFFFFFFF,
    });
    tx.outputs.push(TransactionOutput {
        satoshis: Some(9_500),
        locking_script: LockingScript::from_hex(&format!("76a914{}88ac", "11".repeat(20)))
            .unwrap(),
        change: false,
    });
    tx
}

/// A single-leaf merkle path "proving" `parent_txid` at block_height 800_000.
/// We don't need the merkle root to actually verify — `hex_to_bsv_tx` calls
/// `Beef::from_hex` → `into_transaction`, which doesn't verify SPV; it only
/// parses the envelope and links source transactions.
fn trivial_merkle_path(block_height: u32, parent_txid: &str) -> MerklePath {
    MerklePath {
        block_height,
        path: vec![vec![MerklePathLeaf {
            offset: 0,
            hash: Some(parent_txid.to_string()),
            txid: true,
            duplicate: false,
        }]],
    }
}

#[test]
fn r_ab_hex_to_bsv_tx_unwraps_atomic_beef_and_links_parent() {
    let parent = make_parent();
    let parent_txid = parent.id().expect("parent id");
    let child = make_child(&parent_txid);
    let child_txid = child.id().expect("child id");

    // Build a BEEF V1 envelope with parent + child, and mark it atomic on child.
    let mut beef = Beef::new(BEEF_V1);
    beef.bumps
        .push(trivial_merkle_path(800_000, &parent_txid));
    beef.txs
        .push(BeefTx::from_tx(parent.clone(), Some(0)).expect("BeefTx parent"));
    beef.txs
        .push(BeefTx::from_tx(child.clone(), None).expect("BeefTx child"));
    beef.atomic_txid = Some(child_txid.clone());

    let atomic_beef_hex = beef.to_hex().expect("Beef::to_hex must succeed");

    let parsed = hex_to_bsv_tx(&atomic_beef_hex)
        .expect("R-AB regression: hex_to_bsv_tx must parse AtomicBEEF bytes");

    assert_eq!(
        parsed.id().expect("parsed.id"),
        child_txid,
        "R-AB regression: unwrapped tx must be the AtomicBEEF subject (child), not parent"
    );
    assert_eq!(parsed.inputs.len(), 1, "child must have 1 input");
    assert!(
        parsed.inputs[0].source_transaction.is_some(),
        "R-AB regression: child.input[0].source_transaction must be Some(parent) after \
         AtomicBEEF unwrap. This is the load-bearing assertion — downstream broadcast \
         skips the parent-fetch loop when source_transaction is populated."
    );
    let linked_parent = parsed.inputs[0]
        .source_transaction
        .as_ref()
        .unwrap();
    assert_eq!(
        linked_parent.id().expect("linked parent id"),
        parent_txid,
        "linked source_transaction must be the BEEF-attached parent"
    );
}

#[test]
fn r_ab_hex_to_bsv_tx_falls_back_to_raw_tx_when_no_beef_magic() {
    // Raw tx (1 input, 1 output) — no BEEF magic prefix, should fall through
    // to BsvTransaction::from_hex unchanged.
    let raw_hex = format!(
        "01000000\
         01{}00000000\
         00ffffffff\
         01e803000000000000\
         00\
         00000000",
        "00".repeat(32)
    );
    let parsed = hex_to_bsv_tx(&raw_hex)
        .expect("hex_to_bsv_tx must still parse raw tx hex (no BEEF magic) unchanged");
    assert_eq!(parsed.inputs.len(), 1);
    assert_eq!(parsed.outputs.len(), 1);
    // Raw tx has no embedded source transaction.
    assert!(
        parsed.inputs[0].source_transaction.is_none(),
        "raw tx fallback must NOT synthesize a source_transaction"
    );
}
