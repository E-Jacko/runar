//! Regression tests for R1 + R2 — WalletProvider error surfacing + transaction parse.
//!
//! Uses ONLY upstream-existing deps:
//!   - `std::net::TcpListener` for hosting a tiny HTTP server that returns
//!     HTTP 461 (R1) or refuses the connection (R1-network-failure).
//!   - `bsv::transaction::Transaction` to construct a known raw tx hex.
//!   - `runar_lang::sdk::wallet::{WalletProvider, WalletClient, ...}` and
//!     `runar_lang::sdk::provider::Provider` directly.
//!
//! Strategy:
//!   R1a (HTTP 461): bind a TcpListener on 127.0.0.1:<random>, hand-craft
//!     an HTTP 461 response, point `arc_url` at it, call broadcast, assert
//!     Err containing "461".
//!   R1b (network failure): point `arc_url` at a port that has nothing
//!     listening, assert broadcast returns Err.
//!   R2 (cache hit): seed tx_cache via `cache_tx()` with a known raw tx
//!     hex (1 input + 1 output). Call get_transaction. Assert
//!     inputs.len() == 1 and outputs.len() == 1 with populated values.

use std::io::{Read, Write};
use std::net::TcpListener;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::thread;
use std::time::Duration;

use bsv::transaction::Transaction as BsvTransaction;

use runar_lang::sdk::provider::Provider;
use runar_lang::sdk::wallet::{
    WalletActionOutput, WalletActionResult, WalletClient, WalletOutput, WalletProvider,
};

// ---------------------------------------------------------------------------
// Trivial WalletClient stub — never called by R1/R2 tests.
// ---------------------------------------------------------------------------

struct NoopWalletClient;

impl WalletClient for NoopWalletClient {
    fn get_public_key(
        &self,
        _protocol_id: &(u32, &str),
        _key_id: &str,
    ) -> Result<String, String> {
        Ok(format!("03{}", "00".repeat(32)))
    }

    fn create_signature(
        &self,
        _hash_to_sign: &[u8],
        _protocol_id: &(u32, &str),
        _key_id: &str,
    ) -> Result<Vec<u8>, String> {
        Ok(vec![0; 71])
    }

    fn create_action(
        &self,
        _description: &str,
        _outputs: &[WalletActionOutput],
    ) -> Result<WalletActionResult, String> {
        Err("NoopWalletClient::create_action not implemented".to_string())
    }

    fn list_outputs(
        &self,
        _basket: &str,
        _tags: &[&str],
        _limit: usize,
    ) -> Result<Vec<WalletOutput>, String> {
        Ok(vec![])
    }
}

fn make_provider(arc_url: String) -> WalletProvider<NoopWalletClient> {
    WalletProvider::new(
        NoopWalletClient,
        (1, "test".to_string()),
        "k1".to_string(),
        "test-basket".to_string(),
        Some("funding".to_string()),
        Some(arc_url),
        None,
        Some("testnet".to_string()),
        Some(100),
    )
}

// ---------------------------------------------------------------------------
// Known raw tx (1 input, 1 output)
// ---------------------------------------------------------------------------

fn known_raw_tx_hex() -> String {
    let mut hex = String::new();
    hex.push_str("01000000"); // version 1
    hex.push_str("01"); // 1 input
    hex.push_str(&"00".repeat(32)); // prev_hash (32 bytes)
    hex.push_str("00000000"); // prev vout 0
    hex.push_str("00"); // unlocking script length 0
    hex.push_str("ffffffff"); // sequence
    hex.push_str("01"); // 1 output
    hex.push_str("e803000000000000"); // satoshis = 1000, little-endian
    hex.push_str("00"); // locking script length 0
    hex.push_str("00000000"); // locktime 0
    hex
}

fn known_raw_tx_bsv() -> BsvTransaction {
    BsvTransaction::from_hex(&known_raw_tx_hex())
        .expect("known_raw_tx_hex must parse as a BSV Transaction")
}

// ---------------------------------------------------------------------------
// Tiny HTTP server returning a fixed status + body, then shuts down.
// ---------------------------------------------------------------------------

fn start_http_server_returning(
    status_line: &'static str,
    body: &'static str,
) -> (String, Arc<AtomicBool>) {
    let listener = TcpListener::bind("127.0.0.1:0").expect("bind 127.0.0.1:0");
    let local_addr = listener.local_addr().expect("local_addr");
    let url = format!("http://{}", local_addr);

    let stop = Arc::new(AtomicBool::new(false));
    let stop_thread = stop.clone();

    listener
        .set_nonblocking(true)
        .expect("set_nonblocking");

    thread::spawn(move || loop {
        if stop_thread.load(Ordering::SeqCst) {
            break;
        }
        match listener.accept() {
            Ok((mut socket, _)) => {
                socket
                    .set_read_timeout(Some(Duration::from_millis(500)))
                    .ok();
                let mut buf = [0u8; 4096];
                let _ = socket.read(&mut buf);
                let resp = format!(
                    "{}\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{}",
                    status_line,
                    body.len(),
                    body
                );
                let _ = socket.write_all(resp.as_bytes());
                let _ = socket.flush();
            }
            Err(ref e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                thread::sleep(Duration::from_millis(20));
            }
            Err(_) => break,
        }
    });

    thread::sleep(Duration::from_millis(50));
    (url, stop)
}

// ---------------------------------------------------------------------------
// R1 — broadcast must surface ARC errors as Err
// ---------------------------------------------------------------------------

#[test]
fn r1_broadcast_returns_err_on_http_461() {
    let (url, stop) = start_http_server_returning(
        "HTTP/1.1 461 Unauthorized",
        r#"{"detail":"Script evaluated without error but finished with a false/empty top stack element"}"#,
    );

    let mut provider = make_provider(url);
    let tx = known_raw_tx_bsv();

    let result = provider.broadcast(&tx);

    stop.store(true, Ordering::SeqCst);

    assert!(
        result.is_err(),
        "R1 regression: broadcast() must return Err on ARC HTTP 461, got Ok({:?})",
        result
    );
    let err = result.unwrap_err();
    assert!(
        err.contains("461"),
        "R1 regression: error must mention status code 461; got: {}",
        err
    );
}

#[test]
fn r1_broadcast_returns_err_on_network_failure() {
    // Bind a listener then immediately drop it — guaranteed-closed port.
    let listener = TcpListener::bind("127.0.0.1:0").expect("bind");
    let addr = listener.local_addr().expect("local_addr");
    drop(listener);
    let url = format!("http://{}", addr);

    let mut provider = make_provider(url);
    let tx = known_raw_tx_bsv();

    let result = provider.broadcast(&tx);

    assert!(
        result.is_err(),
        "R1 regression: broadcast() must return Err on connection refused, got Ok({:?})",
        result
    );
}

// ---------------------------------------------------------------------------
// R2 — get_transaction must populate inputs and outputs from cache.
// ---------------------------------------------------------------------------

#[test]
fn r2_get_transaction_populates_inputs_and_outputs_from_cache() {
    let mut provider = make_provider("http://127.0.0.1:1".to_string());
    let raw_hex = known_raw_tx_hex();
    let tx = known_raw_tx_bsv();
    let txid = tx.id().expect("tx.id");

    provider.cache_tx(&txid, &raw_hex);

    let result = provider
        .get_transaction(&txid)
        .expect("R2 regression: get_transaction must succeed on cache hit");

    assert_eq!(result.txid, txid, "returned txid must match input");
    assert_eq!(
        result.version, 1,
        "version must be parsed (not the hardcoded 1)"
    );
    assert_eq!(
        result.inputs.len(),
        1,
        "R2 regression: get_transaction must populate inputs from raw bytes (not empty)"
    );
    assert_eq!(
        result.outputs.len(),
        1,
        "R2 regression: get_transaction must populate outputs from raw bytes (not empty)"
    );
    assert_eq!(
        result.outputs[0].satoshis, 1000,
        "R2 regression: output satoshis must be parsed (1000 from raw bytes)"
    );
    assert!(
        result.raw.is_some(),
        "raw field should still be Some (the cached raw hex)"
    );
}

#[test]
fn r2_get_transaction_cache_miss_preserves_upstream_fallback() {
    // Locking note: the patch INTENTIONALLY does NOT change cache-miss behavior.
    // Upstream returns Ok(TransactionData { ..., raw: None }) on cache miss,
    // and downstream callers (e.g. broadcaster fetch-loop) may depend on that
    // shape. This test locks the fallback in place so a future "make cache
    // miss return Err" regression is caught immediately.
    let provider = make_provider("http://127.0.0.1:1".to_string());
    let unknown_txid = "a".repeat(64);
    let result = provider
        .get_transaction(&unknown_txid)
        .expect("cache miss must still return Ok (upstream-preserved fallback)");
    assert!(result.raw.is_none(), "raw must be None on cache miss");
    assert!(result.inputs.is_empty());
    assert!(result.outputs.is_empty());
}
