//! BRC-100 wallet integration — WalletClient trait, WalletProvider, and WalletSigner.
//!
//! Provides a bridge between a BRC-100 compatible wallet and the Rúnar SDK's
//! Provider and Signer traits. The wallet handles key derivation, signing, and
//! UTXO management, while the provider layer handles ARC broadcast and overlay
//! transaction lookups.

use std::collections::HashMap;
use bsv::transaction::Transaction as BsvTransaction;
use sha2::{Sha256, Digest};
use ripemd::Ripemd160;
use serde_json::Value;
use super::types::{TransactionData, TxInput, TxOutput, Utxo};
use super::provider::Provider;
use super::signer::Signer;
use super::script_utils::build_p2pkh_script;

// ---------------------------------------------------------------------------
// WalletClient trait
// ---------------------------------------------------------------------------

/// Output specification for a wallet action.
#[derive(Debug, Clone)]
pub struct WalletActionOutput {
    /// Hex-encoded locking script.
    pub locking_script: String,
    /// Amount in satoshis.
    pub satoshis: i64,
    /// Human-readable description for the output.
    pub output_description: String,
    /// Wallet basket to tag the output in.
    pub basket: Option<String>,
    /// Tags for the output within the basket.
    pub tags: Option<Vec<String>>,
}

/// Result of a wallet action (create transaction).
#[derive(Debug, Clone)]
pub struct WalletActionResult {
    /// Transaction ID of the created transaction.
    pub txid: String,
    /// Raw transaction bytes (Atomic BEEF or raw hex), if available.
    pub tx: Option<Vec<u8>>,
}

/// A single output returned from wallet UTXO listing.
#[derive(Debug, Clone)]
pub struct WalletOutput {
    /// Outpoint in "txid.vout" format.
    pub outpoint: String,
    /// Amount in satoshis.
    pub satoshis: i64,
    /// Hex-encoded locking script, if requested.
    pub locking_script: Option<String>,
    /// Whether this output is spendable.
    pub spendable: bool,
}

/// Abstraction over a BRC-100 compatible wallet.
///
/// Implementations bridge to a concrete wallet (e.g. MetaNet Client, browser
/// extension, or a mock for testing). All methods are synchronous in this Rust
/// SDK; async wallet backends should be wrapped at the integration boundary.
pub trait WalletClient {
    /// Get the public key for a given protocol ID and key ID.
    ///
    /// `protocol_id` is a tuple of (security_level, protocol_name).
    /// Returns the hex-encoded compressed public key (33 bytes = 66 hex chars).
    fn get_public_key(
        &self,
        protocol_id: &(u32, &str),
        key_id: &str,
    ) -> Result<String, String>;

    /// Create a signature over a pre-computed hash.
    ///
    /// The wallet signs `hash_to_sign` directly (no additional hashing).
    /// Returns the DER-encoded signature bytes.
    fn create_signature(
        &self,
        hash_to_sign: &[u8],
        protocol_id: &(u32, &str),
        key_id: &str,
    ) -> Result<Vec<u8>, String>;

    /// Create a wallet action (a transaction with specified outputs).
    ///
    /// The wallet handles input selection, signing, and fee calculation internally.
    fn create_action(
        &self,
        description: &str,
        outputs: &[WalletActionOutput],
    ) -> Result<WalletActionResult, String>;

    /// List outputs from a wallet basket, filtered by tags.
    ///
    /// Returns up to `limit` outputs that match all specified tags.
    fn list_outputs(
        &self,
        basket: &str,
        tags: &[&str],
        limit: usize,
    ) -> Result<Vec<WalletOutput>, String>;
}

// ---------------------------------------------------------------------------
// WalletProvider options
// ---------------------------------------------------------------------------

/// Options for constructing a WalletProvider.
pub struct WalletProviderOptions<W: WalletClient> {
    /// The BRC-100 wallet client.
    pub wallet: W,
    /// A WalletSigner derived from the same wallet.
    pub signer: WalletSigner<W>,
    /// Wallet basket name for UTXO management.
    pub basket: String,
    /// Tag for funding UTXOs within the basket (default: "funding").
    pub funding_tag: Option<String>,
    /// ARC broadcast endpoint (default: "https://arc.gorillapool.io").
    pub arc_url: Option<String>,
    /// Overlay service URL for tx lookups (optional).
    pub overlay_url: Option<String>,
    /// Network (default: "mainnet").
    pub network: Option<String>,
    /// Fee rate in sats/KB (default: 100).
    pub fee_rate: Option<i64>,
}

// ---------------------------------------------------------------------------
// WalletProvider
// ---------------------------------------------------------------------------

/// Provider implementation that uses a BRC-100 wallet for UTXO management
/// and GorillaPool ARC for broadcast.
///
/// Mirrors the TypeScript `WalletProvider` from `runar-sdk`.
pub struct WalletProvider<W: WalletClient> {
    wallet: W,
    protocol_id: (u32, String),
    key_id: String,
    basket: String,
    funding_tag: String,
    arc_url: String,
    overlay_url: Option<String>,
    network: String,
    fee_rate: i64,
    tx_cache: HashMap<String, String>,
    /// Cached public key from the wallet (lazily computed).
    cached_pub_key: Option<String>,
}

impl<W: WalletClient> WalletProvider<W> {
    /// Create a new WalletProvider.
    ///
    /// `protocol_id` and `key_id` are used for key derivation from the wallet.
    pub fn new(
        wallet: W,
        protocol_id: (u32, String),
        key_id: String,
        basket: String,
        funding_tag: Option<String>,
        arc_url: Option<String>,
        overlay_url: Option<String>,
        network: Option<String>,
        fee_rate: Option<i64>,
    ) -> Self {
        WalletProvider {
            wallet,
            protocol_id,
            key_id,
            basket,
            funding_tag: funding_tag.unwrap_or_else(|| "funding".to_string()),
            arc_url: arc_url.unwrap_or_else(|| "https://arc.gorillapool.io".to_string()),
            overlay_url,
            network: network.unwrap_or_else(|| "mainnet".to_string()),
            fee_rate: fee_rate.unwrap_or(100),
            tx_cache: HashMap::new(),
            cached_pub_key: None,
        }
    }

    /// Cache a raw transaction hex by its txid (for EF parent lookups).
    pub fn cache_tx(&mut self, txid: &str, raw_hex: &str) {
        self.tx_cache.insert(txid.to_string(), raw_hex.to_string());
    }

    /// Get the derived public key from the wallet, caching the result.
    fn get_derived_pub_key(&mut self) -> Result<String, String> {
        if let Some(ref pk) = self.cached_pub_key {
            return Ok(pk.clone());
        }
        let pid = (self.protocol_id.0, self.protocol_id.1.as_str());
        let pk = self.wallet.get_public_key(&pid, &self.key_id)?;
        self.cached_pub_key = Some(pk.clone());
        Ok(pk)
    }

    /// Ensure there are enough P2PKH funding UTXOs in the wallet basket.
    /// Creates a new funding UTXO via the wallet if the balance is insufficient.
    pub fn ensure_funding(&mut self, min_satoshis: i64) -> Result<(), String> {
        let pub_key = self.get_derived_pub_key()?;
        let expected_script = build_p2pkh_script(&pub_key);
        let tags: Vec<&str> = vec![&self.funding_tag];

        let outputs = self.wallet.list_outputs(&self.basket, &tags, 100)?;

        let total_available: i64 = outputs
            .iter()
            .filter(|o| {
                o.spendable
                    && o.locking_script
                        .as_ref()
                        .map_or(false, |s| s == &expected_script)
            })
            .map(|o| o.satoshis)
            .sum();

        if total_available >= min_satoshis {
            return Ok(());
        }

        let fund_amount = min_satoshis - total_available;
        let funding_tag = self.funding_tag.clone();
        let basket = self.basket.clone();

        let result = self.wallet.create_action(
            "Runar contract funding",
            &[WalletActionOutput {
                locking_script: expected_script,
                satoshis: fund_amount,
                output_description: "Funding UTXO".to_string(),
                basket: Some(basket),
                tags: Some(vec![funding_tag]),
            }],
        )?;

        // Cache the funding tx for future EF lookups
        if !result.txid.is_empty() {
            if let Some(ref tx_bytes) = result.tx {
                let raw_hex = bytes_to_hex(tx_bytes);
                self.tx_cache.insert(result.txid.clone(), raw_hex);
            }
        }

        Ok(())
    }
}

impl<W: WalletClient> Provider for WalletProvider<W> {
    fn get_utxos(&self, _address: &str) -> Result<Vec<Utxo>, String> {
        let pub_key = self.cached_pub_key.as_ref().ok_or_else(|| {
            "WalletProvider: public key not cached. Call ensure_funding() or get_derived_pub_key() first.".to_string()
        })?;
        let expected_script = build_p2pkh_script(pub_key);
        let funding_tag = self.funding_tag.clone();
        let tags: Vec<&str> = vec![&funding_tag];

        let outputs = self.wallet.list_outputs(&self.basket, &tags, 100)?;

        let mut utxos = Vec::new();
        for out in outputs {
            if !out.spendable {
                continue;
            }
            if let Some(ref script) = out.locking_script {
                if script != &expected_script {
                    continue;
                }
            } else {
                continue;
            }

            // Parse outpoint "txid.vout"
            let parts: Vec<&str> = out.outpoint.splitn(2, '.').collect();
            if parts.len() != 2 {
                continue;
            }
            let txid = parts[0].to_string();
            let output_index: u32 = parts[1].parse().unwrap_or(0);

            utxos.push(Utxo {
                txid,
                output_index,
                satoshis: out.satoshis,
                script: out.locking_script.unwrap_or_default(),
            });
        }

        Ok(utxos)
    }

    fn broadcast(&mut self, tx: &BsvTransaction) -> Result<String, String> {
        let raw_hex = tx.to_hex().map_err(|e| format!("WalletProvider broadcast: to_hex failed: {}", e))?;
        let raw_bytes = hex_to_bytes(&raw_hex)?;
        let txid = compute_txid(&raw_bytes);

        // POST to ARC as application/octet-stream.
        // R1 (Wave 1) — surface ARC failures as Err so callers can distinguish
        // accepted from rejected broadcasts. The previous code returned
        // Ok(synthetic_txid) on HTTP non-2xx and on network errors, masking
        // real failures (mainnet ARC 461 from GorillaPool was the trigger).
        let arc_endpoint = format!("{}/v1/tx", self.arc_url);
        let response = ureq::post(&arc_endpoint)
            .set("Content-Type", "application/octet-stream")
            .send_bytes(&raw_bytes);

        let resp = match response {
            Ok(r) => r,
            Err(ureq::Error::Status(code, r)) => {
                let body = r.into_string().unwrap_or_default();
                return Err(format!(
                    "WalletProvider broadcast: ARC HTTP {} from {}: {}",
                    code, arc_endpoint, body
                ));
            }
            Err(e) => {
                return Err(format!(
                    "WalletProvider broadcast: ARC network error against {}: {}",
                    arc_endpoint, e
                ));
            }
        };

        let status_code = resp.status();
        let body = resp.into_string().unwrap_or_default();
        if !(200..300).contains(&status_code) {
            return Err(format!(
                "WalletProvider broadcast: ARC HTTP {} from {}: {}",
                status_code, arc_endpoint, body
            ));
        }

        let json: Value = serde_json::from_str(&body).map_err(|e| {
            format!(
                "WalletProvider broadcast: ARC returned 2xx but body is not JSON ({}): {}",
                e, body
            )
        })?;

        let arc_txid = json
            .get("txid")
            .and_then(|v| v.as_str())
            .ok_or_else(|| {
                format!(
                    "WalletProvider broadcast: ARC accepted but returned no txid; body: {}",
                    body
                )
            })?
            .to_string();

        // Sanity check: ARC's txid must match what we computed locally.
        if arc_txid != txid {
            return Err(format!(
                "WalletProvider broadcast: ARC txid {} != local txid {} (body: {})",
                arc_txid, txid, body
            ));
        }

        self.tx_cache.insert(arc_txid.clone(), raw_hex);
        Ok(arc_txid)
    }

    fn get_transaction(&self, txid: &str) -> Result<TransactionData, String> {
        // R2 (Wave 1) — parse the cached raw bytes so callers receive populated
        // inputs/outputs. Previously this returned empty inputs and outputs
        // even on cache hit, which broke RunarContract::from_txid (which
        // indexes tx.outputs[output_index]) on every deployed stateful contract.
        if let Some(raw) = self.tx_cache.get(txid) {
            let raw_hex = raw.clone();
            let raw_bytes = hex_to_bytes(&raw_hex)?;
            let parsed = parse_raw_tx(&raw_bytes)?;
            let inputs = parsed
                .inputs
                .into_iter()
                .map(|i| {
                    let mut prev_txid_hex = String::with_capacity(64);
                    for b in i.prev_txid_bytes.iter().rev() {
                        prev_txid_hex.push_str(&format!("{:02x}", b));
                    }
                    TxInput {
                        txid: prev_txid_hex,
                        output_index: i.prev_output_index,
                        script: String::new(),
                        sequence: i.sequence,
                    }
                })
                .collect();
            let outputs = parsed
                .outputs
                .into_iter()
                .map(|o| {
                    let mut script_hex = String::with_capacity(o.script.len() * 2);
                    for b in &o.script {
                        script_hex.push_str(&format!("{:02x}", b));
                    }
                    TxOutput {
                        satoshis: o.satoshis as i64,
                        script: script_hex,
                    }
                })
                .collect();
            return Ok(TransactionData {
                txid: txid.to_string(),
                version: parsed.version,
                inputs,
                outputs,
                locktime: parsed.locktime,
                raw: Some(raw_hex),
            });
        }

        // Cache miss — preserve upstream's fallback behavior: return an
        // empty TransactionData with raw: None. Callers that need the parsed
        // transaction will then fall back to get_raw_transaction (overlay).
        Ok(TransactionData {
            txid: txid.to_string(),
            version: 1,
            inputs: vec![],
            outputs: vec![],
            locktime: 0,
            raw: None,
        })
    }

    fn get_contract_utxo(&self, _script_hash: &str) -> Result<Option<Utxo>, String> {
        // Contract UTXOs typically come from overlay services or app logic.
        Ok(None)
    }

    fn get_network(&self) -> &str {
        &self.network
    }

    fn get_fee_rate(&self) -> Result<i64, String> {
        Ok(self.fee_rate)
    }

    fn get_raw_transaction(&self, txid: &str) -> Result<String, String> {
        // Check local cache
        if let Some(raw) = self.tx_cache.get(txid) {
            return Ok(raw.clone());
        }

        // Try overlay service if configured
        if let Some(ref overlay_url) = self.overlay_url {
            let url = format!("{}/api/tx/{}/hex", overlay_url, txid);
            if let Ok(resp) = ureq::get(&url).call() {
                if let Ok(body) = resp.into_string() {
                    return Ok(body.trim().to_string());
                }
            }
        }

        Err(format!(
            "WalletProvider: could not fetch tx {} (not in cache or overlay)",
            txid
        ))
    }
}

// ---------------------------------------------------------------------------
// WalletSigner
// ---------------------------------------------------------------------------

/// Signer implementation that delegates to a BRC-100 wallet.
///
/// Computes BIP-143 sighash locally, then sends the pre-hashed digest to the
/// wallet for ECDSA signing. Mirrors the TypeScript `WalletSigner`.
pub struct WalletSigner<W: WalletClient> {
    wallet: W,
    protocol_id: (u32, String),
    key_id: String,
    cached_pub_key: Option<String>,
}

impl<W: WalletClient> WalletSigner<W> {
    /// Create a new WalletSigner.
    ///
    /// `protocol_id` is the BRC-100 protocol ID tuple, e.g. `(2, "my app")`.
    /// `key_id` is the key derivation ID, e.g. `"1"`.
    pub fn new(wallet: W, protocol_id: (u32, String), key_id: String) -> Self {
        WalletSigner {
            wallet,
            protocol_id,
            key_id,
            cached_pub_key: None,
        }
    }

    /// Sign a raw sighash directly, without computing BIP-143 from a
    /// transaction context. Useful for multi-signer flows where the sighash
    /// has already been computed by `prepare_call()`.
    ///
    /// Returns the DER-encoded signature hex (without sighash flag byte).
    pub fn sign_hash(&self, sighash: &[u8]) -> Result<String, String> {
        let pid = (self.protocol_id.0, self.protocol_id.1.as_str());
        let der_bytes = self.wallet.create_signature(sighash, &pid, &self.key_id)?;
        Ok(bytes_to_hex(&der_bytes))
    }
}

impl<W: WalletClient> Signer for WalletSigner<W> {
    fn get_public_key(&self) -> Result<String, String> {
        if let Some(ref pk) = self.cached_pub_key {
            return Ok(pk.clone());
        }
        let pid = (self.protocol_id.0, self.protocol_id.1.as_str());
        self.wallet.get_public_key(&pid, &self.key_id)
    }

    fn get_address(&self) -> Result<String, String> {
        let pub_key_hex = self.get_public_key()?;
        let pub_key_bytes = hex_to_bytes(&pub_key_hex)?;

        // hash160 = RIPEMD160(SHA256(pubkey))
        let sha_hash = Sha256::digest(&pub_key_bytes);
        let pkh = Ripemd160::digest(sha_hash);

        // Return as 40-char hex (raw pubkey hash)
        Ok(bytes_to_hex(&pkh))
    }

    fn sign(
        &self,
        tx_hex: &str,
        input_index: usize,
        subscript: &str,
        satoshis: i64,
        sig_hash_type: Option<u32>,
    ) -> Result<String, String> {
        let flag = sig_hash_type.unwrap_or(SIGHASH_ALL_FORKID);

        // 1. Compute BIP-143 sighash from the transaction context
        let tx_bytes = hex_to_bytes(tx_hex)?;
        let tx = parse_raw_tx(&tx_bytes)?;

        if input_index >= tx.inputs.len() {
            return Err(format!(
                "WalletSigner: input index {} out of range (tx has {} inputs)",
                input_index,
                tx.inputs.len()
            ));
        }

        let subscript_bytes = hex_to_bytes(subscript)?;
        let sighash = bip143_sighash(&tx, input_index, &subscript_bytes, satoshis as u64, flag);

        // 2. Send to wallet for signing
        let pid = (self.protocol_id.0, self.protocol_id.1.as_str());
        let der_bytes = self.wallet.create_signature(&sighash, &pid, &self.key_id)?;

        // 3. Append sighash flag byte
        let mut result = der_bytes;
        result.push(flag as u8);
        Ok(bytes_to_hex(&result))
    }
}

// ---------------------------------------------------------------------------
// DeployWithWallet options
// ---------------------------------------------------------------------------

/// Options for deploying a contract via a BRC-100 wallet.
#[derive(Debug, Clone)]
pub struct DeployWithWalletOptions {
    /// Satoshis to lock in the contract output (default: 1).
    pub satoshis: Option<i64>,
    /// Human-readable description for the wallet action.
    pub description: Option<String>,
}

impl Default for DeployWithWalletOptions {
    fn default() -> Self {
        DeployWithWalletOptions {
            satoshis: None,
            description: None,
        }
    }
}

/// Deploy a contract using a BRC-100 wallet.
///
/// Creates a wallet action with the contract's locking script as the output.
/// Returns the (txid, output_index) of the deployed contract.
///
/// This is a standalone function rather than a method on RunarContract to avoid
/// generic type parameter complications. The caller should update the contract's
/// UTXO tracking after deployment.
pub fn deploy_with_wallet<W: WalletClient>(
    wallet: &W,
    basket: &str,
    locking_script: &str,
    contract_name: &str,
    options: Option<&DeployWithWalletOptions>,
) -> Result<(String, usize), String> {
    let satoshis = options
        .and_then(|o| o.satoshis)
        .unwrap_or(1);
    let description = options
        .and_then(|o| o.description.clone())
        .unwrap_or_else(|| "Runar contract deployment".to_string());

    let result = wallet.create_action(
        &description,
        &[WalletActionOutput {
            locking_script: locking_script.to_string(),
            satoshis,
            output_description: format!("Deploy {}", contract_name),
            basket: Some(basket.to_string()),
            tags: None,
        }],
    )?;

    let txid = result.txid;
    // Output index defaults to 0 (the wallet places our output first).
    let output_index = 0;

    Ok((txid, output_index))
}

// ---------------------------------------------------------------------------
// BIP-143 sighash computation (local copy for module independence)
// ---------------------------------------------------------------------------

const SIGHASH_ALL_FORKID: u32 = 0x41;

fn sha256d(data: &[u8]) -> [u8; 32] {
    let first = Sha256::digest(data);
    let second = Sha256::digest(first);
    let mut out = [0u8; 32];
    out.copy_from_slice(&second);
    out
}

fn bip143_sighash(
    tx: &ParsedTx,
    input_index: usize,
    subscript: &[u8],
    satoshis: u64,
    sig_hash_type: u32,
) -> [u8; 32] {
    let mut prevouts_data = Vec::new();
    for inp in &tx.inputs {
        prevouts_data.extend_from_slice(&inp.prev_txid_bytes);
        prevouts_data.extend_from_slice(&inp.prev_output_index.to_le_bytes());
    }
    let hash_prevouts = sha256d(&prevouts_data);

    let mut sequence_data = Vec::new();
    for inp in &tx.inputs {
        sequence_data.extend_from_slice(&inp.sequence.to_le_bytes());
    }
    let hash_sequence = sha256d(&sequence_data);

    let mut outputs_data = Vec::new();
    for out in &tx.outputs {
        outputs_data.extend_from_slice(&out.satoshis.to_le_bytes());
        write_var_int(&mut outputs_data, out.script.len() as u64);
        outputs_data.extend_from_slice(&out.script);
    }
    let hash_outputs = sha256d(&outputs_data);

    let input = &tx.inputs[input_index];
    let mut preimage = Vec::new();
    preimage.extend_from_slice(&tx.version.to_le_bytes());
    preimage.extend_from_slice(&hash_prevouts);
    preimage.extend_from_slice(&hash_sequence);
    preimage.extend_from_slice(&input.prev_txid_bytes);
    preimage.extend_from_slice(&input.prev_output_index.to_le_bytes());
    write_var_int(&mut preimage, subscript.len() as u64);
    preimage.extend_from_slice(subscript);
    preimage.extend_from_slice(&satoshis.to_le_bytes());
    preimage.extend_from_slice(&input.sequence.to_le_bytes());
    preimage.extend_from_slice(&hash_outputs);
    preimage.extend_from_slice(&tx.locktime.to_le_bytes());
    preimage.extend_from_slice(&sig_hash_type.to_le_bytes());

    sha256d(&preimage)
}

// ---------------------------------------------------------------------------
// Minimal raw transaction parser
// ---------------------------------------------------------------------------

struct ParsedInput {
    prev_txid_bytes: [u8; 32],
    prev_output_index: u32,
    sequence: u32,
}

struct ParsedOutput {
    satoshis: u64,
    script: Vec<u8>,
}

struct ParsedTx {
    version: u32,
    inputs: Vec<ParsedInput>,
    outputs: Vec<ParsedOutput>,
    locktime: u32,
}

fn parse_raw_tx(bytes: &[u8]) -> Result<ParsedTx, String> {
    let mut offset = 0;

    let read = |offset: &mut usize, n: usize| -> Result<&[u8], String> {
        if *offset + n > bytes.len() {
            return Err("WalletSigner: transaction hex too short".to_string());
        }
        let slice = &bytes[*offset..*offset + n];
        *offset += n;
        Ok(slice)
    };

    let read_u32_le = |offset: &mut usize| -> Result<u32, String> {
        let b = read(offset, 4)?;
        Ok(u32::from_le_bytes([b[0], b[1], b[2], b[3]]))
    };

    let read_u64_le = |offset: &mut usize| -> Result<u64, String> {
        let b = read(offset, 8)?;
        Ok(u64::from_le_bytes([
            b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7],
        ]))
    };

    let read_var_int = |offset: &mut usize| -> Result<u64, String> {
        let first = read(offset, 1)?[0];
        match first {
            0..=0xfc => Ok(first as u64),
            0xfd => {
                let b = read(offset, 2)?;
                Ok(u16::from_le_bytes([b[0], b[1]]) as u64)
            }
            0xfe => {
                let b = read(offset, 4)?;
                Ok(u32::from_le_bytes([b[0], b[1], b[2], b[3]]) as u64)
            }
            0xff => {
                let b = read(offset, 8)?;
                Ok(u64::from_le_bytes([
                    b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7],
                ]))
            }
        }
    };

    let version = read_u32_le(&mut offset)?;

    let input_count = read_var_int(&mut offset)?;
    let mut inputs = Vec::new();
    for _ in 0..input_count {
        let txid_slice = read(&mut offset, 32)?;
        let mut prev_txid_bytes = [0u8; 32];
        prev_txid_bytes.copy_from_slice(txid_slice);
        let prev_output_index = read_u32_le(&mut offset)?;
        let script_len = read_var_int(&mut offset)?;
        let _ = read(&mut offset, script_len as usize)?;
        let sequence = read_u32_le(&mut offset)?;
        inputs.push(ParsedInput {
            prev_txid_bytes,
            prev_output_index,
            sequence,
        });
    }

    let output_count = read_var_int(&mut offset)?;
    let mut outputs = Vec::new();
    for _ in 0..output_count {
        let satoshis = read_u64_le(&mut offset)?;
        let script_len = read_var_int(&mut offset)?;
        let script = read(&mut offset, script_len as usize)?.to_vec();
        outputs.push(ParsedOutput { satoshis, script });
    }

    let locktime = read_u32_le(&mut offset)?;

    Ok(ParsedTx {
        version,
        inputs,
        outputs,
        locktime,
    })
}

fn write_var_int(buf: &mut Vec<u8>, n: u64) {
    if n < 0xfd {
        buf.push(n as u8);
    } else if n <= 0xffff {
        buf.push(0xfd);
        buf.extend_from_slice(&(n as u16).to_le_bytes());
    } else if n <= 0xffff_ffff {
        buf.push(0xfe);
        buf.extend_from_slice(&(n as u32).to_le_bytes());
    } else {
        buf.push(0xff);
        buf.extend_from_slice(&n.to_le_bytes());
    }
}

// ---------------------------------------------------------------------------
// Hex helpers
// ---------------------------------------------------------------------------

fn hex_to_bytes(hex: &str) -> Result<Vec<u8>, String> {
    if hex.len() % 2 != 0 {
        return Err("odd-length hex string".to_string());
    }
    (0..hex.len())
        .step_by(2)
        .map(|i| {
            u8::from_str_radix(&hex[i..i + 2], 16)
                .map_err(|_| format!("invalid hex at position {}", i))
        })
        .collect()
}

fn bytes_to_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{:02x}", b)).collect()
}

/// Compute the txid (double SHA-256 of raw tx, reversed) from raw tx bytes.
fn compute_txid(raw_bytes: &[u8]) -> String {
    let hash = sha256d(raw_bytes);
    // txid is displayed in reversed byte order
    let mut reversed = hash;
    reversed.reverse();
    bytes_to_hex(&reversed)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::RefCell;

    // -----------------------------------------------------------------------
    // MockWalletClient
    // -----------------------------------------------------------------------

    /// A mock WalletClient for testing.
    struct MockWalletClient {
        public_key: String,
        signature: Vec<u8>,
        outputs: RefCell<Vec<WalletOutput>>,
        actions: RefCell<Vec<String>>,
    }

    impl MockWalletClient {
        fn new() -> Self {
            // Use a known test public key (generator point, compressed)
            MockWalletClient {
                public_key: "0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798".to_string(),
                // Minimal DER-encoded signature (mock): 30 + len + 02 + r_len + r + 02 + s_len + s
                signature: vec![
                    0x30, 0x44, // SEQUENCE, 68 bytes
                    0x02, 0x20, // INTEGER, 32 bytes (r)
                    0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,
                    0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,
                    0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,
                    0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,
                    0x02, 0x20, // INTEGER, 32 bytes (s)
                    0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02,
                    0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02,
                    0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02,
                    0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02,
                ],
                outputs: RefCell::new(Vec::new()),
                actions: RefCell::new(Vec::new()),
            }
        }

        fn add_output(&self, outpoint: &str, satoshis: i64, script: &str) {
            self.outputs.borrow_mut().push(WalletOutput {
                outpoint: outpoint.to_string(),
                satoshis,
                locking_script: Some(script.to_string()),
                spendable: true,
            });
        }
    }

    impl WalletClient for MockWalletClient {
        fn get_public_key(
            &self,
            _protocol_id: &(u32, &str),
            _key_id: &str,
        ) -> Result<String, String> {
            Ok(self.public_key.clone())
        }

        fn create_signature(
            &self,
            _hash_to_sign: &[u8],
            _protocol_id: &(u32, &str),
            _key_id: &str,
        ) -> Result<Vec<u8>, String> {
            Ok(self.signature.clone())
        }

        fn create_action(
            &self,
            description: &str,
            outputs: &[WalletActionOutput],
        ) -> Result<WalletActionResult, String> {
            self.actions.borrow_mut().push(description.to_string());
            let mock_txid = format!("{:0>64}", format!("action{}", self.actions.borrow().len()));
            // Verify outputs were passed
            assert!(!outputs.is_empty(), "create_action should have at least one output");
            Ok(WalletActionResult {
                txid: mock_txid,
                tx: None,
            })
        }

        fn list_outputs(
            &self,
            _basket: &str,
            _tags: &[&str],
            _limit: usize,
        ) -> Result<Vec<WalletOutput>, String> {
            Ok(self.outputs.borrow().clone())
        }
    }

    // -----------------------------------------------------------------------
    // WalletSigner tests
    // -----------------------------------------------------------------------

    #[test]
    fn wallet_signer_get_public_key() {
        let wallet = MockWalletClient::new();
        let signer = WalletSigner::new(wallet, (2, "test".to_string()), "1".to_string());
        let pk = signer.get_public_key().unwrap();
        assert_eq!(pk.len(), 66);
        assert!(pk.starts_with("02") || pk.starts_with("03"));
    }

    #[test]
    fn wallet_signer_get_address() {
        let wallet = MockWalletClient::new();
        let signer = WalletSigner::new(wallet, (2, "test".to_string()), "1".to_string());
        let addr = signer.get_address().unwrap();
        // Address is a 40-char hex pubkey hash
        assert_eq!(addr.len(), 40);
        assert!(addr.chars().all(|c| c.is_ascii_hexdigit()));
    }

    #[test]
    fn wallet_signer_sign_returns_hex_with_sighash_byte() {
        let wallet = MockWalletClient::new();
        let signer = WalletSigner::new(wallet, (2, "test".to_string()), "1".to_string());

        // Build a minimal transaction for signing
        let tx_hex = format!(
            "01000000\
             01\
             {}\
             00000000\
             00\
             ffffffff\
             01\
             5000000000000000\
             01\
             51\
             00000000",
            "00".repeat(32)
        );

        let sig = signer.sign(&tx_hex, 0, "51", 100, None).unwrap();
        assert!(sig.chars().all(|c| c.is_ascii_hexdigit()));
        // Should end with sighash byte 0x41
        assert!(
            sig.ends_with("41"),
            "signature should end with sighash byte 41, got: {}",
            sig
        );
    }

    #[test]
    fn wallet_signer_sign_starts_with_der_prefix() {
        let wallet = MockWalletClient::new();
        let signer = WalletSigner::new(wallet, (2, "test".to_string()), "1".to_string());

        let tx_hex = format!(
            "01000000\
             01\
             {}\
             00000000\
             00\
             ffffffff\
             01\
             5000000000000000\
             01\
             51\
             00000000",
            "00".repeat(32)
        );

        let sig = signer.sign(&tx_hex, 0, "51", 100, None).unwrap();
        assert!(
            sig.starts_with("30"),
            "signature should start with DER prefix 30, got: {}",
            sig
        );
    }

    #[test]
    fn wallet_signer_sign_hash_returns_der() {
        let wallet = MockWalletClient::new();
        let signer = WalletSigner::new(wallet, (2, "test".to_string()), "1".to_string());

        let fake_hash = [0u8; 32];
        let sig = signer.sign_hash(&fake_hash).unwrap();
        assert!(sig.starts_with("30"));
        // sign_hash does NOT append sighash byte
        assert!(!sig.ends_with("41"));
    }

    #[test]
    fn wallet_signer_sign_rejects_out_of_range_input() {
        let wallet = MockWalletClient::new();
        let signer = WalletSigner::new(wallet, (2, "test".to_string()), "1".to_string());

        let tx_hex = format!(
            "01000000\
             01\
             {}\
             00000000\
             00\
             ffffffff\
             01\
             5000000000000000\
             01\
             51\
             00000000",
            "00".repeat(32)
        );

        let result = signer.sign(&tx_hex, 5, "51", 100, None);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("out of range"));
    }

    // -----------------------------------------------------------------------
    // WalletProvider tests
    // -----------------------------------------------------------------------

    #[test]
    fn wallet_provider_get_network() {
        let wallet = MockWalletClient::new();
        let provider = WalletProvider::new(
            wallet,
            (2, "test".to_string()),
            "1".to_string(),
            "my-basket".to_string(),
            None, None, None, None, None,
        );
        assert_eq!(provider.get_network(), "mainnet");
    }

    #[test]
    fn wallet_provider_get_fee_rate() {
        let wallet = MockWalletClient::new();
        let provider = WalletProvider::new(
            wallet,
            (2, "test".to_string()),
            "1".to_string(),
            "my-basket".to_string(),
            None, None, None, None, Some(200),
        );
        assert_eq!(provider.get_fee_rate().unwrap(), 200);
    }

    #[test]
    fn wallet_provider_default_fee_rate() {
        let wallet = MockWalletClient::new();
        let provider = WalletProvider::new(
            wallet,
            (2, "test".to_string()),
            "1".to_string(),
            "my-basket".to_string(),
            None, None, None, None, None,
        );
        assert_eq!(provider.get_fee_rate().unwrap(), 100);
    }

    #[test]
    fn wallet_provider_cache_tx() {
        let wallet = MockWalletClient::new();
        let mut provider = WalletProvider::new(
            wallet,
            (2, "test".to_string()),
            "1".to_string(),
            "my-basket".to_string(),
            None, None, None, None, None,
        );

        let txid = "aa".repeat(32);
        let raw_hex = "deadbeef";
        provider.cache_tx(&txid, raw_hex);

        let raw = provider.get_raw_transaction(&txid).unwrap();
        assert_eq!(raw, raw_hex);
    }

    #[test]
    fn wallet_provider_get_raw_transaction_not_found() {
        let wallet = MockWalletClient::new();
        let provider = WalletProvider::new(
            wallet,
            (2, "test".to_string()),
            "1".to_string(),
            "my-basket".to_string(),
            None, None, None, None, None,
        );

        let result = provider.get_raw_transaction(&"ff".repeat(32));
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("not in cache"));
    }

    #[test]
    fn wallet_provider_get_utxos_filters_by_script() {
        let wallet = MockWalletClient::new();
        let pub_key = wallet.public_key.clone();
        let expected_script = build_p2pkh_script(&pub_key);

        // Add matching and non-matching outputs
        wallet.add_output(
            &format!("{}.0", "aa".repeat(32)),
            50_000,
            &expected_script,
        );
        wallet.add_output(
            &format!("{}.1", "bb".repeat(32)),
            30_000,
            "76a914ffffffffffffffffffffffffffffffffffffffff88ac",
        );

        let mut provider = WalletProvider::new(
            wallet,
            (2, "test".to_string()),
            "1".to_string(),
            "my-basket".to_string(),
            None, None, None, None, None,
        );

        // Prime the pub key cache
        provider.get_derived_pub_key().unwrap();

        let utxos = provider.get_utxos("ignored").unwrap();
        assert_eq!(utxos.len(), 1);
        assert_eq!(utxos[0].satoshis, 50_000);
        assert_eq!(utxos[0].txid, "aa".repeat(32));
        assert_eq!(utxos[0].output_index, 0);
    }

    #[test]
    fn wallet_provider_ensure_funding_creates_action_when_insufficient() {
        let wallet = MockWalletClient::new();
        let pub_key = wallet.public_key.clone();
        let expected_script = build_p2pkh_script(&pub_key);

        // Add one small UTXO
        wallet.add_output(
            &format!("{}.0", "aa".repeat(32)),
            10_000,
            &expected_script,
        );

        let mut provider = WalletProvider::new(
            wallet,
            (2, "test".to_string()),
            "1".to_string(),
            "my-basket".to_string(),
            None, None, None, None, None,
        );

        // Request more than available
        provider.ensure_funding(50_000).unwrap();

        // Verify a create_action was called
        assert_eq!(provider.wallet.actions.borrow().len(), 1);
        assert_eq!(
            provider.wallet.actions.borrow()[0],
            "Runar contract funding"
        );
    }

    #[test]
    fn wallet_provider_ensure_funding_skips_when_sufficient() {
        let wallet = MockWalletClient::new();
        let pub_key = wallet.public_key.clone();
        let expected_script = build_p2pkh_script(&pub_key);

        // Add a large UTXO
        wallet.add_output(
            &format!("{}.0", "aa".repeat(32)),
            100_000,
            &expected_script,
        );

        let mut provider = WalletProvider::new(
            wallet,
            (2, "test".to_string()),
            "1".to_string(),
            "my-basket".to_string(),
            None, None, None, None, None,
        );

        // Request less than available
        provider.ensure_funding(50_000).unwrap();

        // No create_action should have been called
        assert_eq!(provider.wallet.actions.borrow().len(), 0);
    }

    #[test]
    fn wallet_provider_get_contract_utxo_returns_none() {
        let wallet = MockWalletClient::new();
        let provider = WalletProvider::new(
            wallet,
            (2, "test".to_string()),
            "1".to_string(),
            "my-basket".to_string(),
            None, None, None, None, None,
        );
        let result = provider.get_contract_utxo("somehash").unwrap();
        assert!(result.is_none());
    }

    // -----------------------------------------------------------------------
    // deploy_with_wallet tests
    // -----------------------------------------------------------------------

    #[test]
    fn deploy_with_wallet_creates_action() {
        let wallet = MockWalletClient::new();
        let (txid, output_index) = deploy_with_wallet(
            &wallet,
            "my-basket",
            "76a91400000000000000000000000000000000000000008888ac",
            "TestContract",
            None,
        )
        .unwrap();

        assert_eq!(txid.len(), 64);
        assert_eq!(output_index, 0);
        assert_eq!(wallet.actions.borrow().len(), 1);
        assert_eq!(
            wallet.actions.borrow()[0],
            "Runar contract deployment"
        );
    }

    #[test]
    fn deploy_with_wallet_custom_options() {
        let wallet = MockWalletClient::new();
        let opts = DeployWithWalletOptions {
            satoshis: Some(5000),
            description: Some("My custom deploy".to_string()),
        };
        let (txid, _) = deploy_with_wallet(
            &wallet,
            "my-basket",
            "51",
            "MyContract",
            Some(&opts),
        )
        .unwrap();

        assert!(!txid.is_empty());
        assert_eq!(wallet.actions.borrow().len(), 1);
        assert_eq!(wallet.actions.borrow()[0], "My custom deploy");
    }

    // -----------------------------------------------------------------------
    // Hex helper tests
    // -----------------------------------------------------------------------

    #[test]
    fn compute_txid_produces_64_hex_chars() {
        let fake_tx = vec![0u8; 100];
        let txid = compute_txid(&fake_tx);
        assert_eq!(txid.len(), 64);
        assert!(txid.chars().all(|c| c.is_ascii_hexdigit()));
    }

    #[test]
    fn wallet_provider_get_transaction_from_cache() {
        let wallet = MockWalletClient::new();
        let mut provider = WalletProvider::new(
            wallet,
            (2, "test".to_string()),
            "1".to_string(),
            "my-basket".to_string(),
            None, None, None, None, None,
        );

        let txid = "cc".repeat(32);
        provider.cache_tx(&txid, "01000000deadbeef");
        let tx = provider.get_transaction(&txid).unwrap();
        assert_eq!(tx.txid, txid);
        assert_eq!(tx.raw.as_deref(), Some("01000000deadbeef"));
    }

    #[test]
    fn wallet_provider_get_transaction_fallback() {
        let wallet = MockWalletClient::new();
        let provider = WalletProvider::new(
            wallet,
            (2, "test".to_string()),
            "1".to_string(),
            "my-basket".to_string(),
            None, None, None, None, None,
        );

        let txid = "dd".repeat(32);
        let tx = provider.get_transaction(&txid).unwrap();
        assert_eq!(tx.txid, txid);
        assert!(tx.raw.is_none());
    }
}
