//! Independent OFFICIAL crypto known-answer tests.
//!
//! Unlike `runtime_vectors.rs` (cross-SDK goldens the tiers agree on), the
//! vectors here are copied verbatim from external authorities — the BLAKE3
//! team's own reference test file and RFC 6979 — and are NOT re-derived from
//! any Runar tier. They guard the BUG-101 failure mode (a primitive
//! "validated" only against self-produced, wrong goldens).
//!
//! Sources live in the `_source` field of each vendored JSON:
//!   conformance/runtime-vectors/blake3-official-kat.json  (BLAKE3-team/BLAKE3)
//!   conformance/runtime-vectors/ecdsa-rfc6979.json        (RFC 6979 A.2.5/A.2.6)

use serde::Deserialize;
use std::fs;
use std::path::PathBuf;

use runar_lang::p256::verify_ecdsa_p256;
use runar_lang::p384::verify_ecdsa_p384;
use runar_lang::prelude::blake3_hash;

fn vectors_dir() -> PathBuf {
    let mut dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    loop {
        let candidate = dir.join("conformance/runtime-vectors");
        if candidate.is_dir() {
            return candidate;
        }
        if !dir.pop() {
            panic!(
                "could not locate conformance/runtime-vectors walking up from {}",
                env!("CARGO_MANIFEST_DIR")
            );
        }
    }
}

fn read_kat<T: for<'de> Deserialize<'de>>(name: &str) -> T {
    let path = vectors_dir().join(name);
    let data =
        fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {}", path.display(), e));
    serde_json::from_str(&data).unwrap_or_else(|e| panic!("parse {}: {}", path.display(), e))
}

fn from_hex(s: &str) -> Vec<u8> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).expect("invalid hex digit"))
        .collect()
}

fn to_hex(b: &[u8]) -> String {
    let mut out = String::with_capacity(b.len() * 2);
    for byte in b {
        out.push_str(&format!("{:02x}", byte));
    }
    out
}

// ---------------------------------------------------------------------------
// BLAKE3 — official reference vectors (BLAKE3-team/BLAKE3 test_vectors.json)
// ---------------------------------------------------------------------------

#[derive(Deserialize)]
struct Blake3OfficialVector {
    input_len: usize,
    input: String,
    expected: String,
}

#[derive(Deserialize)]
struct Blake3OfficialKat {
    blake3_hash_official: Vec<Blake3OfficialVector>,
}

#[test]
fn official_kat_blake3_hash() {
    let kat: Blake3OfficialKat = read_kat("blake3-official-kat.json");
    assert!(
        !kat.blake3_hash_official.is_empty(),
        "blake3-official-kat.json carries no vectors"
    );
    for v in &kat.blake3_hash_official {
        let input = from_hex(&v.input);
        assert_eq!(
            input.len(),
            v.input_len,
            "input_len={} but decoded {} bytes",
            v.input_len,
            input.len()
        );
        let got = to_hex(&blake3_hash(&input));
        assert_eq!(
            got, v.expected,
            "blake3_hash(len={}) disagrees with official BLAKE3 KAT",
            v.input_len
        );
    }
}

// ---------------------------------------------------------------------------
// ECDSA P-256 / P-384 — RFC 6979 deterministic-ECDSA vectors
// ---------------------------------------------------------------------------

#[derive(Deserialize)]
struct EcdsaVector {
    name: String,
    curve: String,
    message_ascii: String,
    qx: String,
    qy: String,
    r: String,
    s: String,
    source: String,
}

#[derive(Deserialize)]
struct EcdsaKat {
    ecdsa_rfc6979: Vec<EcdsaVector>,
}

/// SEC1 compressed public key from (Qx, Qy): 0x02/0x03 (y parity) || Qx.
fn compressed_pubkey(qx_hex: &str, qy_hex: &str) -> Vec<u8> {
    let qx = from_hex(qx_hex);
    let qy = from_hex(qy_hex);
    let prefix = if qy.last().map_or(0, |b| b & 1) == 0 {
        0x02
    } else {
        0x03
    };
    let mut pk = Vec::with_capacity(1 + qx.len());
    pk.push(prefix);
    pk.extend_from_slice(&qx);
    pk
}

/// Raw r||s signature, each coordinate left-padded to `width` bytes.
fn raw_sig(r_hex: &str, s_hex: &str, width: usize) -> Vec<u8> {
    let mut sig = vec![0u8; 2 * width];
    let r = from_hex(r_hex);
    let s = from_hex(s_hex);
    sig[width - r.len()..width].copy_from_slice(&r);
    sig[2 * width - s.len()..].copy_from_slice(&s);
    sig
}

#[test]
fn official_kat_ecdsa_rfc6979() {
    let kat: EcdsaKat = read_kat("ecdsa-rfc6979.json");
    assert!(
        !kat.ecdsa_rfc6979.is_empty(),
        "ecdsa-rfc6979.json carries no vectors"
    );
    for v in &kat.ecdsa_rfc6979 {
        let width = match v.curve.as_str() {
            "P-256" => 32,
            "P-384" => 48,
            other => panic!("unknown curve {other}"),
        };
        let verify: fn(&[u8], &[u8], &[u8]) -> bool = match v.curve.as_str() {
            "P-256" => verify_ecdsa_p256,
            "P-384" => verify_ecdsa_p384,
            other => panic!("unknown curve {other}"),
        };

        let pubkey = compressed_pubkey(&v.qx, &v.qy);
        let sig = raw_sig(&v.r, &v.s, width);
        let msg = v.message_ascii.as_bytes();

        // The published (r,s) MUST verify.
        assert!(
            verify(msg, &sig, &pubkey),
            "{}: native verify_ecdsa rejected the OFFICIAL signature ({}) — impl disagrees with RFC 6979",
            v.name,
            v.source
        );

        // A 1-bit-flipped signature MUST be rejected.
        let mut tampered = sig.clone();
        *tampered.last_mut().unwrap() ^= 0x01;
        assert!(
            !verify(msg, &tampered, &pubkey),
            "{}: accepted a 1-bit-tampered signature — must reject",
            v.name
        );

        // A different message MUST be rejected.
        assert!(
            !verify(b"wrong message", &sig, &pubkey),
            "{}: accepted signature against the wrong message — must reject",
            v.name
        );
    }
}
