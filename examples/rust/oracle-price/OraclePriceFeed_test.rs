#[path = "OraclePriceFeed.runar.rs"]
mod contract;

use contract::*;
use runar::prelude::*;

fn new_oracle_feed() -> OraclePriceFeed {
    OraclePriceFeed {
        oracle_pub_key: oracle::pubkey_le(),
        receiver: ALICE.pub_key.to_vec(),
    }
}

/// Honestly sign a price with the shared test Rabin key. `verify_rabin_sig`
/// performs REAL Rabin verification (with the on-chain padding bound
/// 0 <= padding < 65536), so the trivial sig=0 / padding=hash-mod-n scheme is
/// no longer a representative way to drive the contract. Mirrors the Go
/// (`runar.RabinSignToBytes`), Java (`OraclePriceFeedTest`), and TS
/// (`rabinSign(RABIN_TEST_KEY)`) example tests.
fn sign_price(price: Bigint) -> (Vec<u8>, Vec<u8>) {
    let msg = num2bin(&price, 8);
    oracle::sign(&msg)
}

#[test]
fn test_settle() {
    let price: Bigint = 60000;
    let (sig, pad) = sign_price(price);
    new_oracle_feed().settle(price, &sig, &pad, &ALICE.sign_test_message());
}

#[test]
#[should_panic(expected = "price > 50000")]
fn test_settle_price_too_low_fails() {
    // Honestly signed so the Rabin layer passes and the failure is
    // attributable to the threshold assert, not the signature check.
    let price: Bigint = 50000;
    let (sig, pad) = sign_price(price);
    new_oracle_feed().settle(price, &sig, &pad, &ALICE.sign_test_message());
}

#[test]
fn test_settle_high_price() {
    let price: Bigint = 100000;
    let (sig, pad) = sign_price(price);
    new_oracle_feed().settle(price, &sig, &pad, &ALICE.sign_test_message());
}

#[test]
#[should_panic(expected = "verify_rabin_sig")]
fn test_settle_forged_oracle_sig_rejected() {
    // Price exceeds the threshold but the oracle signature is garbage — the
    // Rabin layer must reject it.
    let forged_sig: RabinSig = b"not_a_signature".to_vec();
    let pad: ByteString = vec![0u8];
    new_oracle_feed().settle(60000, &forged_sig, &pad, &ALICE.sign_test_message());
}

#[test]
fn test_compile() {
    runar::compile_check(
        include_str!("OraclePriceFeed.runar.rs"),
        "OraclePriceFeed.runar.rs",
    ).unwrap();
}

/// Test-only honest Rabin oracle. Same p, q ≡ 3 (mod 4) test key as the Go
/// (`runar.RabinTestP/Q`), Java (`OraclePriceFeedTest`), and integration-test
/// (`integration/rust/tests/helpers/crypto.rs`) tiers. Square roots mod p are
/// computable as a^((p+1)/4) mod p because p ≡ 3 (mod 4).
mod oracle {
    use num_bigint::BigUint;

    const P_DEC: &str = "1361129467683753853853498429727072846227";
    const Q_DEC: &str = "1361129467683753853853498429727082846007";

    fn p() -> BigUint {
        P_DEC.parse().unwrap()
    }

    fn q() -> BigUint {
        Q_DEC.parse().unwrap()
    }

    /// Rabin modulus n = p * q as unsigned LE bytes (the contract's RabinPubKey).
    pub fn pubkey_le() -> Vec<u8> {
        (p() * q()).to_bytes_le()
    }

    /// sqrt of `a` mod prime `p` where p ≡ 3 (mod 4); None if `a` is not a
    /// quadratic residue.
    fn sqrt_mod(a: &BigUint, p: &BigUint) -> Option<BigUint> {
        let a = a % p;
        if a == BigUint::from(0u8) {
            return Some(a);
        }
        let r = a.modpow(&((p + 1u8) >> 2), p);
        if (&r * &r) % p == a {
            Some(r)
        } else {
            None
        }
    }

    /// Honest Rabin signature: returns (sig, padding) as unsigned LE bytes
    /// with padding < 65536 such that (sig² + padding) mod n == SHA256(msg)
    /// mod n. Finds the padding by quadratic-residue search and the root via
    /// CRT (modular inverses by Fermat, since p and q are prime).
    pub fn sign(msg: &[u8]) -> (Vec<u8>, Vec<u8>) {
        let (p, q) = (p(), q());
        let n = &p * &q;
        let hash = runar::prelude::sha256(msg);
        let hash_mod_n = BigUint::from_bytes_le(&hash) % &n;
        let q_inv_p = q.modpow(&(&p - 2u8), &p);
        let p_inv_q = p.modpow(&(&q - 2u8), &q);
        for pad in 0u32..65536 {
            let pad_bn = BigUint::from(pad);
            let target = (&hash_mod_n + &n - &pad_bn) % &n;
            let (Some(rp), Some(rq)) = (sqrt_mod(&target, &p), sqrt_mod(&target, &q)) else {
                continue;
            };
            let sig = (&rp * &q * &q_inv_p + &rq * &p * &p_inv_q) % &n;
            if (&sig * &sig + &pad_bn) % &n == hash_mod_n {
                return (sig.to_bytes_le(), pad_bn.to_bytes_le());
            }
        }
        panic!("no valid padding < 65536 found for test message");
    }
}
