#[path = "PriceBet.runar.rs"]
mod contract;

use contract::*;
use runar::prelude::*;

fn new_price_bet() -> PriceBet {
    PriceBet {
        alice_pub_key: ALICE.pub_key.to_vec(),
        bob_pub_key: BOB.pub_key.to_vec(),
        oracle_pub_key: oracle::pubkey_le(),
        strike_price: 50000,
    }
}

/// Honestly sign a price with the shared test Rabin key. Mirrors
/// `examples/end2end-example/go/PriceBet_test.go::signPrice` (which uses
/// `runar.RabinSignToBytes`) and the TS test's `rabinSign(RABIN_TEST_KEY)`.
/// `verify_rabin_sig` performs REAL Rabin verification (with the on-chain
/// padding bound 0 <= padding < 65536), so garbage (sig, padding) pairs no
/// longer verify.
fn sign_price(price: Bigint) -> (Vec<u8>, Vec<u8>) {
    let msg = num2bin(&price, 8);
    oracle::sign(&msg)
}

#[test]
fn test_settle_alice_wins() {
    let (rabin_sig, pad) = sign_price(60000);
    let alice_sig = ALICE.sign_test_message();
    let bob_sig = BOB.sign_test_message();
    new_price_bet().settle(60000, &rabin_sig, &pad, &alice_sig, &bob_sig);
}

#[test]
fn test_settle_bob_wins() {
    let (rabin_sig, pad) = sign_price(30000);
    let alice_sig = ALICE.sign_test_message();
    let bob_sig = BOB.sign_test_message();
    new_price_bet().settle(30000, &rabin_sig, &pad, &alice_sig, &bob_sig);
}

#[test]
fn test_settle_bob_wins_at_strike() {
    let (rabin_sig, pad) = sign_price(50000);
    let alice_sig = ALICE.sign_test_message();
    let bob_sig = BOB.sign_test_message();
    new_price_bet().settle(50000, &rabin_sig, &pad, &alice_sig, &bob_sig);
}

#[test]
#[should_panic(expected = "price > 0")]
fn test_settle_zero_price_rejected() {
    // Honestly signed so the Rabin layer passes and the failure is
    // attributable to the `price > 0` assert, not the signature check.
    let (rabin_sig, pad) = sign_price(0);
    let alice_sig = ALICE.sign_test_message();
    let bob_sig = BOB.sign_test_message();
    new_price_bet().settle(0, &rabin_sig, &pad, &alice_sig, &bob_sig);
}

#[test]
#[should_panic(expected = "verify_rabin_sig")]
fn test_settle_forged_oracle_sig_rejected() {
    // Price favors Alice but the oracle signature is garbage — the Rabin
    // layer must reject it.
    let alice_sig = ALICE.sign_test_message();
    let bob_sig = BOB.sign_test_message();
    let forged_sig: RabinSig = b"not_a_signature".to_vec();
    let pad: ByteString = vec![0u8];
    new_price_bet().settle(60000, &forged_sig, &pad, &alice_sig, &bob_sig);
}

#[test]
fn test_cancel() {
    let alice_sig = ALICE.sign_test_message();
    let bob_sig = BOB.sign_test_message();
    new_price_bet().cancel(&alice_sig, &bob_sig);
}

#[test]
fn test_compile() {
    runar::compile_check(
        include_str!("PriceBet.runar.rs"),
        "PriceBet.runar.rs",
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
