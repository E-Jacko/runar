//! Real secp256k1 elliptic curve operations for testing.
//!
//! Uses the `k256` crate for real EC arithmetic. Point encoding is
//! 64 bytes: `x[32] || y[32]` (big-endian, no prefix byte).

use k256::elliptic_curve::group::{Group, GroupEncoding};
use k256::elliptic_curve::sec1::{FromEncodedPoint, ToEncodedPoint};
use k256::{AffinePoint, ProjectivePoint, Scalar};

use crate::prelude::{Bigint, ByteString, Point};

/// Parse a 64-byte Point (x[32] || y[32]) into a ProjectivePoint.
fn point_to_projective(p: &[u8]) -> ProjectivePoint {
    assert_eq!(p.len(), 64, "Point must be exactly 64 bytes");

    // Check for point at infinity (all zeros)
    if p.iter().all(|&b| b == 0) {
        return ProjectivePoint::IDENTITY;
    }

    // Build uncompressed SEC1 encoding: 0x04 || x || y
    let mut sec1 = vec![0x04u8];
    sec1.extend_from_slice(p);
    let encoded = k256::EncodedPoint::from_bytes(&sec1)
        .expect("invalid SEC1 encoding");
    let affine = AffinePoint::from_encoded_point(&encoded)
        .expect("point not on curve");
    ProjectivePoint::from(affine)
}

/// Serialize a ProjectivePoint to a 64-byte Point (x[32] || y[32]).
fn projective_to_point(p: &ProjectivePoint) -> Point {
    if p.is_identity().into() {
        return vec![0u8; 64];
    }
    let affine = p.to_affine();
    let encoded = affine.to_encoded_point(false); // uncompressed
    let bytes = encoded.as_bytes(); // 0x04 || x[32] || y[32]
    bytes[1..65].to_vec()
}

/// Convert an i64 scalar to a k256::Scalar (mod N).
fn i64_to_scalar(k: Bigint) -> Scalar {
    if k >= 0 {
        Scalar::from(k as u64)
    } else {
        // Negative: compute N - |k|
        Scalar::ZERO - Scalar::from((-k) as u64)
    }
}

/// Point addition on secp256k1.
pub fn ec_add(a: &[u8], b: &[u8]) -> Point {
    let pa = point_to_projective(a);
    let pb = point_to_projective(b);
    projective_to_point(&(pa + pb))
}

/// Scalar multiplication: k * P.
pub fn ec_mul(p: &[u8], k: Bigint) -> Point {
    let pp = point_to_projective(p);
    let s = i64_to_scalar(k);
    projective_to_point(&(pp * s))
}

/// Scalar multiplication with the generator: k * G.
pub fn ec_mul_gen(k: Bigint) -> Point {
    let s = i64_to_scalar(k);
    projective_to_point(&(ProjectivePoint::GENERATOR * s))
}

/// Point negation: returns (x, p - y).
pub fn ec_negate(p: &[u8]) -> Point {
    let pp = point_to_projective(p);
    projective_to_point(&(-pp))
}

/// Check if a point is on the secp256k1 curve.
pub fn ec_on_curve(p: &[u8]) -> bool {
    if p.len() != 64 {
        return false;
    }
    // The all-zero blob is this codegen's encoding of the point at infinity,
    // and it is NOT on the curve: the emitted ec_on_curve is exactly
    // x < p AND y < p AND y^2 == x^3 + 7, and 0 != 7. Returning true here (the
    // projective convention) made this mock disagree with the script it stands
    // in for, so `assert(ec_on_curve(r))` passed off-chain and failed on-chain
    // for r = O — an unspendable output found only after deploy. O is now
    // reachable from ec_add(P, -P), so this matters in practice.
    let mut sec1 = vec![0x04u8];
    sec1.extend_from_slice(p);
    let Ok(enc) = k256::EncodedPoint::from_bytes(&sec1) else { return false };
    let ct = AffinePoint::from_encoded_point(&enc);
    ct.is_some().into()
}

/// Non-negative modular reduction: ((value % m) + m) % m.
pub fn ec_mod_reduce(value: Bigint, m: Bigint) -> Bigint {
    let r = value % m;
    if r < 0 { r + m } else { r }
}

/// Encode a point as a 33-byte compressed public key.
pub fn ec_encode_compressed(p: &[u8]) -> ByteString {
    let pp = point_to_projective(p);
    let affine = pp.to_affine();
    affine.to_bytes().to_vec()
}

/// Construct a Point from two coordinate integers.
pub fn ec_make_point(x: Bigint, y: Bigint) -> Point {
    let mut buf = vec![0u8; 64];
    let xb = (x as u64).to_be_bytes();
    let yb = (y as u64).to_be_bytes();
    buf[24..32].copy_from_slice(&xb);
    buf[56..64].copy_from_slice(&yb);
    buf
}

/// Extract the x-coordinate from a Point as an i64.
/// Note: only meaningful for small test values; real coordinates are 256-bit.
pub fn ec_point_x(p: &[u8]) -> Bigint {
    assert_eq!(p.len(), 64, "Point must be exactly 64 bytes");
    // Return as i64 — will only work for small coordinates
    let mut bytes = [0u8; 8];
    bytes.copy_from_slice(&p[24..32]);
    u64::from_be_bytes(bytes) as i64
}

/// Extract the y-coordinate from a Point as an i64.
/// Note: only meaningful for small test values; real coordinates are 256-bit.
pub fn ec_point_y(p: &[u8]) -> Bigint {
    assert_eq!(p.len(), 64, "Point must be exactly 64 bytes");
    let mut bytes = [0u8; 8];
    bytes.copy_from_slice(&p[56..64]);
    u64::from_be_bytes(bytes) as i64
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: the secp256k1 generator point as a 64-byte Point.
    fn ec_g() -> Point {
        ec_mul_gen(1)
    }

    #[test]
    fn ec_g_is_64_bytes() {
        assert_eq!(ec_g().len(), 64);
    }

    #[test]
    fn ec_g_is_on_curve() {
        assert!(ec_on_curve(&ec_g()));
    }

    #[test]
    fn ec_add_g_g_equals_ec_mul_g_2() {
        let g = ec_g();
        let sum = ec_add(&g, &g);
        let doubled = ec_mul(&g, 2);
        assert_eq!(sum, doubled);
    }

    #[test]
    fn ec_add_g_g_equals_ec_mul_gen_2() {
        let g = ec_g();
        let sum = ec_add(&g, &g);
        let gen2 = ec_mul_gen(2);
        assert_eq!(sum, gen2);
    }

    #[test]
    fn ec_mul_gen_1_equals_g() {
        let g = ec_g();
        let gen1 = ec_mul_gen(1);
        assert_eq!(gen1, g);
    }

    #[test]
    fn ec_negate_produces_on_curve_point() {
        let g = ec_g();
        let neg = ec_negate(&g);
        assert_eq!(neg.len(), 64);
        assert!(ec_on_curve(&neg));
        // Negated point should differ from original (y coordinate differs)
        assert_ne!(neg, g);
    }

    #[test]
    fn ec_negate_double_negate_is_identity() {
        let g = ec_g();
        let double_neg = ec_negate(&ec_negate(&g));
        assert_eq!(double_neg, g);
    }

    #[test]
    fn ec_add_point_and_negation_is_identity() {
        let g = ec_g();
        let neg = ec_negate(&g);
        let sum = ec_add(&g, &neg);
        // Point at infinity = 64 zero bytes
        assert_eq!(sum, vec![0u8; 64]);
    }

    #[test]
    fn ec_make_point_round_trip() {
        let x: Bigint = 12345;
        let y: Bigint = 67890;
        let p = ec_make_point(x, y);
        assert_eq!(p.len(), 64);
        assert_eq!(ec_point_x(&p), x);
        assert_eq!(ec_point_y(&p), y);
    }

    #[test]
    fn ec_encode_compressed_produces_33_bytes() {
        let g = ec_g();
        let compressed = ec_encode_compressed(&g);
        assert_eq!(compressed.len(), 33);
        // First byte must be 0x02 or 0x03 (compressed prefix)
        assert!(compressed[0] == 0x02 || compressed[0] == 0x03);
    }

    #[test]
    fn ec_on_curve_rejects_invalid_point() {
        // Random 64 bytes very unlikely to be on the curve
        let bad_point = vec![0xffu8; 64];
        assert!(!ec_on_curve(&bad_point));
    }

    #[test]
    fn ec_on_curve_rejects_wrong_length() {
        assert!(!ec_on_curve(&[0u8; 32]));
    }

    #[test]
    fn ec_on_curve_rejects_identity() {
        // The all-zero blob is the point at infinity, and it is NOT on the
        // curve — 0^2 != 0^3 + 7. That is the ONLY way a contract can detect O,
        // and the compiled script agrees. This used to assert the opposite, so
        // an `assert(ec_on_curve(r))` that was green off-chain deployed an
        // unspendable output whenever r was O. O is reachable from
        // ec_add(P, -P) and from ec_mul(P, 0).
        assert!(!ec_on_curve(&vec![0u8; 64]));
    }

    #[test]
    fn ec_mod_reduce_basic() {
        assert_eq!(ec_mod_reduce(10, 3), 1);
        assert_eq!(ec_mod_reduce(-1, 5), 4);
        assert_eq!(ec_mod_reduce(0, 7), 0);
    }

    #[test]
    fn ec_mul_associative() {
        // (G * 3) * 2 should equal G * 6
        let g = ec_g();
        let g3 = ec_mul(&g, 3);
        let g3x2 = ec_mul(&g3, 2);
        let g6 = ec_mul_gen(6);
        assert_eq!(g3x2, g6);
    }
}
