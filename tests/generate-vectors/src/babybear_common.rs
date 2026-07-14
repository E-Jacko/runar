//! Shared Baby Bear field and extension field helpers for test vector generators.

pub use p3_baby_bear::BabyBear;
use p3_field::extension::BinomialExtensionField;
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing, PrimeField32};
use rand::rngs::StdRng;
use rand::Rng;

pub const P: u64 = 2013265921; // Baby Bear prime: 2^31 - 2^27 + 1

pub type EF4 = BinomialExtensionField<BabyBear, 4>;

pub fn bb(val: u64) -> BabyBear {
    BabyBear::new(val as u32)
}

pub fn to_u64(f: BabyBear) -> u64 {
    f.as_canonical_u32() as u64
}

pub fn ef4(a0: u64, a1: u64, a2: u64, a3: u64) -> EF4 {
    EF4::new([bb(a0), bb(a1), bb(a2), bb(a3)])
}

pub fn ef4_to_array(f: EF4) -> [u64; 4] {
    let coeffs = f.as_basis_coefficients_slice();
    [
        to_u64(coeffs[0]),
        to_u64(coeffs[1]),
        to_u64(coeffs[2]),
        to_u64(coeffs[3]),
    ]
}

pub fn random_ef4(rng: &mut StdRng) -> EF4 {
    ef4(
        rng.gen_range(0..P),
        rng.gen_range(0..P),
        rng.gen_range(0..P),
        rng.gen_range(0..P),
    )
}

pub fn random_nonzero_base(rng: &mut StdRng) -> BabyBear {
    bb(rng.gen_range(1..P))
}

/// Embed a base field element into ext4: (val, 0, 0, 0)
pub fn embed_base(val: BabyBear) -> EF4 {
    EF4::new([val, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO])
}
