//! Generates FRI colinearity check test vectors using Plonky3's Baby Bear
//! extension field as the reference implementation.
//!
//! The FRI folding relation:
//!   g(x²) = (f(x) + f(-x)) / 2 + alpha * (f(x) - f(-x)) / (2 * x)
//!
//! Where:
//!   x     — base field element (domain point)
//!   f(x), f(-x), alpha, g(x²) — extension field elements (BabyBear ext4)
//!
//! Output: JSON file in ../vectors/fri_colinearity.json

mod babybear_common;

use p3_field::Field;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use serde::Serialize;
use std::fs;
use std::path::Path;

use babybear_common::*;

#[derive(Serialize)]
struct FRIVectorFile {
    field: String,
    prime: u64,
    description: String,
    vectors: Vec<FRIVector>,
}

#[derive(Serialize)]
struct FRIVector {
    x: u64,
    f_x: [u64; 4],
    f_neg_x: [u64; 4],
    alpha: [u64; 4],
    expected_g_x2: [u64; 4],
    expected: String,
    description: String,
}

/// Compute the FRI folding relation using Plonky3 field types:
///   g(x²) = (f(x) + f(-x)) / 2 + alpha * (f(x) - f(-x)) / (2 * x)
fn compute_g_x2(x: BabyBear, f_x: EF4, f_neg_x: EF4, alpha: EF4) -> EF4 {
    let two = BabyBear::new(2);
    let two_inv = two.inverse();
    let two_x_inv = (two * x).inverse();

    // Embed base field scalars into extension field for arithmetic
    let sum = f_x + f_neg_x;
    let diff = f_x - f_neg_x;

    // half_sum = (f(x) + f(-x)) / 2
    let half_sum = sum * embed_base(two_inv);

    // alpha_term = alpha * (f(x) - f(-x)) / (2 * x)
    let alpha_diff = alpha * diff;
    let alpha_term = alpha_diff * embed_base(two_x_inv);

    half_sum + alpha_term
}

fn generate_accept_vectors(rng: &mut StdRng) -> Vec<FRIVector> {
    let mut vectors = Vec::new();

    // --- Edge cases ---

    // f(x) = f(-x) → diff = 0, g(x²) = f(x) (pure averaging, alpha term vanishes)
    {
        let x = random_nonzero_base(rng);
        let f_val = random_ef4(rng);
        let alpha = random_ef4(rng);
        let g = compute_g_x2(x, f_val, f_val, alpha);
        vectors.push(FRIVector {
            x: to_u64(x),
            f_x: ef4_to_array(f_val),
            f_neg_x: ef4_to_array(f_val),
            alpha: ef4_to_array(alpha),
            expected_g_x2: ef4_to_array(g),
            expected: "accept".into(),
            description: "f(x) = f(-x): alpha term vanishes".into(),
        });
    }

    // alpha = 0 → g(x²) = (f(x) + f(-x)) / 2
    {
        let x = random_nonzero_base(rng);
        let f_x = random_ef4(rng);
        let f_neg_x = random_ef4(rng);
        let alpha = ef4(0, 0, 0, 0);
        let g = compute_g_x2(x, f_x, f_neg_x, alpha);
        vectors.push(FRIVector {
            x: to_u64(x),
            f_x: ef4_to_array(f_x),
            f_neg_x: ef4_to_array(f_neg_x),
            alpha: ef4_to_array(alpha),
            expected_g_x2: ef4_to_array(g),
            expected: "accept".into(),
            description: "alpha = 0: pure averaging".into(),
        });
    }

    // f(x) = 0
    {
        let x = random_nonzero_base(rng);
        let f_x = ef4(0, 0, 0, 0);
        let f_neg_x = random_ef4(rng);
        let alpha = random_ef4(rng);
        let g = compute_g_x2(x, f_x, f_neg_x, alpha);
        vectors.push(FRIVector {
            x: to_u64(x),
            f_x: ef4_to_array(f_x),
            f_neg_x: ef4_to_array(f_neg_x),
            alpha: ef4_to_array(alpha),
            expected_g_x2: ef4_to_array(g),
            expected: "accept".into(),
            description: "f(x) = 0".into(),
        });
    }

    // x = 1 (simplest domain point)
    {
        let x = bb(1);
        let f_x = random_ef4(rng);
        let f_neg_x = random_ef4(rng);
        let alpha = random_ef4(rng);
        let g = compute_g_x2(x, f_x, f_neg_x, alpha);
        vectors.push(FRIVector {
            x: to_u64(x),
            f_x: ef4_to_array(f_x),
            f_neg_x: ef4_to_array(f_neg_x),
            alpha: ef4_to_array(alpha),
            expected_g_x2: ef4_to_array(g),
            expected: "accept".into(),
            description: "x = 1".into(),
        });
    }

    // Base field only (all ext4 elements have components 1-3 = 0)
    for i in 0..5 {
        let x = random_nonzero_base(rng);
        let f_x = ef4(rng.gen_range(1..P), 0, 0, 0);
        let f_neg_x = ef4(rng.gen_range(1..P), 0, 0, 0);
        let alpha = ef4(rng.gen_range(1..P), 0, 0, 0);
        let g = compute_g_x2(x, f_x, f_neg_x, alpha);
        vectors.push(FRIVector {
            x: to_u64(x),
            f_x: ef4_to_array(f_x),
            f_neg_x: ef4_to_array(f_neg_x),
            alpha: ef4_to_array(alpha),
            expected_g_x2: ef4_to_array(g),
            expected: "accept".into(),
            description: format!("base field only #{}", i),
        });
    }

    // --- Domain point powers of the Baby Bear generator (g = 31) ---
    {
        let gen = bb(31);
        let mut x = gen;
        for i in 1..=10 {
            let f_x = random_ef4(rng);
            let f_neg_x = random_ef4(rng);
            let alpha = random_ef4(rng);
            let g = compute_g_x2(x, f_x, f_neg_x, alpha);
            vectors.push(FRIVector {
                x: to_u64(x),
                f_x: ef4_to_array(f_x),
                f_neg_x: ef4_to_array(f_neg_x),
                alpha: ef4_to_array(alpha),
                expected_g_x2: ef4_to_array(g),
                expected: "accept".into(),
                description: format!("generator power: x = g^{}", i),
            });
            x = x * gen;
        }
    }

    // --- Fully random vectors ---
    for i in 0..50 {
        let x = random_nonzero_base(rng);
        let f_x = random_ef4(rng);
        let f_neg_x = random_ef4(rng);
        let alpha = random_ef4(rng);
        let g = compute_g_x2(x, f_x, f_neg_x, alpha);
        vectors.push(FRIVector {
            x: to_u64(x),
            f_x: ef4_to_array(f_x),
            f_neg_x: ef4_to_array(f_neg_x),
            alpha: ef4_to_array(alpha),
            expected_g_x2: ef4_to_array(g),
            expected: "accept".into(),
            description: format!("random #{}", i),
        });
    }

    // --- Near-prime boundary values ---
    for offset in [1u64, 2, 3] {
        let x = bb(P - offset);
        let f_x = ef4(P - 1, P - 2, 1, 0);
        let f_neg_x = ef4(1, 2, P - 1, 0);
        let alpha = ef4(P - 1, P - 1, P - 1, P - 1);
        let g = compute_g_x2(x, f_x, f_neg_x, alpha);
        vectors.push(FRIVector {
            x: to_u64(x),
            f_x: ef4_to_array(f_x),
            f_neg_x: ef4_to_array(f_neg_x),
            alpha: ef4_to_array(alpha),
            expected_g_x2: ef4_to_array(g),
            expected: "accept".into(),
            description: format!("boundary: x = p-{}", offset),
        });
    }

    vectors
}

fn generate_reject_vectors(rng: &mut StdRng) -> Vec<FRIVector> {
    let mut vectors = Vec::new();

    // Corrupted g(x²) — flip one component
    for i in 0..10 {
        let x = random_nonzero_base(rng);
        let f_x = random_ef4(rng);
        let f_neg_x = random_ef4(rng);
        let alpha = random_ef4(rng);
        let g = compute_g_x2(x, f_x, f_neg_x, alpha);
        let mut bad_g = ef4_to_array(g);
        let component = i % 4;
        bad_g[component] = (bad_g[component] + 1) % P;
        vectors.push(FRIVector {
            x: to_u64(x),
            f_x: ef4_to_array(f_x),
            f_neg_x: ef4_to_array(f_neg_x),
            alpha: ef4_to_array(alpha),
            expected_g_x2: bad_g,
            expected: "reject".into(),
            description: format!("corrupted g component {}", component),
        });
    }

    // Wrong alpha (correct g for different alpha)
    for _ in 0..5 {
        let x = random_nonzero_base(rng);
        let f_x = random_ef4(rng);
        let f_neg_x = random_ef4(rng);
        let alpha = random_ef4(rng);
        let wrong_alpha = random_ef4(rng);
        let g_wrong = compute_g_x2(x, f_x, f_neg_x, wrong_alpha);
        vectors.push(FRIVector {
            x: to_u64(x),
            f_x: ef4_to_array(f_x),
            f_neg_x: ef4_to_array(f_neg_x),
            alpha: ef4_to_array(alpha),
            expected_g_x2: ef4_to_array(g_wrong),
            expected: "reject".into(),
            description: "g computed with wrong alpha".into(),
        });
    }

    // Swapped f(x) and f(-x)
    for _ in 0..5 {
        let x = random_nonzero_base(rng);
        let f_x = random_ef4(rng);
        let f_neg_x = random_ef4(rng);
        let alpha = random_ef4(rng);
        // Compute g with swapped inputs
        let g_swapped = compute_g_x2(x, f_neg_x, f_x, alpha);
        vectors.push(FRIVector {
            x: to_u64(x),
            f_x: ef4_to_array(f_x),
            f_neg_x: ef4_to_array(f_neg_x),
            alpha: ef4_to_array(alpha),
            expected_g_x2: ef4_to_array(g_swapped),
            expected: "reject".into(),
            description: "g computed with swapped f(x)/f(-x)".into(),
        });
    }

    vectors
}

fn main() {
    let vectors_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../vectors");
    fs::create_dir_all(&vectors_dir).expect("create vectors dir");

    let mut rng = StdRng::seed_from_u64(300);

    let mut all_vectors = generate_accept_vectors(&mut rng);
    let reject = generate_reject_vectors(&mut rng);
    let accept_count = all_vectors.len();
    let reject_count = reject.len();
    all_vectors.extend(reject);

    let file = FRIVectorFile {
        field: "babybear_ext4".into(),
        prime: P,
        description: "FRI colinearity check: g(x²) = (f(x)+f(-x))/2 + alpha*(f(x)-f(-x))/(2*x)".into(),
        vectors: all_vectors,
    };
    let json = serde_json::to_string_pretty(&file).unwrap();
    fs::write(vectors_dir.join("fri_colinearity.json"), &json).unwrap();
    println!(
        "Generated {} FRI colinearity vectors ({} accept, {} reject)",
        accept_count + reject_count,
        accept_count,
        reject_count
    );
}
