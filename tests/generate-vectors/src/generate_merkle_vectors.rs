//! Generates SHA-256 Merkle tree test vectors for FRI verification.
//!
//! Builds trees of various sizes, generates valid inclusion proofs and
//! invalid proofs (corrupted siblings, wrong leaf, wrong index).
//!
//! Output: JSON files in ../vectors/ for inclusion and rejection tests.

use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use serde::Serialize;
use sha2::{Digest, Sha256};
use std::fs;
use std::path::Path;

// ---------------------------------------------------------------------------
// Merkle tree
// ---------------------------------------------------------------------------

struct MerkleTree {
    /// All nodes stored level-by-level, leaves first.
    /// Level 0 = leaves, level `depth` = [root].
    levels: Vec<Vec<[u8; 32]>>,
}

impl MerkleTree {
    fn build(leaves: &[[u8; 32]]) -> Self {
        assert!(leaves.len().is_power_of_two(), "leaf count must be power of 2");
        let mut levels: Vec<Vec<[u8; 32]>> = vec![leaves.to_vec()];
        let mut current = leaves.to_vec();
        while current.len() > 1 {
            let mut next = Vec::with_capacity(current.len() / 2);
            for pair in current.chunks(2) {
                next.push(hash_pair(&pair[0], &pair[1]));
            }
            levels.push(next.clone());
            current = next;
        }
        MerkleTree { levels }
    }

    fn root(&self) -> [u8; 32] {
        self.levels.last().unwrap()[0]
    }

    fn depth(&self) -> usize {
        self.levels.len() - 1
    }

    /// Returns the authentication path (siblings) for the given leaf index.
    /// Siblings are ordered from level 0 (leaf level) upward.
    fn proof(&self, index: usize) -> Vec<[u8; 32]> {
        let mut siblings = Vec::with_capacity(self.depth());
        let mut idx = index;
        for level in 0..self.depth() {
            let sibling_idx = idx ^ 1; // flip the lowest bit
            siblings.push(self.levels[level][sibling_idx]);
            idx >>= 1;
        }
        siblings
    }
}

fn hash_pair(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(left);
    hasher.update(right);
    let result = hasher.finalize();
    let mut out = [0u8; 32];
    out.copy_from_slice(&result);
    out
}

fn hash_leaf(data: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(data);
    let result = hasher.finalize();
    let mut out = [0u8; 32];
    out.copy_from_slice(&result);
    out
}

fn to_hex(bytes: &[u8]) -> String {
    hex::encode(bytes)
}

fn concat_proof(siblings: &[[u8; 32]]) -> String {
    let mut buf = Vec::with_capacity(siblings.len() * 32);
    for s in siblings {
        buf.extend_from_slice(s);
    }
    hex::encode(&buf)
}

// ---------------------------------------------------------------------------
// Test vector types
// ---------------------------------------------------------------------------

#[derive(Serialize)]
struct MerkleVectorFile {
    hash: String,
    vectors: Vec<MerkleVector>,
}

#[derive(Serialize)]
struct MerkleVector {
    tree_size: usize,
    depth: usize,
    leaf_index: usize,
    leaf: String,
    proof: String,
    root: String,
    expected: String,
    description: String,
}

// ---------------------------------------------------------------------------
// Vector generators
// ---------------------------------------------------------------------------

fn random_leaves(rng: &mut StdRng, count: usize) -> Vec<[u8; 32]> {
    (0..count).map(|_| {
        let mut leaf = [0u8; 32];
        rng.fill(&mut leaf);
        leaf
    }).collect()
}

fn generate_inclusion_vectors() -> Vec<MerkleVector> {
    let mut vectors = Vec::new();
    let mut rng = StdRng::seed_from_u64(100);

    for &size in &[8usize, 16, 32, 64, 256, 1024] {
        let leaves = random_leaves(&mut rng, size);
        let tree = MerkleTree::build(&leaves);
        let depth = tree.depth();
        let root = tree.root();

        // Test specific indices: first, last, middle, and random
        let mut indices: Vec<usize> = vec![0, size - 1, size / 2];
        // Add random indices
        for _ in 0..std::cmp::min(10, size) {
            indices.push(rng.gen_range(0..size));
        }
        indices.sort();
        indices.dedup();

        for &idx in &indices {
            let siblings = tree.proof(idx);
            vectors.push(MerkleVector {
                tree_size: size,
                depth,
                leaf_index: idx,
                leaf: to_hex(&leaves[idx]),
                proof: concat_proof(&siblings),
                root: to_hex(&root),
                expected: "accept".into(),
                description: format!("valid proof: tree={}, leaf={}", size, idx),
            });
        }
    }

    // Deterministic small tree for manual verification
    let small_leaves: Vec<[u8; 32]> = (0u8..8).map(|i| {
        let mut leaf = [0u8; 32];
        leaf[31] = i;
        leaf
    }).collect();
    let tree = MerkleTree::build(&small_leaves);
    for idx in 0..8 {
        let siblings = tree.proof(idx);
        vectors.push(MerkleVector {
            tree_size: 8,
            depth: tree.depth(),
            leaf_index: idx,
            leaf: to_hex(&small_leaves[idx]),
            proof: concat_proof(&siblings),
            root: to_hex(&tree.root()),
            expected: "accept".into(),
            description: format!("deterministic small tree: leaf {}", idx),
        });
    }

    vectors
}

fn generate_rejection_vectors() -> Vec<MerkleVector> {
    let mut vectors = Vec::new();
    let mut rng = StdRng::seed_from_u64(200);

    for &size in &[8usize, 16, 32, 1024] {
        let leaves = random_leaves(&mut rng, size);
        let tree = MerkleTree::build(&leaves);
        let depth = tree.depth();
        let root = tree.root();

        // Pick a leaf to corrupt proofs for
        let idx = rng.gen_range(0..size);
        let siblings = tree.proof(idx);

        // 1. Corrupt a sibling hash (flip one bit at each level)
        for level in 0..depth {
            let mut bad_siblings = siblings.clone();
            bad_siblings[level][0] ^= 0x01; // flip first bit
            vectors.push(MerkleVector {
                tree_size: size,
                depth,
                leaf_index: idx,
                leaf: to_hex(&leaves[idx]),
                proof: concat_proof(&bad_siblings),
                root: to_hex(&root),
                expected: "reject".into(),
                description: format!(
                    "corrupted sibling at level {}: tree={}, leaf={}",
                    level, size, idx
                ),
            });
        }

        // 2. Wrong leaf value (correct proof, wrong leaf)
        let mut wrong_leaf = leaves[idx];
        wrong_leaf[0] ^= 0xFF;
        vectors.push(MerkleVector {
            tree_size: size,
            depth,
            leaf_index: idx,
            leaf: to_hex(&wrong_leaf),
            proof: concat_proof(&siblings),
            root: to_hex(&root),
            expected: "reject".into(),
            description: format!("wrong leaf value: tree={}, leaf={}", size, idx),
        });

        // 3. Wrong index (correct leaf + proof, but wrong position)
        let wrong_idx = (idx + 1) % size;
        vectors.push(MerkleVector {
            tree_size: size,
            depth,
            leaf_index: wrong_idx,
            leaf: to_hex(&leaves[idx]),
            proof: concat_proof(&siblings),
            root: to_hex(&root),
            expected: "reject".into(),
            description: format!(
                "wrong index {} (should be {}): tree={}",
                wrong_idx, idx, size
            ),
        });

        // 4. Wrong root (correct proof, but check against different root)
        let mut wrong_root = root;
        wrong_root[31] ^= 0x01;
        vectors.push(MerkleVector {
            tree_size: size,
            depth,
            leaf_index: idx,
            leaf: to_hex(&leaves[idx]),
            proof: concat_proof(&siblings),
            root: to_hex(&wrong_root),
            expected: "reject".into(),
            description: format!("wrong root: tree={}, leaf={}", size, idx),
        });

        // 5. Truncated proof (missing last sibling)
        if depth > 1 {
            let short_siblings = &siblings[..depth - 1];
            vectors.push(MerkleVector {
                tree_size: size,
                depth,
                leaf_index: idx,
                leaf: to_hex(&leaves[idx]),
                proof: concat_proof(short_siblings),
                root: to_hex(&root),
                expected: "reject".into(),
                description: format!("truncated proof: tree={}, leaf={}", size, idx),
            });
        }
    }

    vectors
}

fn main() {
    let vectors_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../vectors");
    fs::create_dir_all(&vectors_dir).expect("create vectors dir");

    // Inclusion vectors
    let inclusion = generate_inclusion_vectors();
    let inclusion_file = MerkleVectorFile {
        hash: "sha256".into(),
        vectors: inclusion,
    };
    let json = serde_json::to_string_pretty(&inclusion_file).unwrap();
    fs::write(vectors_dir.join("merkle_inclusion.json"), &json).unwrap();
    println!("Generated {} inclusion vectors", inclusion_file.vectors.len());

    // Rejection vectors
    let rejection = generate_rejection_vectors();
    let rejection_file = MerkleVectorFile {
        hash: "sha256".into(),
        vectors: rejection,
    };
    let json = serde_json::to_string_pretty(&rejection_file).unwrap();
    fs::write(vectors_dir.join("merkle_rejection.json"), &json).unwrap();
    println!("Generated {} rejection vectors", rejection_file.vectors.len());

    println!(
        "\nMerkle test vectors written to {:?}",
        vectors_dir
    );
}
