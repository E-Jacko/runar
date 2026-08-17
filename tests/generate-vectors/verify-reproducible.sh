#!/usr/bin/env bash
# -----------------------------------------------------------------------------
# RESEARCH-VECTOR REPRODUCIBILITY CHECK  (v1 audit — Go-only crypto oracle gap)
# -----------------------------------------------------------------------------
#
# BabyBear, KoalaBear, Poseidon2, BN254/Groth16, Merkle and the SP1 FRI verifier
# ship Stack-IR codegen in the GO TIER ONLY by project policy. Cross-tier parity
# is therefore definitionally vacuous for them — one implementation cannot
# disagree with itself — and `tests/vectors/*.json` is their entire oracle.
#
# Those vectors are derived from genuine second implementations (Plonky3 for the
# field/Poseidon2 families, gnark-crypto for BN254), but until this script
# existed nothing proved that the CHECKED-IN BYTES are what those upstreams
# actually produce. "Derived from Plonky3" was a claim in a comment. This script
# turns it into a check: it re-runs every generator and fails if a single byte of
# any checked-in vector moves.
#
# What it does NOT prove: that Plonky3 and gnark-crypto are themselves correct,
# or that the repo-authored parts (the SHA-256 Merkle tree shape, the FRI folding
# equation) match any upstream. See docs/audit/2026-08-go-only-crypto-oracles.md.
#
# Usage:
#   tests/generate-vectors/verify-reproducible.sh            # regenerate + diff
#   tests/generate-vectors/verify-reproducible.sh --list     # list what it covers
#
# Exit code: 0 = every vector reproduced byte-for-byte; 1 = a vector moved;
#            2 = a toolchain or generator failure.
# -----------------------------------------------------------------------------
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
GEN_DIR="$REPO_ROOT/tests/generate-vectors"
VECTORS_DIR="$REPO_ROOT/tests/vectors"

RUST_BINS=(
  generate_babybear_vectors
  generate_koalabear_vectors
  generate_poseidon2_kb_vectors
  generate_merkle_vectors
  generate_fri_vectors
)

if [ "${1:-}" = "--list" ]; then
  echo "Rust generators (Plonky3: p3-baby-bear, p3-koala-bear, p3-poseidon2):"
  printf '  %s\n' "${RUST_BINS[@]}"
  echo "Go generator (gnark-crypto):"
  echo "  tests/generate-vectors/bn254"
  echo ""
  echo "Checked-in vectors under tests/vectors/:"
  ls -1 "$VECTORS_DIR"/*.json | sed "s|$REPO_ROOT/|  |"
  exit 0
fi

fail() { echo "ERROR: $*" >&2; exit 2; }

command -v cargo >/dev/null 2>&1 || fail "cargo not found — needed for the Plonky3 generators"
command -v go    >/dev/null 2>&1 || fail "go not found — needed for the gnark-crypto generator"
command -v git   >/dev/null 2>&1 || fail "git not found — needed to diff the regenerated vectors"

# The checked-in vectors must be clean going in, or the diff at the end cannot
# distinguish "the generator moved a byte" from "someone had edits in flight".
if ! git -C "$REPO_ROOT" diff --quiet -- tests/vectors; then
  echo "ERROR: tests/vectors already has uncommitted changes; commit or stash them first." >&2
  git -C "$REPO_ROOT" status --short -- tests/vectors >&2
  exit 2
fi

echo "==> Building the Plonky3 vector generators (cargo build --release)"
( cd "$GEN_DIR" && cargo build --release ) || fail "cargo build failed"

for bin in "${RUST_BINS[@]}"; do
  echo "==> $bin"
  ( cd "$GEN_DIR" && "./target/release/$bin" ) || fail "$bin failed"
done

echo "==> bn254 (gnark-crypto)"
# GOWORK=off: tests/generate-vectors/bn254 is a standalone module, deliberately
# outside go.work so the gnark-crypto dependency stays out of the main workspace.
( cd "$GEN_DIR/bn254" && GOWORK=off go run . ) || fail "bn254 generator failed"

echo ""
echo "==> Comparing regenerated vectors against the checked-in bytes"
if git -C "$REPO_ROOT" diff --quiet --exit-code -- tests/vectors; then
  count=$(ls -1 "$VECTORS_DIR"/*.json | wc -l | tr -d ' ')
  echo "✓ all $count vector files reproduced BYTE-FOR-BYTE from their upstream generators"
  echo "  (Plonky3 p3-baby-bear / p3-koala-bear / p3-poseidon2, and gnark-crypto for BN254)"
  exit 0
fi

echo "" >&2
echo "✗ RESEARCH VECTORS ARE NOT REPRODUCIBLE — regenerating moved these files:" >&2
git -C "$REPO_ROOT" diff --stat -- tests/vectors >&2
echo "" >&2
echo "These vectors are the ONLY oracle for the Go-only crypto families (BabyBear," >&2
echo "KoalaBear, Poseidon2, BN254/Groth16, Merkle, SP1 FRI): those primitives ship in" >&2
echo "one tier, so cross-tier parity proves nothing about them. If regeneration moves" >&2
echo "a byte, either an upstream dependency changed under us or a checked-in vector was" >&2
echo "hand-edited. Resolve it deliberately — do NOT just commit the new bytes:" >&2
echo "  - upstream bump: pin the reason in tests/generate-vectors/Cargo.toml / go.mod," >&2
echo "    and add a conformance/golden-provenance-allowlist.json entry for each moved file" >&2
echo "  - hand-edit: revert it" >&2
exit 1
