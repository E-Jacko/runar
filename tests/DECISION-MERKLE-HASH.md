# Decision: SHA-256 for On-Chain Merkle Verification

## Context

SP1/Plonky3 uses Poseidon2 over Baby Bear for internal STARK Merkle commitments. The BSVM on-chain FRI verifier needs a hash function for Merkle proof checking. Three options were considered:

1. **Poseidon2 over Baby Bear** — native to SP1, requires implementing the Poseidon2 permutation in Bitcoin Script
2. **SHA-256 with proof format adapter** — restructure the SP1 proof to use SHA-256 Merkle trees at the outer verification layer
3. **STARK-to-SNARK wrapping** — compress to Groth16, verify a pairing check instead of FRI

## Decision

**Option 2: SHA-256 at the outer FRI layer.**

## Rationale

- BSV has native `OP_SHA256` — single opcode, highly efficient in Script
- Avoids implementing the full Poseidon2 permutation in Script (~50 KB estimated)
- The SP1 proof can be restructured at the outer layer to use SHA-256 Merkle commitments while keeping Poseidon2 internally
- Rúnar already has `merkleRootSha256` and `merkleRootHash256` builtins with codegen across all 6 compilers

## Implications

- The proof format adapter must re-hash committed values into a SHA-256 Merkle tree before on-chain verification
- Poseidon2 implementation (Phase 4) is not required for the core FRI verifier path
- Phase 4 (Poseidon2) remains available as a future optimization if native SP1 proof replay is needed
