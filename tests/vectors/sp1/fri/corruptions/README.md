# Corruption fixtures — negative verifier tests

Negative fixtures for the SP1 STARK / FRI verifier. Each is derived from
`../minimal-guest/` by byte-level mutation — no prover run required —
by the generator in this directory.

```bash
cd tests/vectors/sp1/fri/corruptions
go run ./gen.go --base ../minimal-guest --other ../evm-guest --out .
```

Deterministic: the same base fixture always yields byte-identical output,
including every per-directory `README.md`. Each mutation is the *first*
candidate in a fixed search order, and single-byte proof mutations are
length-preserving (the LEB128 continuation bit is never touched), so no
downstream byte offset moves.

Every fixture directory contains the mutated file, an unchanged copy of the
other file, and a `README.md` recording the exact byte offset, original
byte, mutated byte, decoded field path, and observed rejection message.

## What each fixture proves

| Directory | Mutation | Documented reject point (§6) | **Actually rejected at** |
|---|---|---|---|
| `bad_merkle/` | flip one byte in the first input-MMCS sibling digest | Merkle root recompute | ✅ Merkle root recompute |
| `bad_folding/` | change one FRI query opened evaluation (commit-phase sibling) | Colinearity check | ⚠️ FRI commit-phase MMCS opening |
| `bad_final_poly/` | change the first final-poly Ext4 limb | Final-poly equality | ⚠️ input MMCS, via transcript divergence |
| `wrong_public_values/` | flip one byte of `public_values.hex` | Transcript divergence | ✅ commit-phase PoW witness |
| `bad_vk/` | VK hash from a different guest program | Transcript divergence | ❌ **not generated — impossible** |
| `truncated/` | strip the last 100 bytes of `proof.postcard` | Push-and-hash binding | ⚠️ postcard EOF off-chain; ✅ push-and-hash on-chain |
| `wrong_program/` | minimal-guest proof + a different program's public values | Transcript divergence | ✅ query-phase PoW witness |
| `all_zeros/` | 200 KB of `0x00` as `proof.postcard` | bincode length / hash | ✅ postcard trailing-bytes check |

✅ observed == documented · ⚠️ rejected, but elsewhere · ❌ no fixture

## Detection-point reality

Three rows do not reject where the original matrix claimed. The claims were
written before any fixture existed; these are the measured results.

**`bad_folding` — there is no reachable colinearity check.** Plonky3 FRI does
not assert colinearity arithmetically. Every value the fold consumes is
Merkle-committed, so `VerifyBatchExt` for the commit-phase round fires
strictly before any folding arithmetic runs. Colinearity is enforced *by* that
commitment check plus the final-poly equality — not by a separate branch a
corruption can reach.

**`bad_final_poly` — the final-poly equality branch is unreachable by byte
mutation.** `final_poly` is absorbed into the Fiat-Shamir transcript
(`sp1fri/fri.go`, step 4) *before* the query indices are sampled. Mutating it
re-randomises every query index, so the Merkle proof authenticates the wrong
leaf and MMCS fails first. Reaching `fri: query N final_poly mismatch` would
require a prover-side forgery that keeps the transcript fixed, which no
byte-level corruption can do.

**`truncated` — two different detection points.** Off-chain the postcard
decoder hits EOF before the verifier runs. On-chain there is no decoder, so
the documented push-and-hash binding really is the detection point; it is
asserted directly against `EmitProofBlobBindingHash`.

**`bad_vk` — cannot exist yet.** `minimal-guest` is a raw Plonky3 proof with
no SP1 outer wrapper, so it has no verifying key and no VK hash to corrupt.
The PoC parameter set encodes this (`SP1VKeyHashByteSize: 0`), at which the
compiler drops the `sp1VKeyHash` argument and never absorbs it — no VK hash
value can change any verifier decision. See `bad_vk/README.md`. The closest
runnable coverage is `wrong_program/`.

## On-chain coverage is narrower than off-chain — KNOWN GAP

The fixtures are replayed at two levels, and the two levels disagree.

| | off-chain reference (`sp1fri.Verify`) | compiled locking script |
|---|---|---|
| `bad_merkle` | rejects | **ACCEPTS** |
| `bad_folding` | rejects | **ACCEPTS** |
| `bad_final_poly` | rejects | **ACCEPTS** |
| `wrong_public_values` | rejects | rejects (`OP_VERIFY failed`) |
| `wrong_program` | rejects | rejects (`OP_VERIFY failed`) |
| `truncated` | rejects (decoder) | rejects (push-and-hash) |
| canonical fixture | accepts | accepts |

`EmitFullSP1FriVerifierBody` samples each FRI query index and immediately
drops it — its own Step 10 comment says *"For the deployable verifier we
sample-and-drop"*. The input-batch MMCS verify, the FRI fold chain and the
final-poly Horner equality are therefore never emitted. Only transcript-bound
checks (the commit-phase and query-phase grinding witnesses) reach the script,
which is exactly why the two transcript-divergence corruptions are caught and
the three Merkle corruptions are not.

**At the PoC parameter set a spender can supply forged Merkle openings and the
covenant will accept.** Soundness currently rests on the Fiat-Shamir
transcript, not on the proof. This is pinned — not skipped — by
`TestSp1FriVerifier_OnChainRejectsCorruptions`, which asserts the present
behaviour and fails with an ACTION REQUIRED message the moment the missing
emission lands.

## Consumed by

- `compilers/go/codegen/sp1_fri_negative_test.go`
  - `TestSp1FriVerifier_PositiveFixtureStillVerifies` — non-vacuity control.
  - `TestSp1FriVerifier_RejectsCorruptionFixtures` — per-fixture rejection +
    exact detection point + single-byte provenance check.
  - `TestSp1FriVerifier_TruncatedFailsPushAndHashBinding` — script-level
    push-and-hash binding, with its own non-vacuity twin.
  - `TestSp1FriVerifier_BadVkCorruptionIsDocumentedAbsent` — keeps the
    `bad_vk` gap honest in both directions.
- `compilers/go/compiler/sp1_fri_negative_test.go`
  - `TestSp1FriVerifier_OnChainRejectsCorruptions` — compiles the PoC covenant
    and replays each fixture through the go-sdk script interpreter.

## File naming

The proof file is `proof.postcard`, not `proof.bin`. Earlier drafts of these
READMEs said `proof.bin` and described the encoding as bincode; the fixture
that actually landed is postcard-encoded (`sp1fri.DecodeProof` is a postcard
reader). `public_values.hex` is lowercase hex with no `0x` prefix, decoding to
little-endian `u32`s — 12 bytes for the 3-value Fibonacci AIR.
