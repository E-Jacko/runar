# bad_vk — NOT GENERATED

**There is no fixture in this directory, and there cannot be one yet.**

The original corruption matrix specified "use a VK hash from a different guest
program", expecting a `vk_hash.hex` alongside the proof. That file does not
exist for `minimal-guest/`, and a corruption cannot be derived from an input
that has no original.

## Why there is no VK hash to corrupt

`minimal-guest/proof.postcard` is a raw Plonky3 `p3_uni_stark::Proof` — a
Fibonacci AIR proven directly over KoalaBear. It is not wrapped in an SP1
outer proof, so it has no SP1 verifying key and therefore no keccak256 VK
hash. This is not an oversight in the fixture; it is why the validated PoC
parameter set pins

    SP1VKeyHashByteSize: 0

in both `compilers/go/codegen/sp1_fri.go::DefaultSP1FriParams()` and
`packages/runar-go/sp1fri/unlocking.go::MinimalGuestParams()`. At that
parameter set the `sp1VKeyHash` argument is not pushed by the unlocking
script and is not absorbed into the Fiat-Shamir transcript by the emitted
locking script — the compiler explicitly drops it
(`sp1_fri.go::lowerVerifySP1FRI`, the `SP1VKeyHashByteSize == 0` branch).

The off-chain reference verifier agrees: `sp1fri.Verify(proof, publicValues)`
takes no VK hash parameter at all.

**A wrong VK hash therefore cannot change any verifier decision at the PoC
parameter set.** A fixture here would be inert bytes with no test able to
make a meaningful assertion about them, which is worse than an empty
directory.

## What would have to land first

1. A fixture whose proof is a real SP1 outer proof with a verifying key
   (`evm-guest/` is still a raw Plonky3 proof, not an SP1 wrapper).
2. A parameter set with `SP1VKeyHashByteSize == 32` wired end-to-end, so the
   VK hash is actually absorbed into the transcript.

Until both exist, the closest runnable coverage is `../wrong_program/`, which
binds the minimal-guest proof to a different program's public values — the
only program-identifying input the verifier currently consumes.
