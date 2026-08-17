# SP1 STARK / FRI test vectors

Consumed by the off-chain Go reference verifier (`packages/runar-go/sp1fri`)
and by the on-chain `runar.VerifySP1FRI` codegen (see
`docs/sp1-fri-verifier.md`).

## Layout

```text
tests/vectors/sp1/fri/
  minimal-guest/            # PoC fixture — Plonky3 fib_air, KoalaBear, 8-row trace
    proof.postcard          # postcard-encoded p3_uni_stark::Proof<MyConfig>
    public_values.hex       # lowercase hex, no 0x prefix; little-endian u32s
    README.md               # trace width, degree_bits, params, regen cmd
    regen/                  # Rust fixture generator (outside the Go workspace)
  evm-guest/                # production-parameter fixture — 1024-row trace
    ...same shape...
  corruptions/              # negative fixtures, derived from minimal-guest/
    gen.go                  # deterministic generator (stdlib-only, no module)
    README.md               # corruption matrix + measured detection points
    bad_merkle/             # proof.postcard + public_values.hex + README.md
    bad_folding/
    bad_final_poly/
    wrong_public_values/
    bad_vk/                 # README.md only — see below
    truncated/
    wrong_program/
    all_zeros/
```

**There is no `proof.bin` and no `vk_hash.hex`.** Earlier drafts of this file
described a bincode-encoded `proof.bin` plus a per-fixture `vk_hash.hex`;
neither ever landed. The proofs are postcard-encoded, and neither guest
fixture is wrapped in an SP1 outer proof, so no verifying key — and therefore
no VK hash — exists for them. `corruptions/bad_vk/` is a README explaining why
that one corruption cannot be produced.

## Status

- **minimal-guest** — committed. Accepted end-to-end by the Go reference
  verifier (`sp1fri.TestVerifyMinimalGuest`) and by the compiled PoC covenant
  through the go-sdk script interpreter.
- **evm-guest** — committed at the production parameter tuple
  (`num_queries=100`, `log_blowup=1`, `degreeBits=10`). Accepted by
  `sp1fri.TestVerifyEvmGuest`.
- **corruptions** — 7 of the 8 documented corruptions are committed and
  asserted by the negative tests listed in `corruptions/README.md`. The 8th
  (`bad_vk`) is documented as impossible at the current parameter set.

The corruption suite records a real divergence: the off-chain reference
verifier rejects all seven, but the **currently emitted locking script accepts
three of them** (`bad_merkle`, `bad_folding`, `bad_final_poly`) because the
per-query Merkle / fold / final-poly chain is not emitted. See
`corruptions/README.md` ⇒ "On-chain coverage is narrower than off-chain" and
`docs/sp1-fri-verifier.md` §6.

## Regeneration summary

See each subdirectory's `README.md` for exact commands. High-level:

- `minimal-guest` and `evm-guest` are Plonky3 `fib_air` proofs with the
  configuration pinned to SP1 v6.0.2's DuplexChallenger + TwoAdicFriPcs +
  KoalaBear base field. Regeneration requires the Rust toolchain and network
  access to fetch Plonky3; see each fixture's `regen/`.
- Corruption fixtures are produced programmatically from `minimal-guest/` by
  `corruptions/gen.go`. No prover run, no network, no randomness.

## Upstream version pinning

| Component  | Version     | Source                                     |
|------------|-------------|--------------------------------------------|
| SP1        | v6.0.2      | https://github.com/succinctlabs/sp1        |
| Plonky3    | pinned by SP1 v6.0.2 `Cargo.lock`          |  |
| KoalaBear  | Plonky3 koala-bear crate                   |  |
| Poseidon2  | Plonky3 koala-bear/src/poseidon2.rs        |  |

Any version bump MUST (a) regenerate every fixture in this tree — including
re-running `corruptions/gen.go`, (b) re-run the entire verifier test suite
against the new fixtures, (c) re-run the regtest measurement pass, (d) update
`docs/sp1-proof-format.md` §1 with the new pinned version strings.
