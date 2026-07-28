# Per-fixture spend witnesses (TS-GAP-004)

Each `<fixture>.json` declares concrete spend attempts for the differential
execution oracle (`packages/runar-testing/src/oracle/differential-execution.ts`).
The oracle compiles the fixture to its **fold-ON deployed bytes**, runs the
declared spend through the ANF interpreter (source semantics) *and* through the
`@bsv/sdk`-backed `ScriptVM` (script semantics), and asserts both engines agree
on accept/reject — catching a bug all seven compilers share (byte-identical but
wrong). Every non-crypto conformance fixture SHOULD have one.

Schema:

    {
      "fixture": "arithmetic",
      "constructorArgs": { "target": "27n" },
      "spends": [
        { "method": "verify", "args": ["3n", "7n"], "expect": "accept",
          "note": "10 + (-4) + 21 + 0 = 27" },
        { "method": "verify", "args": ["3n", "6n"], "expect": "reject",
          "note": "near-miss: result 24 != target 27" }
      ]
    }

- `fixture` — the directory name under `conformance/tests/`. The `.runar.ts`
  source is resolved from that fixture's `source.json` (`sources[".runar.ts"]`).
- `args` and `constructorArgs` use the trailing-`n` convention for bigints
  (`"27n"`, `"-4n"`), `true`/`false` for booleans, and `"0x…"` for byte strings.
- `method` — a `public` method of the contract (a spending entry point). For a
  contract with more than one public method, the oracle appends the compiled
  method-selector index automatically; witness authors only list the method's
  own args.
- Every fixture MUST have ≥1 `accept` and ≥1 `reject` (near-miss) spend, ENFORCED
  in code by `coverage-claims.test.ts` — not just documented here. A few
  contracts have only tautological asserts (`x >= 0 || x < 0`) or are
  anyone-can-spend, so no rejecting witness exists; those set a top-level
  `"acceptOnly": true` field (see `bitwise-ops.json` / `shift-ops.json`) as an
  explicit, machine-checked opt-out — a silently absent reject spend fails the
  gate. `coverage-claims.test.ts` also flags a spec that sets `acceptOnly` but
  actually has a reject spend (a stale opt-out).

## Real-crypto execution (`real-crypto/`) — post-mortem remediation #1

The plain differential oracle runs on the in-process `ScriptVM`, whose
`checkSigCallback` defaults to MOCK crypto (`() => true`) and which has NO tx
context — so it can neither verify a real signature nor a real BIP-143 sighash
preimage. Every fixture needing a signature or a tx-context preimage was
therefore routed OUT into the coverage ledger (`coverage-ledger.json`)
and got **no real execution** — the exact blind spot behind BUG-100 / #99 /
#100 / #44 (all seven tiers agreed on bytes nobody ever ran with real crypto).

`real-crypto/<fixture>.json` closes that gap. Each spec is EXECUTED by
`real-crypto-execution.test.ts` through `@bsv/sdk`'s production `Spend`
interpreter — real secp256k1, real BIP-143 sighash, real `OP_CHECKSIG` /
`OP_CHECKMULTISIG` / `OP_CODESEPARATOR` / `checkPreimage`. Two kinds:

- **`stateless-signed`** — a stateless `SmartContract`. `$sig` args are filled
  with a real DER signature over the real single-input sighash
  (`runStatelessSigned` in `runar-testing`). The accept path is additionally
  cross-checked against the ANF interpreter (source-vs-script agreement); the
  interpreter's `checkSig` does REAL ECDSA over a fixed `TEST_MESSAGE`, so it is
  fed each key's precomputed `testSig`. (`checkMultiSig` is unimplemented in the
  interpreter, so multisig fixtures set `checkInterpreter: false`.)
- **`stateful`** — a `StatefulSmartContract` driven deploy→call through the SDK
  (`RunarContract` + a real `LocalSigner`) and re-validated on `Spend`
  (`runStatefulSpend`). This exercises the real auto-injected `checkPreimage`
  on-chain state binding (BUG-100) plus any user `checkSig`.

Each fixture carries ≥1 accept and ≥1 reject/near-miss, ENFORCED in code by
`coverage-claims.test.ts` (same `acceptOnly` opt-out convention as above). A
near-miss is a wrong key, a wrong signer (`owner` ≠ the call signer), or a
**tampered continuation output** (`tamperOutput: true` — corrupts output 0 so
the recomputed sighash no longer matches the on-stack preimage; the exact
BUG-100 property). Because the interpreter models crypto with real-but-fixed
`TEST_MESSAGE` checks it cannot model an arbitrary tx-context rejection, so a
crypto near-miss is a script-only rejection flagged `cryptoNearMiss: true`.

Placeholders resolve against `runar-testing`'s deterministic `TEST_KEYS`:
`{"$pubkey":"alice"}`, `{"$pkh":"alice"}` (ctor + args), `{"$sig":"alice"}`
(a real signature slot). Scalars use the trailing-`n` bigint convention, bare
hex for byte payloads, `true`/`false`, and `null` for an SDK-auto-signed Sig.
`satoshis` sets a continuation output amount that must match a method's
explicit `addOutput(<sats>, …)`; `lockTime` threads `nLockTime` for
`extractLocktime` / `currentBlockHeight` introspection.

## Exemptions — every fixture is witnessed, executed, OR in the coverage ledger

`completeness.test.ts` fails CI if any `conformance/tests/<fixture>` is neither
witnessed here, executed in `real-crypto/`, nor listed in **`coverage-ledger.json`**
with a `coveredBy` claim that is NOT `"UNCOVERED"` (and fails if
a `real-crypto/` fixture is ALSO still listed in the ledger — a stale over-claim
guard).

`coverage-ledger.json` is the SINGLE ledger of fixtures the plain differential
oracle does not execute. (It replaces the former `crypto-exempt.json` +
`harness-inapplicable.json` pair, which were the same mechanism read by the same
tests and differed only in that the second carried a `cause` discriminator.)
Each entry is `{fixture, cause, reason, coveredBy}`; the `cause` field is a
closed vocabulary, enforced by `coverage-claims.test.ts`:

- **`crypto-witness-infeasible`** — the spend needs a REAL cryptographic
  witness (ECDSA/Schnorr checkSig, secp256k1 / NIST-P EC, SHA-256 / BLAKE3 /
  RIPEMD / Merkle hash-preimage, Rabin, or a post-quantum SLH-DSA / WOTS+
  signature) that the in-process oracle cannot synthesise from plain args.
  This cause also records PROVENANCE: it marks exactly the entries that used to
  live in `crypto-exempt.json`, so the pre-merge partition stays recoverable.
  A handful of them (`all-readonly-cleanstack`, `covenant-vault`,
  `merkle-proof`, `state-covenant`) were historically filed there but read as
  `stateful-harness-gap` / `go-only`; the merge did NOT silently reclassify
  them. Reclassify deliberately, not as a side effect of another change.
- **`stateful-harness-gap`** — non-crypto: the SDK `call()` continuation path
  cannot reconstruct the exact tx shape a `StatefulSmartContract` method
  demands.
- **`go-only`** — `compilers:[go]` fixtures have no TypeScript codegen, so
  `compile()` cannot emit deployed bytes for the TS-based harness to run.
- **`interpreter-unsupported`** — the ANF interpreter does not model the
  intrinsic the fixture uses (today: the raw-script `asm` intrinsic).

Each entry's free-text `reason` is for humans only, and `cause` says only WHY
the plain oracle is out of the picture — neither is evidence. The MACHINE-CHECKED
truth of "what actually covers this fixture" lives in a structured `coveredBy`
field, verified by `coverage-claims.test.ts` — list membership alone is never
treated as coverage (this is the fix for a past bug where several entries
claimed "Covered by the Go tx-context path" / `script_execution_test.go`
without that file actually referencing the fixture). `coveredBy.kind` is one of:

- `"go-script-exec"` — the fixture's exact name is compiled and executed by
  `conformance/script_execution_test.go` (`compileRúnar("<fixture>", ...)`).
  Verified by grepping that literal call.
- `"go-family-exec"` — the fixture's underlying primitive (not the literal
  fixture contract) is exercised by a real Go test function
  (`coveredBy.marker`, e.g. `"TestSha256Compress_"`) in
  `script_execution_test.go`, via an inline reconstruction of the same
  codegen — real execution, but not of this exact fixture's bytes.
- `"integration"` — an on-chain regtest integration test (`coveredBy.path`
  under `integration/<tier>/`) deploys and spends the fixture's actual
  `.runar.ts` source. Verified by checking the file exists and references the
  fixture name.
- `"interpreter-witness-exec"` — the ANF interpreter (TS tier only) executes
  the fixture with realistic tx-context witness bytes injected via
  `TestContract.setPrevOutScript` / `setSerialisedOutputs` /
  `setMockPreimageBytes` (`coveredBy.path`). Real execution of the desugared
  intrinsics, but not full Bitcoin Script bytes.
- `"anf-cross-tier-parity"` — `conformance/anf-interpreter/cross-interpreter.test.ts`
  runs the fixture's method through the ANF interpreter across all 7 tiers
  (TS reference + per-language drivers under `conformance/anf-interpreter/drivers/`)
  and asserts the resulting state/outputs match a pinned golden
  (`coveredBy.input` names the `conformance/anf-interpreter/inputs/<file>.json`
  case). Proves cross-tier interpreter correctness; it is a DIFFERENT
  guarantee than the source-vs-script differential above (it does not compare
  against compiled Bitcoin Script bytes and has no accept/reject witness
  concept), so it is called out as its own kind rather than folded into
  `interpreter-witness-exec`.
- `"codegen-golden"` — byte-golden only, NOT executed by any engine. An honest
  opt-out: requires the fixture's own `expected-script.hex` to exist and,
  where a family has one, its dedicated codegen module
  (`packages/runar-compiler/src/passes/<family>-codegen.ts`) to exist.
- `"go-only-nocodegen"` — `compilers:["go"]` proof-system fixture; verified
  against the fixture's `source.json`.
- `"sdk-corner"` — an acknowledged SDK/harness limitation with no further
  machine-checkable evidence beyond a non-empty `reason`.
- `"UNCOVERED"` — genuinely unexecuted anywhere today. Requires a non-empty
  `issue` field describing the follow-up. `completeness.test.ts` does NOT
  count an `"UNCOVERED"` fixture as covered — the top-level completeness gate
  fails on it BY DESIGN, so a real coverage hole cannot hide behind list
  membership. No entry currently carries this kind (`asm-raw-script`, the last
  one that did, is now executed by `script_execution_test.go`); the kind stays
  supported so a future hole can be recorded honestly instead of dressed up.

## Why the other ledgers stay separate

`coverage-ledger.json` merged the only two files that were the same mechanism.
The repo has several other allowlist/ledger files. They look similar and are
NOT fragmentation — each answers a different question, has a different
lifecycle, and is enforced by a different gate. Do not fold them in:

- **`conformance/golden-provenance-allowlist.json`** — "was this changed golden
  file's new content reviewed?" Entries are sha256 content-pins plus a reviewer
  sign-off, and they go STALE the moment the golden legitimately changes. The
  coverage ledger pins no bytes and is expected to outlive individual goldens.
- **`conformance/fold-on-allowlist.json`** — the constant-folding parity axis:
  "this fixture's 7 tiers are allowed to disagree with fold ON." Nothing to do
  with whether an execution engine runs the fixture. Currently empty, and the
  right state for it is empty.
- **`conformance/sdk-output/coverage-allowlist.json`** — a different suite
  entirely (the 7-SDK deployed-locking-script comparison), prose-mapped rather
  than `coveredBy`-structured.
- **`conformance/source-map/anchor-known-issues.json`** — per-`(fixture, tier)`
  source-map anchor signatures. It is EMPTY and must stay empty; merging it
  into a populated file would hide that property.
- **`conformance/script-size-baseline.json`**, **`conformance/mutation/baseline.json`**
  — measurements, not exemptions. They record what IS, and a diff against them
  is the signal; they never assert that something is covered.
## Known architectural residual — non-executed goldens (deep-review C24)

Everything above makes coverage *claims* machine-checked. It does not make every
golden *executed*. Deep-review finding C24 names the leftover risk explicitly, and
this section is its acknowledgement rather than a fix, because closing it needs
capability the harness does not have (see "What would actually close it").

**The shape of the risk (the BUG-101 class).** A golden is produced by the very
implementation under test. Cross-tier parity proves the seven compilers *agree*;
it does not prove they are *right*. When no engine ever executes a fixture's
bytes, seven tiers can agree on a wrong answer indefinitely — which is exactly
what happened in BUG-101 (BLAKE3 was byte-identical across all tiers and wrong in
all of them, because nothing ever ran it against a KAT). "Parity-green-but-wrong"
is a real, observed failure mode in this repo, not a hypothetical.

**Current exposure — 15 fixtures.** Both categories are legitimate opt-outs, both
are machine-verified as *claims* by `coverage-claims.test.ts`, and neither is
execution:

- `codegen-golden` (11) — byte-golden only, executed by no engine:
  `convergence-proof`, `ec-demo`, `ec-unit`, `oracle-price`,
  `p256-primitives`, `p256-wallet`, `p384-primitives`, `p384-wallet`,
  `post-quantum-wallet`, `schnorr-zkp`, `sphincs-wallet`.
  Mostly EC / NIST-P / post-quantum verification scripts. They are unexecuted
  because the accept path needs a real cryptographic witness the in-process
  oracle cannot synthesise from plain args, and several compile to 200-900 KB of
  script. Their PRIMITIVES are covered elsewhere (`real-crypto/`, the Go
  `go-family-exec` markers, KAT vector tests) — it is these fixtures' own
  composed bytes that nothing runs.
- `go-only-nocodegen` (4) — `compilers:["go"]` proof-system fixtures:
  `babybear`, `babybear-ext4`, `merkle-proof`, `state-covenant`. Single-tier by
  project policy (see the EVM/STARK note in the root `CLAUDE.md`), so they have
  no cross-tier agreement signal at all — a Go-only bug in these has neither an
  execution check nor a parity check standing behind it.

**What is actually guaranteed today.** For these 15: the bytes are stable
(a silent regeneration fails the golden-provenance gate), the fixture parses in
all seven frontends (the parser-only matrix ignores the `compilers` allowlist),
and for the 11 non-single-tier ones the seven compilers agree byte-for-byte.
That is meaningful but it is *consistency*, not *correctness*.

**What would actually close it.** Per family, one of: (a) an official KAT
executed against the compiled bytes (this is what fixed BUG-101 — SLH-DSA and
BLAKE3 now carry real KATs); (b) a real-crypto witness under
`witnesses/real-crypto/` once the harness can synthesise the needed signature or
proof; or (c) an on-chain regtest integration spend under `integration/`. Prefer
(a) — it is the only one that catches an all-tiers-agree-and-all-are-wrong bug,
because its expected values come from outside this codebase entirely.

**Do not "fix" this by relabelling.** Moving a fixture from `codegen-golden` to a
stronger-sounding `coveredBy.kind` without adding real execution makes the gate
report better coverage than exists — the precise over-claim
`coverage-claims.test.ts` was written to prevent.
