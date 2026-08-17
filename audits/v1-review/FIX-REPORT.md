# Rúnar v1 — three-way audit FIX REPORT

Branch `fix/v1-audit-triage`, 26 commits off `main` @ `52de4384`. Nothing pushed.
Triage and disputes: `TRIAGE.md`, `DISPUTED.md`.

---

## Counts

| | n |
|---|---|
| findings merged (CC 16 + CX 8 + GK 35) | 59 |
| root-cause clusters | 15 |
| S0/S1 reproduced | 4 of 8 claimed |
| **defect clusters FIXED** | **5 of 5** |
| machinery gaps closed | 3 of 9 |
| disputed / not reproduced | 5 |
| Grok probes executed | 50 |

A fourth review set (`codex/v1-review`, 6 findings) was found and is **superseded** —
see `TRIAGE.md` §0. Its headline S1 does not reproduce at HEAD.

---

## Defects fixed

### C1 (S0) — inherited-arm layout rotation, issue #149
**Root cause:** adopting a declared result puts it on TOP, but its pre-`if` binding lived
BENEATH the intervening slots; removing the stale copy does not reorder those, so the
result crosses them — layout rotates while NAME SET and DEPTH are unchanged, invisible to
both the reconcile's name-set check and Layer C's depth check. That is why seven tiers
agreed on broken bytes.

**Fix:** sink the adopted result block back under the slots it crossed. Applied
UNCONDITIONALLY — gating on the `if`'s own empty else was tried and is wrong, because the
asymmetry belongs to the ENCLOSING `if`, which `lowerIf` cannot see. The #149 inner `if`
has a real else, so the gate disabled the repair exactly where it was needed.

**Tests that now prevent it:** the pinned reduction un-skipped
(`nested-declared-results-arm-layout-vm.test.ts`) **plus two surfaces it never covered**
(`branch-inherited-layout-directions-vm.test.ts`): the wrongly-SPENDABLE mirror direction
and the stateful `addOutput` continuation. 12 red → green.

**Tiers:** all 7, byte-identical, verified by me per tier — not taken from agent reports.

### C2 (S1) — `readonly` writes accepted by every tier
`spec/semantics.md:247` defines it as an ERROR; no tier implemented it. A contract
reassigning its readonly owner compiled to `76a97ca9788777` — 7 bytes true for ANY pubkey.
Now rejected in all 7 tiers, constructor assignment still allowed. Verified per tier on
the Python-surface repro.

### C3 (S2) — non-literal property initializer
`rust/zig/python/ruby` accepted a program `ts/go/java` reject. Now all 7 reject.

### C4 (S2) — `MockProvider.broadcast` never registered the tx
`getTransaction` always threw post-broadcast; `contract.ts` swallowed it and returned an
empty shell (`inputs: []`, `outputs: []`), so any test asserting on `result.tx.outputs`
passed vacuously. Fixed in TS and Go SDKs, TDD both. The swallow was deliberately NOT
converted to a throw — a real node can 404 a tx it accepted but hasn't indexed; the
fallback now returns the bytes actually broadcast.

### C5 (S3) — documented axiom count contradicted the enforced gate
`CORRECTNESS.md` said 70; manifest and gate say 71. Corrected, plus the retired
`exists_checkSig_witness_under_validTxContext` no longer described as live.

---

## Machinery closed

### M1 — generator reach (the gap that let C1 ship)
`--spend-oracle` reported 0 failures over 11,750 spend inputs while #149 was open. Root
cause: reaching it needs TWO degrees of freedom the corpus never drew together — a live
UNTOUCHED sibling in the inherited region AND an outer `if` with no else.

Added `nested-sibling` at k=2/3/4 + `merge-nested-sibling` in `REQUIRED_TAGS`.
**RED/GREEN proof:** 62/56/86/72/42 failures across 5 fresh seeds without the fix,
**0 with it**. Also extended `arbExecMethodBody` (previously emitted ZERO `if`s) with
branch shapes and an ORDER-SENSITIVE terminal assert — a commutative assert reports
agreement on a script that read the wrong slots, measured directly.

### M2-partial — the axiom inventory is now machine-checked
`check-tcb-drift.sh` enforced only the grand total; the per-file table was unverified
prose and had drifted in FOUR rows (`Eval` 24→7, `Crypto/Spec` 46→38, `Rabin` 1→0,
`StatefulBridge` 1→0) with `AgreesStateful` (2) missing — the column summed to **96, not
71**. Now parsed and verified per file, both directions. **Demonstrated failing:**

```
DRIFT: TRUST_MANIFEST.md claims .../Stack/Blake3.lean has 99 axiom(s); the source has 2
DRIFT: inventory sum = 168 (expected 71)     EXIT=1
```

### CI — spend-oracle PR gate raised 32 → 35
`REQUIRED_CASE_COUNT` is 35; families draw round-robin, so `--num 32` skipped exactly the
three families added to cover #149 — while still reporting a pass.

---

## Verification at HEAD — full `test:ci` + all native suites

**`pnpm run test:ci`, every stage:**

| stage | result |
|---|---|
| `lint:silent-skips` | ✅ 133 skip sites / 65 inventory rows, every site documented, every row live |
| `typecheck` | ✅ 13 / 13 |
| `test:all` → conformance TS goldens | ✅ 71 / 71 |
| `test:all` → multi-format parity (fold-off **and** fold-on) | ✅ **639 / 639** each |
| `test:all` → sdk-output conformance | ✅ 59 fixtures × 7 SDK tiers |
| `test:all` → anf-parity ×3, examples ×7, e2e ×7, wallet-client ×7 | ✅ exit 0 |
| **`integration:all`** (`RUNAR_INTEGRATION_STRICT=1`, live regtest) | ✅ **all 7 tiers PASSED**, exit 0 |
| `lean:verify` | ✅ exit 0 (see re-attestation note) |

**Native compiler suites, all seven:**

| tier | result |
|---|---|
| TypeScript | 274 files pass, 4 skipped, 0 fail |
| Go | all packages `ok` |
| Rust | 0 failed |
| Python | 1160 passed, 1 skipped |
| Zig | exit 0 |
| Ruby | 0 failures, 0 errors |
| Java | BUILD SUCCESSFUL |

This closes the gap flagged earlier: C2/C3 changed the validator in every tier,
and each tier's own suite now confirms no false positives (constructor
assignment to a readonly property still compiles everywhere).

**Two things that needed intervention, recorded rather than smoothed over:**

1. `conformance:sdk` invokes `npx tsx` from the repo root, and the runner then
   spawns `tsx` again for the TypeScript tier. In a worktree with no root-level
   tsx this dies as `sh: tsx: command not found` — reported as a TypeScript-TIER
   FAILURE while the other six tiers pass, which reads like a code defect. Run
   with tsx on PATH it is 59 × 7 green. **The stage as written did not run clean
   end-to-end here**; this is real CI fragility, listed as open risk 10.
2. `lean:verify` initially exited 1: the comment-only Lean edits moved the
   content-hashed model fingerprint, invalidating recorded attestations for four
   fixtures. Re-attested — but backed by a `RUNAR_VERIFICATION_REGEN=1` re-derive
   reporting `[fresh]` (stored == live `compileHex`) for all four, plus a strict
   axiom count of 71 on both revisions and no changed declaration line. That gate
   was right to refuse a bare re-stamp.

**Other gates:**

| gate | result |
|---|---|
| `lake build` | exit 0, 0 errors, **0 `sorry`** |
| `check-tcb-drift.sh` | axioms 71, **inventory sum 71**, exit 0 |
| golden-provenance gate | exit 0 (`differential-oracle`) |

**Goldens changed: exactly one**, with approval — `assert-false-guard` 2019 → 2033 bytes
(+0.69%, inside the 10% tolerance; `script-size-baseline.json` NOT edited). `expected-ir.json`
untouched (fix is pass 5; IR golden is pass-4 ANF). Stamped only after all seven tiers
independently regenerated the bytes. **No `intentional-spec-change` entry was added. No
allowlist entry of any other kind was added.**

The provenance entry states plainly that the fixture's real-crypto witness passed on the
OLD bytes too, so it does **not** claim the old golden was wrong — this fixture behaved
correctly before and after; what moved is codegen.

---

## Two claims I had to overturn

**A subagent reported a second S0** — a guard bypass "orthogonal to #149, not fixed by the
C1 commit", firing on 5/5 seeds. It is neither. Reproducing its own minimized contract:
without the fix → bypass on `param0` = 0 and −1 in both fold modes; **with the fix → all
agree**. The agent applied the fix to TypeScript source but the oracle runs from `dist/`;
without a rebuild its "with fix" and "without fix" runs executed identical bytes. Not filed.

**I nearly filed a false S0 myself.** Seven of Grok's probes showed `interp=true /
spend=false`, three with clean-stack violations — broader than #149. All are STATELESS
contracts I was driving through the STATEFUL `deploy`+`call` path. Through the correct
stateless oracle every one agrees. Recorded in `DISPUTED.md`.

Both were the same failure mode — a stale or wrong harness — which is exactly what the
audit says lets defects through.

---

## Round 2 — resolving the open risks

### A NEW S0 fell out of risk 7, and it was hiding behind a vacuous test

Probes P16/P17/P18 were recorded INCONCLUSIVE. Resolving them properly:

- **P16** (negative `OP_DIV`/`OP_MOD`) — **cleared**. 12 runs, both fold modes,
  0 divergences, and **non-vacuous**: 2 accepts / 10 rejects, so both verdicts
  are genuinely exercised.
- **P17** (`safediv`/`safemod` zero divisor) — **probe authoring error**, not a
  defect. `spec/grammar.md:676` defines these as *asserting* `b != 0`, so a zero
  divisor correctly aborts; the probe expected `0`.
- **P18** (shift ≥ width) — agreement was **VACUOUS**: every input rejected, so
  interpreter/script agreement proved nothing. Forcing an accepting input
  exposed a real, previously-unknown **S0**.

**The defect.** `OP_LSHIFT`/`OP_RSHIFT` preserve byte length, so `1 >> 1` leaves
`[0x00]` — a NON-MINIMAL zero. Every numeric consumer on chain decodes with
`fRequireMinimal=true` and ABORTS. The ANF interpreter threaded `scriptBytes`
through `& | ^ << >>` (the 2026-07 #141 fix) but the numeric cases read only the
decoded value and dropped them — re-minimising and ACCEPTING a spend no node
accepts. `TestContract` green, deployed UTXO unspendable.

```
n=1  (n >> 1) === 0   interp=true  spend=false   "non-minimally encoded script number"
n=1  (n << 64) === 0  interp=true  spend=false   same
n=2  (n >> 1) === 1   both accept                (minimal result — unaffected)
```

Fixed in TS by gating exactly the numeric consumers (`+ - * / %`, the
comparisons, and a shift's COUNT); byte ops untouched so
`2026-07-14-chained-shift-or-nonminimal` still passes. Ported to the other tiers
(in flight at time of writing — see status below).

**It also exposed a weak oracle.** `script-number-bitwise-chained.test.ts`
compared against the bare `ScriptVM`, whose `success` is "no evaluation error and
truthy top of stack" — no consensus wrappers, so no minimal-encoding rule.
Measured over its own 126-case sweep after the fix: interpreter vs **consensus
`Spend` = 0 mismatches**; vs bare `ScriptVM` = **22**. Re-keyed onto consensus,
and the replay harness gained an `oracle: tri-modal` mode so a divergence only a
real node sees can be pinned at all.

**Regression entry proven, not assumed:** with the fix reverted the new entry
FAILS; restored, the corpus is 6/6. That is the property CC-012 found missing.

### Risk 5 reclassified — it is dead code, not a coverage hole

CC-016 called `05-stack-lower.ts:2212` a zero-coverage *reachable* path. Measured
by instrumenting the body and counting firings: **0** across all 71 fixtures,
9 hand-designed terminal-`if` shapes, 1200 `--tri-modal` runs and 400
`--spend-oracle` cases. So the surviving mutant there is an **equivalent mutant
over dead code**, not coverage debt — a different finding, and the mutation score
should stop counting it. Not deleted: "I could not reach it" is not "provably
unreachable", and removing a defensive cleanup from `lowerIf` on that evidence is
not a trade worth making before v1. Recorded in-code with what would change the
decision either way.

## Open v1 risks — final

Every item the audit raised is now closed, deferred with a stated reason, or
recorded as an accepted limitation with a detector attached. Nothing below is a
known-wrong behaviour that ships silently.

| # | item | disposition |
|---|---|---|
| 1 | `--execute` blind to #149 | **CLOSED.** `nested-sibling-no-else` shape added; control run (pristine generator, same broken compiler) = **0** divergences, extended generator = **11/14/17** across three seeds. |
| 1b | `fuzz:execute:gate` could not catch it | **CLOSED.** Sized empirically against the regression: 60→0, 300→0, 600→10, 1000→11. Raised to 1000 (31s). |
| 2 | GK-031 upstream BIP-143 | **CLOSED.** Fixed upstream; the repo held the bug with a stale `<0.3` floor. Now `>=0.2.89`, carve-out removed, **all** inputs validated. |
| 2b | GK-032 OP_PUSH_TX | **CLOSED as a non-defect, and re-diagnosed.** Not a parser desync: Rúnar deliberately emits `OP_2MUL` (Chronicle, `06-emit.ts:89`); Rust's `bsv-sdk` is pre-Chronicle. Opcode-profile mismatch, nothing to file. Two pins added, one mutation-checked. |
| 3 | 27 self-attested provenance entries | **CLOSED.** All 27 substantiated by running their named oracles; **14 carried factually wrong text**, 3 materially so. Zero self-attested entries remain, and the gate now rejects them (demonstrated failing). |
| 4 | Go-only crypto KATs | **CLASSIFIED + strengthened.** No family has an official upstream KAT for its arithmetic; most are (b) second-implementation (Plonky3/gnark) and now **reproducibility-enforced**. `bn254_pairing.json` had **zero consumers** — 4 vectors never executed; now 34 with a consumer. |
| 5 | `lowerIf:2212` mutation survivor | **RECLASSIFIED.** Measured unreachable (0 firings across 71 fixtures, 1200 tri-modal, 400 spend-oracle). Equivalent mutant over dead code — and it accounts for 8 of the class, not 1. |
| 6 | Axiom taxonomy drift | **CLOSED.** Labelled a dated snapshot; the authoritative table is now machine-checked per file. |
| 7 | Probes P16/P17/P18 | **CLOSED** — and P18's *vacuous* agreement exposed a new S0 (non-minimal shift), fixed in **all seven** ANF interpreters plus the AST interpreter. |
| 8 | `test:ci` end-to-end | **CLOSED.** All stages green incl. on-chain integration on 7 tiers. |
| 9 | Zig diagnostic | **CLOSED — and my finding was wrong.** Zig exits 1 with a descriptive message; "terse" was an artefact of my own `tail -1`. Only the property name was missing; added. |
| 10 | `conformance:sdk` ambient tsx | **CLOSED.** Resolves the repo-local binary. |
| 11 | 24 untriaged mutation survivors | **CLOSED.** All **66** triaged (not 25): 60 equivalent with stated reasons, **6 real holes** — including the `sinkBelow` DISTANCE at `05-stack-lower.ts:2538`, i.e. a gap in the #149 fix's own coverage. 16 pins added and verified by running the mutation gate. |
| **NEW** | **SP1 FRI on-chain verifier is not sound** | **CLOSED as a shippable defect.** `sample-and-drop` means the per-query chain is never emitted, so `bad_merkle`/`bad_folding`/`bad_final_poly` are ACCEPTED on-chain. The compiler now **REFUSES** to emit `verifySP1FRI` unless the source carries `@acknowledgeUnsoundSP1FriVerifier` (scanned over raw source, so all nine surfaces honour it); opting in still warns on every compile. The unsound artefact can no longer be produced by accident. Implementing the per-query chain remains the real feature work. |

### Residual items, stated plainly

- **The SP1 FRI per-query verification chain is still unimplemented.** This is
  now a FEATURE GAP, not a shippable defect: the compiler refuses to emit the
  verifier at all without an explicit in-source acknowledgement, so an unsound
  covenant cannot be produced by accident. Implementing the chain (input-batch
  MMCS verify, reduced-opening accumulator, per-fold-step MMCS verify,
  colinearity fold, final-poly Horner) is real work and needs the per-query
  opening layout in the unlocking script — roughly 50 KB per query. I did not
  attempt it: a hastily written FRI verifier that LOOKS sound is strictly worse
  than one that refuses to compile.
- `conformance/mutation/baseline.json` not re-stamped (new ids are simply not
  compared; cannot cause a false pass).
- The 60 "equivalent" mutation verdicts are evidence (2101 compiles found no
  witness), **not proof**.
- The Go CLI computes diagnostics and discards them — the SP1 warning reaches the
  API, not `runar-go` stdout. Not changed because the conformance runner reads
  that binary with combined stdout+stderr.
- `bad_vk` corruption fixture is impossible at `SP1VKeyHashByteSize: 0`; the
  documented colinearity and final-poly branches are unreachable by byte mutation.
- SP1 Groth16 vk cites a local `/Users/<user>/.sp1/...` path CI cannot re-derive.

## Reviewer scorecard

| | Claude (CC) | Codex (CX) | Grok (GK) |
|---|---|---|---|
| findings | 16 | 8 | 35 |
| S0/S1 claimed | 4 | 1 | 6 |
| reproduced as claimed | 4/4 | 1/1 | 2/6 |
| false positives | 0 | 0 | 1 (GK-021, own confidence `guess`) |
| not-a-defect (accurate but no code change) | 0 | 0 | 3 (GK-007/008/025) |
| already-known-and-pinned filed as new S1 | 0 | 0 | 2 (GK-031/032) |
| unique finds that became fixes | CC-014, CC-016, CC-013 | CX-006, CX-008 | GK-019, GK-030 |

**Weighting for next time.** Codex was the most precise per finding — 8 findings, zero
noise, and its exhaustive matrices are what made the provenance and skip work actionable.
Claude's execution-verified findings were the only ones carrying minimized repros that ran,
and produced the S0 surface (`CC-014`) the recorded #149 reduction missed. Grok has the
worst precision — 3 of 6 S1s are not defects and 2 more are already-pinned known issues —
but its 35-finding sweep surfaced two real defects nobody else saw (`GK-030`'s vacuous
assertions, `GK-019`'s count drift), and `PROBES.md`, despite 14 of 50 contracts failing to
compile from authoring errors, produced 2 genuine divergences.

Read Grok for coverage, Codex for precision, Claude for anything you intend to act on
without re-deriving. And treat Grok's `confidence` field as load-bearing: its one true false
positive was self-labelled `guess`.
