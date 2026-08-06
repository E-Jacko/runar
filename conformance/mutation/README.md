# Mutation scoring — measuring the safety net's detection power (TS-GAP-006)

The audit finding TS-GAP-006 observed that the *detection power of the whole
test net is unmeasured*: dozens of gates exist, but nothing proves they would
actually catch a compiler regression. This harness measures that power directly.

Rather than a generic mutation tool, it applies a **curated corpus of
representative compiler bugs** (`mutants.json`) — one targeted find/replace per
mutant into a real line of a TypeScript compiler source file — runs the mapped
fast in-process gate(s), and records **caught vs survived**. A mutant that
*should* be caught but **survives** is a measured hole in the net.

## Why no rebuild is needed (src alias, not dist)

The gates resolve `runar-compiler` / `runar-testing` through the **root
`vitest.config.ts` src alias** (`runar-compiler` → `packages/runar-compiler/src/index.ts`).
`conformance/` has no nearer vitest config, so `cd conformance && npx vitest run …`
inherits the same aliases. Mutating a file under `packages/runar-compiler/src/`
is therefore observed by the gates **without `pnpm run build`** — apply, run the
gate, revert. Fast and correct. (If the gates ever move to built `dist`, this
harness would need a per-mutant rebuild; they do not today.)

## Gates

| gate name | command | catches |
|---|---|---|
| `differential-witness` | `cd conformance && npx vitest run witnesses/differential.test.ts` | source-semantics (ANF interpreter) vs script-semantics (`@bsv/sdk` `ScriptVM`) disagreement on any fold-ON deployed contract, over declared accept + near-miss witnesses |
| `fold-equivalence` | `cd conformance && npx vitest run witnesses/fold-equivalence.test.ts` | fold-OFF vs fold-ON execution divergence per witnessed fixture |
| `fold-execution` | `cd conformance && npx vitest run witnesses/fold-execution.test.ts` | accept/reject verdict that depends on a folded all-constant subexpression (closes the `constantfold-add-to-sub` hole — see below) |
| `peephole-exhaustive` | `cd packages/runar-compiler && npx vitest run src/__tests__/peephole-exhaustive.test.ts` | any peephole rule whose `pattern` ≠ `replacement` in stack effect over the CScriptNum edge domain |
| `branch-merged-locals-vm` | `npx vitest run packages/runar-testing/src/__tests__/branch-merged-locals-vm.test.ts` | branch-merged locals (≥2, or asymmetric arms) deployed and called through the real `@bsv/sdk` `Spend`, asserting `expectedState` — not just accept/reject (PALMER-1, `23ef2d2b`) |
| `state-push-framing-vm` | `npx vitest run packages/runar-testing/src/__tests__/state-push-framing-vm.test.ts` | state-section `<len><data>` framing through a deployed continuation and the real Script VM, over the full 1-byte value-class matrix (PALMER-2, `23ef2d2b`) |
| `c28-state-strict` | `npx vitest run packages/runar-sdk/src/__tests__/c28-state-strict.test.ts` | `deserializeState` strictness unit pins, including a direct malformed-input case (`deserializeState(fields, '55')` must throw `/is not a push opcode/`) — the gate that actually detects a *decoder*-only OP_N regression (see Phase E1 below) |
| `sdk-vertical-constructor-slots` | `cd conformance && npx tsx sdk-vertical/runner/vertical-runner.ts --tiers typescript --filter bigint-0` | TS SDK's constructor-slot splice (`buildCodeScript()` in `contract.ts`) against the independently-derived code part in `conformance/sdk-vertical` (Phase C3 / TG-016) |
| `sdk-vertical-codeseparator` | `cd conformance && npx tsx sdk-vertical/runner/vertical-runner.ts --tiers typescript --filter codesep-tag-zero` | TS SDK's `codeSepIndexSlots` resolution (`_resolvedCodeSepSlotValues()` in `contract.ts`) against the independently-derived code part for the `CodeSepMatrix` fixture (Phase C4 / TG-016) |

`execute-fuzz` (`cd conformance && npx tsx fuzzer/index.ts --execute …`) is a
slower randomized oracle and is **not** wired into per-mutant scoring here.

The two `sdk-vertical-*` gates are scoped to the **TypeScript tier only**
(`--tiers typescript`), consistent with this corpus's existing TS-only scope,
and to a single currently-green case each (`--filter`) for speed and
determinism — `conformance/sdk-vertical` is a large fixture set (31 cases ×
7 SDK tools) built out by a parallel work stream; do not widen the filter or
drop `--tiers typescript` without first confirming the whole case set is
green (as of this writing 2 of 31 cases — `bigint-neg1`,
`multi-slot-mixed-a` — are missing goldens, which would make these gates
"catch" every mutant for a reason unrelated to the mutation).

## Corpus shape

`mutants.json` has 22 mutants across two groups:

- 16 covering the four original audit bug classes — **off-by-one stack
  index**, **swapped operands**, **dropped OP_VERIFY**, **if-without-else
  regression** — across the **stack-lower**, **emit**, **constant-fold**, and
  **peephole** stages. All 16 carry a non-empty `expectCaughtBy`.
- 6 **Phase E1 / TG-007** (2026-08) Palmer-class additions — see below.

Note on the peephole stage: `peephole-rules.ts` is the declarative mirror the
bounded-exhaustive sweep executes rule-by-rule, so corrupting a rule's
`replacement` into an unsound one is exactly what `peephole-exhaustive` exists
to catch — a faithful test of that gate's detection power.

## Formerly a documented survivor, now closed

`constantfold-add-to-sub` flips `evalBinOp('+')` in the ANF constant-fold pass.
It **used to survive** both `differential-witness` and `fold-equivalence`,
because no witnessed conformance fixture executed an all-constant subexpression
through the fold pass. `conformance/witnesses/fold-execution.test.ts` closed the
hole (its accept/reject verdict depends on a folded `2n + 3n`); the mutant's
`expectCaughtBy` is `["fold-execution"]` and its `finding` records the
before/after. Kept as an example of the corpus's own discipline: a real hole
was measured, named, and closed with new execution — not by relabelling.

## Phase E1 additions — Palmer-class corpus (TS-GAP-007, 2026-08)

Two fund-safety miscompilations (PALMER-1: branch-merged locals; PALMER-2:
state-section MINIMALDATA framing — see `docs/audit/2026-08-testing-gap-remediation-plan.md`
§0, fixed in `23ef2d2b`) shipped with a fully green suite because the mutation
corpus had no mutant of either shape. These 6 mutants close that specific gap
by **inverting the fix commit's hunks** — each is a literal reproduction of
the historical bug, not a synthetic one:

| id | file | inverts | verified caught by |
|---|---|---|---|
| `anflower-merge-locals-single-only` | `04-anf-lower.ts` | the `mergedLocals.length >= 2` branch-merge normalisation | `branch-merged-locals-vm` |
| `stacklower-merge-locals-property-only` | `05-stack-lower.ts` | dropping the `_properties`-only restriction on the N≥2 reconcile | `branch-merged-locals-vm` |
| `sdkstate-encode-minimaldata-opn` | `packages/runar-sdk/src/state.ts` | restoring the #110 MINIMALDATA short-circuit in `encodePushDataState` | `state-push-framing-vm`, `c28-state-strict` |
| `sdkstate-decode-opn-as-length` | `packages/runar-sdk/src/state.ts` | restoring the OP_N decode branch in `decodePushData` | `c28-state-strict` **only** — see finding below |
| `sdksplice-constructor-slot-wrong-length` | `packages/runar-sdk/src/contract.ts` | new Phase C3 family: 1 stray byte per constructor-slot substitution | `sdk-vertical-constructor-slots` |
| `sdksplice-codeseparator-off-by-one` | `packages/runar-sdk/src/contract.ts` | new Phase C4 family: off-by-one on the baked `codeSepIndexSlots` value | `sdk-vertical-codeseparator` |

### Measured finding: `sdkstate-decode-opn-as-length` (execution-verified, not tuned away)

This mutant restores ONLY the decode-side OP_N branch (the encoder stays
correct). Run against `state-push-framing-vm` alone it **survives**: every
test in that file constructs its state blob through the (correct) encoder, so
an OP_N-framed byte sequence never reaches the decoder — the added leniency is
dead code for every case that file exercises. `caughtBy` for this mutant is
`["c28-state-strict"]` while `expectCaughtBy` lists both gates; the scorer's
own `missedExpectedGates` reporting prints
`⚠ expected gate(s) did NOT fire: state-push-framing-vm` for exactly this
reason — the mutant is caught overall (`c28-state-strict.test.ts` has a direct
`expect(() => deserializeState(fields, '55')).toThrow(/is not a push opcode/)`
pin), but the gate this corpus's own Phase E1 table proposed for it does
**not**, on its own, provide that coverage. This was verified by running the
mutant, not asserted — it was NOT tuned to pass; the honest result is recorded
as-is. Fix candidate (out of scope for this PR): give
`state-push-framing-vm.test.ts` a direct malformed-input decode case, per P3
("round-trip alone is never sufficient for a listed wire primitive").

### `stateful-bytestring-op-n-state` sdk-output golden: NOT wired (documented, not invented)

The Phase E1 table in the remediation plan also names the
`conformance/sdk-output` `stateful-bytestring-op-n-state` golden as an
intended gate for the two `sdkstate-*` mutants. It was **not** added:
`conformance/sdk-output/runner/sdk-runner.ts`'s coverage audit currently fails
before running any fixture (4 compiler-conformance fixtures added by a
parallel work stream — `loop-carried-locals`, `merge-locals-prop-updates`,
`merge-locals-shapes`, `state-bigint-edges` — are not yet registered in
`sdk-output` or `coverage-allowlist.json`). A gate whose unmutated baseline
already fails would "catch" every mutant for a reason that has nothing to do
with the mutation, which is worse than not having the gate. `c28-state-strict`
was substituted as an execution-verified alternative that exercises the same
underlying regression. Re-add `stateful-bytestring-op-n-state` once the
`sdk-output` coverage audit is green again.

### `constructorSlots` / `codeSeparatorIndex`: wired to `conformance/sdk-vertical`

`conformance/sdk-vertical` (Phase C3/C4) existed by the time this work started
and is used directly — see the `sdk-vertical-*` gates above and their caveats
about the in-progress case set.

## Running

```bash
cd conformance && npx tsx mutation/run-mutation.ts     # or: npm run mutation:score
```

Prints a scorecard (`caught N/M`, survivors listed with class + stage) and exits
**non-zero if any mutant with a non-empty `expectCaughtBy` survives** — i.e. the
net weakened. `baseline.json` is the stamped reference; the nightly CI job
(`.github/workflows/fuzzer-nightly.yml`) fails if a previously-caught mutant
becomes a survivor.

The scorer **always reverts** every mutant (try/finally, snapshot restore), so
the working tree is left clean; a mutated compiler source is never committed.

## Future extension

The corpus is TS-only. Go / Rust / other-tier mutants (mutating
`compilers/go/**`, etc. and scoring against that tier's suites) are a documented
future extension — they would require a native build per mutant and are out of
scope for this first increment.
