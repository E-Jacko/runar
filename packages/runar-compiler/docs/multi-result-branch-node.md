# Should the ANF `if` node yield multiple results?

**Status: assessed 2026-08-06, NOT implemented. Recommendation: do it, but not
as the next change — land the two cheap prerequisites first (§7).**

This note sits beside the passes it concerns (`src/passes/04-anf-lower.ts`,
`src/passes/05-stack-lower.ts`) rather than under `docs/`, because it is a
compiler-internal design question, not user documentation.

---

## 1. The recurring bug

Six confirmed miscompiles in one week share one root cause: **one stack carrier
is asked to hold N live values.** `lowerIf` registers exactly ONE `stackMap`
name for whatever the arms leave behind. When the arms leave more than one
physical slot, every later operand resolves N−1 slots off — and because the
`stackMap` is the compiler's only model of the stack, nothing notices.

| # | Shape | Symptom | Closed by |
|---|---|---|---|
| P1 | `if` merging K≥2 locals | wrong-but-accepted continuation | `mergedLocals >= 2` normalisation (`appendMergedLocalResults`) + `countMergedLocalResults` trim + `elseMatchesThenNResultLayout` |
| P2 | K=1 local both arms rebind in place | compile error `Value '<if>' not found on stack` | `branchInPlaceRebindDepth` |
| P3 | loop-carried local rebound then read again | `wacc = step*N` instead of `step*N*(N+1)/2` | `collectLoopCarriedRebinds` |
| P4 | same, one loop deeper | `wacc = 24` instead of `30` | `flattenNestedLoopBodies` |
| P5 | constant-fold blanking an untaken arm | silent at K=2, loud at K=1 | fold both arms unconditionally |
| P6 | K≥2 merged locals **dead after the `if`** | `wacc = 3` instead of `9` | merged-local protection in `lowerIf` (2026-08-06) |
| **P7** | **arm writes a property AND rebinds a merged local** | **UNSPENDABLE script** | **OPEN** — see §6 |

Six patches around one gap, and the seventh instance is open and fund-critical.

## 2. The proposal

Give the `if` node an explicit result list: one slot for the branch's
serialised output bytes, plus N for merged locals **and property writes**.
`lowerIf` then registers N+1 `stackMap` names instead of 1, and
`drainBranchPrivateResidue` stops inferring liveness by name.

## 3. What it would touch

Root `CLAUDE.md`'s "Adding a New ANF Value Kind" checklist is the real blast
radius. This is not a new kind — it is a **shape change to an existing kind**,
which is strictly worse, because the existing kind is already serialised into
checked-in goldens and read by other tiers.

**Per tier (×7):** ANF IR type, ANF lowering, stack lowering, the ANF JSON
loader's known-kinds/field dispatch. Plus TS-only: `constant-fold.ts`,
`packages/runar-ir-schema/src/anf-ir.ts` (kept in sync by hand with
`src/ir/anf-ir.ts`), and the seven SDK ANF interpreters
(`packages/runar-{sdk,go,rs,py,zig,rb,java}`, 1169–2477 lines each).

The two functions that carry the logic are large everywhere:

| tier | stack lowering | ANF lowering |
|---|---|---|
| TypeScript | 5540 | 2662 |
| Go | 5549 | 2837 |
| Rust | 6873 | 3948 |
| Python | 4793 | 2670 |
| Zig | 6370 | 3898 |
| Ruby | 4245 | 2850 |
| Java | 4072 | 2489 |

**The part that is easy to miss: the ANF `if` node is a cross-tier wire
format.** `conformance/tests/*/expected-ir.json` is the **ANF** IR, not the
Stack IR, and `conformance/runner/index.ts --ir-parity` feeds the TypeScript
tier's checked-in ANF JSON to all six non-TS tiers and requires byte-identical
hex out. So a shape change means:

- all **70** `expected-ir.json` goldens are rewritten, each needing a
  content-pinned `golden-provenance-allowlist.json` entry or a co-changed
  witness (the gate in `conformance/scripts/check-golden-provenance.mjs`);
- the ANF loader in all six non-TS tiers must accept the new shape **in the
  same commit**, or `--ir-parity` cannot pass at any intermediate point;
- four fixtures have `__merge$` blocks baked into their goldens
  (`branch-merged-locals`, `merge-locals-shapes`, `merge-locals-prop-updates`,
  `loop-if-merged-locals`) and those blocks disappear entirely.

There is no incremental path through this: it is one atomic 7-tier commit or a
broken parity gate.

## 4. Byte neutrality

**No.** Concretely, what moves:

- **ANF goldens: all 70** if the result list is an unconditional field on the
  node (`"results": []` serialises everywhere). Keeping it optional/omitted
  when empty would confine ANF movement to the ~4 merge fixtures — worth doing,
  and it is the difference between 70 provenance entries and 4.
- **Script hex: the merge fixtures.** `appendMergedLocalResults`' two-pass
  copy-then-rebind block is *exactly* what produces today's PICK/ROLL sequence
  for K≥2. Delete the block and the arms' opcode sequences change. Affected:
  `branch-merged-locals`, `merge-locals-shapes`, `merge-locals-prop-updates`,
  `loop-if-merged-locals`, plus the `BranchMergedLocals` example in 9 formats.
  Expect the merge arms to get *smaller* (the `__merge$` temps exist only to
  work around single-result), so `script-size-baseline.json` moves down for
  those fixtures.
- **Everything else: unchanged**, provided the new path is taken only where an
  `if` actually has >1 result. That is the same discipline that made all six
  patches byte-neutral, and it is checkable the same way (repo-wide sweep ×
  both fold modes).

Rough size: 4 of 70 fixtures move hex, ~4–70 move ANF depending on the optional
-field decision. That is a reviewable diff, but every moved golden is a
self-produced artifact that needs independent justification — which is real
work, not a rubber stamp.

## 5. Does it subsume the six patches?

Honestly: **three yes, one partly, two no.**

- **P1 — subsumed, and deleted.** The whole `__merge$` convention exists only
  because the node carries one value. `appendMergedLocalResults`,
  `countMergedLocalResults`, `mergedLocalResultNames`, the trim loop and
  `elseMatchesThenNResultLayout` all go away. This is the single biggest
  simplification on offer.
- **P2 — subsumed.** `branchInPlaceRebindDepth` exists because at K=1 the arms'
  net depth change is zero and nothing gets registered. With a declared result
  list there is a name to register regardless of depth arithmetic.
- **P6 — subsumed.** My 2026-08-06 fix makes `appendMergedLocalResults`' stated
  premise true by protecting the merged locals. If the node declares its
  results, lowering must materialise them, so the premise is structural rather
  than assumed.
- **P5 — partly.** Blanking an arm would become a *loud* structural violation
  (the node says N results, the arm produces 0) instead of a silent
  miscompile. But the second half of P5 — propagating a taken arm's constants
  into the enclosing env while the `if` survives — is unrelated and still needs
  its own fix.
- **P3, P4 — NOT subsumed at all.** These are loop-carried liveness, not branch
  results: `acc = acc + step` at a loop body's top level involves no `if`.
  `collectLoopCarriedRebinds` and `flattenNestedLoopBodies` stay exactly as they
  are. Two of the seven defects — and the two that were hardest to find — are
  outside this proposal's reach.

That is the honest scorecard: the proposal fixes the **branch** half of the
family and leaves the **loop** half untouched. The loop half would need its own
analogous change (a loop node that declares its carried values), which nobody
has proposed and which this note does not assess.

## 6. P7 — the open defect this assessment turned up

While assessing, I added a temporary `stackMap`-vs-physical-depth invariant to
`lowerIf` and ran the whole suite under it. It held for **4614 tests** and fired
on exactly one shape, the fuzzer's `prop-write-in-arm`. Reproduced end to end:

```ts
let na = 1n;
if (flag > 0n) { this.p = x + 100n; na = x + 1n; } else { na = x + 2n; }
this.addOutput(1000n, this.p, na, this.b);
```

The then-arm produces **an UNSPENDABLE script** — `@bsv/sdk`'s `Spend` runs to
the end and rejects on a falsy top of stack. Pre-existing at `32b9cb2a`, and
TS and Go emit byte-identical wrong hex, so it is a seven-tier defect. Both
arities (K=1 and K=2) fail; both fold modes fail; the else-arm is fine. Pinned
in `packages/runar-testing/src/__tests__/branch-prop-write-with-merged-local-vm.test.ts`.

No shipped artifact reaches it — a structural sweep of every `.runar.*` in the
repo found zero methods with a property write and a local rebind in the same
arm. `cond-write-multi-field` writes only properties in its arm;
`merge-locals-prop-updates` writes its properties *after* the `if`. The
combination is unfixtured, which is why it survived.

**It is not patchable the way its six siblings were.** The merged-local
normalisation covers LOCALS; a property written in an arm is a second result
kind it does not model, so the arms end at different depths *with different
layouts*:

```
then: [ ..., p(new), na(new) ]   +2
else: [ ..., na(new) ]           +1
```

`lowerIf`'s phase-3 padding assumes the missing slots are the **topmost** ones
and pads on top. Here the missing slot is `p`, which sits *beneath* `na`. The
bug is in the padding loop's slot **selection**, not in a liveness predicate —
there is no "protect this name" patch that fixes it. Fixing it properly means
an arm's result set must include property writes, which is exactly this
proposal.

**P7 is therefore the strongest argument in favour of the proposal, and the
clearest evidence that the patch-a-predicate strategy has reached its limit.**

## 7. Cheaper intermediates

**(a) A `stackMap`-vs-physical-depth invariant on `lowerIf` — do this first.**
This is the highest-value/lowest-cost item in the whole analysis. It emits no
opcodes, so it is byte-neutral by construction, and it is ~10 lines per tier.
Measured: it holds across 4614 existing tests with the P6 fix in place, and it
catches P1, P2, P6 and P7 at **compile time, loudly**, instead of on-chain.
It is the same genre as the existing "Layer B" branch-balance guard, which was
added for exactly this reason after issue #99. Note the naive form
(`this.stackMap.depth === thenCtx.stackMap.depth`) is wrong — the post-`ENDIF`
reconcile legitimately drops stale slots — so it must be stated as
`this.stackMap.depth + physicalDropsEmittedAfterEndif === armDepth`.

**(b) A result COUNT on the stackMap, keeping the single-result node.** Much of
this already exists as `nResults` plus the N≥2 adopt path; the gap was never the
count, it was the *precondition* that both arms actually leave N equally-named
slots. Adding a count without fixing arm layout does not close P7. Low value.

**(c) Extend `mergedLocals` to include arm-written properties, keeping the
`__merge$` block.** This would close P7 within today's architecture, at the cost
of moving hex for `cond-write-multi-field` and friends. It is a smaller change
than the full node migration, but it doubles down on the convention the
migration exists to delete — the classic "one more patch" that makes the
eventual migration harder.

## 8. Recommendation

**Do it — but not next. Order: (a), then P7 via (c) or the migration, then the
migration.**

Justification from the evidence:

1. **The invariant (a) is unambiguously right and nearly free.** Six of seven
   defects in this family were silent; the invariant makes four of them loud for
   ~70 lines total across 7 tiers, byte-neutral, no goldens touched. There is no
   argument against doing it immediately, and it protects the migration itself —
   a 7-tier IR migration without a stack-shape invariant is exactly the change
   most likely to add defect #8.
2. **The migration is right in the medium term.** P1 is pure workaround
   scaffolding, P7 proves the workaround does not generalise to a second result
   kind, and the trend line is one new instance per few days of looking. The
   proposal deletes the scaffolding rather than extending it.
3. **But it is not right *now*, for three concrete reasons.** It cannot be
   staged: the ANF `if` node is a cross-tier wire format with a hard parity gate,
   so it is one atomic 7-tier commit. It moves goldens that each need
   independent provenance justification. And it closes only 3.5 of the 7 known
   defects — the two loop-carried ones are untouched — so it is not the "one
   change that ends the family" it looks like.
4. **A half-done migration is the worst outcome available.** Between "seven
   tiers on the old shape" and "seven tiers on the new shape" there is no green
   state: `--ir-parity` fails for every intermediate commit. It needs a
   dedicated change with all seven tiers moving together, not a slice of a
   remediation pass.

The concrete next action is (a): add the depth invariant to `lowerIf` in all
seven tiers, verify byte-neutrality by the usual sweep, and let it turn P7 —
and any future member of this family — into a compile error instead of a locked
UTXO.
