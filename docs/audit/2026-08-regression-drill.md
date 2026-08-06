# Consolidated regression drill — §10.5 evidence (2026-08-06)

**Scope:** `docs/audit/2026-08-testing-gap-remediation-plan.md` §10 criterion 5.
**Worktree:** `.worktrees/testing-gap`, branch `fix/testing-gap-remediation`, HEAD
`4b0f688f` (multi-result branch node), clean tree throughout — verified with
`git status --porcelain` before and after every mutation below.

Each drill temporarily re-introduced a defect, ran the gates the plan claims
would catch it, recorded the verbatim result, then reverted and re-verified a
clean tree + green gates. No permanent change was made outside this file.

**Verdict up front (as measured, 2026-08-06):** §10.5 was **not fully
satisfied**. Drills (a) and (b) pass once the pre-existing corpus is
repaired/derived against the current tree, but that repair itself surfaced a
live regression in the mutation corpus (below). Drill (c) **failed outright**
on the literal historical replay the plan text specifies — the single most
important finding of this drill. Details and full reasoning follow; do not
skip to the table without reading the drill (c) section.

> **UPDATE — both findings were fixed the same day; this document is kept as
> the dated record of the measurement, not as current state.**
>
> - **Drill (c) — FIXED.** `weakPinOnly` is now a hard failure:
>   `ok = problems.length === 0 && (wireHits.length === 0 || pinHits.some(isStrongPin))`.
>   Replaying the literal `bd7ec284` changed-set now **exits 1**, pinned by
>   `describe('wire-format-pr-audit — bd7ec284 (the incident this gate exists for)')`.
>   Measured false-positive cost: **8 of the last 60 first-parent commits on
>   `main`** now fail — and **7 of those 8 are the same incident family** (the
>   C9+S1 MINIMALDATA port series, each evidenced only by its own round-trip
>   test), i.e. `bd7ec284` repeated seven times. Nothing was softened.
> - **Drill (a) — FIXED.** Both PALMER-1 mutants were re-derived against the
>   current tree and their `expectCaughtBy` now lists only the gates that
>   *actually* fire — the depth invariant is deliberately absent from the
>   anf-lower mutant, because that defect is depth-preserving and
>   name-corrupting. A **stale-mutant guard** was added: a patch that no longer
>   applies is now a loud `STALE` failure excluded from the denominator, rather
>   than a silent survivor indistinguishable from a real detection gap — which
>   is exactly the ambiguity that let this sit.
>
> **Residual, still open:** the guard catches "the patch no longer applies".
> "The patch applies but hits dead code" is still caught only by the
> `mutation-score` baseline-regression job in `fuzzer-nightly.yml`, which is
> gated `if: github.event_name != 'pull_request'`. Promoting it to run on PRs
> that touch `04-anf-lower.ts` / `05-stack-lower.ts` would have caught this in
> ~40s on the PR that caused it.

---

## Drill (a) — single-local-only ANF merge

### Step 0 — the curated mutants are stale against `4b0f688f`

`conformance/mutation/mutants.json` carries two PALMER-1 mutants:
`anflower-merge-locals-single-only` (04-anf-lower.ts) and
`stacklower-merge-locals-property-only` (05-stack-lower.ts). Both `find`
strings still occur exactly once in the current source (mechanically
"applicable"), but the multi-result branch node (`4b0f688f`, "close the
merged-local defect family") moved the real merge decision to new code both
mutants' target lines no longer gate:

- `anflower-merge-locals-single-only` targets `if (mergedLocals.length >= 2)`
  inside `branchOutputRejectionReason` — a function that only runs when an
  `if` arm contains an output intrinsic. The branch-merged-locals fixtures
  never emit outputs *inside* a branch, so this code path never executes for
  them.
- `stacklower-merge-locals-property-only` targets the `_properties`
  membership check inside `elseMatchesThenNResultLayout` — a **fallback**
  used only when `nDeclared === 0` (no `results` were declared by
  04-anf-lower's new normalisation block). Every branch-merged-locals shape
  with ≥2 merged locals now takes the `nDeclared >= 1` declared-results path
  instead, so this fallback is also dead for them.

Applied each literally (via mutants.json's own find/replace, one at a time,
each reverted before the next) and ran the intended gate:

```
$ npx vitest run packages/runar-testing/src/__tests__/branch-merged-locals-vm.test.ts \
                 packages/runar-compiler/src/__tests__/branch-result-depth-invariant.test.ts
 Test Files  2 passed (2)
      Tests  27 passed (27)          # anflower-merge-locals-single-only mutant applied
```
```
 Test Files  2 passed (2)
      Tests  27 passed (27)          # stacklower-merge-locals-property-only mutant applied
```
```
$ cd conformance && npx vitest run witnesses/real-crypto-execution.test.ts -t "branch-merged-locals"
 Tests  3 passed | 90 skipped (93)   # both mutants — witness unaffected either time
```

**Both SURVIVE.** Confirmed authoritatively with the project's own harness
(not just my manual replication):

```
$ cd conformance && npx tsx mutation/run-mutation.ts --json-out /tmp/mutation-current.json
  caught 20/22 mutants that MUST be caught
  SURVIVED         anflower-merge-locals-single-only  branch-merge regression / anf-lower
  SURVIVED         stacklower-merge-locals-property-only branch-merge regression / stack-lower
  ✗ UNEXPECTED SURVIVORS (real holes in the net — MUST be addressed):
   • anflower-merge-locals-single-only (branch-merge regression / anf-lower) — expected branch-merged-locals-vm
   • stacklower-merge-locals-property-only (branch-merge regression / stack-lower) — expected branch-merged-locals-vm
(33.2s wall, 22 mutants)
```

**This is a live, currently-undetected regression, not a hypothetical one.**
`conformance/mutation/baseline.json` (checked in) records both mutants as
`"caught": true`. `.github/workflows/fuzzer-nightly.yml`'s `mutation-score`
job diffs a fresh run against that baseline and fails on
`b.caught && c.survived` ("MUTATION REGRESSION — the net weakened") — but
that job runs **nightly only** (`if: github.event_name != 'pull_request'`),
not on PRs, and per its own comment it has not run since `4b0f688f` landed.
The corpus has silently lost detection power for the exact defect family the
plan calls its highest-priority regression target (§3 Phase E1), and nothing
has said so yet. Reverted cleanly (`git status --porcelain` empty, re-run
green) after each of the two probes above.

### Step 1 — derive the equivalent defect against current source

Faithful "rewire only a single local" for the current (multi-result-node)
architecture is one line in the function that actually decides how many
locals get normalised, `collectBranchMergedLocals`
(`packages/runar-compiler/src/passes/04-anf-lower.ts`):

```diff
   const merged = lastRebindOrder(thenCtx);
   for (const name of lastRebindOrder(elseCtx)) {
     if (!merged.includes(name)) merged.push(name);
   }
-  return merged;
+  return merged.slice(0, 1);
```

This truncates the canonical merge list to its first entry regardless of how
many locals either arm actually reassigns, so only one local ever gets the
explicit two-pass copy-then-rebind block both arms need; every other
genuinely-reassigned local silently falls through to whatever machinery
handles undeclared results.

**Gates that fired:**

| Gate | Result | Detail |
|---|---|---|
| `branch-merged-locals-vm.test.ts` | **CAUGHT** | 5/9 failed: S3 (k=2 same-set), S6 (k=3), S7 (k=2 mixed types), S8 (k=4 asymmetric, the filed repro), S9 (nested). S1/S2 (k=1, untouched by this code path) and S5 (`if` w/o `else`, separate path) still pass, as expected. |
| real-crypto witness `branch-merged-locals.json` | **PARTIALLY CAUGHT** | 1/3 failed: the `toFirst==0` accept (else-arm reassigns `nb`, `na` must survive) — real `@bsv/sdk` Spend rejected the call as script-invalid. The `toFirst>0` accept and the tamper-reject still passed. |
| `branch-result-depth-invariant.test.ts` | **did NOT fire** | 18/18 pass. The invariant added in `7b888035` to make "the next one LOUD instead of silent" does not see this shape — both arms end at a depth the invariant's `stackMap.depth + postEndifDrops === armDepth` check accepts; the bug is which *name* occupies a slot, not the slot count. |

Gates that stayed green did so honestly (they check depth, not value/name
identity) — this is not a harness flake.

**Timing:** unit gates (`branch-merged-locals-vm` + `branch-result-depth-invariant`)
~1.4s wall; real-crypto witness (`-t` filtered) ~1.35s wall. Both are PR-speed,
not nightly-only.

**Horizontal check (P7):** ran the cross-tier conformance fixture for this
exact construct:

```
$ cd conformance && npx tsx runner/index.ts --multi-format --filter branch-merged-locals
Summary: 0 passed, 9 failed, 0 skipped (9 total)
  IR mismatch between compilers: majority [go, rust, python, zig, ruby, java] vs [ts]
  Script hex mismatch between compilers: ... first differs at byte 809
```

The horizontal gate **also fired** — but for a different, weaker reason than
the plan's P7 claim. My mutation only touched the TypeScript compiler source
(`04-anf-lower.ts`), so TS trivially diverges from the other six unmutated
tiers; that is ordinary cross-tier disagreement, not "all tiers silently
agree on a wrong answer." Demonstrating the plan's actual P7 claim
(*horizontal agreement hides the bug*) would require applying the same
defect identically across all seven `anf_lower` implementations, which this
drill did not attempt (out of scope for a single-session drill covering
three separate defects). The historical record is stronger evidence than a
synthetic single-tier repro could be: `git show 23ef2d2b --stat` — the
original fix commit — states outright **"Branch-merged locals (all 7
compilers)"**: the real PALMER-1 defect was independently present in all
seven `anf_lower` ports before the fix, so seven-way cross-tier agreement
genuinely stayed green for it in production. That is the real P7 proof;
this drill's single-tier variant is a strictly easier catch and should not
be read as equivalent evidence.

Reverted (`return merged.slice(0, 1)` → `return merged;`), confirmed
`git status --porcelain` empty, re-ran all four gates green: 27/27 unit,
3/3 witness, 9/9 conformance PASS.

---

## Drill (b) — OP_N state serialize (encoder + decoder co-changed)

Applied both mutants.json PALMER-2 entries together — the faithful version,
exactly as `bd7ec284` co-changed encode and decode in the same commit:

```diff
 function encodePushDataState(dataHex: string): string {
   const len = dataHex.length / 2;
+  if (len === 1) {
+    const byte = parseInt(dataHex, 16);
+    if (byte >= 0x01 && byte <= 0x10) return (0x50 + byte).toString(16).padStart(2, '0');
+    if (byte === 0x81) return '4f';
+  }
   if (len <= 75) { ... }
@@ decodePushData
-  if (opcode <= 75) {
+  if (opcode >= 0x51 && opcode <= 0x60) {
+    return { data: (opcode - 0x50).toString(16).padStart(2, '0'), bytesRead: 2 };
+  } else if (opcode === 0x4f) {
+    return { data: '81', bytesRead: 2 };
+  } else if (opcode <= 75) { ... }
```

(`packages/runar-sdk/src/state.ts`.) Ran the four target gates:

| Gate | Result | Detail |
|---|---|---|
| `state-push-framing-vm.test.ts` | **CAUGHT** — 9/36 failed | Write-path real deploy→call→Spend failures for handle=01,02,05,10,81 (broadcast rejected — the client-built output no longer matches what the on-chain script recomputes for `hashOutputs`); the PRESET read-path (spendability of a pre-deployed OP_N-range value) failed outright; 2 direct absolute-pin unit assertions (`serializeState(...) toBe('0105')` / `'0181'`) failed; the mixed-carrier value-pin failed. |
| `c28-state-strict.test.ts` | **CAUGHT** — 2/18 failed | `expect(hex).toBe('0105')` failed (got `'55'`); `expect(() => deserializeState(fields,'55')).toThrow(/is not a push opcode/)` failed — with decode also mutated, `'55'` now decodes successfully instead of throwing. |
| `encode-push-data-minimaldata.test.ts` (**C2/C5 divergence test** — construct-ledger.json names this file explicitly: *"Pins the DIVERGENCE deliberately: serializeState keeps `<len><data>`... while encodeArg... keeps MINIMALDATA"*) | **CAUGHT** — 5/15 failed | 3 direct absolute-pin assertions on `serializeState` output, plus both dedicated `C5` tests (`serializeState` and `encodeArg` must produce DIFFERENT bytes for an OP_N value) — those two exist specifically to fail the moment the two encoders are unified, which is exactly what this mutation does. |
| sdk-output golden `stateful-bytestring-op-n-state` | **CAUGHT** | `ERROR: typescript: does not match golden file` + cross-SDK mismatch vs the 6 unmutated tiers. Caveat below. |

**The round-trip stayed green, as the plan predicts.** Inside
`state-push-framing-vm.test.ts`, `'round-trips through deserializeState for
every 1-byte value'` (loops byte 0–0xff through `serializeState` then
`deserializeState` and asserts equality) is **not** in the failure list — it
passed under full co-mutation, because a co-changed encoder/decoder pair
round-trips for *any* self-consistent framing, wrong ones included. This is
an empirical, not asserted, confirmation of plan §2 P3 for this exact file.

**Caveat on the sdk-output golden:** this drill mutated the TypeScript SDK
only, so the golden fails two ways at once (cross-SDK disagreement with the
six untouched tiers, *and* disagreement with the pinned
`expected-locking.hex`). The historical incident was stronger and quieter:
`bd7ec284`'s own commit message reports **"SDK-output conformance
46/46"** — all seven SDKs agreed with each other for weeks, because no
fixture exercising a 1-byte OP_N-range ByteString state field existed yet.
`stateful-bytestring-op-n-state` (added later, by this remediation plan) is
what closes that hole now; a fresh single-tier drill can only show the
weaker "diverges from its unmutated peers" version of the catch.

**Timing:** the three unit-test files together ran in ~1.5–1.8s wall
(vitest startup dominates); the sdk-output golden ran in ~1.6–2.7s wall
across 7 SDK tools (rust 2–9ms, zig 14–37ms, ruby 82–131ms, java 53–133ms,
python 251–403ms, go 126–336ms, typescript 464ms–1.2s). All PR-speed.

Reverted both mutants (`git status --porcelain` empty), re-ran all four
gates green: 69/69 unit tests, sdk-output 7/7 PASS.

---

## Drill (c) — wire serializer change with zero golden diffs

Reproduced the #110 *process* failure by feeding
`conformance/scripts/wire-format-pr-audit.ts --changed-file` the **exact,
literal** changed-file set of the incident commit `bd7ec284` ("port #110
MINIMALDATA encode_push_data to the other 6 SDKs" — the commit whose own
message states "No golden change... SDK-output conformance 46/46"):

```
packages/runar-go/sdk_state.go
packages/runar-go/sdk_test.go
packages/runar-java/src/main/java/runar/lang/sdk/ScriptUtils.java
packages/runar-java/src/test/java/runar/lang/sdk/ScriptUtilsTest.java
packages/runar-py/runar/sdk/state.py
packages/runar-py/tests/test_sdk_state.py
packages/runar-rb/lib/runar/sdk/state.rb
packages/runar-rb/spec/sdk/state_spec.rb
packages/runar-sdk/src/__tests__/encode-push-data-minimaldata.test.ts
packages/runar-sdk/src/contract.ts
packages/runar-sdk/src/state.ts
packages/runar-zig/src/sdk_state.zig
```

```
$ cd conformance && npx tsx scripts/wire-format-pr-audit.ts --changed-file /tmp/bd7ec284-changed.txt
✓ Must-move-a-golden gate: 7 wire-format path(s) changed, 1 pinned byte artifact(s) moved with them.
    pin: packages/runar-sdk/src/__tests__/encode-push-data-minimaldata.test.ts

⚠ Every pin in this PR is a tier-local test file. A tier-local codec test is
often the encoder graded against its own inverse (round-trip class, plan P3 /
reviewer #4) — it holds for ANY self-consistent framing, including a wrong
one. Prefer moving a cross-component byte pin as well: ...
$ echo $?
0
```

### This gate does NOT fail on the literal replay. This is the most important finding in this drill.

`bd7ec284` also **created** (63 new lines, 0 deletions —
`packages/runar-sdk/src/__tests__/encode-push-data-minimaldata.test.ts`) a
brand-new test file in the same commit as the wire change. That path matches
the gate's own `TIER_LOCAL_PIN_NAME_GLOBS` (`*minimaldata*`) under
`TIER_LOCAL_PIN_TEST_ROOT_GLOBS` (`packages/*/src/__tests__/**`), so
`pinKindOf()` classifies it as a **weak** pin. The satisfiability check —
`ok = problems.length === 0 && (wireHits.length === 0 || pinHits.length > 0)`
— treats *any* pin, weak or strong, as sufficient: `weakPinOnly` is computed,
threaded through to the rendered message as a `⚠` warning, and **never once
flips `ok` to `false`**. This is not an oversight I'm inferring — it is
explicitly unit-tested behaviour:
`conformance/scripts/__tests__/wire-format-pr-audit.test.ts:324`,
*"flags a tier-local unit test as a WEAK pin (round-trip class) **without
failing**"*.

At the time it shipped, that new test file asserted the *wrong* (MINIMALDATA)
behaviour for state serialization as correct — it was the "co-changed pair"
test the docstring at the top of `wire-format-pr-audit.ts` itself calls out
("the encoder and the decoder were co-changed and every test was a
round-trip... It was green because... every test was a round-trip"). Feeding
this gate the literal historical changed-set does not fail — it passes with
a warning, on the strength of exactly the kind of test the plan says must
never be sufficient (P3).

**Contrast — the wire-format *detection* half is not broken.** Stripping the
test-file additions and running only the seven non-test implementation paths
`bd7ec284` touched:

```
$ cd conformance && npx tsx scripts/wire-format-pr-audit.ts --changed-file /tmp/bd7ec284-impl-only.txt
✗ MUST-MOVE-A-GOLDEN GATE FAILED
7 wire-format implementation path(s) changed and NOT ONE pinned byte artifact moved with them:
  [sdk-state-serialization] ✗ sdk_state.go ✗ state.py ✗ state.rb ✗ state.ts ✗ sdk_state.zig
  [push-data-encoding]      ✗ ScriptUtils.java
  [constructor-slot-splicing] ✗ contract.ts
$ echo $?
1
```

correctly fires. So the family/glob classification of wire-format
implementation paths is sound; the failure is specifically that a co-added
weak/tier-local test is enough to silence the block for a PR that also
touches implementation paths — which is precisely the shape the real #110
incident had.

**Timing:** both invocations ran in ~0.27–0.28s wall — no compiler/SDK
spawning, pure path-glob classification. This is by far the cheapest gate
in the whole drill and the one place where "nightly-only" cannot be used
as an excuse for not firing.

No file mutation was needed for this drill (`--changed-file` reads an
arbitrary path list; nothing in the tree was touched), so there was nothing
to revert. `git status --porcelain` was empty before, during, and after.

---

## Gate summary table

| Drill | Gate | Fired? | Time | Notes |
|---|---|---|---|---|
| (a) | `branch-merged-locals-vm.test.ts` (pre-existing mutants, literal) | **NO — SURVIVED** | ~1.4s | Both PALMER-1 mutants stale post-`4b0f688f`; confirmed by live `run-mutation.ts` run, contradicts checked-in `baseline.json` |
| (a) | `branch-merged-locals-vm.test.ts` (derived mutation) | **YES** | ~1.4s | 5/9 shapes (k≥2 same-arm-multi-push); S4/S5/S1/S2 unaffected |
| (a) | real-crypto witness `branch-merged-locals.json` | **partial YES** | ~1.35s | 1/3 spends (toFirst==0 direction) |
| (a) | `branch-result-depth-invariant.test.ts` | **NO** | ~1.4s (combined) | Depth-only invariant; this defect preserves depth, changes name binding |
| (a) | horizontal: `conformance/tests/branch-merged-locals` (7-tier) | YES, but weak evidence | ~3.6s | TS-only mutation trivially diverges from 6 unmutated tiers; real historical bug was 7-tier-identical (git show 23ef2d2b) |
| (a) | nightly mutation baseline-regression check (`fuzzer-nightly.yml`) | **latent — has not run since `4b0f688f`** | ~33s (full corpus), nightly cadence only | Will fire "MUTATION REGRESSION" for both stale mutants on next scheduled run |
| (b) | `state-push-framing-vm.test.ts` | **YES** | ~1.5–1.8s | 9/36; round-trip sub-test stayed green (expected, P3-consistent) |
| (b) | `c28-state-strict.test.ts` | **YES** | ~1.5–1.8s (combined) | 2/18, including the negative `deserializeState('55')` throw |
| (b) | `encode-push-data-minimaldata.test.ts` (C2/C5 divergence) | **YES** | ~1.5–1.8s (combined) | 5/15, incl. both dedicated divergence assertions |
| (b) | sdk-output golden `stateful-bytestring-op-n-state` | **YES** | ~1.6–2.7s | Fails both cross-tier and vs. absolute golden; single-tier mutation caveat noted |
| (c) | `wire-format-pr-audit.ts`, literal `bd7ec284` changed-set | **NO — exit 0** | ~0.28s | Co-added `*minimaldata*` test file satisfies the gate as a weak pin; deliberate, tested behaviour, not a bug |
| (c) | `wire-format-pr-audit.ts`, impl-paths-only subset | YES — exit 1 | ~0.27s | Confirms glob/family classification itself is sound |

---

## Verdict on §10.5

**Not satisfied as written.**

1. **(a)** passes only after deriving a new mutation against the current
   source, because both pre-existing PALMER-1 mutants in
   `conformance/mutation/mutants.json` are now dead relative to `4b0f688f`
   and — more importantly — this is not yet visible anywhere except a
   nightly job that has not run since the refactor landed.
   `conformance/mutation/baseline.json` currently overstates detection power
   for exactly the defect family the plan treats as its flagship regression
   target. **Action needed:** update or replace both mutants (target
   `collectBranchMergedLocals`'s truncation as demonstrated here, or an
   equivalent that also perturbs the declared-results path), regenerate
   `baseline.json`, and consider promoting the mutation-score job's
   regression check to run on PRs touching `04-anf-lower.ts` /
   `05-stack-lower.ts` rather than nightly-only.
2. **(b)** passes cleanly, with the round-trip-stays-green / absolute-pin-
   catches contrast empirically demonstrated exactly as the plan predicts.
3. **(c)** **fails.** Driving `wire-format-pr-audit.ts` with the literal,
   real changed-set of the incident commit it was built to catch produces
   exit 0, not exit 1, because that commit's own test-file addition
   satisfies the gate's weak-pin allowance. The plan's §10.5(c) explicitly
   asks to "confirm exit 1"; the honest result is that it does not, on the
   exact input specified. The gate's core wire-path/pin-family
   classification is sound (proven by the impl-only-subset control run) —
   the gap is specifically that a same-PR, tier-local, round-trip-class test
   addition is accepted as sufficient evidence, which is the identical
   pattern the plan's own P3 principle says must never be sufficient. This
   is a genuine, currently-live hole in the Phase F1 gate, not a flake or a
   scope artifact of this drill.

The P7 (horizontal ≠ vertical) claim is well supported overall, but by a mix
of this drill's absolute/vertical gates (which did fire in (a) and (b)) and
the historical record (`git show 23ef2d2b`, `bd7ec284`'s own "46/46"
message) rather than by a from-scratch 7-tier-synchronized horizontal-stays-
green reproduction, which this single drill session did not attempt.
