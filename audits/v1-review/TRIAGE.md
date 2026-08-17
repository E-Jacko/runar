# Rúnar v1 — three-way audit TRIAGE

Worktree: `.worktrees/v1-fixes` on branch `fix/v1-audit-triage`, off `main` @ `52de4384`.
**No source file has been modified.** Everything below is merge, reproduction and
classification only, per the fix protocol.

---

## 0. Input provenance — read this first, it changes what "codex" means

The prompt specifies three inputs. The tree actually contains **four** review sets,
and two of them are both called `codex` with **colliding `CX-###` ids**:

| set | location | branch | findings | status |
|---|---|---|---|---|
| claude | `runar-claude` worktree (untracked) | detached @ 52de4384 | 16 | complete |
| **codex** | **main working tree (untracked)** | `audit/codex/exhaustive-v1` @ 52de4384 | **8** | complete |
| grok | `runar-grok` worktree (untracked) | detached @ 52de4384 | 35 | complete + PROBES/BLINDSPOT/SELF-CRITIQUE |
| codex-v1review | `runar-codex` worktree | `audit/codex/v1-review` @ aca61c33 | 6 (4 committed, dirty) | **superseded** |

**Resolution: `audit/codex/exhaustive-v1` is the `CX-###` input.** Two independent
reasons, not just one:

1. It ships `conformance-matrix.md`, `provenance-matrix.md`, `rejection-matrix.md`,
   `skip-matrix.md` — precisely the deliverables the fix prompt attributes to Codex
   ("all 58 provenance entries, all 64 skip rows, full conformance and rejection
   matrices"). The `v1-review` set has neither the matrices nor that shape.
2. **The `v1-review` set is demonstrably stale.** Its headline S1 (`CX-002`,
   "ecMul and ecMulGen return the zero point for scalar 2") **does not reproduce at
   HEAD** — see §2. HEAD's tip merge is literally "EC formula fixes".

The superseded set is preserved at `audits/v1-review/codex-v1review/` and its one
S1 was still verified on its merits rather than discarded.

All four sets audited the same commit except `codex-v1review`.

---

## 1. Merge and dedup

59 primary findings (16 CC + 8 CX + 35 GK) → **15 root-cause clusters**.
Full id mapping in §5. Convergence counted across the three primary reviewers.

---

## 2. S0 / S1 reproduction — verify before fixing

| finding | sev | reviewers | verdict | evidence |
|---|---|---|---|---|
| #149 branch layout (CC-001, CC-002, CC-014, CX-001, GK-001) | S0 | **3/3** | **reproduced** | fold-ON `param2`=0,1,−1,−2 → `interp=false, spend=true` (bypass); fold-OFF `param2=5` → `interp=true, spend=false` (lock). Stateful `addOutput` surface reproduces on 4/4 fresh seeds. |
| CC-007 readonly write accepted by all 7 tiers | S1 | 1/3 | **reproduced** | go/rust/python all emit `76a97ca9788777` for `Hijack.runar.py`; `spec/semantics.md:247` defines it as an ERROR |
| GK-031 Rust bsv-sdk `hashPrevouts` order | S1 | 1/3 | **reproduced — but already known** | `docs/audit/upstream-bsv-sdk-bip143-hashprevouts.md` exists in-repo, status "confirmed, pinned in-repo, **not yet filed upstream**", pin test `pin_bsv_sdk_cannot_sighash_input_index_above_zero` |
| GK-032 Rust bsv-sdk OP_PUSH_TX `0x8d` desync | S1 | 1/3 | **reproduced — but already known** | recorded verbatim in `packages/runar-rs/tests/mock_broadcast_validation.rs` module docs; such inputs counted UNVALIDATABLE, cannot satisfy non-vacuity |
| GK-007 / GK-008 Lean axiom scope | S1 | 1/3 | **accurate description, not a defect** | both are documented axioms in `TRUST_MANIFEST.md`; the axiom count gate passes at exactly 71 |
| GK-025 "historical pattern" | S1 | 1/3 | **not a defect** | a meta-observation about how past bugs shipped; no code change is implied |
| GK-002 oracles blind to quiet wrong-state | S0 | 1/3 | **partially** | the *shape* claim is right and is exactly CC-013; but `--spend-oracle` **does** check state VALUE against an independent model, so "blind" overstates it. Reclassified to the machinery cluster M1. |
| **CX-002 (v1review) ecMul/ecMulGen → zero point** | S1 | 1/4 | **NOT REPRODUCED** | `ecMulGen(2)` and `ecMul(G,2)` both return correct 2G; k=1,3 also correct. → `DISPUTED.md` |

Notable S2s checked:

| finding | verdict | evidence |
|---|---|---|
| GK-019 CORRECTNESS.md says 70 axioms | **reproduced** | `CORRECTNESS.md:9,127` say 70; `TRUST_MANIFEST.md:35` and `check-tcb-drift.sh:23` say 71 |
| GK-030 MockProvider.broadcast never registers tx | **reproduced** | `broadcast()` sets `rawTransactions`+`knownOutpoints` but never `this.transactions`; `getTransaction` reads only the latter → always throws; `contract.ts:1784` swallows it and returns an **empty shell** (`inputs: []`, `outputs: []`). Observed firing on nearly every probe run. |
| GK-010 30 of 71 fixtures have no witness | **reproduced** | 10 plain + 31 real-crypto witnesses = 41 covered; `coverage-ledger.json` has exactly **30** residual entries |
| CC-008 non-literal initializer accepted by 4 tiers | inherited `verified` from a same-commit run | not re-derived this session |

---

## 3. Grok PROBES.md — 50 probes executed (step 1.3)

Harness: `probe-extract.mjs` (compile matrix) + `probe-exec.mjs` (execution).

| outcome | n | meaning |
|---|---|---|
| no code block | 12 | nothing to run |
| **compile-rejected — probe authoring errors** | 14 | `bytes` type, missing constructor, missing terminal `assert`, a quoting bug yielding `''''`. Grok's contracts, not compiler defects. |
| compile-rejected — **correct compiler diagnostic** | 2 | P04, P27 hit real `addOutput`-in-conditional guards; Grok predicted "may hard-fail compile — pin diagnostic". Correct prediction. |
| compiled and executed, agreed | 20 | no divergence |
| **compiled, genuinely DIVERGENT** | **2** | **P01, P02** |
| divergent under the wrong oracle — **my harness's fault** | 7 | see below |

### P01 / P02 — genuine, and they corroborate the C1 cluster
Both are `StatefulSmartContract` with a nested declared-results merge.
`interp=true, spend=false` — real `@bsv/sdk` Spend rejects with *"The top stack
element must be truthy after script evaluation"*. Source semantics accept, so the
UTXO is unspendable. Independently authored by a different reviewer, and they land
on the same root cause as CC-001/CC-002/CC-014. **Promoted into C1 as corroboration,
not as new root causes.**

### The 7 that were my harness, not the compiler — recorded so the probe list scores honestly
P16, P17, P18, P22, P25, P29, P30 first showed `interp=true / spend=false`, three of
them with **clean-stack violations** — which would have been a broader S0 than #149.
They are all **stateless** `SmartContract`s and I was driving them through
`deploy` + `call`, the stateful continuation path. Re-run through
`runTriModalExecution` (the correct stateless oracle, which applies the clean-stack /
push-only / minimal-push consensus wrappers):

```
P29.f(1) interp=true vm=true spend=true      P22.m1(1) interp=true vm=true spend=true
P30.f(1) interp=true vm=true spend=true      P22.m1(0) interp=true vm=true spend=true
P29.f(0) interp=true vm=true spend=true
```

All agree. **No clean-stack defect exists.** P25 is additionally a harness artifact by
construction: it passes a fake `Sig` while the ANF interpreter mocks `checkSig` as
always-true, so `interp=true / spend=false` is the expected, correct outcome.

**P16 / P17 / P18 are INCONCLUSIVE, not cleared.** They probe genuine consensus edges
(negative `OP_DIV`/`OP_MOD` operands, `safediv`/`safemod` zero divisor, shift ≥ width →
non-minimal encoding). Under tri-modal both engines agreed on *reject*, but with
different constructor args than the deploy path used, so the two runs are not
comparable. These need a targeted re-test with matched inputs before v1.

---

## 4. Defects vs machinery gaps

**Defects (wrong behaviour) — fix these:**

| cluster | sev | reviewers | root cause |
|---|---|---|---|
| **C1 branch-merge layout (#149)** | **S0** | 3/3 | `lowerIf` reconciles arms by name-set and depth but not by slot **layout**; an inner declared-results `if` rotates a slot inherited from the enclosing arm. Needs BOTH a live untouched sibling AND an outer `if` without `else`. |
| **C2 readonly not enforced** | **S1** | 1/3 | `02-validate`/`03-typecheck` never implement `spec/semantics.md:247`; the write lowers to a local rebind |
| C3 tier reject-parity divergence | S2 | 2/3 | rust/zig/python/ruby accept a non-literal property initializer ts/go/java reject |
| C4 MockProvider tx registration | S2 | 1/3 | `broadcast()` omits `this.transactions.set` → post-broadcast assertions run against an empty shell |
| C5 docs axiom-count drift | S3 | 1/3 | `CORRECTNESS.md` says 70, gate enforces 71 |

**Machinery gaps (why the defects escaped) — different work, separate commits:**

| cluster | reviewers | substance |
|---|---|---|
| M1 generator reach | 3/3 | `--spend-oracle` 0 failures / 11,750 spend inputs; `arbExecMethodBody` emits zero `if`; spend-shapes `nested` cannot express the #149 topology |
| M2 provenance self-attestation | 3/3 | 210 entries, 27 self-declared `unreviewed`; `tests/vectors/*.json` outside `GOLDEN_MATCHERS`; fold-on allowlist accepts nonexistent fixture names |
| M3 mutation corpus | 2/3 | curated 22 @ 100% vs mechanical 578 @ 68.3%; 25/25 escalated survivors caught by nothing; a zero-coverage path inside `lowerIf` |
| M4 regression corpus | 3/3 | neither HEAD-fixed miscompilation has a replayable entry |
| M5 Go-only crypto KATs | 3/3 | Merkle and friends have only repo-generated vectors |
| M6 witness coverage | 1/3 | 30 of 71 fixtures are ledger residuals |
| M7 skip/vacuous tests | 2/3 | 18 tests pass while asserting nothing; skip lint red on a design doc's TODOs |
| M8 canonicalJson tier skip | 1/3 | `zig=skip` still reports "0 mismatches", exit 0 |
| M9 upstream Rust bsv-sdk | 1/3 | known, pinned, **not yet filed upstream** |

---

## 5. Fix order

1. **C1** (S0, 3/3, 7 tiers) — highest blast radius; C2 is independent and can land in parallel.
2. **C2** (S1, 7 tiers, small self-contained validator rule).
3. **C3, C4, C5** (S2/S3, cheap).
4. **M1 → M4** — M1 first: its generator extension is what proves C1's fix, and M4 depends on it.
5. **M2, M5, M6, M7, M8** — gate work.
6. **M9** — file upstream; not fixable here.

---

## 6. Full id mapping

- **C1**: CC-001, CC-002, CC-014, CX-001, GK-001, GK-005, GK-027, GK-029 (+probes P01, P02)
- **C2**: CC-007 · **C3**: CC-008, GK-020 · **C4**: GK-030 · **C5**: GK-019, GK-034
- **M1**: CC-003, CC-004, CC-006, CC-013, CC-016, CX-004, GK-002, GK-015, GK-016
- **M2**: CC-005, CC-010, CX-002, CX-008, GK-003, GK-004, GK-012, GK-017, GK-018
- **M3**: CC-015, CC-016, GK-033 · **M4**: CC-012, CX-005, GK-006
- **M5**: CX-006, GK-009 · **M6**: GK-010, GK-035 · **M7**: CC-009, CX-003, GK-011, GK-022
- **M8**: CC-011, GK-026 · **M9**: GK-031, GK-032
- **Lean/scope (accurate, no code change)**: CX-007, GK-007, GK-008, GK-013, GK-019
- **Not defects / disputed**: CX-002(v1review) *not reproduced*; GK-021 (`guess`, contradicted by a 6-tier × 5-process determinism run); GK-025 (meta); GK-014, GK-023, GK-024, GK-028 (`inferred`, no reproduction offered)
