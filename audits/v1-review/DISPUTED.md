# DISPUTED — findings that did not reproduce at `52de4384`

Per the fix protocol: nothing here gets fixed. Each entry records the evidence that
the claim does not hold at HEAD.

---

## CX-002 (codex `v1-review` set) — "ecMul and ecMulGen return the zero point for scalar 2"

**Claimed:** S1, all 7 tiers. "Contracts using `ecMul(P, 2)` or `ecMulGen(2)` compile
successfully and agree across tiers but evaluate the wrong group element; the shipped
ec-unit locking script is unspendable."

**Verdict: NOT REPRODUCED.**

Ran the finding's own reproduction script (`repro/ecmul-k2.mjs`) unmodified against a
build of `52de4384`:

```json
{ "success": true,
  "expected": "c6047f9441ed7d6d...1236431a950cfe52a",
  "actual":   "c6047f9441ed7d6d...1236431a950cfe52a" }
```

Exit 0 — the script's own assertion passes. Extended to `ecMul` (the finding names
both emitters) over k = 1, 2, 3:

```
ecMul(G,1) success=true zeroPoint=false matchesG=true
ecMul(G,2) success=true zeroPoint=false matches2G=true
ecMul(G,3) success=true zeroPoint=false
```

No zero point at any tested scalar; k=2 returns exactly 2G.

**Why it was true when written and is false now:** the finding was authored against
`audit/codex/v1-review` (`aca61c33`), which predates HEAD's tip merge — *"Merge
integration/ec-formulas-and-testing-gap: **EC formula fixes**, testing-gap remediation,
Lean multi-result branch support"*. The k=2 doubling case in the Jacobian ladder is
what that merge repaired.

**Disposition:** no action. This is the single strongest piece of evidence that the
`codex/v1-review` set is superseded by `codex/exhaustive-v1` (see `TRIAGE.md` §0).
`CORRECTNESS.md:240` still lists `ecMul`/`ecMulGen` among the documented axiom
scope-outs, which is a *documentation* matter (cluster C5), not this defect.

---

## GK-021 — "Host-language map/hash iteration order is a latent non-determinism class"

**Claimed:** S2, area `emit`. Reviewer's own `confidence` field: **`guess`**.

**Verdict: NOT REPRODUCED — and contradicted by direct measurement.**

A determinism run across 6 tiers × 5 separate processes produced byte-identical
output with no ordering variation. The finding offers no reproduction, and its own
confidence field concedes it is speculative.

**Disposition:** no action. Re-open only if a concrete ordering divergence is observed.

---

## GK-025 — "Historical pattern: shared codegen defects reach RC via parity+self-golden"

**Claimed:** S1, area `crypto`.

**Verdict: NOT A DEFECT.** This is a true and useful *observation about the project's
history* (SLH-DSA, P-256), not a statement about current behaviour. There is no code
change it implies and no test that could go red for it. Its substance is already
carried by clusters M2 (provenance self-attestation) and M5 (Go-only KATs), which are
scheduled.

**Disposition:** folded into M2/M5; not tracked as a separate S1.

---

## GK-007 / GK-008 — Lean axiom scope (`checkPreimage` blob opaque; `crypto_call` residue)

**Verdict: ACCURATE DESCRIPTION, NOT A DEFECT.**

Both describe axioms that `TRUST_MANIFEST.md` already documents explicitly, and the
drift gate passes at exactly 71 axioms (`check-tcb-drift.sh` → `OK: axioms = 71`,
opaques 0, partial defs 0). Calling a documented, gated, deliberately-scoped axiom an
S1 *finding* conflates "the formal boundary is here" with "something is wrong".

**Disposition:** the boundary itself is a real v1 risk and is carried in the FIX-REPORT
open-risks section. No code change; no severity.

---

## Probe divergences that were harness artifacts, not defects

P22, P25, P29, P30 initially showed `interp=true / spend=false` — three of them
**clean-stack violations**, which would have been a broader S0 than #149. They are
**stateless** `SmartContract`s and were being driven through `deploy` + `call`, the
stateful continuation path. Re-run through `runTriModalExecution` — the correct
stateless oracle, which applies the clean-stack, push-only and minimal-push consensus
wrappers — all agree:

```
P29.f(1) interp=true vm=true spend=true    P22.m1(1) interp=true vm=true spend=true
P29.f(0) interp=true vm=true spend=true    P22.m1(0) interp=true vm=true spend=true
P30.f(1) interp=true vm=true spend=true
```

P25 is an artifact by construction: it passes a fake `Sig` while the ANF interpreter
mocks `checkSig` as always-true, so the split verdict is the *expected* outcome.

**Disposition:** no defect. Recorded because the near-miss is the point — the first
result would have been a false S0.

**P16 / P17 / P18 are NOT cleared, only inconclusive** — see `TRIAGE.md` §3. They
probe negative `OP_DIV`/`OP_MOD`, zero divisor, and shift ≥ width; the two runs used
mismatched constructor args so they are not comparable. They need a targeted re-test.
