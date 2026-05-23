import RunarVerification.ANF.Syntax
import RunarVerification.ANF.Eval
import RunarVerification.Stack.Lower

/-!
# Stage D2 — stateful-prologue substrate (investigation PoC)

This file is the **map substrate** for retiring the omnibus sub-axiom
`compileSafe_observational_correct_modulo_stateful_codegen`
(`Pipeline.lean`), the FIRST branch in the omnibus dispatch — it fires
when `Lower.bindingsUseCheckPreimage anfM.body = true`.

It mirrors, for the auto-injected stateful prologue, the decidable
fragment-classifier + extraction pattern that the RETIRED `update_prop`
sub-axiom used (`Stack/AgreesA5.lean#updatePropConsumeShapeBool` +
`updatePropConsumeShapeBool_extract`).  Nothing here is import-wired into
`Pipeline.lean`; this is the standalone substrate the retirement would
consume.

## What the stateful lowering actually does

A `StatefulSmartContract` method gets the compiler to AUTO-INJECT a
`checkPreimage(preimage)` at method entry.  Concretely:

* **ANF side** (`ANF/Eval.lean:2070`): `.checkPreimage preimage` resolves
  the preimage ref, requires it to be byte-coercible (`asBytes?`), and on
  success produces `.vBool (Crypto.checkPreimage bytes)` — threading the
  state UNCHANGED.  Note: the ANF evaluator does NOT abort on an invalid
  preimage; the binding's *value* is a bool and the script-level abort
  happens at a later `.assert`/`OP_VERIFY`.
* **Stack side** (`Stack/Lower.lean:949 lowerCheckPreimageOpsLive`): emits
  `OP_CODESEPARATOR ; <load preimage> ; <load _opPushTxSig> ; push G ;
  OP_CHECKSIGVERIFY`.  The `OP_CHECKSIGVERIFY` (`Stack/Eval.lean:610`)
  runs `Crypto.checkSig` (the AUTH backend) — NOT `Crypto.checkPreimage`
  (the PREIMAGE backend, `ANF/Eval.lean:1213`) — and ABORTS on failure.

So the two sides run **different backends** and have **different abort
semantics** at the prologue: this is exactly the open content the D2.a
operational claim must bridge.  This file pins down the ANF-side
operational fact (the prologue's step shape) precisely, leaving the
backend-bridge as the documented remaining blocker.

## Hypothesis hygiene (§2.1)

Every lemma here takes only INPUT-side facts (the preimage ref resolves
to bytes — a domain-readiness fact about the *initial* state, like the
allowed `hParamDom` example in PATH2_PLAN §2.1).  No lemma takes a
conclusion-restating hypothesis.  No new axioms; no `sorry`/`admit`.
-/

namespace RunarVerification
namespace Stack
namespace AgreesD2

open RunarVerification.ANF
open RunarVerification.ANF.Eval

/-- **The canonical auto-injected stateful prologue body.**

Mirrors `Stack/Lower.lean#lowerMethod`: a stateful method's body begins
with a single `check_preimage(preimage)` binding (named `_cp0` here over a
preimage param `pre`).  Decidable, witness-parameterised — the exact
counterpart of `AgreesA5.updatePropConsumeBody`. -/
def statefulPrologueBody (pre : String) : List ANFBinding :=
  [ ⟨"_cp0", .checkPreimage pre, none⟩ ]

/-- **Decidable BODY-shape classifier for the stateful prologue.**

Recognises EXACTLY a one-binding body `_cp0 := check_preimage pre`.
VACUOUS (`_ => false`) on every other body, so a keyed omnibus premise
built on it would stay jointly satisfiable — same discipline as
`AgreesA5.updatePropConsumeShapeBool`. -/
def statefulPrologueShapeBool : List ANFBinding → Bool
  | [ .mk "_cp0" (.checkPreimage _) none ] => true
  | _ => false

/-- **Extraction.**  A `statefulPrologueShapeBool`-true body is EXACTLY
`statefulPrologueBody pre` for the recovered preimage witness `pre`. -/
theorem statefulPrologueShapeBool_extract (body : List ANFBinding)
    (h : statefulPrologueShapeBool body = true) :
    ∃ pre : String, body = statefulPrologueBody pre := by
  unfold statefulPrologueShapeBool at h
  split at h
  next pre => exact ⟨pre, rfl⟩
  next => exact absurd h (by decide)

/-- **The structural connective into the omnibus dispatch.**

`Lower.bindingsUseCheckPreimage` is exactly the `_hStateful` trigger of
the stateful sub-axiom (`Pipeline.lean:2880`); this proves the canonical
prologue body lands in that branch.  This is the load-bearing fact the
retirement needs: the discharged theorem must apply on EXACTLY the bodies
the dispatch sends to the stateful arm. -/
theorem bindingsUseCheckPreimage_statefulPrologue (pre : String) :
    Lower.bindingsUseCheckPreimage (statefulPrologueBody pre) = true := by
  unfold statefulPrologueBody Lower.bindingsUseCheckPreimage
  rfl

/-- The `bindingsUseCodePart` flag is `false` on the bare prologue (no
`add_output`/`add_raw_output`/`computeStateOutput*`).  This pins the
`lowerMethod` initial-stack-map branch to `userMap ++ ["_opPushTxSig"]`
(one implicit param, not two) — a precise structural fact about which
implicit-param layout the prologue alone triggers. -/
theorem bindingsUseCodePart_statefulPrologue (pre : String) :
    Lower.bindingsUseCodePart (statefulPrologueBody pre) = false := by
  simp only [statefulPrologueBody, Lower.bindingsUseCodePart, Bool.or_self]

/-- **ANF-side prologue reduction (the genuine operational content).**

From the INPUT-side domain fact that the preimage ref resolves to bytes
(`resolveRef pre = some (.vBytes b)` — a readiness fact about the initial
state, §2.1-allowed), the ANF evaluator's run of the prologue SUCCEEDS
and produces the entry state with the bool binding `_cp0` pushed.  The
threaded state is otherwise UNCHANGED — capturing precisely the
"prologue is a pure entry-side check that leaves the body's state intact"
property the D2.a bridge relies on.

This is NOT a degenerate `success → success` transport: it computes the
exact post-state of the prologue from a structural input fact. -/
theorem evalBindingsP_statefulPrologue_reduces
    (methods : List ANFMethod) (s : State) (pre : String) (b : ByteArray)
    (hPre : s.resolveRef pre = some (.vBytes b)) :
    evalBindingsP methods s (statefulPrologueBody pre)
      = .ok (s.addBinding "_cp0" (.vBool (Crypto.checkPreimage b))) := by
  unfold statefulPrologueBody
  show evalBindingsP methods s
        [⟨"_cp0", .checkPreimage pre, none⟩] = _
  unfold evalBindingsP
  simp only [evalValueP, lookupRef, hPre, Value.asBytes?, bind, Except.bind,
    evalBindingsP]

/-- **Corollary: the ANF prologue run is `.isSome` (always succeeds).**

The ANF model of `check_preimage` never aborts (its value is a bool); the
abort lives in a downstream assert.  This is the ANF half of the success
bit the omnibus `successAgrees` compares — making explicit that any
prologue-driven `successAgrees` divergence must come from the STACK side
(`OP_CHECKSIGVERIFY` aborting), never the ANF side. -/
theorem evalBindingsP_statefulPrologue_isSome
    (methods : List ANFMethod) (s : State) (pre : String) (b : ByteArray)
    (hPre : s.resolveRef pre = some (.vBytes b)) :
    (evalBindingsP methods s (statefulPrologueBody pre)).toOption.isSome = true := by
  rw [evalBindingsP_statefulPrologue_reduces methods s pre b hPre]
  rfl

/-! ## In-file smokes

Concrete witnesses pinning every exported symbol.  `native_decide` is
used only on fully-concrete Bool computations (per HARD CONSTRAINT 6). -/

/-- Concrete preimage-bearing entry state: param `pre ↦ vBytes #[0xAB]`. -/
def smokeState : State :=
  { params := [("pre", .vBytes (ByteArray.mk #[0xAB]))] }

/-- Smoke: classifier accepts the canonical prologue body. -/
example : statefulPrologueShapeBool (statefulPrologueBody "pre") = true := by
  native_decide

/-- Smoke: classifier rejects a non-prologue body (vacuity witness). -/
example : statefulPrologueShapeBool [⟨"x", .loadParam "pre", none⟩] = false := by
  native_decide

/-- Smoke: extraction recovers the witness. -/
example : ∃ pre : String, statefulPrologueBody "pre" = statefulPrologueBody pre :=
  statefulPrologueShapeBool_extract (statefulPrologueBody "pre") (by native_decide)

/-- Smoke: the canonical prologue trips the stateful dispatch trigger. -/
example : Lower.bindingsUseCheckPreimage (statefulPrologueBody "pre") = true := by
  native_decide

/-- Smoke: the bare prologue needs only `_opPushTxSig` (no `_codePart`). -/
example : Lower.bindingsUseCodePart (statefulPrologueBody "pre") = false := by
  native_decide

/-- Smoke: the preimage ref resolves to bytes in the concrete entry state.
(`Value` has no `DecidableEq` — ByteArray blocks it — so this is `rfl`, a
definitional computation through `find?`/`==` on the string key.) -/
example : smokeState.resolveRef "pre" = some (.vBytes (ByteArray.mk #[0xAB])) := rfl

/-- Smoke: the ANF prologue run succeeds on the concrete entry state.
Exercises `evalBindingsP_statefulPrologue_isSome` end-to-end. -/
example :
    (evalBindingsP [] smokeState (statefulPrologueBody "pre")).toOption.isSome = true :=
  evalBindingsP_statefulPrologue_isSome [] smokeState "pre" (ByteArray.mk #[0xAB]) rfl

end AgreesD2
end Stack
end RunarVerification
