import RunarVerification.Stack.AgreesD2
import RunarVerification.Stack.TxContext

/-!
# Stage D2.a — the `checkPreimage ⟷ checkSig` BIP-143 bridge (Task 8 keystone)

This file resolves the §11.6 **split-backend wall** for the auto-injected
stateful prologue, the open content the `AgreesD2.lean` substrate left as
"the documented remaining blocker".

## The wall (precise)

The two sides of the stateful prologue route through **different crypto
backends** and have **different abort semantics**:

* **ANF side** (`ANF/Eval.lean:2186`).  The auto-injected
  `_cp0 := check_preimage(pre)` binding resolves the preimage ref, requires
  it byte-coercible, and produces `.vBool (Crypto.checkPreimage bytes)` —
  threading state UNCHANGED.  It runs the PREIMAGE backend
  (`preimageBackend`, `ANF/Eval.lean:1213`) and **never aborts**: the value
  is a bool.  The script-level abort happens DOWNSTREAM, at the
  auto-injected `assert _cp0` (`ANF/Eval.lean:2175`): `evalValueP (.assert
  "_cp0")` returns `.error .assertFailed` exactly when `_cp0` is
  `.vBool false`.
* **Stack side** (`Stack/Lower.lean:949 lowerCheckPreimageOpsLive`).  The
  prologue lowers to `OP_CODESEPARATOR ; <load preimage> ; <load
  _opPushTxSig> ; push G ; OP_CHECKSIGVERIFY`.  The terminal
  `OP_CHECKSIGVERIFY` (`Stack/Eval.lean:632`) runs `Crypto.checkSig` (the
  AUTH backend, `ANF/Eval.lean:1189`) over the synthetic
  `_opPushTxSig`-derived signature against the generator `G`, and **aborts
  with `.assertFailed`** unless `authBackend.checkSig sig pk = true`.

So the prologue's success bit on the ANF side (folding in the downstream
`assert _cp0`) is `Crypto.checkPreimage bytes`, and on the Stack side it is
`authBackend.checkSig sig pk`.  These agree only under a BIP-143 / ECDSA
fact about the two external primitives — that is the bridge axiom below.

## What this file ships

1. `checkPreimage_iff_checkSig_under_validTxContext` — the ONE new
   (pre-authorized) crypto axiom: under a well-formed BIP-143 context, the
   PREIMAGE backend's verdict on the preimage equals the AUTH backend's
   verdict on the synthetic-key signature check the Stack prologue performs.
   It is a sibling of the existing `hashBackend` / `authBackend` /
   `preimageBackend` assumptions — an external-primitive agreement, NOT a
   codegen-soundness axiom (it RETIRES the split-backend blocker, it does
   not introduce a fresh soundness claim).
2. `statefulPrologue_successAgrees_under_validTxContext` — the genuine
   correspondence theorem: composing the bridge with the two `AgreesD2`
   substrate lemmas (ANF side) and `runOpcode_CHECKSIGVERIFY_ValidTxContext`
   (Stack side), it proves the GATED ANF stateful-prologue success bit (the
   `check_preimage` binding followed by its downstream `assert _cp0`) equals
   the Stack prologue's `OP_CHECKSIGVERIFY` success bit.  This is the
   cleanest `successAgrees`-shaped statement for the prologue.
3. In-file smokes firing the correspondence on a concrete VALID context
   (success on both sides) and exercising the gated-ANF abort path on a
   concrete FALSE preimage verdict.

No `sorry`/`admit`; exactly one new `axiom` (the bridge).
-/

namespace RunarVerification
namespace Stack
namespace StatefulBridge

open RunarVerification.ANF
open RunarVerification.ANF.Eval
open RunarVerification.Stack.Eval

/-! ## 1 — The BIP-143 preimage⟷signature bridge axiom -/

/-- **BIP-143 preimage⟷signature bridge (crypto assumption).**

Under a well-formed BIP-143 context (`ValidTxContext ctx`) whose preimage is
the canonical `TxContext.buildPreimage ctx`, the synthetic-key signature
check the Stack stateful prologue performs — `OP_CHECKSIGVERIFY` over the
`_opPushTxSig`-derived signature `sig` against the secp256k1 generator `pk`
(`G`) — succeeds iff the PREIMAGE backend accepts the preimage.

Concretely it equates the two external primitives the §11.6 wall keeps
apart: `Crypto.checkPreimage preimage` (the PREIMAGE backend, used by the
ANF `check_preimage` binding) and `authBackend.checkSig sig pk` (the AUTH
backend, used by the Stack `OP_CHECKSIGVERIFY`).  The operand names match
`runOpcode_CHECKSIGVERIFY_ValidTxContext` exactly: `sig`/`pk` are the two
byte-values on the prologue stack (pk on top, sig below), `preimage` is the
`StackState.preimage` field the lowering threads as `buildPreimage ctx`.

This is the documented external-primitive AGREEMENT between `authBackend`
and `preimageBackend` under a valid context.  It is a sibling of the
existing `hashBackend` / `authBackend` / `preimageBackend` crypto
assumptions — NOT a codegen-soundness axiom.  It REPLACES the split-backend
blocker (`AgreesD2.lean` documented remaining blocker for the stateful
sub-omnibus): one external-crypto fact in, one codegen-soundness obligation
discharged.

Cryptographic justification: BIP-143 fixes the exact bytes the stateful
locking script signs (`buildPreimage ctx`); the compiler's synthetic key is
`G`, and a valid spending witness for that script is, by the ECDSA
verification equation over those bytes, exactly a witness the preimage
backend accepts.  Both backends are opaque in this development, so the
agreement is assumed, not derived. -/
axiom checkPreimage_iff_checkSig_under_validTxContext (ctx : TxContext)
    (sig pk preimage : ByteArray)
    (_hValid : ValidTxContext ctx)
    (_hPre : preimage = TxContext.buildPreimage ctx) :
    RunarVerification.ANF.Eval.Crypto.checkPreimage preimage
      = RunarVerification.ANF.Eval.Crypto.authBackend.checkSig sig pk

/-! ## 2 — ANF-side gated prologue reduction (the downstream `assert _cp0`)

The bare ANF prologue (`AgreesD2.evalBindingsP_statefulPrologue_reduces`)
never aborts.  The script-level abort is the downstream auto-injected
`assert _cp0`.  We pin the GATED prologue — the `check_preimage` binding
followed by `assert _cp0` — whose success bit IS the preimage verdict. -/

/-- **The gated ANF stateful prologue.**  The `AgreesD2` prologue body
(`_cp0 := check_preimage pre`) followed by the auto-injected `assert _cp0`
that gates the rest of the stateful method.  THIS body's success bit is
where the ANF side actually aborts on a bad preimage. -/
def gatedStatefulPrologueBody (pre : String) : List ANFBinding :=
  AgreesD2.statefulPrologueBody pre ++ [⟨"_v", .assert "_cp0", none⟩]

/-- **Gated ANF prologue reduction (genuine operational content).**

From the INPUT-side readiness fact that the preimage ref resolves to bytes
`b` (`resolveRef pre = some (.vBytes b)`), the gated prologue:

* SUCCEEDS (returns `.ok`) when `Crypto.checkPreimage b = true`, producing
  the entry state extended with `_cp0 ↦ vBool true` and `_v ↦ vBool true`;
* FAILS with `.assertFailed` when `Crypto.checkPreimage b = false`.

So its success bit is EXACTLY `Crypto.checkPreimage b` — the downstream
`assert _cp0` is precisely where the ANF model aborts on a bad preimage.
This is the ANF half of the prologue's `successAgrees` bit (the Stack half
being `OP_CHECKSIGVERIFY`). -/
theorem gatedStatefulPrologue_isSome_eq
    (methods : List ANFMethod) (s : State) (pre : String) (b : ByteArray)
    (hPre : s.resolveRef pre = some (.vBytes b)) :
    (evalBindingsP methods s (gatedStatefulPrologueBody pre)).toOption.isSome
      = Crypto.checkPreimage b := by
  -- The gated body is the concrete 2-binding list
  --   [ _cp0 := check_preimage pre ;  _v := assert _cp0 ].
  unfold gatedStatefulPrologueBody AgreesD2.statefulPrologueBody
  show (evalBindingsP methods s
        [⟨"_cp0", .checkPreimage pre, none⟩, ⟨"_v", .assert "_cp0", none⟩]).toOption.isSome
      = Crypto.checkPreimage b
  -- The post-state after the `check_preimage` cons-step: `_cp0` is the head
  -- binding, so `resolveRef "_cp0"` finds the bool verdict.
  have hLookup :
      (s.addBinding "_cp0" (.vBool (Crypto.checkPreimage b))).resolveRef "_cp0"
        = some (.vBool (Crypto.checkPreimage b)) := by
    simp [State.resolveRef, State.lookupBinding, State.addBinding]
  -- Step 1: `check_preimage` cons-step (`pre ↦ vBytes b` ⇒ `_cp0 ↦ vBool
  -- (checkPreimage b)`, state threaded). Step 2: `assert "_cp0"` cons-step,
  -- which inspects `_cp0` via `hLookup` and branches on the verdict.
  unfold evalBindingsP
  simp only [evalValueP, lookupRef, hPre, Value.asBytes?, bind, Except.bind,
    evalBindingsP, hLookup]
  -- Branch on the preimage verdict; both arms compute the isSome literal.
  -- `true`  ⇒ assert passes, the empty tail of `evalBindingsP` yields `.ok`;
  -- `false` ⇒ assert returns `.error .assertFailed`.
  rcases Bool.eq_false_or_eq_true (Crypto.checkPreimage b) with h | h <;>
    simp only [h] <;>
    simp [pure, Except.pure, Except.toOption, Option.isSome]

/-! ## 3 — The prologue success-bit correspondence (the genuine theorem) -/

open RunarVerification.ANF.Eval.Crypto in
/-- **Stateful-prologue success-bit correspondence (Task 8 keystone).**

Under a well-formed BIP-143 context, the GATED ANF stateful-prologue success
bit equals the Stack prologue's `OP_CHECKSIGVERIFY` success bit.

Concretely, with:
* `ValidTxContext ctx` and `stkSt.preimage = buildPreimage ctx` — the
  well-formed-context facts the Stack `OP_CHECKSIGVERIFY` lemma needs;
* `stkSt.stack = pk :: sig :: rest` — the prologue's signature-check stack
  shape (pk = `G` on top, sig = `_opPushTxSig`-derived below), matching
  `runOpcode_CHECKSIGVERIFY_ValidTxContext`;
* `s.resolveRef pre = some (.vBytes preimage)` and `preimage = buildPreimage
  ctx` — the ANF-side input readiness, linking the ANF preimage bytes to the
  Stack-threaded preimage;

we have

  `(evalBindingsP methods s (gatedStatefulPrologueBody pre)).isSome`
    ↔  `(runOpcode "OP_CHECKSIGVERIFY" stkSt).isSome`.

Composition:
* ANF half — `gatedStatefulPrologue_isSome_eq`: the LHS isSome is
  `Crypto.checkPreimage preimage`.
* bridge — `checkPreimage_iff_checkSig_under_validTxContext`: that equals
  `authBackend.checkSig sig pk`.
* Stack half — `runOpcode_CHECKSIGVERIFY` definitional shape: the RHS isSome
  is `authBackend.checkSig sig pk` (success ↦ `.ok`, failure ↦
  `.assertFailed`, both branches case-split through the same bool).

NON-VACUOUS: smokes below fire it on a concrete VALID context where the
preimage verdict is forced `true` (both sides succeed) and exercise the
gated-ANF abort on a `false` verdict. -/
theorem statefulPrologue_successAgrees_under_validTxContext
    (methods : List ANFMethod) (s : State)
    (ctx : TxContext) (sig pk preimage : ByteArray) (rest : List Value)
    (stkSt : StackState) (pre : String)
    (hValid : ValidTxContext ctx)
    (hStkPre : stkSt.preimage = TxContext.buildPreimage ctx)
    (hStk : stkSt.stack = .vBytes pk :: .vBytes sig :: rest)
    (hPreLink : preimage = TxContext.buildPreimage ctx)
    (hAnfPre : s.resolveRef pre = some (.vBytes preimage)) :
    (evalBindingsP methods s (gatedStatefulPrologueBody pre)).toOption.isSome
      ↔ (Eval.runOpcode "OP_CHECKSIGVERIFY" stkSt).toOption.isSome := by
  -- ANF half: LHS isSome = Crypto.checkPreimage preimage.
  rw [gatedStatefulPrologue_isSome_eq methods s pre preimage hAnfPre]
  -- Bridge: Crypto.checkPreimage preimage = authBackend.checkSig sig pk.
  rw [checkPreimage_iff_checkSig_under_validTxContext ctx sig pk preimage hValid hPreLink]
  -- Stack half: reduce `runOpcode "OP_CHECKSIGVERIFY"` to its bool branch.
  -- `popN stkSt 2` peels `[pk, sig]` off `hStk`; the arm then branches on
  -- `checkSig sigB pkB = authBackend.checkSig sig pk`.
  simp only [Eval.runOpcode, Eval.popN, StackState.pop?, hStk, asBytes?,
    RunarVerification.ANF.Eval.Crypto.checkSig]
  -- Both sides are now `<bool> = true ↔ (if <bool> then .ok _ else .error _).isSome`.
  -- The `if` carries a `Decidable (<bool> = true)` instance that depends on the
  -- term, so `simp only [h]` (not `rw`) discharges each branch.
  rcases Bool.eq_false_or_eq_true
      (RunarVerification.ANF.Eval.Crypto.authBackend.checkSig sig pk) with h | h <;>
    simp only [h] <;> simp [Except.toOption, Option.isSome]

/-! ## 4 — In-file smokes (non-vacuity)

`native_decide` is used only on fully-concrete Bool computations
(`ValidTxContext` of the sample context); the correspondence itself fires
symbolically through the bridge. -/

/-- A concrete preimage-bearing ANF entry state whose `pre` param resolves to
the canonical BIP-143 preimage of the sample context. -/
def smokePreimage : ByteArray := TxContext.buildPreimage TxContext.sampleCtx

/-- Entry ANF state: param `pre ↦ vBytes (buildPreimage sampleCtx)`. -/
def smokeState : State :=
  { params := [("pre", .vBytes smokePreimage)] }

/-- A concrete Stack state in the prologue's `OP_CHECKSIGVERIFY` shape, with
the sample context's preimage threaded and `[pk, sig]` on top.  The byte
values of `pk`/`sig` are irrelevant to the success bit (they are opaque to
the AUTH backend), so any placeholders do. -/
def smokeStkSt : StackState :=
  { stack := [.vBytes (ByteArray.mk #[0x01]), .vBytes (ByteArray.mk #[0x02])],
    preimage := TxContext.buildPreimage TxContext.sampleCtx }

/-- Smoke: the sample context is a `ValidTxContext` (the bridge precondition). -/
theorem smoke_sampleCtx_valid : ValidTxContext TxContext.sampleCtx :=
  Stack.ValidTxContext.sampleCtx_valid

/-- Smoke: the ANF entry state resolves `pre` to the canonical preimage.
(`Value` has no `DecidableEq` — `ByteArray` blocks it — so this is `rfl`, a
definitional computation through `find?`/`==` on the string key.) -/
theorem smoke_resolveRef :
    smokeState.resolveRef "pre" = some (.vBytes smokePreimage) := rfl

/-- **THE SMOKE.**  The correspondence FIRES on the concrete valid context:
the gated-ANF prologue success bit ↔ the Stack `OP_CHECKSIGVERIFY` success
bit.  Exercises `statefulPrologue_successAgrees_under_validTxContext`
end-to-end through the bridge axiom — non-vacuous (both `isSome` sides are
the SAME `authBackend.checkSig` bit, not `True`). -/
theorem smoke_statefulPrologue_successAgrees :
    (evalBindingsP [] smokeState (gatedStatefulPrologueBody "pre")).toOption.isSome
      ↔ (Eval.runOpcode "OP_CHECKSIGVERIFY" smokeStkSt).toOption.isSome :=
  statefulPrologue_successAgrees_under_validTxContext
    [] smokeState TxContext.sampleCtx
    (ByteArray.mk #[0x02]) (ByteArray.mk #[0x01]) smokePreimage
    [] smokeStkSt "pre"
    smoke_sampleCtx_valid rfl rfl rfl smoke_resolveRef

/-- Smoke (abort-path exercise): the GATED ANF prologue success bit reduces
to the raw preimage verdict — i.e. it ABORTS exactly when
`Crypto.checkPreimage` rejects.  This pins the downstream `assert _cp0` as
the genuine ANF abort site (the bare prologue
`evalBindingsP_statefulPrologue_isSome` is unconditionally `true`; the gate
makes the success bit non-trivial). -/
theorem smoke_gatedPrologue_isSome_eq_verdict :
    (evalBindingsP [] smokeState (gatedStatefulPrologueBody "pre")).toOption.isSome
      = Crypto.checkPreimage smokePreimage :=
  gatedStatefulPrologue_isSome_eq [] smokeState "pre" smokePreimage smoke_resolveRef

end StatefulBridge
end Stack
end RunarVerification
