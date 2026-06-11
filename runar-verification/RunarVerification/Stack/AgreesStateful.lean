import RunarVerification.Stack.StatefulBridge
import RunarVerification.Script.Parse
import RunarVerification.Script.Emit
import RunarVerification.Script.EmitCorrect

/-! # `Stack/AgreesStateful.lean` — canonical stateful-method consume substrate

**Path 2 — stateful sub-omnibus retirement substrate.** This file carries the
lowering, runtime, and parse-round-trip facts for the CANONICAL stateful
method — a single-param public method whose body is exactly the gated
stateful prologue

    `_cp0 := check_preimage pre ;  _v := assert _cp0`

(the auto-injected entry wrapper of `StatefulSmartContract` methods, with no
user logic and no state-output epilogue).  Together with the
`StatefulBridge` keystone (the `checkPreimage ⟷ checkSig` BIP-143 bridge)
these discharge the stateful family's omnibus branch for the canonical
fragment, replacing the `compileSafe_observational_correct_modulo_stateful_codegen`
axiom with a PROVEN consume theorem (sited in `Pipeline.lean`).

## The constant lowering

The whole method lowers to a CONSTANT op list: the preimage param is
consumed in place (depth-0 last-use ⇒ `bringToTop` emits `[]`), the implicit
`_opPushTxSig` swaps up, the synthetic key `G` is pushed, and the terminal
`assert`'s `OP_VERIFY` is elided (public method, body ends in assert):

    `[OP_CODESEPARATOR, .swap, .push G, OP_CHECKSIGVERIFY]`

Its success bit on the Stack side is exactly `authBackend.checkSig sig G`;
on the ANF side it is `Crypto.checkPreimage preimage`
(`StatefulBridge.gatedStatefulPrologue_isSome_eq`); the bridge axiom equates
the two under a valid BIP-143 context.

Side conditions `pre ≠ "_cp0"` / `pre ≠ "_opPushTxSig"` exclude the
name-collision corner where the lowering would shadow the auto-injected
binding or the implicit signature slot (the classifier checks both).

No `sorry`/`admit`, no new axioms. -/

namespace RunarVerification.Stack.AgreesStateful

open RunarVerification.ANF RunarVerification.Stack RunarVerification.Stack.Eval
open RunarVerification.ANF.Eval (Value)
open RunarVerification.ANF.Eval.Crypto

/-- The compiler's synthetic BIP-143 key: the secp256k1 generator point `G`
in compressed SEC form (33 bytes).  The byte literal now lives in
`StatefulBridge.stG` (the witness-existence axiom is stated over it); this
is a definitional alias, byte-identical to the local constant in
`Lower.lowerCheckPreimageOpsLive`. -/
def stG : ByteArray := StatefulBridge.stG

/-- The canonical stateful method's CONSTANT lowered op list. -/
def statefulPrologueOps : List StackOp :=
  [.opcode "OP_CODESEPARATOR", .swap, .push (.bytes stG), .opcode "OP_CHECKSIGVERIFY"]

/-! ## Part 1 — the lowering reduction (method ops = the constant list) -/

/-- `computeLastUses` of the gated prologue body: the preimage's only read is
binding 0, `_cp0`'s only read is binding 1. -/
theorem computeLastUses_statefulPrologue (pre : String) (hne1 : pre ≠ "_cp0") :
    Lower.computeLastUses (StatefulBridge.gatedStatefulPrologueBody pre)
      = [("_cp0", 1), (pre, 0)] := by
  simp [StatefulBridge.gatedStatefulPrologueBody, AgreesD2.statefulPrologueBody,
    Lower.computeLastUses, Lower.computeLastUses.go, Lower.collectRefs,
    Lower.lastUsesUpdate, hne1]

/-- The `check_preimage` binding lowers to the 4-op prologue: preimage consumed
in place (d0 last-use), `_opPushTxSig` swapped up (d1 consume), `G` pushed,
`OP_CHECKSIGVERIFY`. -/
theorem lowerValueP_checkPreimage_statefulPrologue
    (progMethods : List ANFMethod) (props : List ANFProperty)
    (budget : Nat) (localBindings : List String) (pre : String)
    (hne1 : pre ≠ "_cp0") (hne2 : pre ≠ "_opPushTxSig") :
    Lower.lowerValueP progMethods props budget 0 [("_cp0", 1), (pre, 0)]
        [] localBindings [] [pre, "_opPushTxSig"] "_cp0" (.checkPreimage pre)
      = (statefulPrologueOps, ["_cp0"], localBindings) := by
  unfold Lower.lowerValueP
  simp [Lower.lowerCheckPreimageOpsLive, Lower.loadRefLive, Lower.bringToTop,
    Lower.StackMap.depth?, Lower.StackMap.popN, Lower.isLastUse,
    Lower.lastUsesLookup, Lower.listContains, List.findIdx?, List.findIdx?.go,
    hne2, Ne.symm hne1, statefulPrologueOps, stG, StatefulBridge.stG]

/-- The auto-injected `assert _cp0` lowers to the bare `OP_VERIFY` (the
`_cp0` slot is consumed in place at d0 last-use). -/
theorem lowerValueP_assert_statefulPrologue
    (progMethods : List ANFMethod) (props : List ANFProperty)
    (budget : Nat) (localBindings : List String) (pre : String)
    (hne1 : pre ≠ "_cp0") :
    Lower.lowerValueP progMethods props budget 1 [("_cp0", 1), (pre, 0)]
        [] localBindings [] ["_cp0"] "_v" (.assert "_cp0")
      = ([.opcode "OP_VERIFY"], [], localBindings) := by
  unfold Lower.lowerValueP
  simp [Lower.loadRefLive, Lower.bringToTop, Lower.StackMap.depth?,
    Lower.StackMap.popN, Lower.isLastUse, Lower.lastUsesLookup,
    Lower.listContains, List.findIdx?, List.findIdx?.go, hne1, Ne.symm hne1]

/-- The gated prologue body lowers (program-aware, liveness-on) to the 4-op
prologue followed by the terminal `OP_VERIFY` (elided later by
`lowerMethod`'s terminal-assert pass). Stated on the FULL `(ops, sm)`
pair — the post-body stack map is EMPTY, which the depth-gated epilogue
in `lowerMethod` (TS `cleanupExcessStack` parity) now inspects. -/
theorem lowerBindingsP_statefulPrologue
    (progMethods : List ANFMethod) (props : List ANFProperty)
    (budget : Nat) (localBindings : List String) (pre : String)
    (hne1 : pre ≠ "_cp0") (hne2 : pre ≠ "_opPushTxSig") :
    (Lower.lowerBindingsP progMethods props budget 0 [("_cp0", 1), (pre, 0)]
        [] localBindings [] [pre, "_opPushTxSig"]
        (StatefulBridge.gatedStatefulPrologueBody pre))
      = (statefulPrologueOps ++ [.opcode "OP_VERIFY"], []) := by
  show (Lower.lowerBindingsP progMethods props budget 0 [("_cp0", 1), (pre, 0)]
        [] localBindings [] [pre, "_opPushTxSig"]
        [⟨"_cp0", .checkPreimage pre, none⟩, ⟨"_v", .assert "_cp0", none⟩])
      = (statefulPrologueOps ++ [.opcode "OP_VERIFY"], [])
  rw [Lower.lowerBindingsP.eq_def]
  simp only [lowerValueP_checkPreimage_statefulPrologue progMethods props budget
    localBindings pre hne1 hne2]
  rw [Lower.lowerBindingsP.eq_def]
  simp only [lowerValueP_assert_statefulPrologue progMethods props budget
    localBindings pre hne1]
  rw [Lower.lowerBindingsP.eq_def]
  simp

/-- **The method-level lowering reduction.**  A public single-param method
whose body is the gated stateful prologue lowers to the CONSTANT
`statefulPrologueOps`: the implicit `_opPushTxSig` slot is appended to the
initial stack map (`bindingsUseCheckPreimage = true`, `bindingsUseCodePart =
false`), the body lowers per `lowerBindingsP_statefulPrologue`, and the
terminal-assert elision drops the trailing `OP_VERIFY`. -/
theorem lowerMethod_ops_statefulPrologue
    (progMethods : List ANFMethod) (props : List ANFProperty)
    (anfM : ANFMethod) (pre : String) (ty : ANFType)
    (hParams : anfM.params = [ANFParam.mk pre ty])
    (hBody : anfM.body = StatefulBridge.gatedStatefulPrologueBody pre)
    (hPub : anfM.isPublic = true)
    (hne1 : pre ≠ "_cp0") (hne2 : pre ≠ "_opPushTxSig") :
    (Lower.lowerMethod progMethods props anfM).ops = statefulPrologueOps := by
  unfold Lower.lowerMethod
  rw [hParams, hBody, hPub]
  simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
    List.nil_append]
  have hUsesPre : Lower.bindingsUseCheckPreimage
      (StatefulBridge.gatedStatefulPrologueBody pre) = true := by
    simp [StatefulBridge.gatedStatefulPrologueBody, AgreesD2.statefulPrologueBody,
      Lower.bindingsUseCheckPreimage]
  have hUsesCode : Lower.bindingsUseCodePart
      (StatefulBridge.gatedStatefulPrologueBody pre) = false := by
    simp [StatefulBridge.gatedStatefulPrologueBody, AgreesD2.statefulPrologueBody,
      Lower.bindingsUseCodePart]
  have hConstInts : Lower.collectConstInts
      (StatefulBridge.gatedStatefulPrologueBody pre) = [] := by
    simp [StatefulBridge.gatedStatefulPrologueBody, AgreesD2.statefulPrologueBody,
      Lower.collectConstInts]
  have hEndsAssert : Lower.bodyEndsInAssert
      (StatefulBridge.gatedStatefulPrologueBody pre) = true := by
    simp [StatefulBridge.gatedStatefulPrologueBody, AgreesD2.statefulPrologueBody,
      Lower.bodyEndsInAssert]
  have hNoDeser : Lower.bindingsUseDeserializeState
      (StatefulBridge.gatedStatefulPrologueBody pre) = false := by
    simp [StatefulBridge.gatedStatefulPrologueBody, AgreesD2.statefulPrologueBody,
      Lower.bindingsUseDeserializeState]
  rw [hUsesPre, hUsesCode, computeLastUses_statefulPrologue pre hne1, hConstInts]
  simp only [List.cons_append, List.nil_append]
  rw [show ((StatefulBridge.gatedStatefulPrologueBody pre).map (·.name))
        = ["_cp0", "_v"] by
      simp [StatefulBridge.gatedStatefulPrologueBody, AgreesD2.statefulPrologueBody,
        ANFBinding.name]]
  simp only [Bool.false_eq_true, if_false, if_true]
  simp only [lowerBindingsP_statefulPrologue progMethods props
    Lower.defaultInlineBudget ["_cp0", "_v"] pre hne1 hne2]
  simp [hEndsAssert, hNoDeser, statefulPrologueOps]

/-! ## Part 2 — the runtime walk (Stack success bit = the checkSig verdict) -/

/-- Both-cases `OP_CHECKSIGVERIFY` reduction (the verify-mode peer of
`TxContext.runOpcode_CHECKSIG_…`, stated without the context plumbing): on a
`[pk, sig, …]`-topped stack the opcode either pops both and continues or
aborts with `.assertFailed`, branching on the AUTH backend's verdict. -/
theorem runOpcode_CHECKSIGVERIFY_reduce
    (stkSt : StackState) (pkB sigB : ByteArray) (rest : List Value)
    (hStk : stkSt.stack = .vBytes pkB :: .vBytes sigB :: rest) :
    Eval.runOpcode "OP_CHECKSIGVERIFY" stkSt
      = if authBackend.checkSig sigB pkB then .ok { stkSt with stack := rest }
        else .error .assertFailed := by
  simp only [Eval.runOpcode, Eval.popN, StackState.pop?, hStk,
    RunarVerification.ANF.Eval.Crypto.checkSig]
  rfl

/-- **The Stack half of the prologue's success bit.**  Running the constant
prologue ops on the method-entry stack (preimage value on top, the
`_opPushTxSig`-derived signature below) succeeds iff the AUTH backend
accepts the signature against the synthetic key `G`. -/
theorem runOps_statefulPrologueOps_isSome
    (stkSt : StackState) (preV sigV : ByteArray) (rest : List Value)
    (hStk : stkSt.stack = .vBytes preV :: .vBytes sigV :: rest) :
    (runOps statefulPrologueOps stkSt).toOption.isSome
      = authBackend.checkSig sigV stG := by
  show (runOps (.opcode "OP_CODESEPARATOR"
      :: .swap :: .push (.bytes stG) :: .opcode "OP_CHECKSIGVERIFY" :: [])
      stkSt).toOption.isSome = authBackend.checkSig sigV stG
  unfold runOps
  rw [stepNonIf_opcode]
  have hCS : runOpcode "OP_CODESEPARATOR" stkSt = .ok stkSt := rfl
  rw [hCS]
  show (runOps (.swap :: .push (.bytes stG) :: .opcode "OP_CHECKSIGVERIFY" :: [])
      stkSt).toOption.isSome = _
  unfold runOps
  rw [stepNonIf_swap]
  have hSwap : applySwap stkSt
      = .ok { stkSt with stack := .vBytes sigV :: .vBytes preV :: rest } := by
    unfold applySwap
    rw [hStk]
  rw [hSwap]
  show (runOps (.push (.bytes stG) :: .opcode "OP_CHECKSIGVERIFY" :: [])
      { stkSt with stack := .vBytes sigV :: .vBytes preV :: rest }).toOption.isSome = _
  unfold runOps
  rw [stepNonIf_push_bytes]
  show (runOps (.opcode "OP_CHECKSIGVERIFY" :: [])
      (StackState.push { stkSt with stack := .vBytes sigV :: .vBytes preV :: rest }
        (.vBytes stG))).toOption.isSome = _
  unfold runOps
  rw [stepNonIf_opcode]
  rw [runOpcode_CHECKSIGVERIFY_reduce
        (StackState.push { stkSt with stack := .vBytes sigV :: .vBytes preV :: rest }
          (.vBytes stG))
        stG sigV (.vBytes preV :: rest) rfl]
  rcases Bool.eq_false_or_eq_true (authBackend.checkSig sigV stG) with h | h <;>
    simp only [h] <;>
    simp [Except.toOption, Option.isSome, runOps]

/-! ## Part 3 — the parse round-trip (M4, fully concrete) -/

open RunarVerification.Script RunarVerification.Script.Parse in
/-- Leaf: `parseOps` over the list-level emit of the constant prologue. -/
theorem parseOps_emit_statefulPrologue :
    parseOps (emitOpsL statefulPrologueOps) = .ok statefulPrologueOps := by
  simp +decide [statefulPrologueOps, emitOpsL, emitStackOpL, encodePushValL,
    encodePushBytesL, encodePushDataL, stG, StatefulBridge.stG, opcodeByName?,
    ByteArray.toList_eq_data_toList, ByteArray.size]
  rfl

open RunarVerification.Script RunarVerification.Script.Parse in
/-- Bridge: the ByteArray-level emit agrees with the list-level emit. -/
theorem emitOps_toList_statefulPrologue :
    (Emit.emitOps statefulPrologueOps).toList = emitOpsL statefulPrologueOps := by
  simp +decide [Emit.emitOps, Emit.emitStackOp, Emit.encodePushVal,
    Emit.encodePushBytes, Emit.encodePushData, statefulPrologueOps, emitOpsL,
    emitStackOpL, encodePushValL, encodePushBytesL, encodePushDataL, stG,
    StatefulBridge.stG, opcodeByName?, ByteArray.size, ByteArray.toList_append,
    ByteArray.toList_mk_singleton, ByteArray.toList_eq_data_toList]

open RunarVerification.Script RunarVerification.Script.Parse in
/-- **M4 round-trip.**  The fast-emitted bytes of the constant prologue parse
back to EXACTLY the same op list (no normalization residue). -/
theorem parseScript_emitOpsFast_statefulPrologue :
    parseScript (Emit.emitOpsFast statefulPrologueOps) = .ok statefulPrologueOps := by
  rw [← Emit.EmitFastProof.emitOps_eq_emitOpsFast statefulPrologueOps]
  unfold parseScript
  rw [emitOps_toList_statefulPrologue]
  exact parseOps_emit_statefulPrologue

/-! ## Part 4 — the decidable fragment classifier -/

/-- Decides the canonical stateful consume fragment: one param `pre`, body
EXACTLY the gated stateful prologue on `pre`, with the two name-collision
exclusions. -/
def statefulConsumeShapeBool (m : ANFMethod) : Bool :=
  match m.params, m.body with
  | [p], [⟨bn1, .checkPreimage pre, none⟩, ⟨bn2, .assert ref, none⟩] =>
      (bn1 == "_cp0") && (bn2 == "_v") && (ref == "_cp0") &&
      (p.name == pre) && !(pre == "_cp0") && !(pre == "_opPushTxSig")
  | _, _ => false

/-! ## Part 5 — MANDATORY smokes (anti-vacuity) -/

/-- The canonical stateful method: `verify(pre) { _cp0 := check_preimage pre;
assert _cp0 }`. -/
def smokeMethod : ANFMethod :=
  { name := "verify"
    params := [ANFParam.mk "pre" .byteString]
    body := StatefulBridge.gatedStatefulPrologueBody "pre"
    isPublic := true }

/-- SMOKE — the classifier fires on the canonical method. -/
theorem smoke_classifier_fires : statefulConsumeShapeBool smokeMethod = true := by
  decide +kernel

/-- SMOKE — the method-level lowering reduction fires concretely. -/
theorem smoke_lowerMethod_ops :
    (Lower.lowerMethod [] [] smokeMethod).ops = statefulPrologueOps :=
  lowerMethod_ops_statefulPrologue [] [] smokeMethod "pre" .byteString
    rfl rfl rfl (by decide) (by decide)

end RunarVerification.Stack.AgreesStateful
