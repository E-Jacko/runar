import RunarVerification.Stack.StatefulBridge
import RunarVerification.Stack.Accept
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

/-- **The Stack half of the prologue's ACCEPTANCE bit (truthy-top semantics,
2026-06-11 success-bit repair).**  Running the constant prologue ops on the
method-entry stack is *accepted* (completes with a truthy top) iff the AUTH
backend accepts the signature against the synthetic key `G`: on success
`OP_CHECKSIGVERIFY` pops the sig + key and the (nonempty) preimage bytes are
left on top — truthy under `asBool?` — while on failure the run errors.
The nonemptiness premise `hPre` is discharged from
`buildPreimage`'s structure by the consume theorem (`Pipeline.lean`). -/
theorem runOps_statefulPrologueOps_scriptAccepts
    (stkSt : StackState) (preV sigV : ByteArray) (rest : List Value)
    (hStk : stkSt.stack = .vBytes preV :: .vBytes sigV :: rest)
    (hPre : 0 < preV.size) :
    scriptAccepts (runOps statefulPrologueOps stkSt)
      = authBackend.checkSig sigV stG := by
  show scriptAccepts (runOps (.opcode "OP_CODESEPARATOR"
      :: .swap :: .push (.bytes stG) :: .opcode "OP_CHECKSIGVERIFY" :: [])
      stkSt) = authBackend.checkSig sigV stG
  unfold runOps
  rw [stepNonIf_opcode]
  have hCS : runOpcode "OP_CODESEPARATOR" stkSt = .ok stkSt := rfl
  rw [hCS]
  show scriptAccepts (runOps (.swap :: .push (.bytes stG) :: .opcode "OP_CHECKSIGVERIFY" :: [])
      stkSt) = _
  unfold runOps
  rw [stepNonIf_swap]
  have hSwap : applySwap stkSt
      = .ok { stkSt with stack := .vBytes sigV :: .vBytes preV :: rest } := by
    unfold applySwap
    rw [hStk]
  rw [hSwap]
  show scriptAccepts (runOps (.push (.bytes stG) :: .opcode "OP_CHECKSIGVERIFY" :: [])
      { stkSt with stack := .vBytes sigV :: .vBytes preV :: rest }) = _
  unfold runOps
  rw [stepNonIf_push_bytes]
  show scriptAccepts (runOps (.opcode "OP_CHECKSIGVERIFY" :: [])
      (StackState.push { stkSt with stack := .vBytes sigV :: .vBytes preV :: rest }
        (.vBytes stG))) = _
  unfold runOps
  rw [stepNonIf_opcode]
  rw [runOpcode_CHECKSIGVERIFY_reduce
        (StackState.push { stkSt with stack := .vBytes sigV :: .vBytes preV :: rest }
          (.vBytes stG))
        stG sigV (.vBytes preV :: rest) rfl]
  rcases Bool.eq_false_or_eq_true (authBackend.checkSig sigV stG) with h | h <;>
    simp only [h] <;>
    simp [scriptAccepts, topTruthy, asBool?, runOps, hPre]

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


/-! # Part 6 — the WIDENED fragment: prologue + state-output epilogue

**2026-06-11 stateful widening.**  The discharged stateful fragment grows
from the bare gated prologue to the REAL stateful-method shape: entry
prologue **plus** the canonical one-mutable-prop state-output epilogue

    `_cp0 := check_preimage pre ;  _v := assert _cp0 ;
     _so0 := add_output sats [stateVal] ""`

— the honest composition of the two proven substrates
(`StatefulBridge.gatedStatefulPrologueBody` and
`AgreesD2.statefulEpilogueBody`).  The empty preimage ref on the
`add_output` matches the REAL compiler's auto-injection
(`04-anf-lower.ts:1311` emits `{ kind: 'add_output', …, preimage: '' }`);
the full auto-injection additionally deserializes state and asserts a
`hashOutputs` commitment, which remains future widening work.

## The `_codePart` finding

The epilogue's `add_output` trips `Lower.bindingsUseCodePart`, so
`lowerMethod` prepends BOTH implicit params: the initial stack map becomes
`[pre, stateVal, sats, "_opPushTxSig", "_codePart"]` (vs the prologue-only
fragment's `… ++ ["_opPushTxSig"]`).  The prologue's `_opPushTxSig`
consume therefore lowers to `.roll 3` instead of `.swap`, and the
mid-body `assert`'s `OP_VERIFY` is NOT elided (the body no longer ends in
assert — the trailing value is the output bytes, accepted under the
consensus truthy-top rule).

## The constant lowering and its parse image

The whole method lowers to the CONSTANT 68-op `statefulFullOps`
(prologue + `OP_VERIFY` + `lowerAddOutputOpsLive`'s serialization
including the flat-`OP_IF` varint encoder).  The DEPLOYED bytes parse
back to the structurally distinct `statefulFullParsedOps`: flat
`OP_IF`/`OP_ELSE`/`OP_ENDIF` reconstruct as nested `.ifOp`, `pickStruct`
comes back as `.pick`, and int pushes above `OP_16` come back as their
minimal-LE BYTE pushes — which is why the runtime walk needed the
consensus CScriptNum coercion (`Eval.asNum?`) on `OP_LESSTHAN`.

No `sorry`/`admit`, no new axioms. -/

open RunarVerification.ANF.Eval

/-- **The composed full-consume body**: gated prologue + one-state-value
epilogue (empty preimage ref on the `add_output`, as the real compiler
emits). -/
def statefulFullBody (pre sats stateVal : String) : List ANFBinding :=
  StatefulBridge.gatedStatefulPrologueBody pre
    ++ AgreesD2.statefulEpilogueBody sats stateVal ""

/-- The constant lowered epilogue ops (`lowerAddOutputOpsLive` on the
post-prologue map `[stateVal, sats, "_codePart"]`): copy `_codePart`,
append `OP_RETURN`, serialize the one bigint state value (8-byte LE),
varint-prefix the script, prepend the 8-byte LE amount. -/
def statefulFullEpilogueOps : List StackOp :=
  [.pickStruct 2, .push (.bytes (ByteArray.mk #[0x6a])), .opcode "OP_CAT",
   .swap, .push (.bigint 8), .opcode "OP_NUM2BIN", .opcode "OP_CAT",
   .opcode "OP_SIZE"]
  ++ Lower.varintEncodingOps
  ++ [.swap, .opcode "OP_CAT", .swap, .push (.bigint 8), .opcode "OP_NUM2BIN",
      .swap, .opcode "OP_CAT"]

/-- The composed method's CONSTANT lowered op list. -/
def statefulFullOps : List StackOp :=
  [.opcode "OP_CODESEPARATOR", .roll 3, .push (.bytes stG),
   .opcode "OP_CHECKSIGVERIFY", .opcode "OP_VERIFY"]
  ++ statefulFullEpilogueOps

/-- The varint encoder's PARSE image: the flat `OP_IF` chain reconstructs
as nested `.ifOp`, and the 253 / 65536 / 2^32 literals come back as their
minimal-LE byte pushes. -/
def varintParsedTail : List StackOp :=
  [.dup, .push (.bytes (ByteArray.mk #[0xfd, 0x00])), .opcode "OP_LESSTHAN",
   .ifOp [.push (.bigint 2), .opcode "OP_NUM2BIN", .push (.bigint 1),
          .opcode "OP_SPLIT", .drop]
     (some [.dup, .push (.bytes (ByteArray.mk #[0x00, 0x00, 0x01])), .opcode "OP_LESSTHAN",
            .ifOp [.push (.bigint 3), .opcode "OP_NUM2BIN", .push (.bigint 2),
                   .opcode "OP_SPLIT", .drop, .push (.bytes (ByteArray.mk #[0xfd])),
                   .swap, .opcode "OP_CAT"]
              (some [.dup, .push (.bytes (ByteArray.mk #[0x00, 0x00, 0x00, 0x00, 0x01])),
                     .opcode "OP_LESSTHAN",
                     .ifOp [.push (.bigint 5), .opcode "OP_NUM2BIN", .push (.bigint 4),
                            .opcode "OP_SPLIT", .drop, .push (.bytes (ByteArray.mk #[0xfe])),
                            .swap, .opcode "OP_CAT"]
                       (some [.push (.bigint 9), .opcode "OP_NUM2BIN", .push (.bigint 8),
                              .opcode "OP_SPLIT", .drop, .push (.bytes (ByteArray.mk #[0xff])),
                              .swap, .opcode "OP_CAT"])])])]

/-- The epilogue's parse image (`pickStruct 2` comes back as `.pick 2`). -/
def statefulFullEpilogueParsedOps : List StackOp :=
  [.pick 2, .push (.bytes (ByteArray.mk #[0x6a])), .opcode "OP_CAT",
   .swap, .push (.bigint 8), .opcode "OP_NUM2BIN", .opcode "OP_CAT",
   .opcode "OP_SIZE"]
  ++ varintParsedTail
  ++ [.swap, .opcode "OP_CAT", .swap, .push (.bigint 8), .opcode "OP_NUM2BIN",
      .swap, .opcode "OP_CAT"]

/-- The composed method's parse image — what the DEPLOYED bytes run. -/
def statefulFullParsedOps : List StackOp :=
  [.opcode "OP_CODESEPARATOR", .roll 3, .push (.bytes stG),
   .opcode "OP_CHECKSIGVERIFY", .opcode "OP_VERIFY"]
  ++ statefulFullEpilogueParsedOps

/-! ## Part 6.1 — the lowering reduction (staged) -/

theorem computeLastUses_statefulFull (pre sats stateVal : String)
    (hPC : pre ≠ "_cp0") (hPE : pre ≠ "")
    (hSE : sats ≠ "") (hVE : stateVal ≠ "")
    (hSC : sats ≠ "_cp0") (hVC : stateVal ≠ "_cp0")
    (hSP : sats ≠ pre) (hVP : stateVal ≠ pre) (hSV : sats ≠ stateVal) :
    Lower.computeLastUses (statefulFullBody pre sats stateVal)
      = [("", 2), (stateVal, 2), (sats, 2), ("_cp0", 1), (pre, 0)] := by
  simp [statefulFullBody, StatefulBridge.gatedStatefulPrologueBody,
    AgreesD2.statefulPrologueBody, AgreesD2.statefulEpilogueBody,
    Lower.computeLastUses, Lower.computeLastUses.go, Lower.collectRefs,
    Lower.lastUsesUpdate, hPC, hPE, hSE, hVE, hSC, hVC, hSP, hVP, hSV,
    Ne.symm hPC, Ne.symm hPE, Ne.symm hSE, Ne.symm hVE, Ne.symm hSC,
    Ne.symm hVC, Ne.symm hSP, Ne.symm hVP, Ne.symm hSV]

/-- The `check_preimage` binding on the FULL initial map (both implicit
params): preimage consumed in place (d0 last-use), `_opPushTxSig` rolled
up from depth 3 (the `_codePart` finding), `G` pushed, CHECKSIGVERIFY. -/
theorem lowerValueP_checkPreimage_statefulFull
    (progMethods : List ANFMethod) (props : List ANFProperty)
    (budget : Nat) (localBindings : List String) (pre sats stateVal : String)
    (hPE : pre ≠ "") (hPS : pre ≠ sats) (hPV : pre ≠ stateVal)
    (hPC : pre ≠ "_cp0")
    (hPO : pre ≠ "_opPushTxSig") (hSO : sats ≠ "_opPushTxSig")
    (hVO : stateVal ≠ "_opPushTxSig") :
    Lower.lowerValueP progMethods props budget 0
        [("", 2), (stateVal, 2), (sats, 2), ("_cp0", 1), (pre, 0)]
        [] localBindings [] [pre, stateVal, sats, "_opPushTxSig", "_codePart"]
        "_cp0" (.checkPreimage pre)
      = ([.opcode "OP_CODESEPARATOR", .roll 3, .push (.bytes stG),
          .opcode "OP_CHECKSIGVERIFY"],
         ["_cp0", stateVal, sats, "_codePart"], localBindings) := by
  unfold Lower.lowerValueP
  simp [Lower.lowerCheckPreimageOpsLive, Lower.loadRefLive, Lower.bringToTop,
    Lower.StackMap.depth?, Lower.StackMap.popN, Lower.StackMap.push,
    Lower.StackMap.removeAtDepth, Lower.isLastUse,
    Lower.lastUsesLookup, Lower.listContains, List.findIdx?, List.findIdx?.go,
    stG, RunarVerification.Stack.StatefulBridge.stG,
    hPE, hPS, hPV, hPC, hPO, hSO, hVO,
    Ne.symm hPE, Ne.symm hPS, Ne.symm hPV, Ne.symm hPC, Ne.symm hPO,
    Ne.symm hSO, Ne.symm hVO]

/-- The mid-body `assert _cp0` lowers to a SURVIVING `OP_VERIFY` (no
terminal elision — the body continues into the epilogue). -/
theorem lowerValueP_assert_statefulFull
    (progMethods : List ANFMethod) (props : List ANFProperty)
    (budget : Nat) (localBindings : List String) (pre sats stateVal : String)
    (hPC : pre ≠ "_cp0") (hSC : sats ≠ "_cp0") (hVC : stateVal ≠ "_cp0") :
    Lower.lowerValueP progMethods props budget 1
        [("", 2), (stateVal, 2), (sats, 2), ("_cp0", 1), (pre, 0)]
        [] localBindings [] ["_cp0", stateVal, sats, "_codePart"]
        "_v" (.assert "_cp0")
      = ([.opcode "OP_VERIFY"], [stateVal, sats, "_codePart"], localBindings) := by
  unfold Lower.lowerValueP
  simp [Lower.loadRefLive, Lower.bringToTop, Lower.StackMap.depth?,
    Lower.StackMap.popN, Lower.isLastUse, Lower.lastUsesLookup,
    Lower.listContains, List.findIdx?, List.findIdx?.go,
    hPC, hSC, hVC, Ne.symm hPC, Ne.symm hSC, Ne.symm hVC]

/-- The `add_output` epilogue lowers to the constant
`statefulFullEpilogueOps` (one mutable bigint prop ⇒ one 8-byte
`OP_NUM2BIN` serialization step). -/
theorem lowerValueP_addOutput_statefulFull
    (progMethods : List ANFMethod) (props : List ANFProperty)
    (budget : Nat) (localBindings : List String) (pre sats stateVal pn : String)
    (hProps : props.filter (fun pp => !pp.readonly)
        = [{ name := pn, type := .bigint, readonly := false }])
    (hSE : sats ≠ "") (hVE : stateVal ≠ "") (hSV : sats ≠ stateVal)
    (hVCp : stateVal ≠ "_codePart") (hSCp : sats ≠ "_codePart")
    (hVA : stateVal ≠ "_acc") (hSA : sats ≠ "_acc") :
    Lower.lowerValueP progMethods props budget 2
        [("", 2), (stateVal, 2), (sats, 2), ("_cp0", 1), (pre, 0)]
        [] localBindings [] [stateVal, sats, "_codePart"]
        "_so0" (.addOutput sats [stateVal] "")
      = (statefulFullEpilogueOps, ["_so0", "_codePart"], localBindings) := by
  unfold Lower.lowerValueP
  simp [Lower.lowerAddOutputOpsLive, Lower.addOutputStateValuesLive,
    Lower.loadRefOperand, Lower.operandConsume, Lower.bringToTop,
    Lower.StackMap.depth?, Lower.StackMap.popN, Lower.StackMap.push,
    Lower.StackMap.removeAtDepth, Lower.isLastUse, Lower.lastUsesLookup,
    Lower.listContains, List.findIdx?, List.findIdx?.go,
    hProps, Lower.propTypeIsNumeric, Lower.propTypeFixedSize,
    statefulFullEpilogueOps, Lower.varintEncodingOps,
    hSE, hVE, hSV, hVCp, hSCp, hVA, hSA,
    Ne.symm hSE, Ne.symm hVE, Ne.symm hSV, Ne.symm hVCp, Ne.symm hSCp,
    Ne.symm hVA, Ne.symm hSA]

theorem lowerBindingsP_statefulFull
    (progMethods : List ANFMethod) (props : List ANFProperty)
    (budget : Nat) (localBindings : List String) (pre sats stateVal pn : String)
    (hProps : props.filter (fun pp => !pp.readonly)
        = [{ name := pn, type := .bigint, readonly := false }])
    (hPE : pre ≠ "") (hPS : pre ≠ sats) (hPV : pre ≠ stateVal)
    (hPC : pre ≠ "_cp0") (hPO : pre ≠ "_opPushTxSig")
    (hSE : sats ≠ "") (hVE : stateVal ≠ "") (hSV : sats ≠ stateVal)
    (hSC : sats ≠ "_cp0") (hVC : stateVal ≠ "_cp0")
    (hSO : sats ≠ "_opPushTxSig") (hVO : stateVal ≠ "_opPushTxSig")
    (hVCp : stateVal ≠ "_codePart") (hSCp : sats ≠ "_codePart")
    (hVA : stateVal ≠ "_acc") (hSA : sats ≠ "_acc") :
    Lower.lowerBindingsP progMethods props budget 0
        [("", 2), (stateVal, 2), (sats, 2), ("_cp0", 1), (pre, 0)]
        [] localBindings [] [pre, stateVal, sats, "_opPushTxSig", "_codePart"]
        (statefulFullBody pre sats stateVal)
      = (statefulFullOps, ["_so0", "_codePart"]) := by
  show Lower.lowerBindingsP progMethods props budget 0
        [("", 2), (stateVal, 2), (sats, 2), ("_cp0", 1), (pre, 0)]
        [] localBindings [] [pre, stateVal, sats, "_opPushTxSig", "_codePart"]
        [⟨"_cp0", .checkPreimage pre, none⟩, ⟨"_v", .assert "_cp0", none⟩,
         ⟨"_so0", .addOutput sats [stateVal] "", none⟩]
      = (statefulFullOps, ["_so0", "_codePart"])
  rw [Lower.lowerBindingsP.eq_def]
  simp only [lowerValueP_checkPreimage_statefulFull progMethods props budget
    localBindings pre sats stateVal hPE hPS hPV hPC hPO hSO hVO]
  rw [Lower.lowerBindingsP.eq_def]
  simp only [lowerValueP_assert_statefulFull progMethods props budget
    localBindings pre sats stateVal hPC hSC hVC]
  rw [Lower.lowerBindingsP.eq_def]
  simp only [lowerValueP_addOutput_statefulFull progMethods props budget
    localBindings pre sats stateVal pn hProps hSE hVE hSV hVCp hSCp hVA hSA]
  rw [Lower.lowerBindingsP.eq_def]
  simp [statefulFullOps, statefulFullEpilogueOps]

/-- **The method-level lowering reduction (widened fragment).**  A public
3-param method whose body is the composed prologue+epilogue lowers to the
CONSTANT `statefulFullOps`: BOTH implicit params are appended to the
initial stack map (`bindingsUseCodePart = true` — the `_codePart`
finding), no terminal elision fires (`bodyEndsInAssert = false`), and no
NIP cleanup runs. -/
theorem lowerMethod_ops_statefulFull
    (progMethods : List ANFMethod) (props : List ANFProperty)
    (anfM : ANFMethod) (pre sats stateVal pn : String) (tyS tyV tyP : ANFType)
    (hParams : anfM.params
        = [ANFParam.mk sats tyS, ANFParam.mk stateVal tyV, ANFParam.mk pre tyP])
    (hBody : anfM.body = statefulFullBody pre sats stateVal)
    (hPub : anfM.isPublic = true)
    (hProps : props.filter (fun pp => !pp.readonly)
        = [{ name := pn, type := .bigint, readonly := false }])
    (hPE : pre ≠ "") (hPS : pre ≠ sats) (hPV : pre ≠ stateVal)
    (hPC : pre ≠ "_cp0") (hPO : pre ≠ "_opPushTxSig")
    (hSE : sats ≠ "") (hVE : stateVal ≠ "") (hSV : sats ≠ stateVal)
    (hSC : sats ≠ "_cp0") (hVC : stateVal ≠ "_cp0")
    (hSO : sats ≠ "_opPushTxSig") (hVO : stateVal ≠ "_opPushTxSig")
    (hVCp : stateVal ≠ "_codePart") (hSCp : sats ≠ "_codePart")
    (hVA : stateVal ≠ "_acc") (hSA : sats ≠ "_acc") :
    (Lower.lowerMethod progMethods props anfM).ops = statefulFullOps := by
  unfold Lower.lowerMethod
  rw [hParams, hBody, hPub]
  simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append]
  have hUsesPre : Lower.bindingsUseCheckPreimage
      (statefulFullBody pre sats stateVal) = true := by
    simp [statefulFullBody, StatefulBridge.gatedStatefulPrologueBody,
      AgreesD2.statefulPrologueBody, AgreesD2.statefulEpilogueBody,
      Lower.bindingsUseCheckPreimage]
  have hUsesCode : Lower.bindingsUseCodePart
      (statefulFullBody pre sats stateVal) = true := by
    simp [statefulFullBody, StatefulBridge.gatedStatefulPrologueBody,
      AgreesD2.statefulPrologueBody, AgreesD2.statefulEpilogueBody,
      Lower.bindingsUseCodePart]
  have hConstInts : Lower.collectConstInts
      (statefulFullBody pre sats stateVal) = [] := by
    simp [statefulFullBody, StatefulBridge.gatedStatefulPrologueBody,
      AgreesD2.statefulPrologueBody, AgreesD2.statefulEpilogueBody,
      Lower.collectConstInts]
  have hEndsAssert : Lower.bodyEndsInAssert
      (statefulFullBody pre sats stateVal) = false := by
    simp [statefulFullBody, StatefulBridge.gatedStatefulPrologueBody,
      AgreesD2.statefulPrologueBody, AgreesD2.statefulEpilogueBody,
      Lower.bodyEndsInAssert]
  rw [hUsesPre, hUsesCode,
    computeLastUses_statefulFull pre sats stateVal hPC hPE hSE hVE hSC hVC
      (Ne.symm hPS) (Ne.symm hPV) hSV, hConstInts]
  rw [show ((statefulFullBody pre sats stateVal).map (·.name))
        = ["_cp0", "_v", "_so0"] by
      simp [statefulFullBody, StatefulBridge.gatedStatefulPrologueBody,
        AgreesD2.statefulPrologueBody, AgreesD2.statefulEpilogueBody,
        ANFBinding.name]]
  simp only [if_true]
  simp only [lowerBindingsP_statefulFull progMethods props
    Lower.defaultInlineBudget ["_cp0", "_v", "_so0"] pre sats stateVal pn hProps
    hPE hPS hPV hPC hPO hSE hVE hSV hSC hVC hSO hVO hVCp hSCp hVA hSA]
  simp [hEndsAssert, statefulFullOps, statefulFullEpilogueOps,
    Lower.varintEncodingOps]

/-! ## Part 6.2 — the ANF composed reduction -/

theorem resolveRef_addBinding_ne (s : State) (n r : String) (v : Value)
    (h : r ≠ n) :
    (s.addBinding n v).resolveRef r = s.resolveRef r := by
  simp [State.addBinding, State.resolveRef, State.lookupBinding,
    State.lookupParam, State.lookupProp, List.find?, h, Ne.symm h]

/-- **The composed ANF success bit** = the preimage verdict: the prologue
gates (the `assert _cp0` aborts on a bad preimage), and the epilogue's
`add_output` never aborts (its value is the opaque output handle; the
output record is appended per `AgreesD2.evalValueP_statefulEpilogue_value`). -/
theorem evalBindingsP_statefulFull_isSome_eq
    (methods : List ANFMethod) (s : State) (pre sats stateVal : String)
    (b : ByteArray) (satsV : Int) (svV : Value)
    (hPre : s.resolveRef pre = some (.vBytes b))
    (hSats : s.resolveRef sats = some (.vBigint satsV))
    (hSv : s.resolveRef stateVal = some svV)
    (hS1 : sats ≠ "_cp0") (hS2 : sats ≠ "_v")
    (hV1 : stateVal ≠ "_cp0") (hV2 : stateVal ≠ "_v") :
    (evalBindingsP methods s (statefulFullBody pre sats stateVal)).toOption.isSome
      = Crypto.checkPreimage b := by
  unfold statefulFullBody StatefulBridge.gatedStatefulPrologueBody
    AgreesD2.statefulPrologueBody AgreesD2.statefulEpilogueBody
  show (evalBindingsP methods s
      [⟨"_cp0", .checkPreimage pre, none⟩, ⟨"_v", .assert "_cp0", none⟩,
       ⟨"_so0", .addOutput sats [stateVal] "", none⟩]).toOption.isSome
    = Crypto.checkPreimage b
  have hLookup :
      (s.addBinding "_cp0" (.vBool (Crypto.checkPreimage b))).resolveRef "_cp0"
        = some (.vBool (Crypto.checkPreimage b)) := by
    simp [State.resolveRef, State.lookupBinding, State.addBinding]
  rw [evalBindingsP.eq_def]
  simp only [evalValueP, lookupRef, hPre, Value.asBytes?, bind, Except.bind]
  rw [evalBindingsP.eq_def]
  simp only [evalValueP, lookupRef, hLookup, bind, Except.bind]
  rcases Bool.eq_false_or_eq_true (Crypto.checkPreimage b) with h | h
  case _ =>
    -- verdict TRUE: assert passes, epilogue appends the output.
    simp only [h]
    have hSats2 : ((s.addBinding "_cp0" (Value.vBool true)).addBinding "_v"
        (Value.vBool true)).resolveRef sats = some (.vBigint satsV) := by
      rw [resolveRef_addBinding_ne _ _ _ _ hS2,
        resolveRef_addBinding_ne _ _ _ _ hS1]
      exact hSats
    have hSv2 : ((s.addBinding "_cp0" (Value.vBool true)).addBinding "_v"
        (Value.vBool true)).resolveRef stateVal = some svV := by
      rw [resolveRef_addBinding_ne _ _ _ _ hV2,
        resolveRef_addBinding_ne _ _ _ _ hV1]
      exact hSv
    show (evalBindingsP methods
        ((s.addBinding "_cp0" (Value.vBool true)).addBinding "_v" (Value.vBool true))
        [ANFBinding.mk "_so0" (ANFValue.addOutput sats [stateVal] "") none]).toOption.isSome
      = true
    rw [evalBindingsP.eq_def]
    simp only [AgreesD2.evalValueP_statefulEpilogue_value methods
      ((s.addBinding "_cp0" (Value.vBool true)).addBinding "_v" (Value.vBool true))
      sats stateVal "" satsV svV hSats2 hSv2, bind, Except.bind]
    simp [evalBindingsP, Except.toOption, Option.isSome]
  case _ =>
    -- verdict FALSE: the assert aborts.
    simp only [h]
    simp [Except.toOption, Option.isSome]

/-! ## Part 6.3 — the runtime acceptance walk -/

theorem decodeMinimalLE_fd00 :
    decodeMinimalLE (ByteArray.mk #[0xfd, 0x00]) = 253 := by
  with_unfolding_all rfl

theorem stepNonIf_pick2_cons3
    (s : StackState) (v0 v1 v2 : Value) (rest : List Value)
    (hStk : s.stack = v0 :: v1 :: v2 :: rest) :
    Eval.stepNonIf (.pick 2) s = .ok { s with stack := v2 :: v0 :: v1 :: v2 :: rest } := by
  show Eval.applyPick s 2 = _
  unfold Eval.applyPick
  simp [hStk, StackState.push]

theorem stepNonIf_roll3_cons5
    (s : StackState) (v0 v1 v2 v3 v4 : Value) (rest : List Value)
    (hStk : s.stack = v0 :: v1 :: v2 :: v3 :: v4 :: rest) :
    Eval.stepNonIf (.roll 3) s = .ok { s with stack := v3 :: v0 :: v1 :: v2 :: v4 :: rest } := by
  show Eval.applyRoll s 3 = _
  unfold Eval.applyRoll
  simp [hStk, List.eraseIdx]

/-- `OP_LESSTHAN` with a byte-encoded top operand — the consensus
CScriptNum coercion (`Eval.asNum?`) in action: the parsed `push 253`
re-enters as `vBytes [0xfd, 0x00]` and decodes. -/
theorem runOpcode_LESSTHAN_intBytes
    (s : StackState) (a : Int) (bB : ByteArray) (rest : List Value)
    (hStk : s.stack = .vBytes bB :: .vBigint a :: rest)
    (hSz : bB.size ≤ 4) :
    Eval.runOpcode "OP_LESSTHAN" s
      = .ok ({ s with stack := rest }.push (.vBool (decide (a < decodeMinimalLE bB)))) := by
  rw [Sim.runOpcode_LESSTHAN_def]
  unfold Eval.liftIntBinNum
  simp only [Eval.popN, StackState.pop?, hStk]
  simp [Eval.asNum?, Eval.asInt?, hSz]

/-! ### Byte-coercion fidelity smokes for the widened comparison / select ops

The 2026-06-13 extension wires the consensus `asNum?` coercion into the
comparison and numeric-select opcodes (`OP_GREATERTHAN`,
`OP_LESSTHANOREQUAL`, `OP_GREATERTHANOREQUAL`, `OP_NUMEQUAL`,
`OP_NUMNOTEQUAL`, `OP_MIN`, `OP_MAX`) that deployed-bytes machinery feeds
byte-encoded literals to (the stateful varint encoder, num2bin's
size-dispatch, clamp/pow).  These concrete smokes feed a parsed
`vBytes` numeric push (the wire encoding `[0xfd, 0x00]` = 253, exactly
what `push 253` parses back to) to each newly-widened opcode and confirm
it now evaluates to the CONSENSUS result instead of type-erroring.  The
top operand is the byte vector; the second-from-top is a typed bigint
(`100`), mirroring the real stack shape (`OP_DUP; push 253; OP_…`). -/

/-- A parsed 2-byte CScriptNum push of 253 (the `push 253` wire form). -/
def bytes253 : ByteArray := ByteArray.mk #[0xfd, 0x00]

/-- The load-bearing consensus fact, checked by the kernel evaluator: the
parsed `push 253` byte vector decodes (via the `asNum?` ≤4-byte path) to the
integer 253, and is ≤ 4 bytes so the coercion applies.  Every byte-coercion
smoke below rides on this. -/
theorem bytes253_decodes : decodeMinimalLE bytes253 = 253 ∧ bytes253.size ≤ 4 := by
  native_decide

/-- Generic reduction: a `liftIntBinNum`-wired opcode given a bigint
second-from-top and a ≤4-byte vector top decodes the top via `asNum?` and
applies `f`.  Mirrors `runOpcode_LESSTHAN_intBytes` but parameterised over the
opcode's def-lemma equation `hDef`. -/
private theorem liftIntBinNum_intBytes_reduce
    (s : StackState) (op : String) (f : Int → Int → Value)
    (a : Int) (bB : ByteArray) (rest : List Value)
    (hDef : Eval.runOpcode op s = Eval.liftIntBinNum s f)
    (hStk : s.stack = .vBytes bB :: .vBigint a :: rest)
    (hSz : bB.size ≤ 4) :
    Eval.runOpcode op s
      = .ok ({ s with stack := rest }.push (f a (decodeMinimalLE bB))) := by
  rw [hDef]
  unfold Eval.liftIntBinNum
  simp only [Eval.popN, StackState.pop?, hStk]
  simp [Eval.asNum?, Eval.asInt?, hSz]

/-- SMOKE — `OP_GREATERTHAN` coerces a byte-literal top operand: `100 > 253`
is `false`, matching consensus (the bare `asInt?` would type-error). -/
theorem smoke_GREATERTHAN_byte_coerces (s : StackState) (rest : List Value)
    (hStk : s.stack = .vBytes bytes253 :: .vBigint 100 :: rest) :
    Eval.runOpcode "OP_GREATERTHAN" s
      = .ok ({ s with stack := rest }.push (.vBool false)) := by
  have := liftIntBinNum_intBytes_reduce s "OP_GREATERTHAN"
    (fun a b => .vBool (decide (a > b))) 100 bytes253 rest
    (Sim.runOpcode_GREATERTHAN_def s) hStk bytes253_decodes.2
  rw [this]; simp [bytes253_decodes.1]

/-- SMOKE — `OP_LESSTHANOREQUAL` coerces a byte-literal top: `100 ≤ 253`. -/
theorem smoke_LESSTHANOREQUAL_byte_coerces (s : StackState) (rest : List Value)
    (hStk : s.stack = .vBytes bytes253 :: .vBigint 100 :: rest) :
    Eval.runOpcode "OP_LESSTHANOREQUAL" s
      = .ok ({ s with stack := rest }.push (.vBool true)) := by
  have := liftIntBinNum_intBytes_reduce s "OP_LESSTHANOREQUAL"
    (fun a b => .vBool (decide (a ≤ b))) 100 bytes253 rest
    (Sim.runOpcode_LESSTHANOREQUAL_def s) hStk bytes253_decodes.2
  rw [this]; simp [bytes253_decodes.1]

/-- SMOKE — `OP_GREATERTHANOREQUAL` coerces a byte-literal top: `100 ≥ 253`. -/
theorem smoke_GREATERTHANOREQUAL_byte_coerces (s : StackState) (rest : List Value)
    (hStk : s.stack = .vBytes bytes253 :: .vBigint 100 :: rest) :
    Eval.runOpcode "OP_GREATERTHANOREQUAL" s
      = .ok ({ s with stack := rest }.push (.vBool false)) := by
  have := liftIntBinNum_intBytes_reduce s "OP_GREATERTHANOREQUAL"
    (fun a b => .vBool (decide (a ≥ b))) 100 bytes253 rest
    (Sim.runOpcode_GREATERTHANOREQUAL_def s) hStk bytes253_decodes.2
  rw [this]; simp [bytes253_decodes.1]

/-- SMOKE — `OP_NUMEQUAL` coerces a byte-literal top: `253 = 253`.  This is
the num2bin size-dispatch shape (`OP_DUP; push 254/77; OP_NUMEQUAL`). -/
theorem smoke_NUMEQUAL_byte_coerces (s : StackState) (rest : List Value)
    (hStk : s.stack = .vBytes bytes253 :: .vBigint 253 :: rest) :
    Eval.runOpcode "OP_NUMEQUAL" s
      = .ok ({ s with stack := rest }.push (.vBool true)) := by
  have := liftIntBinNum_intBytes_reduce s "OP_NUMEQUAL"
    (fun a b => .vBool (decide (a = b))) 253 bytes253 rest
    (Sim.runOpcode_NUMEQUAL_def s) hStk bytes253_decodes.2
  rw [this]; simp [bytes253_decodes.1]

/-- SMOKE — `OP_NUMNOTEQUAL` coerces a byte-literal top: `100 ≠ 253`. -/
theorem smoke_NUMNOTEQUAL_byte_coerces (s : StackState) (rest : List Value)
    (hStk : s.stack = .vBytes bytes253 :: .vBigint 100 :: rest) :
    Eval.runOpcode "OP_NUMNOTEQUAL" s
      = .ok ({ s with stack := rest }.push (.vBool true)) := by
  have := liftIntBinNum_intBytes_reduce s "OP_NUMNOTEQUAL"
    (fun a b => .vBool (decide (a ≠ b))) 100 bytes253 rest
    (Sim.runOpcode_NUMNOTEQUAL_def s) hStk bytes253_decodes.2
  rw [this]; simp [bytes253_decodes.1]

/-- SMOKE — `OP_MIN` coerces a byte-literal top: `min 100 253 = 100`.
This is the clamp machinery shape (`OP_MAX … OP_MIN`). -/
theorem smoke_MIN_byte_coerces (s : StackState) (rest : List Value)
    (hStk : s.stack = .vBytes bytes253 :: .vBigint 100 :: rest) :
    Eval.runOpcode "OP_MIN" s
      = .ok ({ s with stack := rest }.push (.vBigint 100)) := by
  have := liftIntBinNum_intBytes_reduce s "OP_MIN"
    (fun a b => .vBigint (min a b)) 100 bytes253 rest
    (Sim.runOpcode_MIN_def s) hStk bytes253_decodes.2
  rw [this]; simp only [bytes253_decodes.1, show min (100 : Int) 253 = 100 from by decide]

/-- SMOKE — `OP_MAX` coerces a byte-literal top: `max 100 253 = 253`. -/
theorem smoke_MAX_byte_coerces (s : StackState) (rest : List Value)
    (hStk : s.stack = .vBytes bytes253 :: .vBigint 100 :: rest) :
    Eval.runOpcode "OP_MAX" s
      = .ok ({ s with stack := rest }.push (.vBigint 253)) := by
  have := liftIntBinNum_intBytes_reduce s "OP_MAX"
    (fun a b => .vBigint (max a b)) 100 bytes253 rest
    (Sim.runOpcode_MAX_def s) hStk bytes253_decodes.2
  rw [this]; simp only [bytes253_decodes.1, show max (100 : Int) 253 = 253 from by decide]

/-- Abbreviation for the accumulated state-script bytes:
`codePart ++ OP_RETURN ++ stateVal(8-byte LE)`. -/
def epiAcc (cpV sv8 : ByteArray) : ByteArray :=
  cpV ++ ByteArray.mk #[0x6a] ++ sv8

/-- **The epilogue suffix walk**: from the post-`OP_VERIFY` stack the
parsed epilogue ops COMPLETE (taking the 1-byte-varint `ifOp` branch
under the `cpV.size + 9 < 253` premise), leaving the serialized output
bytes on top. -/
theorem runOps_statefulFullEpilogueParsed
    (s : StackState) (cpV sv8 var2 sats8 : ByteArray) (svV satsV : Int)
    (rest : List Value)
    (hStk : s.stack = .vBigint svV :: .vBigint satsV :: .vBytes cpV :: rest)
    (hSv8 : num2binEncode? svV 8 = some sv8)
    (hSv8sz : sv8.size = 8)
    (hLt : cpV.size + 9 < 253)
    (hVar : num2binEncode? ((epiAcc cpV sv8).size : Int) 2 = some var2)
    (hVar2 : 1 ≤ var2.size)
    (hSats8 : num2binEncode? satsV 8 = some sats8) :
    runOps statefulFullEpilogueParsedOps s
      = .ok
      { s with stack := Value.vBytes (sats8 ++ (var2.extract 0 1 ++ epiAcc cpV sv8)) :: Value.vBytes cpV :: rest } := by
  have h6a : (ByteArray.mk #[0x6a]).size = 1 := rfl
  have hAccSzLt : (((epiAcc cpV sv8).size : Int) < 253) := by
    have hsz : (epiAcc cpV sv8).size = cpV.size + 9 := by
      simp [epiAcc, ByteArray.size_append, h6a, hSv8sz]
    rw [hsz]
    omega
  -- step 1: pick 2
  show runOps (.pick 2 :: _) s = _
  unfold runOps
  rw [stepNonIf_pick2_cons3 s _ _ _ rest hStk]
  -- step 2: push 0x6a
  show runOps (.push (.bytes (ByteArray.mk #[0x6a])) :: _)
      { s with stack := .vBytes cpV :: .vBigint svV :: .vBigint satsV
          :: .vBytes cpV :: rest } = _
  unfold runOps
  rw [stepNonIf_push_bytes]
  -- step 3: OP_CAT (cpV ++ 6a)
  show runOps (.opcode "OP_CAT" :: _)
      { s with stack := .vBytes (ByteArray.mk #[0x6a]) :: .vBytes cpV
          :: .vBigint svV :: .vBigint satsV :: .vBytes cpV :: rest } = _
  unfold runOps
  rw [stepNonIf_opcode]
  rw [Sim.runOpcode_CAT_bytesBytes _ cpV (ByteArray.mk #[0x6a])
    (.vBigint svV :: .vBigint satsV :: .vBytes cpV :: rest) rfl]
  -- step 4: swap (bring stateVal up)
  show runOps (.swap :: _)
      { s with stack := .vBytes (cpV ++ ByteArray.mk #[0x6a]) :: .vBigint svV
          :: .vBigint satsV :: .vBytes cpV :: rest } = _
  unfold runOps
  rw [stepNonIf_swap]
  have hSw1 : Eval.applySwap
      { s with stack := .vBytes (cpV ++ ByteArray.mk #[0x6a]) :: .vBigint svV
          :: .vBigint satsV :: .vBytes cpV :: rest }
      = .ok
      { s with stack := .vBigint svV :: .vBytes (cpV ++ ByteArray.mk #[0x6a])
          :: .vBigint satsV :: .vBytes cpV :: rest } := by
    unfold Eval.applySwap
    rfl
  rw [hSw1]
  -- step 5: push 8
  show runOps (.push (.bigint 8) :: _)
      { s with stack := .vBigint svV :: .vBytes (cpV ++ ByteArray.mk #[0x6a])
          :: .vBigint satsV :: .vBytes cpV :: rest } = _
  unfold runOps
  rw [stepNonIf_push_bigint]
  -- step 6: OP_NUM2BIN (stateVal → 8-byte LE)
  show runOps (.opcode "OP_NUM2BIN" :: _)
      { s with stack := .vBigint 8 :: .vBigint svV
          :: .vBytes (cpV ++ ByteArray.mk #[0x6a]) :: .vBigint satsV
          :: .vBytes cpV :: rest } = _
  unfold runOps
  rw [stepNonIf_opcode]
  rw [Sim.runOpcode_NUM2BIN_intNat _ svV 8 sv8
    (.vBytes (cpV ++ ByteArray.mk #[0x6a]) :: .vBigint satsV :: .vBytes cpV :: rest)
    rfl hSv8]
  -- step 7: OP_CAT (acc := cp6a ++ sv8)
  show runOps (.opcode "OP_CAT" :: _)
      { s with stack := .vBytes sv8 :: .vBytes (cpV ++ ByteArray.mk #[0x6a])
          :: .vBigint satsV :: .vBytes cpV :: rest } = _
  unfold runOps
  rw [stepNonIf_opcode]
  rw [Sim.runOpcode_CAT_bytesBytes _ (cpV ++ ByteArray.mk #[0x6a]) sv8
    (.vBigint satsV :: .vBytes cpV :: rest) rfl]
  -- step 8: OP_SIZE
  show runOps (.opcode "OP_SIZE" :: _)
      { s with stack := .vBytes (epiAcc cpV sv8)
          :: .vBigint satsV :: .vBytes cpV :: rest } = _
  unfold runOps
  rw [stepNonIf_opcode]
  rw [Sim.runOpcode_SIZE_bytes _ (epiAcc cpV sv8)
    (.vBigint satsV :: .vBytes cpV :: rest) rfl]
  -- step 9: dup
  show runOps (.dup :: _)
      { s with stack := .vBigint ((epiAcc cpV sv8).size)
          :: .vBytes (epiAcc cpV sv8)
          :: .vBigint satsV :: .vBytes cpV :: rest } = _
  unfold runOps
  rw [stepNonIf_dup]
  have hDup : Eval.applyDup
      { s with stack := .vBigint ((epiAcc cpV sv8).size)
          :: .vBytes (epiAcc cpV sv8)
          :: .vBigint satsV :: .vBytes cpV :: rest }
      = .ok
      { s with stack := .vBigint ((epiAcc cpV sv8).size)
          :: .vBigint ((epiAcc cpV sv8).size)
          :: .vBytes (epiAcc cpV sv8)
          :: .vBigint satsV :: .vBytes cpV :: rest } := by
    unfold Eval.applyDup
    rfl
  rw [hDup]
  -- step 10: push [0xfd, 0x00]
  show runOps (.push (.bytes (ByteArray.mk #[0xfd, 0x00])) :: _)
      { s with stack := .vBigint ((epiAcc cpV sv8).size)
          :: .vBigint ((epiAcc cpV sv8).size)
          :: .vBytes (epiAcc cpV sv8)
          :: .vBigint satsV :: .vBytes cpV :: rest } = _
  unfold runOps
  rw [stepNonIf_push_bytes]
  -- step 11: OP_LESSTHAN (size < 253 — TRUE)
  show runOps (.opcode "OP_LESSTHAN" :: _)
      { s with stack := .vBytes (ByteArray.mk #[0xfd, 0x00])
          :: .vBigint ((epiAcc cpV sv8).size)
          :: .vBigint ((epiAcc cpV sv8).size)
          :: .vBytes (epiAcc cpV sv8)
          :: .vBigint satsV :: .vBytes cpV :: rest } = _
  unfold runOps
  rw [stepNonIf_opcode]
  rw [runOpcode_LESSTHAN_intBytes _ ((epiAcc cpV sv8).size)
    (ByteArray.mk #[0xfd, 0x00])
    (.vBigint ((epiAcc cpV sv8).size)
      :: .vBytes (epiAcc cpV sv8)
      :: .vBigint satsV :: .vBytes cpV :: rest) rfl (by decide)]
  rw [decodeMinimalLE_fd00]
  rw [show (decide (((epiAcc cpV sv8).size : Int) < 253)) = true
      from decide_eq_true hAccSzLt]
  -- step 12: the ifOp — condition TRUE, then-branch only
  show runOps (.ifOp [.push (.bigint 2), .opcode "OP_NUM2BIN", .push (.bigint 1),
        .opcode "OP_SPLIT", .drop] _ :: _)
      { s with stack := .vBool true
          :: .vBigint ((epiAcc cpV sv8).size)
          :: .vBytes (epiAcc cpV sv8)
          :: .vBigint satsV :: .vBytes cpV :: rest } = _
  unfold runOps
  have hPop : StackState.pop?
      { s with stack := Value.vBool true
          :: .vBigint ((epiAcc cpV sv8).size)
          :: .vBytes (epiAcc cpV sv8)
          :: .vBigint satsV :: .vBytes cpV :: rest }
      = some (Value.vBool true,
      { s with stack := Value.vBigint ((epiAcc cpV sv8).size)
          :: .vBytes (epiAcc cpV sv8)
          :: .vBigint satsV :: .vBytes cpV :: rest }) := by
    unfold StackState.pop?
    rfl
  rw [hPop]
  show (match runOps [.push (.bigint 2), .opcode "OP_NUM2BIN", .push (.bigint 1),
        .opcode "OP_SPLIT", .drop]
      { s with stack := .vBigint ((epiAcc cpV sv8).size)
          :: .vBytes (epiAcc cpV sv8)
          :: .vBigint satsV :: .vBytes cpV :: rest } with
      | .error e => (Except.error e : RunarVerification.ANF.Eval.EvalResult StackState)
      | .ok s'' => runOps [.swap, .opcode "OP_CAT", .swap, .push (.bigint 8),
          .opcode "OP_NUM2BIN", .swap, .opcode "OP_CAT"] s'') = _
  -- then-branch: push 2; NUM2BIN; push 1; SPLIT; drop
  have hThen : runOps [.push (.bigint 2), .opcode "OP_NUM2BIN", .push (.bigint 1),
        .opcode "OP_SPLIT", .drop]
      { s with stack := .vBigint ((epiAcc cpV sv8).size)
          :: .vBytes (epiAcc cpV sv8)
          :: .vBigint satsV :: .vBytes cpV :: rest }
      = .ok
      { s with stack := .vBytes (var2.extract 0 1)
          :: .vBytes (epiAcc cpV sv8)
          :: .vBigint satsV :: .vBytes cpV :: rest } := by
    unfold runOps
    rw [stepNonIf_push_bigint]
    show runOps (.opcode "OP_NUM2BIN" :: _)
        { s with stack := .vBigint 2
            :: .vBigint ((epiAcc cpV sv8).size)
            :: .vBytes (epiAcc cpV sv8)
            :: .vBigint satsV :: .vBytes cpV :: rest } = _
    unfold runOps
    rw [stepNonIf_opcode]
    rw [Sim.runOpcode_NUM2BIN_intNat _ ((epiAcc cpV sv8).size) 2 var2
      (.vBytes (epiAcc cpV sv8)
        :: .vBigint satsV :: .vBytes cpV :: rest) rfl hVar]
    show runOps (.push (.bigint 1) :: _)
        { s with stack := .vBytes var2
            :: .vBytes (epiAcc cpV sv8)
            :: .vBigint satsV :: .vBytes cpV :: rest } = _
    unfold runOps
    rw [stepNonIf_push_bigint]
    show runOps (.opcode "OP_SPLIT" :: _)
        { s with stack := .vBigint 1 :: .vBytes var2
            :: .vBytes (epiAcc cpV sv8)
            :: .vBigint satsV :: .vBytes cpV :: rest } = _
    unfold runOps
    rw [stepNonIf_opcode]
    rw [Sim.runOpcode_SPLIT_bytesNat _ var2 1
      (.vBytes (epiAcc cpV sv8)
        :: .vBigint satsV :: .vBytes cpV :: rest) rfl hVar2]
    show runOps (.drop :: _)
        { s with stack := .vBytes (var2.extract 1 var2.size)
            :: .vBytes (var2.extract 0 1)
            :: .vBytes (epiAcc cpV sv8)
            :: .vBigint satsV :: .vBytes cpV :: rest } = _
    unfold runOps
    rw [stepNonIf_drop]
    have hDrop : Eval.applyDrop
        { s with stack := .vBytes (var2.extract 1 var2.size)
            :: .vBytes (var2.extract 0 1)
            :: .vBytes (epiAcc cpV sv8)
            :: .vBigint satsV :: .vBytes cpV :: rest }
        = .ok
        { s with stack := .vBytes (var2.extract 0 1)
            :: .vBytes (epiAcc cpV sv8)
            :: .vBigint satsV :: .vBytes cpV :: rest } := by
      unfold Eval.applyDrop
      rfl
    rw [hDrop]
    exact runOps_nil _
  rw [hThen]
  -- post-if: swap; CAT; swap; push 8; NUM2BIN; swap; CAT
  show runOps (.swap :: _)
      { s with stack := .vBytes (var2.extract 0 1)
          :: .vBytes (epiAcc cpV sv8)
          :: .vBigint satsV :: .vBytes cpV :: rest } = _
  unfold runOps
  rw [stepNonIf_swap]
  have hSw2 : Eval.applySwap
      { s with stack := .vBytes (var2.extract 0 1)
          :: .vBytes (epiAcc cpV sv8)
          :: .vBigint satsV :: .vBytes cpV :: rest }
      = .ok
      { s with stack := .vBytes (epiAcc cpV sv8)
          :: .vBytes (var2.extract 0 1)
          :: .vBigint satsV :: .vBytes cpV :: rest } := by
    unfold Eval.applySwap
    rfl
  rw [hSw2]
  show runOps (.opcode "OP_CAT" :: _)
      { s with stack := .vBytes (epiAcc cpV sv8)
          :: .vBytes (var2.extract 0 1)
          :: .vBigint satsV :: .vBytes cpV :: rest } = _
  unfold runOps
  rw [stepNonIf_opcode]
  rw [Sim.runOpcode_CAT_bytesBytes _ (var2.extract 0 1)
    (epiAcc cpV sv8)
    (.vBigint satsV :: .vBytes cpV :: rest) rfl]
  show runOps (.swap :: _)
      { s with stack := .vBytes (var2.extract 0 1 ++ epiAcc cpV sv8)
          :: .vBigint satsV :: .vBytes cpV :: rest } = _
  unfold runOps
  rw [stepNonIf_swap]
  have hSw3 : Eval.applySwap
      { s with stack := .vBytes (var2.extract 0 1 ++ epiAcc cpV sv8)
          :: .vBigint satsV :: .vBytes cpV :: rest }
      = .ok
      { s with stack := .vBigint satsV
          :: .vBytes (var2.extract 0 1 ++ epiAcc cpV sv8)
          :: .vBytes cpV :: rest } := by
    unfold Eval.applySwap
    rfl
  rw [hSw3]
  show runOps (.push (.bigint 8) :: _)
      { s with stack := .vBigint satsV
          :: .vBytes (var2.extract 0 1 ++ epiAcc cpV sv8)
          :: .vBytes cpV :: rest } = _
  unfold runOps
  rw [stepNonIf_push_bigint]
  show runOps (.opcode "OP_NUM2BIN" :: _)
      { s with stack := .vBigint 8 :: .vBigint satsV
          :: .vBytes (var2.extract 0 1 ++ epiAcc cpV sv8)
          :: .vBytes cpV :: rest } = _
  unfold runOps
  rw [stepNonIf_opcode]
  rw [Sim.runOpcode_NUM2BIN_intNat _ satsV 8 sats8
    (.vBytes (var2.extract 0 1 ++ epiAcc cpV sv8)
      :: .vBytes cpV :: rest) rfl hSats8]
  show runOps (.swap :: _)
      { s with stack := .vBytes sats8
          :: .vBytes (var2.extract 0 1 ++ epiAcc cpV sv8)
          :: .vBytes cpV :: rest } = _
  unfold runOps
  rw [stepNonIf_swap]
  have hSw4 : Eval.applySwap
      { s with stack := .vBytes sats8
          :: .vBytes (var2.extract 0 1 ++ epiAcc cpV sv8)
          :: .vBytes cpV :: rest }
      = .ok
      { s with stack := .vBytes (var2.extract 0 1 ++ epiAcc cpV sv8)
          :: .vBytes sats8 :: .vBytes cpV :: rest } := by
    unfold Eval.applySwap
    rfl
  rw [hSw4]
  show runOps (.opcode "OP_CAT" :: _)
      { s with stack := .vBytes (var2.extract 0 1 ++ epiAcc cpV sv8)
          :: .vBytes sats8 :: .vBytes cpV :: rest } = _
  unfold runOps
  rw [stepNonIf_opcode]
  rw [Sim.runOpcode_CAT_bytesBytes _ sats8
    (var2.extract 0 1 ++ epiAcc cpV sv8)
    (.vBytes cpV :: rest) rfl]
  show runOps ([] : List StackOp)
      { s with stack := Value.vBytes (sats8 ++ (var2.extract 0 1 ++ epiAcc cpV sv8)) :: Value.vBytes cpV :: rest } = _
  exact runOps_nil _

/-- **The composed acceptance walk**: running the parse image of the full
method on the entry stack `[pre, stateVal, sats, sig, codePart]` is
ACCEPTED (truthy top — the nonempty serialized output bytes) iff the AUTH
backend accepts the `_opPushTxSig` witness against the synthetic key. -/
theorem runOps_statefulFullParsedOps_scriptAccepts
    (stkSt : StackState) (preV sigV cpV sv8 var2 sats8 : ByteArray)
    (svV satsV : Int) (rest : List Value)
    (hStk : stkSt.stack = .vBytes preV :: .vBigint svV :: .vBigint satsV
        :: .vBytes sigV :: .vBytes cpV :: rest)
    (hPre : 0 < preV.size)
    (hSv8 : num2binEncode? svV 8 = some sv8)
    (hSv8sz : sv8.size = 8)
    (hLt : cpV.size + 9 < 253)
    (hVar : num2binEncode? ((epiAcc cpV sv8).size : Int) 2 = some var2)
    (hVar2 : 1 ≤ var2.size)
    (hSats8 : num2binEncode? satsV 8 = some sats8) :
    scriptAccepts (runOps statefulFullParsedOps stkSt)
      = authBackend.checkSig sigV stG := by
  show scriptAccepts (runOps (.opcode "OP_CODESEPARATOR" :: _) stkSt) = _
  unfold runOps
  rw [stepNonIf_opcode]
  have hCSep : Eval.runOpcode "OP_CODESEPARATOR" stkSt = .ok stkSt := rfl
  rw [hCSep]
  show scriptAccepts (runOps (.roll 3 :: _) stkSt) = _
  unfold runOps
  rw [stepNonIf_roll3_cons5 stkSt _ _ _ _ _ rest hStk]
  show scriptAccepts (runOps (.push (.bytes stG) :: _)
      { stkSt with stack := .vBytes sigV :: .vBytes preV :: .vBigint svV
          :: .vBigint satsV :: .vBytes cpV :: rest }) = _
  unfold runOps
  rw [stepNonIf_push_bytes]
  show scriptAccepts (runOps (.opcode "OP_CHECKSIGVERIFY" :: _)
      { stkSt with stack := .vBytes stG :: .vBytes sigV :: .vBytes preV
          :: .vBigint svV :: .vBigint satsV :: .vBytes cpV :: rest }) = _
  unfold runOps
  rw [stepNonIf_opcode]
  rw [runOpcode_CHECKSIGVERIFY_reduce
    { stkSt with stack := .vBytes stG :: .vBytes sigV :: .vBytes preV
        :: .vBigint svV :: .vBigint satsV :: .vBytes cpV :: rest }
    stG sigV
    (.vBytes preV :: .vBigint svV :: .vBigint satsV :: .vBytes cpV :: rest) rfl]
  rcases Bool.eq_false_or_eq_true (authBackend.checkSig sigV stG) with h | h
  case _ =>
    -- witness ACCEPTED: walk the rest.
    rw [h]
    simp only [if_true]
    show scriptAccepts (runOps (.opcode "OP_VERIFY" :: statefulFullEpilogueParsedOps)
        { stkSt with stack := .vBytes preV :: .vBigint svV :: .vBigint satsV
            :: .vBytes cpV :: rest }) = true
    unfold runOps
    rw [stepNonIf_opcode]
    have hVer : Eval.runOpcode "OP_VERIFY"
        { stkSt with stack := .vBytes preV :: .vBigint svV :: .vBigint satsV
            :: .vBytes cpV :: rest }
        = .ok
        { stkSt with stack := .vBigint svV :: .vBigint satsV
            :: .vBytes cpV :: rest } := by
      rw [Sim.runOpcode_VERIFY_def]
      have hPop : StackState.pop?
          { stkSt with stack := Value.vBytes preV :: .vBigint svV :: .vBigint satsV
              :: .vBytes cpV :: rest }
          = some (Value.vBytes preV,
          { stkSt with stack := Value.vBigint svV :: .vBigint satsV
              :: .vBytes cpV :: rest }) := by
        unfold StackState.pop?
        rfl
      rw [hPop]
      have hb : decide (preV.size > 0) = true := decide_eq_true hPre
      simp [asBool?, hb]
    rw [hVer]
    show scriptAccepts (runOps statefulFullEpilogueParsedOps
        { stkSt with stack := .vBigint svV :: .vBigint satsV
            :: .vBytes cpV :: rest }) = true
    rw [runOps_statefulFullEpilogueParsed
      { stkSt with stack := .vBigint svV :: .vBigint satsV :: .vBytes cpV :: rest }
      cpV sv8 var2 sats8 svV satsV rest rfl hSv8 hSv8sz hLt hVar hVar2 hSats8]
    have hAcc9 : (epiAcc cpV sv8).size = cpV.size + 9 := by
      have h6a : (ByteArray.mk #[0x6a]).size = 1 := rfl
      simp [epiAcc, ByteArray.size_append, h6a, hSv8sz]
    simp [scriptAccepts, topTruthy, asBool?]
    omega
  case _ =>
    -- witness REJECTED: CHECKSIGVERIFY aborts; not accepted.
    rw [h]
    simp [scriptAccepts]

/-! ## Part 6.4 — the parse round-trip (M4, fully concrete) -/

section ConcreteRoundTrip

set_option maxRecDepth 8192

open RunarVerification.Script RunarVerification.Script.Parse

/-- Leaf: `parseOps` over the list-level emit of the composed constant
ops yields EXACTLY the structural parse image (`with_unfolding_all` —
default-transparency `rfl` is blocked by irreducibility annotations on
the ByteArray helpers). -/
theorem parseOps_emit_statefulFull :
    parseOps (emitOpsL statefulFullOps) = .ok statefulFullParsedOps := by
  with_unfolding_all rfl

/-- Bridge: the ByteArray-level emit agrees with the list-level emit. -/
theorem emitOps_toList_statefulFull :
    (Emit.emitOps statefulFullOps).toList = emitOpsL statefulFullOps := by
  with_unfolding_all rfl

end ConcreteRoundTrip

open RunarVerification.Script RunarVerification.Script.Parse in
/-- **M4 round-trip.**  The fast-emitted bytes of the composed constant
ops parse back to the structural parse image. -/
theorem parseScript_emitOpsFast_statefulFull :
    parseScript (Emit.emitOpsFast statefulFullOps) = .ok statefulFullParsedOps := by
  rw [← Emit.EmitFastProof.emitOps_eq_emitOpsFast statefulFullOps]
  unfold parseScript
  rw [emitOps_toList_statefulFull]
  exact parseOps_emit_statefulFull

/-! ## Part 6.5 — the decidable fragment classifier -/

/-- Reserved names the widened fragment's user-visible identifiers must
avoid: the auto-injected binding names, the implicit stack params, and
the anonymous stack-map placeholders of the addOutput lowering. -/
def statefulFullReservedNames : List String :=
  ["", "_cp0", "_v", "_so0", "_opPushTxSig", "_codePart", "_acc", "_varint", "_conv"]

/-- All name-collision exclusions of the widened fragment, decidably. -/
def statefulFullNamesOk (pre sats stateVal : String) : Bool :=
  !(statefulFullReservedNames.contains pre) &&
  !(statefulFullReservedNames.contains sats) &&
  !(statefulFullReservedNames.contains stateVal) &&
  pre != sats && pre != stateVal && sats != stateVal

/-- One mutable property, `bigint`-typed, no initializer — the property
table shape whose `add_output` serialization the widened fragment pins. -/
def mutablePropsBigintOne (props : List ANFProperty) : Bool :=
  match props.filter (fun pp => !pp.readonly) with
  | [pp] => (match pp.type with | .bigint => true | _ => false)
              && pp.initialValue.isNone
  | _ => false

/-- Decides the WIDENED stateful consume fragment: three params
`(sats, stateVal, pre)`, body EXACTLY the composed prologue+epilogue,
one mutable bigint property, all name-collision exclusions. -/
def statefulFullConsumeShapeBool (props : List ANFProperty) (m : ANFMethod) : Bool :=
  match m.params, m.body with
  | [pS, pV, pP],
    [⟨bn1, .checkPreimage pre, none⟩, ⟨bn2, .assert ref, none⟩,
     ⟨bn3, .addOutput sats [stateVal] epre, none⟩] =>
      (bn1 == "_cp0") && (bn2 == "_v") && (ref == "_cp0") && (bn3 == "_so0") &&
      (epre == "") &&
      (pS.name == sats) && (pV.name == stateVal) && (pP.name == pre) &&
      statefulFullNamesOk pre sats stateVal &&
      mutablePropsBigintOne props
  | _, _ => false

/-- **Extraction**: a classifier-true method has EXACTLY the composed
body, the matching 3-param list, the one-mutable-bigint-prop filter
shape (its `readonly` pinned `false` by the filter predicate), and the
name exclusions. -/
theorem statefulFullConsumeShapeBool_extract (props : List ANFProperty)
    (m : ANFMethod) (h : statefulFullConsumeShapeBool props m = true) :
    ∃ (pre sats stateVal pn : String) (tyS tyV tyP : ANFType),
      m.params = [ANFParam.mk sats tyS, ANFParam.mk stateVal tyV, ANFParam.mk pre tyP] ∧
      m.body = statefulFullBody pre sats stateVal ∧
      props.filter (fun pp => !pp.readonly)
        = [{ name := pn, type := .bigint, readonly := false }] ∧
      statefulFullNamesOk pre sats stateVal = true := by
  unfold statefulFullConsumeShapeBool at h
  split at h
  case _ =>
    rename_i pS pV pP bn1 pre bn2 ref bn3 sats stateVal epre hParamsEq hBodyEq
    -- peel the `&&`-conjuncts right-to-left
    rw [Bool.and_eq_true] at h; obtain ⟨h, hPropsB⟩ := h
    rw [Bool.and_eq_true] at h; obtain ⟨h, hNames⟩ := h
    rw [Bool.and_eq_true] at h; obtain ⟨h, hPP⟩ := h
    rw [Bool.and_eq_true] at h; obtain ⟨h, hPV⟩ := h
    rw [Bool.and_eq_true] at h; obtain ⟨h, hPS⟩ := h
    rw [Bool.and_eq_true] at h; obtain ⟨h, hEpre⟩ := h
    rw [Bool.and_eq_true] at h; obtain ⟨h, hBn3⟩ := h
    rw [Bool.and_eq_true] at h; obtain ⟨h, hRef⟩ := h
    rw [Bool.and_eq_true] at h; obtain ⟨hBn1, hBn2⟩ := h
    have hBn1' : bn1 = "_cp0" := beq_iff_eq.mp hBn1
    have hBn2' : bn2 = "_v" := beq_iff_eq.mp hBn2
    have hRef' : ref = "_cp0" := beq_iff_eq.mp hRef
    have hBn3' : bn3 = "_so0" := beq_iff_eq.mp hBn3
    have hEpre' : epre = "" := beq_iff_eq.mp hEpre
    have hPS' : pS.name = sats := beq_iff_eq.mp hPS
    have hPV' : pV.name = stateVal := beq_iff_eq.mp hPV
    have hPP' : pP.name = pre := beq_iff_eq.mp hPP
    subst hBn1'; subst hBn2'; subst hRef'; subst hBn3'; subst hEpre'
    refine ⟨pre, sats, stateVal, ?_⟩
    -- analyze the one-mutable-bigint-prop check
    unfold mutablePropsBigintOne at hPropsB
    rcases hF : props.filter (fun pq => !pq.readonly) with _ | ⟨pp, rest⟩
    case _ =>
      rw [hF] at hPropsB
      exact absurd hPropsB (by decide)
    case _ =>
      rcases rest with _ | ⟨pp2, rest2⟩
      case _ =>
        rw [hF] at hPropsB
        simp only [Bool.and_eq_true] at hPropsB
        obtain ⟨hTy, hIv⟩ := hPropsB
        have hMem : pp ∈ props.filter (fun pq => !pq.readonly) := by
          rw [hF]; exact List.mem_singleton.mpr rfl
        have hRo : pp.readonly = false := by
          have := (List.mem_filter.mp hMem).2
          simpa using this
        have hTy' : pp.type = .bigint := by
          revert hTy; cases pp.type <;> simp
        have hIv' : pp.initialValue = none := by
          cases hI : pp.initialValue
          · rfl
          · rw [hI] at hIv; simp [Option.isNone] at hIv
        have hpp : pp = ⟨pp.name, .bigint, false, none⟩ := by
          cases pp; simp_all
        refine ⟨pp.name, pS.type, pV.type, pP.type, ?_, ?_, ?_, hNames⟩
        · rw [hParamsEq, ← hPS', ← hPV', ← hPP']
        · rw [hBodyEq]; rfl
        · rw [hF, hpp]
      case _ =>
        rw [hF] at hPropsB
        simp at hPropsB
  case _ => exact absurd h (by decide)

/-- Unpack the decidable name-exclusion bundle into the 16 disequalities
the lowering/ANF reductions consume. -/
theorem statefulFullNamesOk_unpack (pre sats stateVal : String)
    (h : statefulFullNamesOk pre sats stateVal = true) :
    pre ≠ "" ∧ pre ≠ "_cp0" ∧ pre ≠ "_v" ∧ pre ≠ "_so0" ∧
    pre ≠ "_opPushTxSig" ∧ pre ≠ "_codePart" ∧
    sats ≠ "" ∧ sats ≠ "_cp0" ∧ sats ≠ "_v" ∧ sats ≠ "_so0" ∧
    sats ≠ "_opPushTxSig" ∧ sats ≠ "_codePart" ∧ sats ≠ "_acc" ∧
    stateVal ≠ "" ∧ stateVal ≠ "_cp0" ∧ stateVal ≠ "_v" ∧ stateVal ≠ "_so0" ∧
    stateVal ≠ "_opPushTxSig" ∧ stateVal ≠ "_codePart" ∧ stateVal ≠ "_acc" ∧
    pre ≠ sats ∧ pre ≠ stateVal ∧ sats ≠ stateVal := by
  simp only [statefulFullNamesOk, statefulFullReservedNames, List.contains_cons,
    List.contains_nil, Bool.or_false, Bool.not_or, Bool.and_eq_true,
    Bool.not_eq_true', beq_eq_false_iff_ne, bne_iff_ne] at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all

/-! ## Part 6.6 — MANDATORY smokes (anti-vacuity) -/

/-- The canonical widened stateful method:
`verify(sats, stateVal, pre) { _cp0 := check_preimage pre; assert _cp0;
_so0 := add_output(sats, [stateVal], "") }`. -/
def smokeFullMethod : ANFMethod :=
  { name := "verify"
    params := [ANFParam.mk "sats" .bigint, ANFParam.mk "stateVal" .bigint,
               ANFParam.mk "pre" .byteString]
    body := statefulFullBody "pre" "sats" "stateVal"
    isPublic := true }

/-- The one-mutable-prop property table the widened fragment serializes. -/
def smokeFullProps : List ANFProperty :=
  [{ name := "count", type := .bigint, readonly := false }]

/-- SMOKE — the widened classifier fires on the canonical method. -/
theorem smoke_full_classifier_fires :
    statefulFullConsumeShapeBool smokeFullProps smokeFullMethod = true := by
  native_decide

/-- SMOKE — the widened classifier REJECTS the prologue-only method
(the two fragments are disjoint). -/
theorem smoke_full_classifier_rejects_prologueOnly :
    statefulFullConsumeShapeBool smokeFullProps smokeMethod = false := by
  native_decide

/-- SMOKE — the prologue-only classifier rejects the widened body. -/
theorem smoke_prologue_classifier_rejects_full :
    statefulConsumeShapeBool smokeFullMethod = false := by
  native_decide

/-- SMOKE — the method-level lowering reduction fires concretely. -/
theorem smoke_full_lowerMethod_ops :
    (Lower.lowerMethod [] smokeFullProps smokeFullMethod).ops = statefulFullOps :=
  lowerMethod_ops_statefulFull [] smokeFullProps smokeFullMethod
    "pre" "sats" "stateVal" "count" .bigint .bigint .byteString rfl rfl rfl rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

end RunarVerification.Stack.AgreesStateful
