import RunarVerification.Stack.AgreesLoopParsed

/-! # Omnibus-with-loop — the downstream loop-widened observational omnibus

This module is the CAPSTONE of the loop frontier. The main omnibus
`compileSafe_observational_correct_modulo_codegen_axioms`
(`RunarVerification/Pipeline.lean`) covers LOOP-FREE programs only — its
`hNoLoop : programUsesLoopB p = false` premise is the documented exclusion.
The genuine accumulator consume theorem
`RunarVerification.Stack.LoopBridge.loopOk_acceptAgrees_parsedBytes`
(`RunarVerification/Stack/AgreesLoopParsed.lean`) proves the canonical
loop correct over the ACTUAL parsed bytes, GENERAL over the entry `start`.

That consume theorem is strictly DOWNSTREAM of `Pipeline` (it imports
`AgreesLoopBridge` which imports `Pipeline`), so `Pipeline` cannot reference
it without a circular import. Hence this WRAPPER: a NEW theorem, identical
in conclusion and premise list to the main omnibus EXCEPT the `hNoLoop`
premise is replaced by a disjunctive `hLoopGate` that admits the canonical
loop program. It composes the EXISTING omnibus (applied as a black box in
the loop-free disjunct) with the loop consume theorem (in the loop
disjunct). Purely ADDITIVE — the omnibus and `Pipeline.lean` are UNTOUCHED.
-/

namespace RunarVerification.Pipeline.Soundness

open RunarVerification.ANF
open RunarVerification.ANF.Eval (State)
open RunarVerification.Stack
open RunarVerification.Stack.Eval (StackState acceptAgrees topTruthy)

/-- **The loop-widened observational omnibus.** Same conclusion and same
premise list as `compileSafe_observational_correct_modulo_codegen_axioms`,
EXCEPT the loop-exclusion guard `hNoLoop : programUsesLoopB p = false` is
replaced by the disjunctive gate `hLoopGate`: either the program is
loop-free (defer to the existing omnibus verbatim), OR it is the canonical
accumulator `loopOk` program entered with a `start :: rest` runtime stack
(defer to the genuine loop consume theorem
`LoopBridge.loopOk_acceptAgrees_parsedBytes`).

This is the top-level theorem that provably covers a real loop: in the
right disjunct the omnibus's correctness conclusion is discharged for the
canonical loop accumulator from the actual parsed bytes. -/
theorem compileSafe_observational_correct_modulo_codegen_axioms_with_loop
    (p : ANFProgram)
    (hWF : WF.ANF p) (anfM : ANFMethod) (bytes : ByteArray)
    (hMem : anfM ∈ p.methods) (hPublic : anfM.isPublic = true)
    (hSafe : compileSafe p = .ok bytes)
    (initialAnf : State) (initialStack : StackState)
    (tsm : Agrees.TaggedStackMap)
    (hAgrees : Agrees.agreesTagged tsm initialAnf initialStack)
    -- Loop GATE (downstream widening; replaces `hNoLoop`). Either the
    -- program is loop-free (the existing omnibus applies verbatim), or it
    -- is the canonical accumulator `loopOk` entered with a `start :: rest`
    -- runtime stack and the matching ANF entry (the genuine loop consume
    -- theorem applies).
    (hLoopGate : programUsesLoopB p = false ∨
      (p = RunarVerification.Stack.LoopBridge.loopOkProg ∧
       anfM = RunarVerification.Stack.LoopBridge.loopOkM ∧
       ∃ start rest,
         initialAnf =
           { params := [("start", RunarVerification.ANF.Eval.Value.vBigint start)]
           , props := [("expectedSum", RunarVerification.ANF.Eval.Value.vBigint 0)] }
         ∧ initialStack.stack =
             (RunarVerification.ANF.Eval.Value.vBigint start) :: rest))
    (Γ : RunarVerification.ANF.WellTyped.TypeEnv)
    (hUntag : (p.methods.filter (·.isPublic)).length < 2 →
      Agrees.untagSm tsm = List.reverse (anfM.params.map (·.name)))
    (hTypedEntry : RunarVerification.ANF.WellTyped.EntryBigintTyped Γ initialAnf)
    (hTsmTyped :
      (anfM.name ≠ "constructor" ∧
        Agrees.emittableArithChainReadyNoDblNeg
          (Lower.computeLastUses anfM.body) anfM.body
          (List.reverse (anfM.params.map (·.name))) 0 false) →
      Agrees.entryTsmArithTyped Γ tsm)
    (hIfValTyped :
      ∀ (bn cond : String) (thn els : List ANFBinding) (src : Option SourceLoc),
        anfM.body = [.mk bn (.ifVal cond thn els) src] →
        ∃ (k : Agrees.SlotKind) (branchTsm : Agrees.TaggedStackMap),
          tsm = (cond, k) :: branchTsm ∧
          RunarVerification.ANF.WellTyped.CondBoolTyped Γ initialAnf cond ∧
          Agrees.entryTsmArithTyped Γ branchTsm)
    (hMathByteFrag :
      AgreesA4.mathByteSingleArgShapeNoLenBool anfM.body tsm = true →
        AgreesA4.structuralCallBody (Lower.computeLastUses anfM.body) []
          anfM.body (anfM.params.map (fun pp => pp.name) |>.reverse) 0 ∧
        AgreesA4.mathByteSingleArgBody anfM.body tsm initialAnf)
    (hMathByteCatFrag : (p.methods.filter (·.isPublic)).length < 2 →
      RunarVerification.Stack.AgreesCat.catConsumeShapeBool anfM = true →
        ∃ (bn a b : String) (src : Option SourceLoc)
          (ba bb : ByteArray) (rest : List RunarVerification.ANF.Eval.Value),
          (anfM.params.map (·.name)).reverse = [b, a] ∧
          anfM.body = [ANFBinding.mk bn (.call "cat" [a, b]) src] ∧
          a ≠ b ∧
          initialAnf.resolveRef a = some (.vBytes ba) ∧
          initialAnf.resolveRef b = some (.vBytes bb) ∧
          initialStack.stack = .vBytes bb :: .vBytes ba :: rest)
    (hUpdatePropFrag :
      Agrees.updatePropConsumeShapeBool anfM.body = true →
        ∀ (prop op : String) (c : Int),
          anfM.body = Agrees.updatePropConsumeBody prop op c →
          tsm = [(prop, Agrees.SlotKind.prop)] ∧
          Agrees.entryTsmArithTyped Γ tsm)
    (hMethodCallFrag :
      Agrees.methodCallConsumeShapeBool p.methods anfM = true →
        ∃ a, (anfM.params.map (·.name)).reverse = [a] ∧
             tsm = [(a, Agrees.SlotKind.param)])
    (hHashCallFrag : (p.methods.filter (·.isPublic)).length < 2 →
      RunarVerification.Stack.AgreesHashCall.hashCallConsumeShapeBool anfM = true →
        ∃ (bn arg func : String) (src : Option SourceLoc)
          (argBytes : ByteArray) (rest : List RunarVerification.ANF.Eval.Value),
          (anfM.params.map (·.name)).reverse = [arg] ∧
          anfM.body = [ANFBinding.mk bn (.call func [arg]) src] ∧
          (func = "sha256" ∨ func = "hash160") ∧
          initialAnf.resolveRef arg = some (.vBytes argBytes) ∧
          initialStack.stack = .vBytes argBytes :: rest ∧
          argBytes.size ≤ 520)
    (hHashAssertFrag : (p.methods.filter (·.isPublic)).length < 2 →
      RunarVerification.Stack.AgreesHashCall.hashAssertConsumeShapeBool anfM = true →
        ∃ (d ok anm arg expected func : String) (tyE tyA : ANFType)
          (s1 s2 s3 : Option SourceLoc) (argBytes expBytes : ByteArray)
          (rest : List RunarVerification.ANF.Eval.Value),
          anfM.params = [ANFParam.mk expected tyE, ANFParam.mk arg tyA] ∧
          anfM.body = RunarVerification.Stack.AgreesHashCall.hashAssertBody
            d ok anm arg expected func s1 s2 s3 ∧
          (func = "sha256" ∨ func = "hash160") ∧
          RunarVerification.Stack.AgreesHashCall.hashAssertNamesOk
            d ok arg expected = true ∧
          initialAnf.resolveRef arg = some (.vBytes argBytes) ∧
          initialAnf.resolveRef expected = some (.vBytes expBytes) ∧
          initialStack.stack = .vBytes argBytes :: .vBytes expBytes :: rest ∧
          argBytes.size ≤ 520)
    (hHashChainFrag : (p.methods.filter (·.isPublic)).length < 2 →
      RunarVerification.Stack.AgreesHashCall.hashChainConsumeShapeBool anfM = true →
        ∃ (d1 d2 arg f1 f2 : String) (ty : ANFType)
          (s1 s2 : Option SourceLoc) (argBytes : ByteArray)
          (rest : List RunarVerification.ANF.Eval.Value),
          anfM.params = [ANFParam.mk arg ty] ∧
          anfM.body = RunarVerification.Stack.AgreesHashCall.hashChainBody
            d1 d2 arg f1 f2 s1 s2 ∧
          RunarVerification.Stack.AgreesHashCall.hashChainFuncsOk f1 f2 = true ∧
          d1 ≠ arg ∧
          initialAnf.resolveRef arg = some (.vBytes argBytes) ∧
          initialStack.stack = .vBytes argBytes :: rest ∧
          argBytes.size ≤ 520)
    (hStatefulFrag : (p.methods.filter (·.isPublic)).length < 2 →
      RunarVerification.Stack.AgreesStateful.statefulConsumeShapeBool anfM = true →
        ∃ (pre : String) (ty : ANFType) (ctx : Stack.TxContext)
          (sigV preimage : ByteArray) (rest : List RunarVerification.ANF.Eval.Value),
          anfM.params = [ANFParam.mk pre ty] ∧
          anfM.body = Stack.StatefulBridge.gatedStatefulPrologueBody pre ∧
          pre ≠ "_cp0" ∧ pre ≠ "_opPushTxSig" ∧
          Stack.ValidTxContext ctx ∧
          preimage = Stack.TxContext.buildPreimage ctx ∧
          initialAnf.resolveRef pre = some (.vBytes preimage) ∧
          initialStack.stack = .vBytes preimage :: .vBytes sigV :: rest ∧
          RunarVerification.ANF.Eval.Crypto.authBackend.checkSig sigV
              Stack.AgreesStateful.stG
            = RunarVerification.ANF.Eval.Crypto.checkPreimage preimage)
    (hStatefulFullFrag : (p.methods.filter (·.isPublic)).length < 2 →
      RunarVerification.Stack.AgreesStateful.statefulFullConsumeShapeBool
          p.properties anfM = true →
        ∃ (pre sats stateVal pn : String) (tyS tyV tyP : ANFType)
          (ctx : Stack.TxContext)
          (sigV preimage cpV sv8 var2 sats8 : ByteArray) (svV satsV : Int)
          (rest : List RunarVerification.ANF.Eval.Value),
          anfM.params = [ANFParam.mk sats tyS, ANFParam.mk stateVal tyV,
            ANFParam.mk pre tyP] ∧
          anfM.body = Stack.AgreesStateful.statefulFullBody pre sats stateVal ∧
          p.properties.filter (fun pp => !pp.readonly)
            = [{ name := pn, type := .bigint, readonly := false }] ∧
          Stack.AgreesStateful.statefulFullNamesOk pre sats stateVal = true ∧
          Stack.ValidTxContext ctx ∧
          preimage = Stack.TxContext.buildPreimage ctx ∧
          initialAnf.resolveRef pre = some (.vBytes preimage) ∧
          initialAnf.resolveRef sats = some (.vBigint satsV) ∧
          initialAnf.resolveRef stateVal = some (.vBigint svV) ∧
          initialStack.stack = .vBytes preimage :: .vBigint svV
            :: .vBigint satsV :: .vBytes sigV :: .vBytes cpV :: rest ∧
          Stack.num2binEncode? svV 8 = some sv8 ∧ sv8.size = 8 ∧
          cpV.size + 9 < 253 ∧
          Stack.num2binEncode?
            ((Stack.AgreesStateful.epiAcc cpV sv8).size : Int) 2 = some var2 ∧
          1 ≤ var2.size ∧
          Stack.num2binEncode? satsV 8 = some sats8 ∧
          RunarVerification.ANF.Eval.Crypto.authBackend.checkSig sigV
              Stack.AgreesStateful.stG
            = RunarVerification.ANF.Eval.Crypto.checkPreimage preimage)
    (hDispatchFrag :
      dispatchConsumeShapeBool p = true →
        ∃ (i : Nat) (rest : List RunarVerification.ANF.Eval.Value)
          (v : RunarVerification.ANF.Eval.Value),
          (p.methods.filter (·.isPublic))[i]? = some anfM ∧
          initialStack.stack = .vBigint (Int.ofNat i) :: rest ∧
          ∀ (x : String) (ty : ANFType), anfM.params = [ANFParam.mk x ty] →
            initialAnf.lookupParam x = some v)
    (hDispatchMixedFrag :
      dispatchMixedConsumeShapeBool p = true →
        ∃ (i : Nat) (rest : List RunarVerification.ANF.Eval.Value),
          (p.methods.filter (·.isPublic))[i]? = some anfM ∧
          initialStack.stack = .vBigint (Int.ofNat i) :: rest ∧
          (dispatchPassthroughMethodBool anfM = true →
            ∃ (x bn : String) (ty : ANFType) (src : Option SourceLoc)
              (v : RunarVerification.ANF.Eval.Value),
              anfM.params = [ANFParam.mk x ty] ∧
              anfM.body = [ANFBinding.mk bn (.loadParam x) src] ∧
              initialAnf.lookupParam x = some v) ∧
          (dispatchHashLockMethodBool anfM = true →
            ∃ (d ok anm arg expected func : String) (tyE tyA : ANFType)
              (s1 s2 s3 : Option SourceLoc) (argB expB : ByteArray)
              (rest' : List RunarVerification.ANF.Eval.Value),
              anfM.params = [ANFParam.mk expected tyE, ANFParam.mk arg tyA] ∧
              anfM.body = RunarVerification.Stack.AgreesHashCall.hashAssertBody
                d ok anm arg expected func s1 s2 s3 ∧
              (func = "sha256" ∨ func = "hash160") ∧
              RunarVerification.Stack.AgreesHashCall.hashAssertNamesOk
                d ok arg expected = true ∧
              initialAnf.resolveRef arg = some (.vBytes argB) ∧
              initialAnf.resolveRef expected = some (.vBytes expB) ∧
              rest = .vBytes argB :: .vBytes expB :: rest' ∧
              argB.size ≤ 520))
    (hValueTruthy : statefulFullDischargedB p anfM = false →
      Lower.bodyEndsInAssert anfM.body = false →
      ∀ s, runParsedBytes bytes initialStack = .ok s →
        topTruthy s.stack = true)
    (hCoh : Agrees.tsmCoherent initialAnf tsm) :
    acceptAgrees
      (RunarVerification.ANF.Eval.evalBindingsP p.methods initialAnf anfM.body)
      (runParsedBytes bytes initialStack) := by
  rcases hLoopGate with hNoLoop | ⟨hP, hM, start, rest, hAnf, hStk⟩
  · -- Loop-free disjunct: defer to the EXISTING omnibus, threading every
    -- premise verbatim (with `hNoLoop` in the `hNoLoop`-slot).
    exact compileSafe_observational_correct_modulo_codegen_axioms
      p hWF anfM bytes hMem hPublic hSafe initialAnf initialStack tsm hAgrees
      hNoLoop Γ hUntag hTypedEntry hTsmTyped hIfValTyped hMathByteFrag
      hMathByteCatFrag hUpdatePropFrag hMethodCallFrag hHashCallFrag
      hHashAssertFrag hHashChainFrag hStatefulFrag hStatefulFullFrag
      hDispatchFrag hDispatchMixedFrag hValueTruthy hCoh
  · -- Canonical-loop disjunct: defer to the genuine loop consume theorem.
    subst hP; subst hM
    rw [hAnf]
    -- The consume theorem's RHS is `runParsedBytes bytes
    -- { initialStack with stack := .vBigint start :: rest }`; structure eta
    -- on `StackState` plus `hStk` collapses that to `runParsedBytes bytes
    -- initialStack`.
    have hEta : initialStack
        = { initialStack with stack := (RunarVerification.ANF.Eval.Value.vBigint start) :: rest } := by
      rw [← hStk]
    rw [hEta]
    exact RunarVerification.Stack.LoopBridge.loopOk_acceptAgrees_parsedBytes
      bytes hSafe start rest initialStack

/-! ## Capstone smoke — the wrapper provably covers the canonical loop

`omnibus_covers_loopOk` instantiates the loop-widened omnibus at
`p := loopOkProg`, `anfM := loopOkM`, with the canonical deployed entry
(`start = 0`, `rest = []`, the matching ANF state), supplying the RIGHT
disjunct of `hLoopGate`. The wrapper then routes through the `inr` branch —
the genuine loop consume theorem — NOT through the loop-free omnibus. This
is the capstone evidence: a top-level theorem whose conclusion is the
omnibus correctness statement, discharged for a REAL loop program from its
actual parsed bytes.

The remaining (loop-irrelevant) omnibus premises are taken as hypotheses
rather than re-derived: in the `inr` branch the wrapper never consumes
them (they gate the loop-free dispatch cascade only), so the conclusion
follows for the canonical loop regardless of their content. This keeps the
smoke a faithful witness that the `inr` path fires without re-running the
full per-fixture discharge harness. -/
theorem omnibus_covers_loopOk
    (bytes : ByteArray)
    (hWF : WF.ANF RunarVerification.Stack.LoopBridge.loopOkProg)
    (hMem : RunarVerification.Stack.LoopBridge.loopOkM
      ∈ RunarVerification.Stack.LoopBridge.loopOkProg.methods)
    (hSafe : compileSafe RunarVerification.Stack.LoopBridge.loopOkProg = .ok bytes)
    (tsm : Agrees.TaggedStackMap)
    (Γ : RunarVerification.ANF.WellTyped.TypeEnv)
    -- The canonical deployed entry: ANF state `{start ↦ 0, expectedSum ↦ 0}`
    -- and runtime stack `[start] = [0]`.
    (initialAnf : State)
    (hAnf : initialAnf =
      { params := [("start", RunarVerification.ANF.Eval.Value.vBigint 0)]
      , props := [("expectedSum", RunarVerification.ANF.Eval.Value.vBigint 0)] })
    (initialStack : StackState)
    (hStk : initialStack.stack = [RunarVerification.ANF.Eval.Value.vBigint 0])
    (hAgrees : Agrees.agreesTagged tsm initialAnf initialStack)
    -- Loop-irrelevant cascade premises (consumed only by the loop-free
    -- disjunct; abstracted here — the `inr` path discharges the conclusion
    -- without them).
    (hUntag : ((RunarVerification.Stack.LoopBridge.loopOkProg.methods.filter
        (·.isPublic)).length < 2 →
      Agrees.untagSm tsm =
        List.reverse (RunarVerification.Stack.LoopBridge.loopOkM.params.map (·.name))))
    (hTypedEntry : RunarVerification.ANF.WellTyped.EntryBigintTyped Γ initialAnf)
    (hTsmTyped :
      (RunarVerification.Stack.LoopBridge.loopOkM.name ≠ "constructor" ∧
        Agrees.emittableArithChainReadyNoDblNeg
          (Lower.computeLastUses RunarVerification.Stack.LoopBridge.loopOkM.body)
          RunarVerification.Stack.LoopBridge.loopOkM.body
          (List.reverse
            (RunarVerification.Stack.LoopBridge.loopOkM.params.map (·.name))) 0 false) →
      Agrees.entryTsmArithTyped Γ tsm)
    (hIfValTyped :
      ∀ (bn cond : String) (thn els : List ANFBinding) (src : Option SourceLoc),
        RunarVerification.Stack.LoopBridge.loopOkM.body
            = [.mk bn (.ifVal cond thn els) src] →
        ∃ (k : Agrees.SlotKind) (branchTsm : Agrees.TaggedStackMap),
          tsm = (cond, k) :: branchTsm ∧
          RunarVerification.ANF.WellTyped.CondBoolTyped Γ initialAnf cond ∧
          Agrees.entryTsmArithTyped Γ branchTsm)
    (hMathByteFrag :
      AgreesA4.mathByteSingleArgShapeNoLenBool
          RunarVerification.Stack.LoopBridge.loopOkM.body tsm = true →
        AgreesA4.structuralCallBody
          (Lower.computeLastUses RunarVerification.Stack.LoopBridge.loopOkM.body) []
          RunarVerification.Stack.LoopBridge.loopOkM.body
          (RunarVerification.Stack.LoopBridge.loopOkM.params.map
            (fun pp => pp.name) |>.reverse) 0 ∧
        AgreesA4.mathByteSingleArgBody
          RunarVerification.Stack.LoopBridge.loopOkM.body tsm initialAnf)
    (hMathByteCatFrag : (RunarVerification.Stack.LoopBridge.loopOkProg.methods.filter
        (·.isPublic)).length < 2 →
      RunarVerification.Stack.AgreesCat.catConsumeShapeBool
          RunarVerification.Stack.LoopBridge.loopOkM = true →
        ∃ (bn a b : String) (src : Option SourceLoc)
          (ba bb : ByteArray) (rest : List RunarVerification.ANF.Eval.Value),
          (RunarVerification.Stack.LoopBridge.loopOkM.params.map (·.name)).reverse
            = [b, a] ∧
          RunarVerification.Stack.LoopBridge.loopOkM.body
            = [ANFBinding.mk bn (.call "cat" [a, b]) src] ∧
          a ≠ b ∧
          initialAnf.resolveRef a = some (.vBytes ba) ∧
          initialAnf.resolveRef b = some (.vBytes bb) ∧
          initialStack.stack = .vBytes bb :: .vBytes ba :: rest)
    (hUpdatePropFrag :
      Agrees.updatePropConsumeShapeBool
          RunarVerification.Stack.LoopBridge.loopOkM.body = true →
        ∀ (prop op : String) (c : Int),
          RunarVerification.Stack.LoopBridge.loopOkM.body
            = Agrees.updatePropConsumeBody prop op c →
          tsm = [(prop, Agrees.SlotKind.prop)] ∧
          Agrees.entryTsmArithTyped Γ tsm)
    (hMethodCallFrag :
      Agrees.methodCallConsumeShapeBool
          RunarVerification.Stack.LoopBridge.loopOkProg.methods
          RunarVerification.Stack.LoopBridge.loopOkM = true →
        ∃ a, (RunarVerification.Stack.LoopBridge.loopOkM.params.map (·.name)).reverse
              = [a] ∧
             tsm = [(a, Agrees.SlotKind.param)])
    (hHashCallFrag : (RunarVerification.Stack.LoopBridge.loopOkProg.methods.filter
        (·.isPublic)).length < 2 →
      RunarVerification.Stack.AgreesHashCall.hashCallConsumeShapeBool
          RunarVerification.Stack.LoopBridge.loopOkM = true →
        ∃ (bn arg func : String) (src : Option SourceLoc)
          (argBytes : ByteArray) (rest : List RunarVerification.ANF.Eval.Value),
          (RunarVerification.Stack.LoopBridge.loopOkM.params.map (·.name)).reverse
            = [arg] ∧
          RunarVerification.Stack.LoopBridge.loopOkM.body
            = [ANFBinding.mk bn (.call func [arg]) src] ∧
          (func = "sha256" ∨ func = "hash160") ∧
          initialAnf.resolveRef arg = some (.vBytes argBytes) ∧
          initialStack.stack = .vBytes argBytes :: rest ∧
          argBytes.size ≤ 520)
    (hHashAssertFrag : (RunarVerification.Stack.LoopBridge.loopOkProg.methods.filter
        (·.isPublic)).length < 2 →
      RunarVerification.Stack.AgreesHashCall.hashAssertConsumeShapeBool
          RunarVerification.Stack.LoopBridge.loopOkM = true →
        ∃ (d ok anm arg expected func : String) (tyE tyA : ANFType)
          (s1 s2 s3 : Option SourceLoc) (argBytes expBytes : ByteArray)
          (rest : List RunarVerification.ANF.Eval.Value),
          RunarVerification.Stack.LoopBridge.loopOkM.params
            = [ANFParam.mk expected tyE, ANFParam.mk arg tyA] ∧
          RunarVerification.Stack.LoopBridge.loopOkM.body
            = RunarVerification.Stack.AgreesHashCall.hashAssertBody
            d ok anm arg expected func s1 s2 s3 ∧
          (func = "sha256" ∨ func = "hash160") ∧
          RunarVerification.Stack.AgreesHashCall.hashAssertNamesOk
            d ok arg expected = true ∧
          initialAnf.resolveRef arg = some (.vBytes argBytes) ∧
          initialAnf.resolveRef expected = some (.vBytes expBytes) ∧
          initialStack.stack = .vBytes argBytes :: .vBytes expBytes :: rest ∧
          argBytes.size ≤ 520)
    (hHashChainFrag : (RunarVerification.Stack.LoopBridge.loopOkProg.methods.filter
        (·.isPublic)).length < 2 →
      RunarVerification.Stack.AgreesHashCall.hashChainConsumeShapeBool
          RunarVerification.Stack.LoopBridge.loopOkM = true →
        ∃ (d1 d2 arg f1 f2 : String) (ty : ANFType)
          (s1 s2 : Option SourceLoc) (argBytes : ByteArray)
          (rest : List RunarVerification.ANF.Eval.Value),
          RunarVerification.Stack.LoopBridge.loopOkM.params = [ANFParam.mk arg ty] ∧
          RunarVerification.Stack.LoopBridge.loopOkM.body
            = RunarVerification.Stack.AgreesHashCall.hashChainBody
            d1 d2 arg f1 f2 s1 s2 ∧
          RunarVerification.Stack.AgreesHashCall.hashChainFuncsOk f1 f2 = true ∧
          d1 ≠ arg ∧
          initialAnf.resolveRef arg = some (.vBytes argBytes) ∧
          initialStack.stack = .vBytes argBytes :: rest ∧
          argBytes.size ≤ 520)
    (hStatefulFrag : (RunarVerification.Stack.LoopBridge.loopOkProg.methods.filter
        (·.isPublic)).length < 2 →
      RunarVerification.Stack.AgreesStateful.statefulConsumeShapeBool
          RunarVerification.Stack.LoopBridge.loopOkM = true →
        ∃ (pre : String) (ty : ANFType) (ctx : Stack.TxContext)
          (sigV preimage : ByteArray) (rest : List RunarVerification.ANF.Eval.Value),
          RunarVerification.Stack.LoopBridge.loopOkM.params = [ANFParam.mk pre ty] ∧
          RunarVerification.Stack.LoopBridge.loopOkM.body
            = Stack.StatefulBridge.gatedStatefulPrologueBody pre ∧
          pre ≠ "_cp0" ∧ pre ≠ "_opPushTxSig" ∧
          Stack.ValidTxContext ctx ∧
          preimage = Stack.TxContext.buildPreimage ctx ∧
          initialAnf.resolveRef pre = some (.vBytes preimage) ∧
          initialStack.stack = .vBytes preimage :: .vBytes sigV :: rest ∧
          RunarVerification.ANF.Eval.Crypto.authBackend.checkSig sigV
              Stack.AgreesStateful.stG
            = RunarVerification.ANF.Eval.Crypto.checkPreimage preimage)
    (hStatefulFullFrag : (RunarVerification.Stack.LoopBridge.loopOkProg.methods.filter
        (·.isPublic)).length < 2 →
      RunarVerification.Stack.AgreesStateful.statefulFullConsumeShapeBool
          RunarVerification.Stack.LoopBridge.loopOkProg.properties
          RunarVerification.Stack.LoopBridge.loopOkM = true →
        ∃ (pre sats stateVal pn : String) (tyS tyV tyP : ANFType)
          (ctx : Stack.TxContext)
          (sigV preimage cpV sv8 var2 sats8 : ByteArray) (svV satsV : Int)
          (rest : List RunarVerification.ANF.Eval.Value),
          RunarVerification.Stack.LoopBridge.loopOkM.params
            = [ANFParam.mk sats tyS, ANFParam.mk stateVal tyV,
            ANFParam.mk pre tyP] ∧
          RunarVerification.Stack.LoopBridge.loopOkM.body
            = Stack.AgreesStateful.statefulFullBody pre sats stateVal ∧
          RunarVerification.Stack.LoopBridge.loopOkProg.properties.filter
              (fun pp => !pp.readonly)
            = [{ name := pn, type := .bigint, readonly := false }] ∧
          Stack.AgreesStateful.statefulFullNamesOk pre sats stateVal = true ∧
          Stack.ValidTxContext ctx ∧
          preimage = Stack.TxContext.buildPreimage ctx ∧
          initialAnf.resolveRef pre = some (.vBytes preimage) ∧
          initialAnf.resolveRef sats = some (.vBigint satsV) ∧
          initialAnf.resolveRef stateVal = some (.vBigint svV) ∧
          initialStack.stack = .vBytes preimage :: .vBigint svV
            :: .vBigint satsV :: .vBytes sigV :: .vBytes cpV :: rest ∧
          Stack.num2binEncode? svV 8 = some sv8 ∧ sv8.size = 8 ∧
          cpV.size + 9 < 253 ∧
          Stack.num2binEncode?
            ((Stack.AgreesStateful.epiAcc cpV sv8).size : Int) 2 = some var2 ∧
          1 ≤ var2.size ∧
          Stack.num2binEncode? satsV 8 = some sats8 ∧
          RunarVerification.ANF.Eval.Crypto.authBackend.checkSig sigV
              Stack.AgreesStateful.stG
            = RunarVerification.ANF.Eval.Crypto.checkPreimage preimage)
    (hDispatchFrag :
      dispatchConsumeShapeBool RunarVerification.Stack.LoopBridge.loopOkProg = true →
        ∃ (i : Nat) (rest : List RunarVerification.ANF.Eval.Value)
          (v : RunarVerification.ANF.Eval.Value),
          (RunarVerification.Stack.LoopBridge.loopOkProg.methods.filter (·.isPublic))[i]?
            = some RunarVerification.Stack.LoopBridge.loopOkM ∧
          initialStack.stack = .vBigint (Int.ofNat i) :: rest ∧
          ∀ (x : String) (ty : ANFType),
            RunarVerification.Stack.LoopBridge.loopOkM.params = [ANFParam.mk x ty] →
            initialAnf.lookupParam x = some v)
    (hDispatchMixedFrag :
      dispatchMixedConsumeShapeBool RunarVerification.Stack.LoopBridge.loopOkProg = true →
        ∃ (i : Nat) (rest : List RunarVerification.ANF.Eval.Value),
          (RunarVerification.Stack.LoopBridge.loopOkProg.methods.filter (·.isPublic))[i]?
            = some RunarVerification.Stack.LoopBridge.loopOkM ∧
          initialStack.stack = .vBigint (Int.ofNat i) :: rest ∧
          (dispatchPassthroughMethodBool RunarVerification.Stack.LoopBridge.loopOkM = true →
            ∃ (x bn : String) (ty : ANFType) (src : Option SourceLoc)
              (v : RunarVerification.ANF.Eval.Value),
              RunarVerification.Stack.LoopBridge.loopOkM.params = [ANFParam.mk x ty] ∧
              RunarVerification.Stack.LoopBridge.loopOkM.body
                = [ANFBinding.mk bn (.loadParam x) src] ∧
              initialAnf.lookupParam x = some v) ∧
          (dispatchHashLockMethodBool RunarVerification.Stack.LoopBridge.loopOkM = true →
            ∃ (d ok anm arg expected func : String) (tyE tyA : ANFType)
              (s1 s2 s3 : Option SourceLoc) (argB expB : ByteArray)
              (rest' : List RunarVerification.ANF.Eval.Value),
              RunarVerification.Stack.LoopBridge.loopOkM.params
                = [ANFParam.mk expected tyE, ANFParam.mk arg tyA] ∧
              RunarVerification.Stack.LoopBridge.loopOkM.body
                = RunarVerification.Stack.AgreesHashCall.hashAssertBody
                d ok anm arg expected func s1 s2 s3 ∧
              (func = "sha256" ∨ func = "hash160") ∧
              RunarVerification.Stack.AgreesHashCall.hashAssertNamesOk
                d ok arg expected = true ∧
              initialAnf.resolveRef arg = some (.vBytes argB) ∧
              initialAnf.resolveRef expected = some (.vBytes expB) ∧
              rest = .vBytes argB :: .vBytes expB :: rest' ∧
              argB.size ≤ 520))
    (hValueTruthy :
      statefulFullDischargedB RunarVerification.Stack.LoopBridge.loopOkProg
          RunarVerification.Stack.LoopBridge.loopOkM = false →
      Lower.bodyEndsInAssert RunarVerification.Stack.LoopBridge.loopOkM.body = false →
      ∀ s, runParsedBytes bytes initialStack = .ok s →
        topTruthy s.stack = true)
    (hCoh : Agrees.tsmCoherent initialAnf tsm) :
    acceptAgrees
      (RunarVerification.ANF.Eval.evalBindingsP
        RunarVerification.Stack.LoopBridge.loopOkProg.methods initialAnf
        RunarVerification.Stack.LoopBridge.loopOkM.body)
      (runParsedBytes bytes initialStack) :=
  compileSafe_observational_correct_modulo_codegen_axioms_with_loop
    RunarVerification.Stack.LoopBridge.loopOkProg hWF
    RunarVerification.Stack.LoopBridge.loopOkM bytes hMem rfl hSafe
    initialAnf initialStack tsm hAgrees
    -- The RIGHT disjunct of the gate fires the loop consume theorem.
    (Or.inr ⟨rfl, rfl, 0, [], hAnf, hStk⟩)
    Γ hUntag hTypedEntry hTsmTyped hIfValTyped hMathByteFrag hMathByteCatFrag
    hUpdatePropFrag hMethodCallFrag hHashCallFrag hHashAssertFrag hHashChainFrag
    hStatefulFrag hStatefulFullFrag hDispatchFrag hDispatchMixedFrag hValueTruthy hCoh

end RunarVerification.Pipeline.Soundness
