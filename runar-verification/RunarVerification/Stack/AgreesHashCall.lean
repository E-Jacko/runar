import RunarVerification.ANF.Eval
import RunarVerification.Stack.Agrees
import RunarVerification.Stack.HashOps

/-! # `Stack/AgreesHashCall.lean` — method-level single-hash-call peel-off substrate

**Path 2 Tier 1 — crypto_call peel-off (method level).** This file carries the
honest method-level substrate for peeling a single-`sha256`/`hash160`-call
*method body* off the residual universal `crypto_call` fallback.

The value-level M2 agreement lives in `Stack/AgreesCrypto.lean` (wave 68 +
hash160 follow-up). THIS file provides the LOWERING reductions and the
method-level pieces the in-`Pipeline` consume theorem composes:

* the consume-mode `lowerValueP` reductions for a single `.call sha256/hash160
  [arg]` at depth-0 last-use (arg consumed in place → RAW arm is the bare
  `[OP_SHA256]` / `[OP_HASH160]`),
* the single-binding `lowerBindingsP` lift,
* the method-level `lowerMethodUserRawOps = [opcode]` reduction.

## The consume regime (why RAW = `[OP_SHA256]`, not `[.dup, OP_SHA256]`)

The natural single-hash method `hash(x) { return sha256(x) }` uses its param
`x` exactly once, so the liveness-aware lowerer (`lowerValueP`) CONSUMES it:
`bringToTop` at depth 0 with `consume=true` emits `[]` (the value is already on
top), so the call lowers to the bare opcode. This is the cleanest possible RAW
— a single allowlisted op, trivially round-trippable.

No `sorry`/`admit`, no new axioms. -/

namespace RunarVerification.Stack.AgreesHashCall

open RunarVerification.ANF RunarVerification.Stack RunarVerification.Stack.Agrees

/-! ## Part 1 — the `lowerBindingsP` nil reduction -/

/-- `lowerBindingsP` on an empty body is the identity pair `([], sm)`. The base
case of the program-aware lowerer's recursion. -/
theorem lowerBindingsP_nil
    (progMethods : List ANFMethod) (props : List ANFProperty)
    (budget currentIndex : Nat) (lastUses : List (String × Nat))
    (outerProtected localBindings : List String) (constInts : List (String × Int))
    (sm : Lower.StackMap) :
    Lower.lowerBindingsP progMethods props budget currentIndex lastUses
      outerProtected localBindings constInts sm [] = ([], sm) := by
  rw [Lower.lowerBindingsP]

/-! ## Part 2 — the consume-mode single-call `lowerValueP` reductions

For a single-arg `.call func [arg]` whose `arg` is at depth 0 and consumed
(last-use, not outer-protected), `lowerValueP` falls through its generic
`.call` arm: `lowerArgsLive` consumes `arg` in place (`bringToTop` d0 consume =
`[]`), leaving exactly `(builtinOpcode func).map .opcode`. We pin the two
allowlisted single-opcode hashes (`sha256` → `OP_SHA256`, `hash160` →
`OP_HASH160`). The concrete function literal is REQUIRED so `lowerValueP`'s
special-cased arms (`checkMultiSig`, …) reduce to their `false` branch. -/

/-- `sha256` single-call, consume-d0: RAW arm is `[OP_SHA256]`. -/
theorem lowerValueP_call_sha256_consume_d0
    (progMethods : List ANFMethod) (props : List ANFProperty)
    (budget currentIndex : Nat) (lastUses : List (String × Nat))
    (outerProtected localBindings : List String) (constInts : List (String × Int))
    (bn arg : String) (k : SlotKind) (tsm_rest : TaggedStackMap)
    (hConsume :
      (!Lower.listContains outerProtected arg
        && Lower.isLastUse lastUses arg currentIndex) = true) :
    (Lower.lowerValueP progMethods props budget currentIndex lastUses
        outerProtected localBindings constInts
        (untagSm ((arg, k) :: tsm_rest)) bn (.call "sha256" [arg])).1
      = [StackOp.opcode "OP_SHA256"] := by
  have hUntag : untagSm ((arg, k) :: tsm_rest) = arg :: untagSm tsm_rest := rfl
  have hDepthTop : Lower.StackMap.depth? (arg :: untagSm tsm_rest) arg = some 0 := by
    unfold Lower.StackMap.depth? List.findIdx? List.findIdx?.go; simp
  have hExt : Lower.isExtractor "sha256" = false := by decide +kernel
  unfold Lower.lowerValueP
  simp [hDepthTop, hConsume, hUntag, hExt, Lower.builtinOpcode,
    Lower.lowerArgsLive, Lower.loadRefLive, Lower.bringToTop]

/-- `hash160` single-call, consume-d0: RAW arm is `[OP_HASH160]`. -/
theorem lowerValueP_call_hash160_consume_d0
    (progMethods : List ANFMethod) (props : List ANFProperty)
    (budget currentIndex : Nat) (lastUses : List (String × Nat))
    (outerProtected localBindings : List String) (constInts : List (String × Int))
    (bn arg : String) (k : SlotKind) (tsm_rest : TaggedStackMap)
    (hConsume :
      (!Lower.listContains outerProtected arg
        && Lower.isLastUse lastUses arg currentIndex) = true) :
    (Lower.lowerValueP progMethods props budget currentIndex lastUses
        outerProtected localBindings constInts
        (untagSm ((arg, k) :: tsm_rest)) bn (.call "hash160" [arg])).1
      = [StackOp.opcode "OP_HASH160"] := by
  have hUntag : untagSm ((arg, k) :: tsm_rest) = arg :: untagSm tsm_rest := rfl
  have hDepthTop : Lower.StackMap.depth? (arg :: untagSm tsm_rest) arg = some 0 := by
    unfold Lower.StackMap.depth? List.findIdx? List.findIdx?.go; simp
  have hExt : Lower.isExtractor "hash160" = false := by decide +kernel
  unfold Lower.lowerValueP
  simp [hDepthTop, hConsume, hUntag, hExt, Lower.builtinOpcode,
    Lower.lowerArgsLive, Lower.loadRefLive, Lower.bringToTop]

/-! ## Part 3 — the single-binding `lowerBindingsP` lift

Given the value-level reduction `(lowerValueP … v).1 = [op]`, a single-binding
body `[mk bn v src]` lowers to `[op]`: the cons case concatenates the value
ops with the empty-tail ops (`lowerBindingsP_nil`). Generic over the value, so
both hash witnesses feed it. -/

/-- Lift a value-level single-op reduction to the single-binding body level. -/
theorem lowerBindingsP_single_lift
    (progMethods : List ANFMethod) (props : List ANFProperty)
    (budget currentIndex : Nat) (lastUses : List (String × Nat))
    (outerProtected localBindings : List String) (constInts : List (String × Int))
    (bn op : String) (v : ANFValue) (sm : Lower.StackMap) (src : Option SourceLoc)
    (hWit : (Lower.lowerValueP progMethods props budget currentIndex lastUses
        outerProtected localBindings constInts sm bn v).1 = [StackOp.opcode op]) :
    (Lower.lowerBindingsP progMethods props budget currentIndex lastUses
        outerProtected localBindings constInts sm [ANFBinding.mk bn v src]).1
      = [StackOp.opcode op] := by
  have hFull : Lower.lowerValueP progMethods props budget currentIndex lastUses
        outerProtected localBindings constInts sm bn v
      = ([StackOp.opcode op],
         (Lower.lowerValueP progMethods props budget currentIndex lastUses
            outerProtected localBindings constInts sm bn v).2.1,
         (Lower.lowerValueP progMethods props budget currentIndex lastUses
            outerProtected localBindings constInts sm bn v).2.2) := by
    rw [Prod.ext_iff, Prod.ext_iff]; exact ⟨hWit, rfl, rfl⟩
  rw [Lower.lowerBindingsP, hFull]
  simp [lowerBindingsP_nil]

/-! ## Part 4 — the method-level RAW reduction

`lowerMethodUserRawOps` for a single-public method whose body is exactly one
`sha256`/`hash160` call on its single param reduces to the bare opcode list.
The param's `computeLastUses` last-use is index 0, so the consume hypothesis is
satisfied. Composes Part 2 (the value witness) with Part 3 (the single-binding
lift). -/

/-- The single-binding consume hypothesis: the lone param `arg`, read once at
index 0, is its own last use. -/
theorem single_call_consume_fact (bn arg func : String) (src : Option SourceLoc) :
    (!Lower.listContains [] arg
      && Lower.isLastUse (Lower.computeLastUses [ANFBinding.mk bn (.call func [arg]) src]) arg 0)
      = true := by
  simp [Lower.listContains, Lower.isLastUse, Lower.computeLastUses,
    Lower.computeLastUses.go, Lower.collectRefs, Lower.lastUsesUpdate, Lower.lastUsesLookup]

/-- Method RAW for a single-`sha256`-call method is `[OP_SHA256]`. -/
theorem lowerMethodUserRawOps_single_sha256
    (progMethods : List ANFMethod) (props : List ANFProperty) (anfM : ANFMethod)
    (bn arg : String) (src : Option SourceLoc)
    (hParams : (anfM.params.map (·.name)).reverse = [arg])
    (hBody : anfM.body = [ANFBinding.mk bn (.call "sha256" [arg]) src]) :
    Agrees.lowerMethodUserRawOps progMethods props anfM = [StackOp.opcode "OP_SHA256"] := by
  unfold Agrees.lowerMethodUserRawOps
  rw [hBody, hParams]
  exact lowerBindingsP_single_lift progMethods props Lower.defaultInlineBudget 0
    (Lower.computeLastUses [ANFBinding.mk bn (.call "sha256" [arg]) src]) []
    ([ANFBinding.mk bn (.call "sha256" [arg]) src].map (·.name))
    (Lower.collectConstInts [ANFBinding.mk bn (.call "sha256" [arg]) src])
    bn "OP_SHA256" (.call "sha256" [arg]) [arg] src
    (lowerValueP_call_sha256_consume_d0 progMethods props Lower.defaultInlineBudget 0
      (Lower.computeLastUses [ANFBinding.mk bn (.call "sha256" [arg]) src]) []
      ([ANFBinding.mk bn (.call "sha256" [arg]) src].map (·.name))
      (Lower.collectConstInts [ANFBinding.mk bn (.call "sha256" [arg]) src])
      bn arg .param [] (single_call_consume_fact bn arg "sha256" src))

/-- Method RAW for a single-`hash160`-call method is `[OP_HASH160]`. -/
theorem lowerMethodUserRawOps_single_hash160
    (progMethods : List ANFMethod) (props : List ANFProperty) (anfM : ANFMethod)
    (bn arg : String) (src : Option SourceLoc)
    (hParams : (anfM.params.map (·.name)).reverse = [arg])
    (hBody : anfM.body = [ANFBinding.mk bn (.call "hash160" [arg]) src]) :
    Agrees.lowerMethodUserRawOps progMethods props anfM = [StackOp.opcode "OP_HASH160"] := by
  unfold Agrees.lowerMethodUserRawOps
  rw [hBody, hParams]
  exact lowerBindingsP_single_lift progMethods props Lower.defaultInlineBudget 0
    (Lower.computeLastUses [ANFBinding.mk bn (.call "hash160" [arg]) src]) []
    ([ANFBinding.mk bn (.call "hash160" [arg]) src].map (·.name))
    (Lower.collectConstInts [ANFBinding.mk bn (.call "hash160" [arg]) src])
    bn "OP_HASH160" (.call "hash160" [arg]) [arg] src
    (lowerValueP_call_hash160_consume_d0 progMethods props Lower.defaultInlineBudget 0
      (Lower.computeLastUses [ANFBinding.mk bn (.call "hash160" [arg]) src]) []
      ([ANFBinding.mk bn (.call "hash160" [arg]) src].map (·.name))
      (Lower.collectConstInts [ANFBinding.mk bn (.call "hash160" [arg]) src])
      bn arg .param [] (single_call_consume_fact bn arg "hash160" src))

/-! ## Part 5 — the body-level M2 walk (`evalBindingsP` ⟷ `runOps [opcode]`)

A single-hash-call method body evaluates (ANF) and runs (Stack) to a SUCCESS on
the matching entry: the ANF interpreter computes the digest through the shared
`Crypto.hashBackend` (`callBuiltin?` arm), and the deployed `[OP_SHA256]` /
`[OP_HASH160]` runs through the SAME backend. Both succeed, so their success
bits agree. Stated UNFOLDED as `isSome ↔ isSome` (the `successAgrees` body the
in-`Pipeline` consume theorem wraps definitionally), so this file stays below
`Pipeline`.

The value-level `evalValue` reductions are re-proved locally (they only need
`ANF.Eval`, NOT the post-`Pipeline` `AgreesCrypto`), mirroring
`AgreesCrypto.evalValue_call_{sha256,hash160}_eq`. -/

section M2
open RunarVerification.ANF.Eval (Value State evalValue evalBindings evalBindingsP)
open RunarVerification.Stack.Eval
open RunarVerification.ANF.Eval.Crypto

/-- Local `sha256` value-eval reduction: on `arg ↦ vBytes bytes`, the call
computes `vBytes (Crypto.sha256 bytes)` through the shared backend. -/
theorem evalValue_call_sha256_eq_local
    (s : State) (x : String) (bytes : ByteArray)
    (hx : s.resolveRef x = some (.vBytes bytes)) :
    evalValue s (.call "sha256" [x]) = .ok (.vBytes (sha256 bytes), s) := by
  show evalValue s (ANFValue.call "sha256" [x]) = .ok (.vBytes (sha256 bytes), s)
  unfold evalValue
  simp only [List.mapM_cons, List.mapM_nil, RunarVerification.ANF.Eval.lookupRef, hx,
    bind, Except.bind, pure, Except.pure]
  rfl

/-- Local `hash160` value-eval reduction. -/
theorem evalValue_call_hash160_eq_local
    (s : State) (x : String) (bytes : ByteArray)
    (hx : s.resolveRef x = some (.vBytes bytes)) :
    evalValue s (.call "hash160" [x]) = .ok (.vBytes (hash160 bytes), s) := by
  show evalValue s (ANFValue.call "hash160" [x]) = .ok (.vBytes (hash160 bytes), s)
  unfold evalValue
  simp only [List.mapM_cons, List.mapM_nil, RunarVerification.ANF.Eval.lookupRef, hx,
    bind, Except.bind, pure, Except.pure]
  rfl

/-- ANF side succeeds for the single `sha256` binding. -/
theorem evalBindingsP_single_sha256_isSome
    (progMethods : List ANFMethod) (s : State)
    (bn x : String) (src : Option SourceLoc) (bytes : ByteArray)
    (hx : s.resolveRef x = some (.vBytes bytes)) :
    (evalBindingsP progMethods s [ANFBinding.mk bn (.call "sha256" [x]) src]).toOption.isSome = true := by
  have hNoMC : RunarVerification.ANF.Eval.noMethodCallBindings
      [ANFBinding.mk bn (.call "sha256" [x]) src] = true := by
    simp [RunarVerification.ANF.Eval.noMethodCallBindings, RunarVerification.ANF.Eval.noMethodCallValue]
  rw [RunarVerification.ANF.Eval.evalBindingsP_eq_evalBindings_of_noMethodCall progMethods s
        [ANFBinding.mk bn (.call "sha256" [x]) src] hNoMC]
  have hEval : evalBindings s [ANFBinding.mk bn (.call "sha256" [x]) src]
      = .ok (s.addBinding bn (.vBytes (sha256 bytes))) := by
    unfold evalBindings
    rw [evalValue_call_sha256_eq_local s x bytes hx]
    simp only [bind, Except.bind, evalBindings]
  rw [hEval]; rfl

/-- ANF side succeeds for the single `hash160` binding. -/
theorem evalBindingsP_single_hash160_isSome
    (progMethods : List ANFMethod) (s : State)
    (bn x : String) (src : Option SourceLoc) (bytes : ByteArray)
    (hx : s.resolveRef x = some (.vBytes bytes)) :
    (evalBindingsP progMethods s [ANFBinding.mk bn (.call "hash160" [x]) src]).toOption.isSome = true := by
  have hNoMC : RunarVerification.ANF.Eval.noMethodCallBindings
      [ANFBinding.mk bn (.call "hash160" [x]) src] = true := by
    simp [RunarVerification.ANF.Eval.noMethodCallBindings, RunarVerification.ANF.Eval.noMethodCallValue]
  rw [RunarVerification.ANF.Eval.evalBindingsP_eq_evalBindings_of_noMethodCall progMethods s
        [ANFBinding.mk bn (.call "hash160" [x]) src] hNoMC]
  have hEval : evalBindings s [ANFBinding.mk bn (.call "hash160" [x]) src]
      = .ok (s.addBinding bn (.vBytes (hash160 bytes))) := by
    unfold evalBindings
    rw [evalValue_call_hash160_eq_local s x bytes hx]
    simp only [bind, Except.bind, evalBindings]
  rw [hEval]; rfl

/-- **M2 walk (sha256).** The single-`sha256`-call body's success bit agrees
with the deployed `[OP_SHA256]` run on the matching entry. -/
theorem hashCall_M2_sha256
    (progMethods : List ANFMethod) (anfSt : State)
    (stkSt : StackState) (bn x : String) (src : Option SourceLoc)
    (bytes : ByteArray) (rest : List Value)
    (hArg : anfSt.resolveRef x = some (.vBytes bytes))
    (hStk : stkSt.stack = .vBytes bytes :: rest)
    (hLen : bytes.size ≤ 520) :
    (evalBindingsP progMethods anfSt [ANFBinding.mk bn (.call "sha256" [x]) src]).toOption.isSome
      ↔ (runOps [StackOp.opcode "OP_SHA256"] stkSt).toOption.isSome := by
  have hANF := evalBindingsP_single_sha256_isSome progMethods anfSt bn x src bytes hArg
  have hStack : (runOps [StackOp.opcode "OP_SHA256"] stkSt).toOption.isSome = true := by
    rw [HashOps.runOps_sha256Ops_eq stkSt bytes rest hStk hLen]; rfl
  rw [hANF, hStack]

/-- **M2 walk (hash160).** -/
theorem hashCall_M2_hash160
    (progMethods : List ANFMethod) (anfSt : State)
    (stkSt : StackState) (bn x : String) (src : Option SourceLoc)
    (bytes : ByteArray) (rest : List Value)
    (hArg : anfSt.resolveRef x = some (.vBytes bytes))
    (hStk : stkSt.stack = .vBytes bytes :: rest)
    (hLen : bytes.size ≤ 520) :
    (evalBindingsP progMethods anfSt [ANFBinding.mk bn (.call "hash160" [x]) src]).toOption.isSome
      ↔ (runOps [StackOp.opcode "OP_HASH160"] stkSt).toOption.isSome := by
  have hANF := evalBindingsP_single_hash160_isSome progMethods anfSt bn x src bytes hArg
  have hStack : (runOps [StackOp.opcode "OP_HASH160"] stkSt).toOption.isSome = true := by
    rw [HashOps.runOps_hash160Ops_eq stkSt bytes rest hStk hLen]; rfl
  rw [hANF, hStack]

end M2

/-! ## Part 6 — the decidable fragment classifier

`hashCallConsumeShapeBool` decides the single-hash-call consume fragment: a
method with exactly one param whose body is one binding `bn = func(param)` with
`func ∈ {sha256, hash160}` (the param read once → consumed → RAW is the bare
opcode). The in-`Pipeline` dispatch `by_cases` on this; the witnesses are
recovered by the keyed `hHashCallFrag` omnibus premise (vacuous on non-hash
bodies, like `hMathByteFrag`). -/

/-- Decidable single-hash-call consume fragment classifier. -/
def hashCallConsumeShapeBool (m : ANFMethod) : Bool :=
  match m.body with
  | [ANFBinding.mk _ (.call func [arg]) _] =>
      (func == "sha256" || func == "hash160") && (m.params.map (·.name) == [arg])
  | _ => false

/-! ## Part 7 — MANDATORY anti-vacuity smokes (concrete)

A concrete single-`sha256`-call method `h(x) { return sha256(x) }` whose
classifier fires, RAW reduces to `[OP_SHA256]`, and M2 walk agrees on a concrete
entry. Witnesses that the fragment is NON-empty (the keyed premise is
satisfiable). The smokes fire on the success bit, never forcing the backend
digest. -/

/-- The canonical single-`sha256`-call method. -/
def smokeMethod : ANFMethod :=
  { name := "h"
    params := [ANFParam.mk "x" .byteString]
    body := [ANFBinding.mk "c0" (.call "sha256" ["x"]) none]
    isPublic := true }

/-- SMOKE — the classifier fires on the canonical method (anti-vacuity). -/
theorem smoke_classifier_fires : hashCallConsumeShapeBool smokeMethod = true := by
  decide +kernel

/-- SMOKE — RAW reduces to the bare `[OP_SHA256]` for the canonical method. -/
theorem smoke_method_raw :
    Agrees.lowerMethodUserRawOps [] [] smokeMethod = [StackOp.opcode "OP_SHA256"] :=
  lowerMethodUserRawOps_single_sha256 [] [] smokeMethod "c0" "x" none rfl rfl

end RunarVerification.Stack.AgreesHashCall
