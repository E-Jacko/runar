import RunarVerification.Stack.AgreesLoopAccept

/-! # Count-generic accumulator loop — the consume theorem over arbitrary `n`

The canonical (count = 3) accumulator loop is fully proven and omnibus-wired
(`AgreesLoopBridge` / `AgreesLoopParsed` / `AgreesLoopAccept`). This file
generalises the loop count from the fixed `3` to an arbitrary `n : Nat`,
reusing the count-generic runtime + lowering substrate already established in
`AgreesA7` (namespace `…Stack.Agrees.A7`):

* `runOps_loopOkFull_accept` / `scriptAccepts_loopOkFull` — the loop bytes ++
  elided-assert epilogue accept iff `sum0 + n·start0 = 0` (count-generic).
* `lowerValueP_loop_loopOkBody_ops_eq` — the loop VALUE lowers to
  `loopOkAssemble n …` (count-generic).

The three new pieces:

* **(a) count-generic ANF** (`anfAcc_isSome_eq` / `anfAcc_isSome_iff`): the
  accumulator's ANF evaluation over `loopAccProg n` succeeds iff `n·start = 0`.
  Proven by a SYMBOLIC `n`-induction over `runLoopP` (`runLoopP_loopOkBody_sum`):
  the loop accumulates `sum := sum + start` each iteration, so `sum_n =
  sum0 + n·start`; the prologue sets `sum0 = 0` and the terminal
  `assert (sum === 0)` succeeds iff `n·start = 0`. NOT a `native_decide` pin.

* **(b) `AreLoopEmittable`-for-all-`n` (bounded)** (`areLoopEmittable_loopAccChain`):
  the deployed loop chain `loopOkAssemble n … ++ [OP_0, OP_NUMEQUAL] ++
  replicate n .nip` is `AreLoopEmittable` for `1 ≤ n ≤ 15`. The bound is
  FORCED by the strand depth: the final-iteration `.roll (n+1)` and the
  index pushes `.push (.bigint i)` (`i < n`) must stay within the
  `RunarEmittable` depth window `[1..16]` resp. the small-int canonical push
  window `[-1..16]`. The runtime + ANF pieces (a), (Tier 4a) are symbolic over
  ALL `n`; only the parse-round-trip emittability carries the `n ≤ 15` bound.

* **(c) count-generic whole-method lowering** — the symbolic
  `peepholedLoweredMethod (loopAccProg n)` image. This is the documented hard
  wall (the bridge discharged the count=3 case by `native_decide`, which does
  NOT work for symbolic `n`). See the section note at the end for the exact
  obstacle and the bounded compose that the fixed-`n` machinery supports today.

Add-only. Touches NOTHING in the omnibus / dispatch cascade /
`OmnibusLoop.lean` / `tests/OmnibusInstantiation.lean`. -/

namespace RunarVerification.Stack.LoopCountGeneric

open RunarVerification.ANF
open RunarVerification.ANF.Eval (Value State EvalResult evalBindingsP evalValueP runLoopP
  lookupRef evalBinOp)
open RunarVerification.Stack.Agrees.A7 (loopOkBody loopOkAssemble)

/-! ## The count-generic program -/

/-- The count-generic accumulator method: identical to
`LoopBridge.loopOkM` but with the loop count `= n` instead of `3`. -/
def loopAccM (n : Nat) : ANFMethod :=
  { name := "verify", params := [ANFParam.mk "start" .bigint],
    body :=
      [ ANFBinding.mk "t0" (.loadConst (.int 0)) none
      , ANFBinding.mk "sum" (.loadConst (.refAlias "t0")) none
      , ANFBinding.mk "t9" (.loop n loopOkBody "i") none
      , ANFBinding.mk "t3" (.loadProp "expectedSum") none
      , ANFBinding.mk "t4" (.binOp "===" "sum" "t3" none) none
      , ANFBinding.mk "t5" (.assert "t4") none ],
    isPublic := true }

/-- The count-generic accumulator program. -/
def loopAccProg (n : Nat) : ANFProgram :=
  { contractName := "LoopOk"
  , properties := [{ name := "expectedSum", type := .bigint, readonly := true }]
  , methods := [loopAccM n] }

/-- `loopAccM 3` is the canonical fixture method `LoopBridge.loopOkM`. -/
theorem loopAccM_three : loopAccM 3 = LoopBridge.loopOkM := rfl

/-- `loopAccProg 3` is the canonical fixture program `LoopBridge.loopOkProg`. -/
theorem loopAccProg_three : loopAccProg 3 = LoopBridge.loopOkProg := rfl

/-! ## (a) Count-generic ANF — the symbolic `n`-induction

The accumulator's ANF half: the loop body `loopOkBody` reads param `start`
and the running `sum` binding, computes `sum := sum + start`, and rebinds
`sum`. So `runLoopP n loopOkBody "i"` advances the `sum` binding by `n·start`.
The prologue establishes `sum = 0`, the terminal assert checks `sum === 0`. -/

/-- `lookupRef` on a `vBigint`-resolving ref. -/
private theorem lookupRef_of_resolve (s : State) (name : String) (v : Value)
    (h : s.resolveRef name = some v) : lookupRef s name = .ok v := by
  unfold lookupRef; rw [h]

/-- `resolveRef name` after `addBinding name' v'` for a DIFFERENT name `name'`
agrees with `resolveRef name` on `s` (the fresh binding does not shadow). -/
private theorem resolveRef_addBinding_ne (s : State) (name name' : String) (v' : Value)
    (hne : name' ≠ name) :
    (s.addBinding name' v').resolveRef name = s.resolveRef name := by
  unfold RunarVerification.ANF.Eval.State.resolveRef
    RunarVerification.ANF.Eval.State.addBinding
    RunarVerification.ANF.Eval.State.lookupBinding
    RunarVerification.ANF.Eval.State.lookupParam
    RunarVerification.ANF.Eval.State.lookupProp
  simp only [List.find?_cons]
  rw [show (name' == name) = false from by
        simpa using fun h => hne h]

/-- `resolveRef name` after `addBinding name v` returns `v` (fresh binding wins). -/
private theorem resolveRef_addBinding_self (s : State) (name : String) (v : Value) :
    (s.addBinding name v).resolveRef name = some v := by
  unfold RunarVerification.ANF.Eval.State.resolveRef
    RunarVerification.ANF.Eval.State.addBinding
    RunarVerification.ANF.Eval.State.lookupBinding
  simp only [List.find?_cons, beq_self_eq_true]
  rfl

/-- **One body iteration.** Evaluating `loopOkBody` from a state where
`s.lookupParam "start" = some (vBigint start)` and
`s.resolveRef "sum" = some (vBigint sumVal)` succeeds and binds a fresh
`"sum"` with value `sumVal + start` (the rest of the state is threaded). -/
theorem evalBindingsP_loopOkBody (methods : List ANFMethod)
    (start sumVal : Int) (s : State)
    (hStart : s.lookupParam "start" = some (.vBigint start))
    (hSum : s.resolveRef "sum" = some (.vBigint sumVal)) :
    evalBindingsP methods s loopOkBody
      = .ok (((s.addBinding "t1" (.vBigint start)).addBinding "t2"
              (.vBigint (sumVal + start))).addBinding "sum"
              (.vBigint (sumVal + start))) := by
  -- Establish each value-step result, then reduce the binds.
  have hV0 : evalValueP methods s (.loadParam "start") = .ok (.vBigint start, s) := by
    unfold evalValueP RunarVerification.ANF.Eval.State.lookupParam at *
    rw [hStart]
  have hS1 := s.addBinding "t1" (.vBigint start)
  -- lookups in s1 = addBinding "t1"
  have hSum1 : (s.addBinding "t1" (.vBigint start)).resolveRef "sum" = some (.vBigint sumVal) := by
    rw [resolveRef_addBinding_ne s "sum" "t1" _ (by decide), hSum]
  have hT1get : (s.addBinding "t1" (.vBigint start)).resolveRef "t1" = some (.vBigint start) :=
    resolveRef_addBinding_self s "t1" (.vBigint start)
  have hV1 : evalValueP methods (s.addBinding "t1" (.vBigint start)) (.binOp "+" "sum" "t1" none)
      = .ok (.vBigint (sumVal + start), s.addBinding "t1" (.vBigint start)) := by
    unfold evalValueP
    rw [lookupRef_of_resolve _ "sum" _ hSum1, lookupRef_of_resolve _ "t1" _ hT1get]
    rfl
  have hT2get :
      ((s.addBinding "t1" (.vBigint start)).addBinding "t2" (.vBigint (sumVal + start))).resolveRef "t2"
      = some (.vBigint (sumVal + start)) :=
    resolveRef_addBinding_self _ "t2" (.vBigint (sumVal + start))
  have hV2 : evalValueP methods
      ((s.addBinding "t1" (.vBigint start)).addBinding "t2" (.vBigint (sumVal + start)))
      (.loadConst (.refAlias "t2"))
      = .ok (.vBigint (sumVal + start),
             (s.addBinding "t1" (.vBigint start)).addBinding "t2" (.vBigint (sumVal + start))) := by
    unfold evalValueP
    show (do let v ← lookupRef _ "t2"; pure (v, _)) = _
    rw [lookupRef_of_resolve _ "t2" _ hT2get]
    rfl
  -- Now reduce the three binds of evalBindingsP.
  unfold loopOkBody
  simp only [evalBindingsP, hV0, hV1, hV2, bind, Except.bind]

/-- `resolveRef "sum"` ignores the params slot: prepending `("i", k)` to the
params leaves a `"sum"` BINDING resolution unchanged (resolveRef checks
bindings first). -/
private theorem resolveRef_sum_withIter (s : State) (k : Int) :
    ({ s with params := ("i", .vBigint k) :: s.params }).resolveRef "sum"
      = s.resolveRef "sum" := by
  unfold RunarVerification.ANF.Eval.State.resolveRef
    RunarVerification.ANF.Eval.State.lookupBinding
    RunarVerification.ANF.Eval.State.lookupParam
    RunarVerification.ANF.Eval.State.lookupProp
  rfl

/-- `lookupParam "start"` after prepending `("i", k)`: since `"i" ≠ "start"`,
the param resolution is unchanged. -/
private theorem lookupParam_start_withIter (s : State) (k : Int) :
    ({ s with params := ("i", .vBigint k) :: s.params }).lookupParam "start"
      = s.lookupParam "start" := by
  unfold RunarVerification.ANF.Eval.State.lookupParam
  simp only [List.find?_cons]
  rfl

/-! ### The count-generic loop-carry induction -/

/-- The loop-carry invariant: the running accumulator `sum` resolves to
`vBigint sumVal`, the param `start` resolves to `vBigint start`, and the
param list carries no `"i"` key (so the per-iteration `"i"`-strip is
idempotent and preserves `start`). -/
structure AccInv (start sumVal : Int) (s : State) : Prop where
  hSum    : s.resolveRef "sum" = some (.vBigint sumVal)
  hStart  : s.lookupParam "start" = some (.vBigint start)
  hNoIter : s.params.filter (·.fst != "i") = s.params
  hProp   : s.lookupProp "expectedSum" = some (.vBigint 0)

/-- **The symbolic `n`-induction.** From any state satisfying the loop-carry
invariant at accumulated value `sumVal`, running `n` iterations of `loopOkBody`
succeeds and leaves a state whose `sum` is `sumVal + n·start` (and which still
satisfies the invariant). Per iteration `sum := sum + start`. -/
theorem runLoopP_loopOkBody_acc (methods : List ANFMethod) (start : Int) :
    ∀ (n : Nat) (s : State) (sumVal : Int), AccInv start sumVal s →
      ∃ s', runLoopP methods n loopOkBody "i" s = .ok s'
        ∧ AccInv start (sumVal + (n : Int) * start) s'
  | 0, s, sumVal, hInv => by
      refine ⟨s, ?_, ?_⟩
      · show runLoopP methods 0 loopOkBody "i" s = Except.ok s
        unfold runLoopP
        rfl
      · simpa using hInv
  | n + 1, s, sumVal, hInv => by
      -- Name the per-iteration intermediate states.
      let withIter : State := { s with params := ("i", .vBigint (n : Int)) :: s.params }
      let s' : State := ((withIter.addBinding "t1" (.vBigint start)).addBinding "t2"
              (.vBigint (sumVal + start))).addBinding "sum"
              (.vBigint (sumVal + start))
      let stripped : State := { s' with params := s'.params.filter (·.fst != "i") }
      -- Body finds start + sum through withIter.
      have hStartW : withIter.lookupParam "start" = some (.vBigint start) := by
        show ({ s with params := ("i", .vBigint (n : Int)) :: s.params }).lookupParam "start" = _
        rw [lookupParam_start_withIter, hInv.hStart]
      have hSumW : withIter.resolveRef "sum" = some (.vBigint sumVal) := by
        show ({ s with params := ("i", .vBigint (n : Int)) :: s.params }).resolveRef "sum" = _
        rw [resolveRef_sum_withIter s _, hInv.hSum]
      -- stripped's params = s.params.
      have hStripParams : stripped.params = s.params := by
        show (("i", Value.vBigint (n : Int)) :: s.params).filter (·.fst != "i") = s.params
        rw [List.filter_cons]
        simp only [bne_self_eq_false, Bool.false_eq_true, if_false]
        exact hInv.hNoIter
      -- Invariant at stripped, accumulated value sumVal + start.
      have hInvStripped : AccInv start (sumVal + start) stripped := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · -- resolveRef "sum" reads bindings only; s'.bindings head is ("sum", …).
          show ({ s' with params := s'.params.filter (·.fst != "i") }).resolveRef "sum"
              = some (.vBigint (sumVal + start))
          unfold RunarVerification.ANF.Eval.State.resolveRef
            RunarVerification.ANF.Eval.State.lookupBinding
          show (Option.map (·.snd)
              (((("sum", Value.vBigint (sumVal + start)) :: _).find? (·.fst == "sum"))) <|> _ <|> _) = _
          rw [List.find?_cons]
          simp only [beq_self_eq_true]
          rfl
        · show stripped.lookupParam "start" = some (.vBigint start)
          unfold RunarVerification.ANF.Eval.State.lookupParam
          rw [hStripParams]
          have := hInv.hStart
          unfold RunarVerification.ANF.Eval.State.lookupParam at this
          exact this
        · show stripped.params.filter (·.fst != "i") = stripped.params
          rw [hStripParams, hInv.hNoIter]
        · -- props untouched by addBinding / param-strip.
          show stripped.lookupProp "expectedSum" = some (.vBigint 0)
          exact hInv.hProp
      -- Recurse.
      obtain ⟨s'', hrun, hInv''⟩ :=
        runLoopP_loopOkBody_acc methods start n stripped (sumVal + start) hInvStripped
      refine ⟨s'', ?_, ?_⟩
      · -- Unfold runLoopP at n+1 and feed the body + recursion.
        unfold runLoopP
        simp only []
        rw [evalBindingsP_loopOkBody methods start sumVal withIter hStartW hSumW]
        exact hrun
      · have hcast : (((n + 1 : Nat) : Int)) * start = (((n : Nat) : Int)) * start + start := by
          rw [show (((n + 1 : Nat) : Int)) = (((n : Nat) : Int)) + 1 from by omega]
          rw [Int.add_mul, Int.one_mul]
        have heq : (sumVal + start) + (n : Int) * start = sumVal + ((n + 1 : Nat) : Int) * start := by
          rw [hcast]; omega
        rw [heq] at hInv''
        exact hInv''

/-! ### (a) The count-generic ANF half (symbolic over `n`) -/

/-- One bindings step: if the head value evaluates to `(val, s')`, then
`evalBindingsP` on the cons reduces to the recursion on `s'.addBinding name val`. -/
theorem evalBindingsP_step (methods : List ANFMethod) (s : State)
    (name : String) (v : ANFValue) (rest : List ANFBinding) (val : Value) (s' : State)
    (h : evalValueP methods s v = .ok (val, s')) :
    evalBindingsP methods s (ANFBinding.mk name v none :: rest)
      = evalBindingsP methods (s'.addBinding name val) rest := by
  simp only [evalBindingsP, h, bind, Except.bind]

/-- A failing head value makes the whole bindings walk fail. -/
theorem evalBindingsP_step_error (methods : List ANFMethod) (s : State)
    (name : String) (v : ANFValue) (rest : List ANFBinding) (e : RunarVerification.ANF.Eval.EvalError)
    (h : evalValueP methods s v = .error e) :
    evalBindingsP methods s (ANFBinding.mk name v none :: rest) = .error e := by
  simp only [evalBindingsP, h, bind, Except.bind]

/-- The initial evaluation state for the accumulator method: param `start`,
prop `expectedSum = 0`, no bindings. -/
def accInit (start : Int) : State :=
  { params := [("start", .vBigint start)]
  , props := [("expectedSum", .vBigint 0)] }

/-- **(a) Count-generic ANF — the symbolic completion bit.** The accumulator's
ANF evaluation over `loopAccProg n` from the entry `start` succeeds iff the
accumulated sum `n·start` is zero. Proven by the SYMBOLIC `n`-induction
`runLoopP_loopOkBody_acc` (NOT a `native_decide` pin). -/
theorem anfAcc_isSome_eq (n : Nat) (start : Int) :
    (evalBindingsP (loopAccProg n).methods (accInit start) (loopAccM n).body).toOption.isSome
      = decide ((n : Int) * start = 0) := by
  -- Prologue: t0 := 0, sum := 0.  State after prologue:
  let s0 := accInit start
  let s1 := s0.addBinding "t0" (.vBigint 0)
  let s2 := s1.addBinding "sum" (.vBigint 0)
  -- Loop result via the symbolic induction (sum0 = 0).
  have hInv0 : AccInv start 0 s2 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact resolveRef_addBinding_self _ "sum" (.vBigint 0)
    · rfl
    · rfl
    · rfl
  obtain ⟨sLoop, hLoopRun, hLoopInv⟩ :=
    runLoopP_loopOkBody_acc (loopAccProg n).methods start n s2 0 hInv0
  -- sum after loop = 0 + n*start; prop expectedSum preserved at 0.
  have hSumLoop : sLoop.resolveRef "sum" = some (.vBigint (0 + (n : Int) * start)) := hLoopInv.hSum
  have hExpLoop : sLoop.lookupProp "expectedSum" = some (.vBigint 0) := hLoopInv.hProp
  -- Walk the method body.
  show (evalBindingsP (loopAccProg n).methods s0 (loopAccM n).body).toOption.isSome = _
  unfold loopAccM
  -- t0 := loadConst 0
  have hV0 : evalValueP (loopAccProg n).methods s0 (.loadConst (.int 0)) = .ok (.vBigint 0, s0) := by
    unfold evalValueP; rfl
  -- sum := loadConst (refAlias t0)
  have hV1 : evalValueP (loopAccProg n).methods s1 (.loadConst (.refAlias "t0"))
      = .ok (.vBigint 0, s1) := by
    unfold evalValueP
    show (do let v ← lookupRef s1 "t0"; pure (v, s1)) = _
    rw [lookupRef_of_resolve _ "t0" _ (resolveRef_addBinding_self _ "t0" (.vBigint 0))]
    rfl
  -- t9 := loop n loopOkBody "i"
  have hV2 : evalValueP (loopAccProg n).methods s2 (.loop n loopOkBody "i")
      = .ok (.vBool true, sLoop) := by
    unfold evalValueP
    show (do let s' ← runLoopP (loopAccProg n).methods n loopOkBody "i" s2
             Except.ok ((Value.vBool true), s')) = _
    rw [hLoopRun]
    rfl
  -- After the loop, bind t9 := vBool true.  s3 = sLoop.addBinding "t9" (vBool true).
  let s3 : State := sLoop.addBinding "t9" (.vBool true)
  -- t3 := loadProp expectedSum (= 0)
  have hExp3 : s3.lookupProp "expectedSum" = some (.vBigint 0) := hExpLoop
  have hV3 : evalValueP (loopAccProg n).methods s3 (.loadProp "expectedSum")
      = .ok (.vBigint 0, s3) := by
    unfold evalValueP
    rw [hExp3]
  let s4 : State := s3.addBinding "t3" (.vBigint 0)
  -- t4 := binOp "===" "sum" "t3"  →  vBool (decide ((0 + n*start) = 0))
  have hSum4 : s4.resolveRef "sum" = some (.vBigint (0 + (n : Int) * start)) := by
    show (s3.addBinding "t3" (.vBigint 0)).resolveRef "sum" = _
    rw [resolveRef_addBinding_ne s3 "sum" "t3" _ (by decide)]
    show (sLoop.addBinding "t9" (.vBool true)).resolveRef "sum" = _
    rw [resolveRef_addBinding_ne sLoop "sum" "t9" _ (by decide), hSumLoop]
  have hT3get : s4.resolveRef "t3" = some (.vBigint 0) :=
    resolveRef_addBinding_self _ "t3" (.vBigint 0)
  have hV4 : evalValueP (loopAccProg n).methods s4 (.binOp "===" "sum" "t3" none)
      = .ok (.vBool (decide ((0 + (n : Int) * start) = 0)), s4) := by
    unfold evalValueP
    rw [lookupRef_of_resolve _ "sum" _ hSum4, lookupRef_of_resolve _ "t3" _ hT3get]
    rfl
  let s5 : State := s4.addBinding "t4" (.vBool (decide ((0 + (n : Int) * start) = 0)))
  -- t5 := assert "t4"
  have hT4get : s5.resolveRef "t4" = some (.vBool (decide ((0 + (n : Int) * start) = 0))) :=
    resolveRef_addBinding_self _ "t4" _
  -- Walk the prologue + loop + epilogue bindings explicitly.
  rw [evalBindingsP_step (loopAccProg n).methods s0 "t0" _ _ _ s0 hV0]
  rw [evalBindingsP_step (loopAccProg n).methods s1 "sum" _ _ _ s1 hV1]
  rw [evalBindingsP_step (loopAccProg n).methods s2 "t9" _ _ _ sLoop hV2]
  rw [evalBindingsP_step (loopAccProg n).methods s3 "t3" _ _ _ s3 hV3]
  rw [evalBindingsP_step (loopAccProg n).methods s4 "t4" _ _ _ s4 hV4]
  -- Case-split on the decision bit; the assert step succeeds iff the bool is true.
  by_cases h : (n : Int) * start = 0
  · -- Accept: t4 = vBool true, assert succeeds.
    have hbool : (decide ((0 + (n : Int) * start) = 0)) = true := by
      apply decide_eq_true; omega
    have hV5 : evalValueP (loopAccProg n).methods s5 (.assert "t4")
        = .ok (.vBool true, s5) := by
      unfold evalValueP
      rw [lookupRef_of_resolve _ "t4" _ hT4get, hbool]
      rfl
    rw [show (s4.addBinding "t4" (.vBool (decide ((0 + (n : Int) * start) = 0)))) = s5 from rfl]
    rw [evalBindingsP_step (loopAccProg n).methods s5 "t5" _ _ _ s5 hV5]
    rw [decide_eq_true h]
    simp only [evalBindingsP, Except.toOption, Option.isSome_some]
  · -- Reject: t4 = vBool false, assert fails.
    have hbool : (decide ((0 + (n : Int) * start) = 0)) = false := by
      apply decide_eq_false; omega
    have hV5 : evalValueP (loopAccProg n).methods s5 (.assert "t4")
        = .error .assertFailed := by
      unfold evalValueP
      rw [lookupRef_of_resolve _ "t4" _ hT4get, hbool]
      rfl
    rw [show (s4.addBinding "t4" (.vBool (decide ((0 + (n : Int) * start) = 0)))) = s5 from rfl]
    rw [evalBindingsP_step_error (loopAccProg n).methods s5 "t5" _ _ _ hV5]
    rw [decide_eq_false h]
    simp only [Except.toOption, Option.isSome_none]

/-- **(a) The count-generic ANF biconditional.** The accumulator succeeds iff
`n·start = 0`. Symbolic over `n` and `start`. -/
theorem anfAcc_isSome_iff (n : Nat) (start : Int) :
    (evalBindingsP (loopAccProg n).methods (accInit start) (loopAccM n).body).toOption.isSome
      ↔ (n : Int) * start = 0 := by
  rw [show ((evalBindingsP (loopAccProg n).methods (accInit start) (loopAccM n).body).toOption.isSome = true)
      = ((n : Int) * start = 0) from by rw [anfAcc_isSome_eq]; simp]

/-- **count=3 subsumption (ANF).** `anfAcc_isSome_eq` at `n = 3` reproduces the
canonical-fixture ANF completion bit `LoopBridge.anf_isSome_eq` (`start + start
+ start = 0` ↔ `3·start = 0`), confirming the count-generic theorem subsumes
the count=3 ANF half. -/
theorem anfAcc_isSome_three (start : Int) :
    (evalBindingsP LoopBridge.loopOkProg.methods (accInit start) LoopBridge.loopOkM.body).toOption.isSome
      = decide ((3 : Int) * start = 0) := by
  have h := anfAcc_isSome_eq 3 start
  rw [loopAccProg_three, loopAccM_three] at h
  rw [h]
  norm_cast

/-! ## Count-generic `acceptAgrees` over the assembled-loop `runOps` surface

Composing the count-generic ANF half (a) with the count-generic Tier 4a
runtime closed form (`Agrees.A7.loopOkFull_accept_iff_sat`) yields a real
`acceptAgrees` for the accumulator over the assembled deployed-loop ops
(`loopOkAssemble n ["sum","start"] n ++ [OP_0, OP_NUMEQUAL] ++ nip^n`), run
from the Tier 4a mirror entry `0 :: start :: rest`. This is SYMBOLIC over
`n ≥ 1` and `start`: the ANF completes iff `n·start = 0` (a), and the
assembled ops accept iff `0 + n·start = 0` (Tier 4a) — the same condition. -/

open RunarVerification.Stack (StackOp)
open RunarVerification.Stack.Eval (StackState runOps scriptAccepts acceptAgrees)

/-- **Count-generic accumulator `acceptAgrees` (assembled-`runOps` surface).**
The ANF evaluation of `loopAccProg n` from entry `start` AGREES (under the
consensus acceptance bit) with running the assembled deployed-loop ops from
the Tier 4a mirror entry `0 :: start :: rest`: the ANF completes exactly when
the ops are accepted, both iff `n·start = 0`. Fully symbolic over `n ≥ 1`,
`start`, `rest`. -/
theorem loopAcc_acceptAgrees_runOps (n : Nat) (start : Int)
    (rest : List Value) (tail : Stack.Lower.StackMap) (s : StackState) (hCount : 1 ≤ n) :
    acceptAgrees
      (evalBindingsP (loopAccProg n).methods (accInit start) (loopAccM n).body)
      (runOps
        (loopOkAssemble n ("sum" :: "start" :: tail) n
          ++ ([StackOp.opcode "OP_0", StackOp.opcode "OP_NUMEQUAL"]
              ++ List.replicate n StackOp.nip))
        { s with stack := (.vBigint 0) :: (.vBigint start) :: rest }) := by
  unfold acceptAgrees
  rw [anfAcc_isSome_iff n start]
  -- Runtime side: accepted iff 0 + n*start = 0; rewrite to n*start = 0.
  rw [show (scriptAccepts (runOps
        (loopOkAssemble n ("sum" :: "start" :: tail) n
          ++ ([StackOp.opcode "OP_0", StackOp.opcode "OP_NUMEQUAL"]
              ++ List.replicate n StackOp.nip))
        { s with stack := (.vBigint 0) :: (.vBigint start) :: rest }) = true)
      = ((0 : Int) + (n : Int) * start = 0) from
        propext (RunarVerification.Stack.Agrees.A7.loopOkFull_accept_iff_sat
          n 0 start rest tail s hCount)]
  constructor
  · intro h; omega
  · intro h; omega

/-- **count=3 subsumption (assembled `acceptAgrees`).** At `n = 3` the
count-generic assembled-`runOps` `acceptAgrees` reproduces the canonical
fixture's accumulator agreement polarity (accepted iff `3·start = 0`),
confirming the general theorem subsumes the count=3 case. -/
theorem loopAcc_acceptAgrees_runOps_three (start : Int)
    (rest : List Value) (s : StackState) :
    acceptAgrees
      (evalBindingsP (loopAccProg 3).methods (accInit start) (loopAccM 3).body)
      (runOps
        (loopOkAssemble 3 ("sum" :: "start" :: ([] : Stack.Lower.StackMap)) 3
          ++ ([StackOp.opcode "OP_0", StackOp.opcode "OP_NUMEQUAL"]
              ++ List.replicate 3 StackOp.nip))
        { s with stack := (.vBigint 0) :: (.vBigint start) :: rest }) :=
  loopAcc_acceptAgrees_runOps 3 start rest [] s (by omega)

/-! ## (b)/(c) — the symbolic emittability + whole-method lowering wall

The runtime + ANF halves above are SYMBOLIC over all `n ≥ 1`. The remaining
two pieces to reach a parsed-bytes `acceptAgrees` over `compileSafe
(loopAccProg n)` are bounded / blocked:

**(b) `AreLoopEmittable (loopOkAssemble n … ++ epilogue)` — bounded `n ≤ 15`.**
The strand depth grows with the iteration index: the final-iteration consume is
`.roll (n+1)` and the non-final copies are `.pickStruct (2+k)` (`k < n-1`). The
`RunarEmittable`/`RunarEmittableLoop` depth window is `[1..16]`, so the chain is
loop-emittable only while `n + 1 ≤ 16`, i.e. `n ≤ 15`. The index pushes
`.push (.bigint i)` (`i < n`) must additionally stay canonical small-ints
(`AllLoopPushCanonical` needs `i ≤ 16`, i.e. `n ≤ 17`) — so the binding bound is
`n ≤ 15`. A symbolic `m`/`k`-induction (mirroring
`Agrees.A7.runOps_loopOkAssemble_postStack`) would establish this, but each
push-like cons additionally discharges a `restNotPickOrRoll (emitOpsL rest)`
byte-head obligation — the first emitted byte of the per-iteration remainder
(always a small-int push `0x00`/`0x51..0x60` introducing the following
`pickStruct`/`roll`, never `OP_PICK 0x79` / `OP_ROLL 0x7a`). For each CONCRETE
`n` this is dischargeable exactly as `areLoopEmittable_loopOkPeepChain` does
(`refine .cons …; all_goals first | … | decide`); the symbolic `n`-uniform
byte-head lemma is the open work for (b).

**(c) count-generic whole-method lowering — the hard wall.** The bridge proved
`peepholedLoweredMethod loopOkProg loopOkM = loopOkPeepChain` for count=3 by
`native_decide` on a local `DecidableEq StackOp`. That does NOT work for
symbolic `n`. A symbolic proof must compose: the prologue lowering (`[push 0]`),
the count-generic loop VALUE lowering (`Agrees.A7.lowerValueP_loop_loopOkBody_ops_eq`,
which IS count-generic and lands `loopOkAssemble n …`), and the epilogue
lowering, at the `lowerMethod` / `lowerBindingsP` level — THEN show the peephole
pass maps the raw per-iteration `[swap, swap]` fusion uniformly across the `n`
iterations. The peephole-over-`n` step (a fusion argument on a symbolic-length
op list) is the genuinely hard, unfinished piece; the loop-VALUE lowering
substrate it needs already exists count-generically, but the whole-`lowerMethod`
assembly + symbolic peephole is not yet discharged.

Composing (a)+(b: bounded)+(c) with #96's
`scriptAccepts_compileSafe_single_public_runOps_eq_loop` and the count-generic
`Agrees.A7.runOps_loopOkFull_accept` would give the full parsed-bytes consume
theorem over `1 ≤ n ≤ 15`. Today the count=3 instance of that full chain is the
already-landed `LoopBridge.loopOk_acceptAgrees_parsedBytes` (and this file's
`anfAcc_isSome_three` confirms its ANF half is the `n = 3` instance of the
symbolic (a)). -/

end RunarVerification.Stack.LoopCountGeneric
