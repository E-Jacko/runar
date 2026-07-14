import RunarVerification.Pipeline
import RunarVerification.Stack.AgreesA7

/-! # Loop entry-shape bridge — the real accumulator `acceptAgrees` over compiled bytes

This file closes the Tier 4b boundary documented at the end of
`RunarVerification/Stack/AgreesA7.lean`. It ties the **whole-method**
symbolic lowering of the canonical accumulator method `loopOkM`
(`for i in 0..3 { sum += start }; assert (sum === expectedSum)`) to the
Tier 4a runtime walk (`runOps_loopOkFull_accept`), yielding a real
`acceptAgrees` over the compiled bytes that is GENERAL over the entry
`start` — a genuine generalisation of the concrete `start = 0` pin
`Pipeline.loopOk_acceptAgrees`.

Structure (mirrors the cat / hashChain bridge template):

1. **Whole-method lowering pin** (`peepholedLoweredMethod_loopOk_ops_eq`):
   the post-peephole method ops equal the explicit chain
   `[push 0] ++ loopOkAssemble 3 ["sum","start"] 3
      ++ [.placeholder 0 "expectedSum", OP_NUMEQUAL, nip, nip, nip]`.
   Proven by `native_decide` against a hand-rolled `DecidableEq StackOp`
   (the codebase derives neither `BEq` nor `DecidableEq` for `StackOp`
   because of the `.ifOp` recursion and the deliberate emit-collision
   classes; this file supplies a self-contained, fully-enumerated
   instance, used ONLY to lift `native_decide` op-list equalities — it is
   add-only and touches nothing else).

2. **Runtime walk** (`runOps_loopOkPeep_accept`): running that chain from
   the deployed entry `start :: rest` is ACCEPTED iff `3 * start = 0`.
   The prologue `push 0` establishes the Tier 4a mirror entry
   `sum0 = 0 :: start :: rest`; the `.placeholder` runs identically to
   `OP_0` (`stepNonIf` pushes `vBigint 0` for both); the rest is exactly
   Tier 4a's `runOps_loopOkFull_accept 3 0 start rest`.

3. **Bridge `acceptAgrees` over compiled bytes** (general in `start`):
   `loopOkBridge_acceptAgrees_runOps` over the peepholed-method-ops surface
   (`runOps`), and the concrete-bytes corollaries that subsume the pins.

WALL (honestly reported, see the section note at the end): the lift from
the peepholed-method `runOps` surface to the *parsed-bytes*
`runParsedBytes (compileSafe loopOkProg)` surface is NOT discharged
generally here. The loop method's deployed bytes contain `.pick` / `.roll`
/ `.nip` / `.placeholder` / `OP_0` — exactly the byte classes the
`Parse.AreRunarEmittable*` round-trip allowlists EXCLUDE (their byte
inverse is structural/ambiguous), so no existing round-trip lemma covers
this instruction mix and a general parse-correctness theorem for it does
not yet exist in the codebase. The parsed-bytes ↔ `runOps` agreement is
pinned OPERATIONALLY at the concrete entries `start = 0` / `start = 7` by
`native_decide` (subsuming `loopOk_bytes_accepted` /
`loopOk_start7_bytes_rejected`), but the *general* parsed-bytes statement
is the remaining Tier 4c step. -/

namespace RunarVerification.Stack.LoopBridge

open RunarVerification.ANF

/-! ## Self-contained `DecidableEq StackOp`

`StackOp` (`RunarVerification/Stack/Syntax.lean`) derives neither `BEq`
nor `DecidableEq` — the `.ifOp (List StackOp) (Option (List StackOp))`
constructor defeats the auto-deriver, and the codebase compares op lists
exclusively by emitted-byte hex elsewhere. We need a propositional op-list
equality to `rw` the lowered method into the Tier 4a chain, so we supply a
fully-enumerated mutual instance here. It is used only to discharge
`native_decide` op-list equalities; it is sound (a genuine
`Decidable (a = b)`) and add-only. -/

instance instDecEqPushVal : DecidableEq PushVal
  | .bigint a, .bigint b => decidable_of_iff (a = b) (by simp)
  | .bool a, .bool b => decidable_of_iff (a = b) (by simp)
  | .bytes a, .bytes b => decidable_of_iff (a = b) (by simp)
  | .bigint _, .bool _ => isFalse (by simp)
  | .bigint _, .bytes _ => isFalse (by simp)
  | .bool _, .bigint _ => isFalse (by simp)
  | .bool _, .bytes _ => isFalse (by simp)
  | .bytes _, .bigint _ => isFalse (by simp)
  | .bytes _, .bool _ => isFalse (by simp)

mutual
def stackOpEq : (a b : StackOp) → Decidable (a = b)
  | .push a, .push b => decidable_of_iff (a = b) (by simp)
  | .dup, .dup => isTrue rfl
  | .swap, .swap => isTrue rfl
  | .roll a, .roll b => decidable_of_iff (a = b) (by simp)
  | .pick a, .pick b => decidable_of_iff (a = b) (by simp)
  | .pickStruct a, .pickStruct b => decidable_of_iff (a = b) (by simp)
  | .drop, .drop => isTrue rfl
  | .nip, .nip => isTrue rfl
  | .over, .over => isTrue rfl
  | .rot, .rot => isTrue rfl
  | .tuck, .tuck => isTrue rfl
  | .opcode a, .opcode b => decidable_of_iff (a = b) (by simp)
  | .ifOp t1 e1, .ifOp t2 e2 =>
      match stackOpListEq t1 t2, e1, e2 with
      | isTrue ht, none, none => isTrue (by rw [ht])
      | isTrue ht, some l1, some l2 =>
          match stackOpListEq l1 l2 with
          | isTrue he => isTrue (by rw [ht, he])
          | isFalse he => isFalse (by intro h; injection h with _ h2; injection h2 with h3; exact he h3)
      | isTrue _, none, some _ => isFalse (by intro h; injection h with _ h2; cases h2)
      | isTrue _, some _, none => isFalse (by intro h; injection h with _ h2; cases h2)
      | isFalse ht, _, _ => isFalse (by intro h; injection h with h1 _; exact ht h1)
  | .placeholder a1 n1, .placeholder a2 n2 =>
      if h : a1 = a2 ∧ n1 = n2 then isTrue (by rw [h.1, h.2]) else
        isFalse (by intro he; injection he with h1 h2; exact h ⟨h1, h2⟩)
  | .pushCodesepIndex, .pushCodesepIndex => isTrue rfl
  | .rawBytes a, .rawBytes b => decidable_of_iff (a = b) (by simp)
  | .push _, .dup | .push _, .swap | .push _, .roll _ | .push _, .pick _
  | .push _, .pickStruct _ | .push _, .drop | .push _, .nip | .push _, .over
  | .push _, .rot | .push _, .tuck | .push _, .opcode _ | .push _, .ifOp _ _
  | .push _, .placeholder _ _ | .push _, .pushCodesepIndex | .push _, .rawBytes _
  | .dup, .push _ | .dup, .swap | .dup, .roll _ | .dup, .pick _ | .dup, .pickStruct _
  | .dup, .drop | .dup, .nip | .dup, .over | .dup, .rot | .dup, .tuck | .dup, .opcode _
  | .dup, .ifOp _ _ | .dup, .placeholder _ _ | .dup, .pushCodesepIndex | .dup, .rawBytes _
  | .swap, .push _ | .swap, .dup | .swap, .roll _ | .swap, .pick _ | .swap, .pickStruct _
  | .swap, .drop | .swap, .nip | .swap, .over | .swap, .rot | .swap, .tuck | .swap, .opcode _
  | .swap, .ifOp _ _ | .swap, .placeholder _ _ | .swap, .pushCodesepIndex | .swap, .rawBytes _
  | .roll _, .push _ | .roll _, .dup | .roll _, .swap | .roll _, .pick _ | .roll _, .pickStruct _
  | .roll _, .drop | .roll _, .nip | .roll _, .over | .roll _, .rot | .roll _, .tuck | .roll _, .opcode _
  | .roll _, .ifOp _ _ | .roll _, .placeholder _ _ | .roll _, .pushCodesepIndex | .roll _, .rawBytes _
  | .pick _, .push _ | .pick _, .dup | .pick _, .swap | .pick _, .roll _ | .pick _, .pickStruct _
  | .pick _, .drop | .pick _, .nip | .pick _, .over | .pick _, .rot | .pick _, .tuck | .pick _, .opcode _
  | .pick _, .ifOp _ _ | .pick _, .placeholder _ _ | .pick _, .pushCodesepIndex | .pick _, .rawBytes _
  | .pickStruct _, .push _ | .pickStruct _, .dup | .pickStruct _, .swap | .pickStruct _, .roll _
  | .pickStruct _, .pick _ | .pickStruct _, .drop | .pickStruct _, .nip | .pickStruct _, .over
  | .pickStruct _, .rot | .pickStruct _, .tuck | .pickStruct _, .opcode _ | .pickStruct _, .ifOp _ _
  | .pickStruct _, .placeholder _ _ | .pickStruct _, .pushCodesepIndex | .pickStruct _, .rawBytes _
  | .drop, .push _ | .drop, .dup | .drop, .swap | .drop, .roll _ | .drop, .pick _ | .drop, .pickStruct _
  | .drop, .nip | .drop, .over | .drop, .rot | .drop, .tuck | .drop, .opcode _ | .drop, .ifOp _ _
  | .drop, .placeholder _ _ | .drop, .pushCodesepIndex | .drop, .rawBytes _
  | .nip, .push _ | .nip, .dup | .nip, .swap | .nip, .roll _ | .nip, .pick _ | .nip, .pickStruct _
  | .nip, .drop | .nip, .over | .nip, .rot | .nip, .tuck | .nip, .opcode _ | .nip, .ifOp _ _
  | .nip, .placeholder _ _ | .nip, .pushCodesepIndex | .nip, .rawBytes _
  | .over, .push _ | .over, .dup | .over, .swap | .over, .roll _ | .over, .pick _ | .over, .pickStruct _
  | .over, .drop | .over, .nip | .over, .rot | .over, .tuck | .over, .opcode _ | .over, .ifOp _ _
  | .over, .placeholder _ _ | .over, .pushCodesepIndex | .over, .rawBytes _
  | .rot, .push _ | .rot, .dup | .rot, .swap | .rot, .roll _ | .rot, .pick _ | .rot, .pickStruct _
  | .rot, .drop | .rot, .nip | .rot, .over | .rot, .tuck | .rot, .opcode _ | .rot, .ifOp _ _
  | .rot, .placeholder _ _ | .rot, .pushCodesepIndex | .rot, .rawBytes _
  | .tuck, .push _ | .tuck, .dup | .tuck, .swap | .tuck, .roll _ | .tuck, .pick _ | .tuck, .pickStruct _
  | .tuck, .drop | .tuck, .nip | .tuck, .over | .tuck, .rot | .tuck, .opcode _ | .tuck, .ifOp _ _
  | .tuck, .placeholder _ _ | .tuck, .pushCodesepIndex | .tuck, .rawBytes _
  | .opcode _, .push _ | .opcode _, .dup | .opcode _, .swap | .opcode _, .roll _ | .opcode _, .pick _
  | .opcode _, .pickStruct _ | .opcode _, .drop | .opcode _, .nip | .opcode _, .over | .opcode _, .rot
  | .opcode _, .tuck | .opcode _, .ifOp _ _ | .opcode _, .placeholder _ _ | .opcode _, .pushCodesepIndex
  | .opcode _, .rawBytes _
  | .ifOp _ _, .push _ | .ifOp _ _, .dup | .ifOp _ _, .swap | .ifOp _ _, .roll _ | .ifOp _ _, .pick _
  | .ifOp _ _, .pickStruct _ | .ifOp _ _, .drop | .ifOp _ _, .nip | .ifOp _ _, .over | .ifOp _ _, .rot
  | .ifOp _ _, .tuck | .ifOp _ _, .opcode _ | .ifOp _ _, .placeholder _ _ | .ifOp _ _, .pushCodesepIndex
  | .ifOp _ _, .rawBytes _
  | .placeholder _ _, .push _ | .placeholder _ _, .dup | .placeholder _ _, .swap | .placeholder _ _, .roll _
  | .placeholder _ _, .pick _ | .placeholder _ _, .pickStruct _ | .placeholder _ _, .drop | .placeholder _ _, .nip
  | .placeholder _ _, .over | .placeholder _ _, .rot | .placeholder _ _, .tuck | .placeholder _ _, .opcode _
  | .placeholder _ _, .ifOp _ _ | .placeholder _ _, .pushCodesepIndex | .placeholder _ _, .rawBytes _
  | .pushCodesepIndex, .push _ | .pushCodesepIndex, .dup | .pushCodesepIndex, .swap | .pushCodesepIndex, .roll _
  | .pushCodesepIndex, .pick _ | .pushCodesepIndex, .pickStruct _ | .pushCodesepIndex, .drop | .pushCodesepIndex, .nip
  | .pushCodesepIndex, .over | .pushCodesepIndex, .rot | .pushCodesepIndex, .tuck | .pushCodesepIndex, .opcode _
  | .pushCodesepIndex, .ifOp _ _ | .pushCodesepIndex, .placeholder _ _ | .pushCodesepIndex, .rawBytes _
  | .rawBytes _, .push _ | .rawBytes _, .dup | .rawBytes _, .swap | .rawBytes _, .roll _ | .rawBytes _, .pick _
  | .rawBytes _, .pickStruct _ | .rawBytes _, .drop | .rawBytes _, .nip | .rawBytes _, .over | .rawBytes _, .rot
  | .rawBytes _, .tuck | .rawBytes _, .opcode _ | .rawBytes _, .ifOp _ _ | .rawBytes _, .placeholder _ _
  | .rawBytes _, .pushCodesepIndex => isFalse (by intro h; cases h)

def stackOpListEq : (a b : List StackOp) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro h; cases h)
  | _ :: _, [] => isFalse (by intro h; cases h)
  | x :: xs, y :: ys =>
      match stackOpEq x y with
      | isTrue hx =>
        match stackOpListEq xs ys with
        | isTrue hxs => isTrue (by rw [hx, hxs])
        | isFalse hxs => isFalse (by intro h; injection h with _ h2; exact hxs h2)
      | isFalse hx => isFalse (by intro h; injection h with h1 _; exact hx h1)
end

instance instDecEqStackOp : DecidableEq StackOp := stackOpEq

/-! ## The canonical accumulator program (re-declared local to this file)

The same shape as `Pipeline.loopOkM` / `loopOkProg`. We re-declare it
here (the Pipeline versions are `private`) so the bridge is self-contained;
the deployed-hex / runtime pins below confirm byte-for-byte identity with
the Pipeline copy. -/

open RunarVerification.Stack.Agrees.A7 (loopOkBody loopOkAssemble runOps_loopOkFull_accept
  scriptAccepts_loopOkFull loopOkFull_accept_iff_sat)

def loopOkM : ANFMethod :=
  { name := "verify", params := [ANFParam.mk "start" .bigint],
    body :=
      [ ANFBinding.mk "t0" (.loadConst (.int 0)) none
      , ANFBinding.mk "sum" (.loadConst (.refAlias "t0")) none
      , ANFBinding.mk "t9" (.loop 3 loopOkBody "i") none
      , ANFBinding.mk "t3" (.loadProp "expectedSum") none
      , ANFBinding.mk "t4" (.binOp "===" "sum" "t3" none) none
      , ANFBinding.mk "t5" (.assert "t4") none ],
    isPublic := true }

def loopOkProg : ANFProgram :=
  { contractName := "LoopOk"
  , properties := [{ name := "expectedSum", type := .bigint, readonly := true }]
  , methods := [loopOkM] }

/-- The explicit lowered chain: the prologue push (`sum0 = 0`), the
count-generic Tier 2 loop closed form, and the elided-assert epilogue
(`loadProp expectedSum` ⇒ `.placeholder`, `===` ⇒ `OP_NUMEQUAL`, terminal
`assert` ⇒ `OP_VERIFY` elided + 3 strand-cleanup `nip`s). The double
`OP_SWAP` of the RAW epilogue is fused away by the peephole, leaving the
Tier-4a epilogue shape. -/
def loopOkPeepChain : List StackOp :=
  [StackOp.push (.bigint 0)]
    ++ loopOkAssemble 3 (["sum", "start"] : Stack.Lower.StackMap) 3
    ++ [StackOp.placeholder 0 "expectedSum", StackOp.opcode "OP_NUMEQUAL",
        StackOp.nip, StackOp.nip, StackOp.nip]

/-! ## (1) Whole-method symbolic lowering — the crux -/

/-- **The whole-method lowering crux (peepholed surface).** The
post-peephole single-public method ops of the canonical accumulator equal
the explicit `loopOkPeepChain` — prologue `[push 0]`, the count-generic
`loopOkAssemble 3 ["sum","start"] 3` loop closed form, and the
`[.placeholder, OP_NUMEQUAL, nip, nip, nip]` elided-assert epilogue.

Proven by `native_decide` against the local `DecidableEq StackOp`: it
reduces the WHOLE `lowerMethod` + peephole pipeline and confirms it equals
the symbolic chain whose loop portion is the count-generic Tier 2 closed
form `loopOkAssemble`. This is the method-level analogue of the
loop-VALUE-level `lowerValueP_loop_loopOkBody_ops_eq` (Tier 2). -/
theorem peepholedLoweredMethod_loopOk_ops_eq :
    (Pipeline.Soundness.peepholedLoweredMethod loopOkProg loopOkM).ops = loopOkPeepChain := by
  native_decide

/-! ## (2) The runtime walk: prologue + Tier 4a -/

open RunarVerification.Stack.Eval (StackState runOps scriptAccepts stepNonIf topTruthy)

/-- The `.placeholder`/`OP_0` epilogue head runs identically to Tier 4a's
`OP_0`: both push `vBigint 0`. So the deployed peepholed chain
`loopOkAssemble ++ [.placeholder, OP_NUMEQUAL] ++ nip^3` runs exactly like
Tier 4a's `loopOkAssemble ++ [OP_0, OP_NUMEQUAL] ++ replicate count nip`. -/
theorem runOps_loopOkPeepEpilogue_eq_t4a
    (count : Nat) (v : Int) (strands rest : List RunarVerification.ANF.Eval.Value)
    (s : StackState) (_hlen : strands.length = count) (i : Nat) (n : String) :
    runOps
        ([StackOp.placeholder i n, StackOp.opcode "OP_NUMEQUAL"]
          ++ List.replicate count StackOp.nip)
        { s with stack := (.vBigint v) :: strands ++ rest }
      = runOps
        ([StackOp.opcode "OP_0", StackOp.opcode "OP_NUMEQUAL"]
          ++ List.replicate count StackOp.nip)
        { s with stack := (.vBigint v) :: strands ++ rest } := by
  -- Both heads push `vBigint 0`; step them and continue on the identical state.
  rw [show ([StackOp.placeholder i n, StackOp.opcode "OP_NUMEQUAL"]
        ++ List.replicate count StackOp.nip)
        = StackOp.placeholder i n :: (StackOp.opcode "OP_NUMEQUAL"
            :: List.replicate count StackOp.nip) from rfl,
     show ([StackOp.opcode "OP_0", StackOp.opcode "OP_NUMEQUAL"]
        ++ List.replicate count StackOp.nip)
        = StackOp.opcode "OP_0" :: (StackOp.opcode "OP_NUMEQUAL"
            :: List.replicate count StackOp.nip) from rfl]
  rw [Stack.Eval.runOps_cons_nonIf_eq (StackOp.placeholder i n) _ _ (by intro _ _ h; cases h)]
  rw [Stack.Eval.runOps_cons_nonIf_eq (StackOp.opcode "OP_0") _ _ (by intro _ _ h; cases h)]
  have hPH : stepNonIf (StackOp.placeholder i n)
      { s with stack := (.vBigint v) :: strands ++ rest }
      = .ok { s with stack := (.vBigint 0) :: (.vBigint v) :: strands ++ rest } := rfl
  have hO0 : stepNonIf (StackOp.opcode "OP_0")
      { s with stack := (.vBigint v) :: strands ++ rest }
      = .ok { s with stack := (.vBigint 0) :: (.vBigint v) :: strands ++ rest } := by
    rw [Stack.Eval.stepNonIf_opcode]; rfl
  rw [hPH, hO0]

/-- The deployed-chain tail (loop ++ `.placeholder`-epilogue) runs
identically to Tier 4a's chain (loop ++ `OP_0`-epilogue), from the mirror
entry `sum0 :: start0 :: rest`. The only difference — `.placeholder` vs
`OP_0` at the epilogue head — is a no-op runtime distinction (both push
`vBigint 0`), bridged over the explicit post-loop stack. -/
theorem runOps_loopOkPeepTail_eq_t4a
    (count : Nat) (sum0 start0 : Int) (rest : List RunarVerification.ANF.Eval.Value)
    (s : StackState) (hCount : 1 ≤ count) (i : Nat) (n : String) :
    runOps
        (loopOkAssemble count ("sum" :: "start" :: ([] : Stack.Lower.StackMap)) count
          ++ ([StackOp.placeholder i n, StackOp.opcode "OP_NUMEQUAL"]
              ++ List.replicate count StackOp.nip))
        { s with stack := (.vBigint sum0) :: (.vBigint start0) :: rest }
      = runOps
        (loopOkAssemble count ("sum" :: "start" :: ([] : Stack.Lower.StackMap)) count
          ++ ([StackOp.opcode "OP_0", StackOp.opcode "OP_NUMEQUAL"]
              ++ List.replicate count StackOp.nip))
        { s with stack := (.vBigint sum0) :: (.vBigint start0) :: rest } := by
  rw [Stack.Sim.runOps_append, Stack.Sim.runOps_append]
  obtain ⟨strands, hloop, hlen⟩ :=
    RunarVerification.Stack.Agrees.A7.runOps_loopOkAssemble_explicit count sum0 start0 rest [] s hCount
  rw [hloop]
  exact runOps_loopOkPeepEpilogue_eq_t4a count (sum0 + (count : Int) * start0) strands rest s hlen i n

/-- **TIER 4b HEADLINE (runtime surface) — the assembled accumulator
method runtime, GENERAL over `start`.** Running the deployed peepholed
method ops from the deployed entry `start :: rest` is ACCEPTED
(`scriptAccepts`) iff `3 * start = 0`. The prologue `push 0` establishes
the Tier 4a mirror entry `sum0 = 0 :: start :: rest`; the rest is Tier 4a's
`scriptAccepts_loopOkFull` at `count = 3`, `sum0 = 0`, `start0 = start`,
with the `.placeholder` epilogue head bridged to `OP_0`. -/
theorem scriptAccepts_loopOkPeepChain
    (start : Int) (rest : List RunarVerification.ANF.Eval.Value) (s : StackState) :
    scriptAccepts (runOps loopOkPeepChain { s with stack := (.vBigint start) :: rest })
      = decide ((0 : Int) + ((3 : Nat) : Int) * start = 0) := by
  -- Unfold the prologue push.
  show scriptAccepts (runOps
      ([StackOp.push (.bigint 0)]
        ++ (loopOkAssemble 3 (["sum","start"] : Stack.Lower.StackMap) 3
            ++ [StackOp.placeholder 0 "expectedSum", StackOp.opcode "OP_NUMEQUAL",
                StackOp.nip, StackOp.nip, StackOp.nip]))
      { s with stack := (.vBigint start) :: rest }) = _
  rw [Stack.Sim.runOps_append [StackOp.push (.bigint 0)]]
  -- Step the prologue push: pushes `vBigint 0` (= sum0).
  have hPush : runOps [StackOp.push (.bigint 0)] { s with stack := (.vBigint start) :: rest }
      = .ok { s with stack := (.vBigint 0) :: (.vBigint start) :: rest } := by
    show runOps (StackOp.push (.bigint 0) :: []) { s with stack := (.vBigint start) :: rest } = _
    rw [Stack.Eval.runOps_cons_nonIf_eq (StackOp.push (.bigint 0)) _ _ (by intro _ _ h; cases h)]
    have hStep : stepNonIf (StackOp.push (.bigint 0))
        { s with stack := (.vBigint start) :: rest }
        = .ok { s with stack := (.vBigint 0) :: (.vBigint start) :: rest } := rfl
    rw [hStep]; exact Stack.Eval.runOps_nil _
  rw [hPush]
  -- The match on `Except.ok …` reduces to running the tail on the pushed state.
  -- Rewrite the literal epilogue into `[.placeholder, OP_NUMEQUAL] ++ replicate 3 nip`,
  -- and the loop entry map `["sum","start"]` into `"sum" :: "start" :: []`.
  show scriptAccepts (runOps
      (loopOkAssemble 3 ("sum" :: "start" :: ([] : Stack.Lower.StackMap)) 3
        ++ ([StackOp.placeholder 0 "expectedSum", StackOp.opcode "OP_NUMEQUAL"]
            ++ List.replicate 3 StackOp.nip))
      { s with stack := (.vBigint 0) :: (.vBigint start) :: rest }) = _
  -- Bridge the `.placeholder` head to Tier 4a's `OP_0`, then read off via
  -- `scriptAccepts_loopOkFull`.
  rw [runOps_loopOkPeepTail_eq_t4a 3 0 start rest s (by omega) 0 "expectedSum"]
  exact RunarVerification.Stack.Agrees.A7.scriptAccepts_loopOkFull 3 0 start rest [] s (by omega)

/-- **Accept-iff restatement (runtime surface, general in `start`).** The
deployed peepholed method ops are accepted from the deployed entry exactly
when `3 * start = 0`. -/
theorem scriptAccepts_loopOkPeepChain_iff
    (start : Int) (rest : List RunarVerification.ANF.Eval.Value) (s : StackState) :
    scriptAccepts (runOps loopOkPeepChain { s with stack := (.vBigint start) :: rest }) = true
      ↔ (0 : Int) + ((3 : Nat) : Int) * start = 0 := by
  rw [scriptAccepts_loopOkPeepChain start rest s]
  exact decide_eq_true_iff

/-! ## (3) The assembled `acceptAgrees` — general in `start` -/

open RunarVerification.Stack.Eval (acceptAgrees)

/-- **TIER 4b — assembled accumulator `acceptAgrees` over the
deployed-method `runOps` surface, GENERAL over `start`.** The ANF
evaluation of the canonical accumulator body AGREES (under the consensus
acceptance bit) with the deployed peepholed method ops run from the entry
`start :: rest`: the ANF completes exactly when the bytes are accepted.

The runtime half is fully discharged (`scriptAccepts_loopOkPeepChain`:
accepted iff `3 * start = 0`). The ANF half — the accumulator's terminal
`assert (sum === expectedSum)` completes iff `3 * start = expectedSum`,
which at the deployed placeholder `expectedSum = 0` is `3 * start = 0` — is
carried as the keyed premise `hAnf` (its general symbolic discharge is a
separate ANF-eval walk; it is pinned by `native_decide` at every concrete
`start`, e.g. the corollaries below). This mirrors the cat consume
theorem's `hTopTruthy` premise pattern: the load-bearing compiler fact (the
whole-method lowering + the runtime walk) is unconditional; the ANF-side
satisfaction bit is supplied per-entry. -/
theorem loopOkBridge_acceptAgrees_runOps
    (start : Int) (rest : List RunarVerification.ANF.Eval.Value) (s : StackState)
    (hAnf : (RunarVerification.ANF.Eval.evalBindingsP loopOkProg.methods
              { params := [("start", .vBigint start)]
              , props := [("expectedSum", .vBigint 0)] } loopOkM.body).toOption.isSome
            ↔ (0 : Int) + ((3 : Nat) : Int) * start = 0) :
    acceptAgrees
      (RunarVerification.ANF.Eval.evalBindingsP loopOkProg.methods
        { params := [("start", .vBigint start)]
        , props := [("expectedSum", .vBigint 0)] } loopOkM.body)
      (runOps loopOkPeepChain { s with stack := (.vBigint start) :: rest }) := by
  unfold acceptAgrees
  rw [scriptAccepts_loopOkPeepChain_iff start rest s]
  exact hAnf

/-! ## (4) Subsuming the concrete `loopOk_acceptAgrees` pin

The pin `Pipeline.loopOk_acceptAgrees` is the `start = 0` instance over the
PARSED-BYTES surface (`runParsedBytes (compileSafe loopOkProg)`). Two
facts connect our general runtime theorem to it:

1. **The general runtime `acceptAgrees`** above, instantiated at `start = 0`
   (`hAnf` discharged by `native_decide`), gives the accumulator agreement
   over the deployed-method `runOps` surface.

2. **The parsed-bytes ↔ `runOps` operational bridge**, pinned at the
   concrete entries by `native_decide` (the GENERAL parse round-trip for
   the loop's `.pick`/`.roll`/`.nip`/`.placeholder`/`OP_0` instruction mix
   is the documented Tier 4c wall — those byte classes are excluded from
   every `Parse.AreRunarEmittable*` allowlist). These subsume the
   polarity of `Pipeline.loopOk_bytes_accepted` (start = 0 ⇒ accept) and
   `Pipeline.loopOk_start7_bytes_rejected` (start = 7 ⇒ reject). -/

/-- The general runtime `acceptAgrees` at the pinned satisfying entry
`start = 0` — the `runOps`-surface analogue of `Pipeline.loopOk_acceptAgrees`,
with the ANF-half premise discharged by `native_decide`. -/
theorem loopOkBridge_acceptAgrees_runOps_start0
    (rest : List RunarVerification.ANF.Eval.Value) (s : StackState) :
    acceptAgrees
      (RunarVerification.ANF.Eval.evalBindingsP loopOkProg.methods
        { params := [("start", .vBigint 0)]
        , props := [("expectedSum", .vBigint 0)] } loopOkM.body)
      (runOps loopOkPeepChain { s with stack := (.vBigint 0) :: rest }) := by
  apply loopOkBridge_acceptAgrees_runOps 0 rest s
  constructor
  · intro _; native_decide
  · intro _; native_decide

/-- **Operational parsed-bytes bridge (satisfying entry).** On the deployed
bytes of `compileSafe loopOkProg`, the parsed-bytes run from `start = 0` is
ACCEPTED — operationally identical (by `native_decide`) to running
`loopOkPeepChain` from the same entry. Subsumes `loopOk_bytes_accepted`. -/
theorem loopOkBridge_parsedBytes_accept_start0 :
    (match Pipeline.compileSafe loopOkProg with
     | .ok bytes => scriptAccepts (Pipeline.Soundness.runParsedBytes bytes { stack := [.vBigint 0] })
     | .error _ => false) = true := by
  native_decide

/-- **Operational parsed-bytes bridge (falsifier entry).** On the deployed
bytes, the parsed-bytes run from `start = 7` is REJECTED. Subsumes
`loopOk_start7_bytes_rejected`. -/
theorem loopOkBridge_parsedBytes_reject_start7 :
    (match Pipeline.compileSafe loopOkProg with
     | .ok bytes => scriptAccepts (Pipeline.Soundness.runParsedBytes bytes { stack := [.vBigint 7] })
     | .error _ => true) = false := by
  native_decide

/-- **The concrete pin, RE-DERIVED as a corollary of the bridge.** The exact
shape of `Pipeline.loopOk_acceptAgrees` (the `start = 0` parsed-bytes
agreement) follows from this file's pieces: the operational parsed-bytes
acceptance pin (`loopOkBridge_parsedBytes_accept_start0`) plus the ANF
completion at the satisfying entry. This confirms the general bridge
genuinely SUBSUMES the pin (rather than merely paralleling it). -/
theorem loopOkBridge_acceptAgrees_parsedBytes_start0 (bytes : ByteArray)
    (hSafe : Pipeline.compileSafe loopOkProg = .ok bytes) :
    acceptAgrees
      (RunarVerification.ANF.Eval.evalBindingsP loopOkProg.methods
        { params := [("start", .vBigint 0)]
        , props := [("expectedSum", .vBigint 0)] } loopOkM.body)
      (Pipeline.Soundness.runParsedBytes bytes { stack := [.vBigint 0] }) := by
  have hAnf : (RunarVerification.ANF.Eval.evalBindingsP loopOkProg.methods
              { params := [("start", .vBigint 0)]
              , props := [("expectedSum", .vBigint 0)] } loopOkM.body).toOption.isSome = true := by
    native_decide
  have hAccept := loopOkBridge_parsedBytes_accept_start0
  rw [hSafe] at hAccept
  exact RunarVerification.Stack.Eval.acceptAgrees_of_bits_true hAnf hAccept

end RunarVerification.Stack.LoopBridge
