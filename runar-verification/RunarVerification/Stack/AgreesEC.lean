import RunarVerification.ANF.Eval
import RunarVerification.Stack.Eval
import RunarVerification.Stack.Ec
import RunarVerification.Crypto.Secp256k1
import RunarVerification.Pipeline

/-! # `Stack/AgreesEC.lean` — single-EC-op codegen-to-spec PoC substrate

**EC sizing PoC (peer of wave-68's `AgreesCrypto.lean`).**  This file is a
STANDALONE sizing proof-of-concept for the secp256k1 EC codegen-to-spec tier
(`Crypto/Spec.lean §7`, the 10 `emitEc*_runOps_eq` axioms).  It is NOT wired
into `RunarVerification.lean`; it is built directly via `lake env lean` to
demonstrate that the SIMPLEST EC op (`ecModReduce`) is dischargeable off the
multi-op operational-M3 template (`runOps_cons_nonIf_eq` chaining), exactly the
way the SHA single-opcode transport was discharged in wave 68 — but for an
8-op fragment rather than a 1-op fragment, and against a FULLY EVALUABLE spec
(no opaque crypto backend).

## What this PoC establishes (and what it deliberately does not)

* `emitEcModReduce` lowers to the 8-op fragment
  `[OP_2DUP, OP_MOD, rot, drop, over, OP_ADD, swap, OP_MOD]`.  Every op is a
  `stepNonIf` arm the Stack VM evaluates concretely.  We prove
  `runOps Stack.Ec.emitEcModReduce stkSt = .ok {... ecModReduce value m ...}`
  by 8 sequential `runOps_cons_nonIf_eq` reductions — the EC analogue of
  `HashOps.runOps_sha256Ops_eq`, scaled to a multi-op fragment.

* **HONEST PRECONDITION (`m ≠ 0`).**  The Stack op `OP_MOD` returns
  `.error .divByZero` when the modulus is `0`, but the spec
  `Crypto.Secp256k1.ecModReduce` returns `0` in that case.  So the
  codegen-to-spec equality holds **only under `m ≠ 0`**.  The former
  `Crypto/Spec.lean` axiom `emitEcModReduce_runOps_eq` carried NO such
  hypothesis — meaning it was FALSE at `m = 0` and could not be discharged
  verbatim.  The fix is (a) adding `m ≠ 0` to the statement.  **This wave does
  exactly that and DISCHARGES the axiom**: Part 6 below restates it with `m ≠ 0`
  and proves it as `emitEcModReduce_runOps_eq` (a theorem) off
  `ecModReduce_step_transport`, removing the `Crypto/Spec` axiom.

* This is a SIZING PoC for ONE op-class (the "tiny / all-evaluable-opcodes"
  class).  It does NOT touch the medium ops (reverse32 ~300-op loops:
  `ecPointX/Y`, `ecMakePoint`, `ecNegate`, `ecEncodeCompressed`, `ecOnCurve`)
  nor the hard ops (`ecAdd`, `ecMul`, `ecMulGen` — Jacobian group law,
  50k+ ops, M4-walled).  See the SIZING REPORT in the task deliverable.

## Constraints honoured

No `sorry`/`admit`.  No new axioms (the spec defs in `Crypto/Secp256k1` and the
Stack VM in `Stack/Eval` are USED, not introduced).  No `...`.  The headline
transport is proved by honest step-chaining (no `simp`/`native_decide` fakes);
`native_decide` appears ONLY in a concrete smoke (the spec is computable, so the
smoke is legitimate, unlike the SHA backend which would panic). -/

-- The per-step `simp only [match_Except_ok_runOps]` reductions trip the
-- unused-simp-arg linter (Lean's iota reducer sometimes fires the match
-- reduction first), but the lemma IS the intended driver and keeping it
-- documents the step. Silence the cosmetic linter only.
set_option linter.unusedSimpArgs false

namespace RunarVerification.Stack.AgreesEC

open RunarVerification.ANF.Eval (Value State EvalResult EvalError evalValue callBuiltin?)
open RunarVerification.Stack
open RunarVerification.Stack.Eval
open RunarVerification.Pipeline.Soundness (successAgrees)

/-! ## Part 1 — the Stack-side multi-op M3 step transport (`ecModReduce`)

`Stack.Ec.emitEcModReduce` is the 8-op fragment

```text
[ .opcode "OP_2DUP", .opcode "OP_MOD", .rot, .drop,
  .over, .opcode "OP_ADD", .swap, .opcode "OP_MOD" ]
```

Run on `stack = vBigint m :: vBigint value :: rest` (TOS = `m`), it computes
`((value % m) + m) % m` = `Crypto.Secp256k1.ecModReduce value m` (the `m ≠ 0`
branch).  This is the EC peer of `HashOps.runOps_sha256Ops_eq` — a
codegen-to-spec operational step, but over 8 ops instead of 1, and against a
concrete (non-axiom) spec. -/

/-- **M3 substrate (ecModReduce).**  Running the lowered `emitEcModReduce`
fragment on `[m, value] ++ rest` (m on TOS) pushes
`Crypto.Secp256k1.ecModReduce value m`, provided `m ≠ 0` (the divByZero guard).

Proof: 8 honest `runOps_cons_nonIf_eq` step reductions.  No `simp` closing the
arithmetic — the result coordinate is exactly the spec def unfolded. -/
theorem ecModReduce_step_transport
    (s : StackState) (value m : Int) (rest : List Value)
    (hStk : s.stack = .vBigint m :: .vBigint value :: rest)
    (hM : m ≠ 0) :
    runOps Stack.Ec.emitEcModReduce s
      = .ok { s with
              stack := .vBigint (RunarVerification.Crypto.Secp256k1.ecModReduce value m)
                        :: rest } := by
  -- Destructure `s` and substitute its stack shape so every `stepNonIf`
  -- reduces by `rfl` (the non-stack fields `alt/out/props/pre` ride along
  -- unchanged through every step). `emitEcModReduce` is a literal 8-op list.
  obtain ⟨stk, alt, out, props, pre⟩ := s
  subst hStk
  -- Generic non-`.ifOp` proofs.
  have niOp : ∀ (c : String) t e, StackOp.opcode c ≠ .ifOp t e := by
    intro c t e h; cases h
  have niRot : ∀ t e, StackOp.rot ≠ .ifOp t e := by intro t e h; cases h
  have niDrop : ∀ t e, StackOp.drop ≠ .ifOp t e := by intro t e h; cases h
  have niOver : ∀ t e, StackOp.over ≠ .ifOp t e := by intro t e h; cases h
  have niSwap : ∀ t e, StackOp.swap ≠ .ifOp t e := by intro t e h; cases h
  -- Field record carried through every step (only `.stack` changes).
  -- Step 1: OP_2DUP.
  show runOps
      ([ StackOp.opcode "OP_2DUP", StackOp.opcode "OP_MOD", StackOp.rot,
         StackOp.drop, StackOp.over, StackOp.opcode "OP_ADD", StackOp.swap,
         StackOp.opcode "OP_MOD" ])
      { stack := .vBigint m :: .vBigint value :: rest, altstack := alt,
        outputs := out, props := props, preimage := pre } = _
  rw [runOps_cons_nonIf_eq _ _ _ (niOp "OP_2DUP"), stepNonIf_opcode]
  rw [show runOpcode "OP_2DUP"
        { stack := .vBigint m :: .vBigint value :: rest, altstack := alt,
          outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBigint m :: .vBigint value :: .vBigint m
                        :: .vBigint value :: rest, altstack := alt,
                outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps]
  -- Step 2: OP_MOD  → value % m on top.
  rw [runOps_cons_nonIf_eq _ _ _ (niOp "OP_MOD"), stepNonIf_opcode]
  rw [show runOpcode "OP_MOD"
        { stack := .vBigint m :: .vBigint value :: .vBigint m :: .vBigint value :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBigint (value % m) :: .vBigint m :: .vBigint value :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } by
      show (if m == 0 then (Except.error EvalError.divByZero : EvalResult StackState)
            else .ok (StackState.push
                  { stack := .vBigint m :: .vBigint value :: rest, altstack := alt,
                    outputs := out, props := props, preimage := pre }
                  (.vBigint (value % m)))) = _
      rw [if_neg (by simpa using hM)]; rfl]
  simp only [match_Except_ok_runOps]
  -- Step 3: rot.
  rw [runOps_cons_nonIf_eq _ _ _ niRot]
  rw [show stepNonIf StackOp.rot
        { stack := .vBigint (value % m) :: .vBigint m :: .vBigint value :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBigint value :: .vBigint (value % m) :: .vBigint m :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps]
  -- Step 4: drop.
  rw [runOps_cons_nonIf_eq _ _ _ niDrop]
  rw [show stepNonIf StackOp.drop
        { stack := .vBigint value :: .vBigint (value % m) :: .vBigint m :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBigint (value % m) :: .vBigint m :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps]
  -- Step 5: over.
  rw [runOps_cons_nonIf_eq _ _ _ niOver]
  rw [show stepNonIf StackOp.over
        { stack := .vBigint (value % m) :: .vBigint m :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBigint m :: .vBigint (value % m) :: .vBigint m :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps]
  -- Step 6: OP_ADD  → (value % m) + m on top.
  rw [runOps_cons_nonIf_eq _ _ _ (niOp "OP_ADD"), stepNonIf_opcode]
  rw [show runOpcode "OP_ADD"
        { stack := .vBigint m :: .vBigint (value % m) :: .vBigint m :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBigint (value % m + m) :: .vBigint m :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps]
  -- Step 7: swap.
  rw [runOps_cons_nonIf_eq _ _ _ niSwap]
  rw [show stepNonIf StackOp.swap
        { stack := .vBigint (value % m + m) :: .vBigint m :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBigint m :: .vBigint (value % m + m) :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps]
  -- Step 8: OP_MOD  → ((value % m) + m) % m on top.
  rw [runOps_cons_nonIf_eq _ _ _ (niOp "OP_MOD"), stepNonIf_opcode]
  rw [show runOpcode "OP_MOD"
        { stack := .vBigint m :: .vBigint (value % m + m) :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBigint ((value % m + m) % m) :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } by
      show (if m == 0 then (Except.error EvalError.divByZero : EvalResult StackState)
            else .ok (StackState.push
                  { stack := rest, altstack := alt,
                    outputs := out, props := props, preimage := pre }
                  (.vBigint ((value % m + m) % m)))) = _
      rw [if_neg (by simpa using hM)]; rfl]
  simp only [match_Except_ok_runOps, runOps_nil]
  -- Final: the pushed coordinate equals the spec def at `m ≠ 0`.
  have hSpec :
      RunarVerification.Crypto.Secp256k1.ecModReduce value m = (value % m + m) % m := by
    unfold RunarVerification.Crypto.Secp256k1.ecModReduce
    rw [if_neg hM]
  rw [hSpec]

/-! ## Part 2 — the M2 success-bit agreement (peer of wave-68)

`successAgrees a b := a.toOption.isSome ↔ b.toOption.isSome`.  The Stack side of
the `ecModReduce` fragment succeeds (Part 1).  An ANF side that COMPUTES
`ecModReduce` (the standalone `Crypto.ecModReduce` def already exists in
`ANF/Eval.lean`, line 417, but is NOT yet wired into `callBuiltin?` — see the
SIZING REPORT) would have success bit `true`, giving the M2 agreement.

Until the `callBuiltin?` arm lands, we state the agreement against the
Stack-side success directly: the deployed `emitEcModReduce` fragment SUCCEEDS on
a well-typed nonzero-modulus stack.  This is the leaf a gated dispatch wave would
hand to the consume theorem once the ANF arm is wired. -/

/-- The deployed `emitEcModReduce` fragment SUCCEEDS (success bit `true`) on a
two-int stack with nonzero modulus.  This is the Stack-side half of the M2 leg;
the ANF half is the (not-yet-wired) `callBuiltin? "ecModReduce"` arm. -/
theorem ecModReduce_stack_succeeds
    (s : StackState) (value m : Int) (rest : List Value)
    (hStk : s.stack = .vBigint m :: .vBigint value :: rest)
    (hM : m ≠ 0) :
    (runOps Stack.Ec.emitEcModReduce s).toOption.isSome = true := by
  rw [ecModReduce_step_transport s value m rest hStk hM]; rfl

/-! ## Part 3 — MANDATORY in-file smokes (anti-vacuous, concrete)

Unlike the SHA PoC, the EC spec is fully EVALUABLE, so the smokes may fire by
`native_decide` on the concrete coordinate (the spec is a closed-form `Int`
function — no opaque backend to panic the kernel evaluator). -/

/-- Concrete stack `[7, 23]` (m = 7 on TOS, value = 23 below). -/
private def smokeStk : StackState :=
  { (default : StackState) with stack := [.vBigint 7, .vBigint 23] }

/-- SMOKE (Part 1, structural).  The transport FIRES on the concrete stack:
running `emitEcModReduce` on `[7, 23]` yields `[23 mod 7 = 2]`.  This is the
anti-vacuity witness that the 8-op fragment really evaluates to the spec value. -/
theorem smoke_ecModReduce_transport :
    runOps Stack.Ec.emitEcModReduce smokeStk
      = .ok { smokeStk with
              stack := .vBigint (RunarVerification.Crypto.Secp256k1.ecModReduce 23 7) :: [] } :=
  ecModReduce_step_transport smokeStk 23 7 [] rfl (by decide)

/-- SMOKE (anti-vacuity, the headline).  The deployed result coordinate is
concretely `2` — the spec value `ecModReduce 23 7 = 2` matches by computation.
`native_decide` is LEGITIMATE here: the EC spec is a closed-form computable
`Int` function (contrast the SHA backend, which is a non-executable TCB axiom). -/
theorem smoke_ecModReduce_value_concrete :
    RunarVerification.Crypto.Secp256k1.ecModReduce 23 7 = 2 := by native_decide

/-- SMOKE (Part 2).  The Stack-side M2 success bit fires on the concrete pair. -/
theorem smoke_ecModReduce_succeeds :
    (runOps Stack.Ec.emitEcModReduce smokeStk).toOption.isSome = true :=
  ecModReduce_stack_succeeds smokeStk 23 7 [] rfl (by decide)

/-! ## Part 4 — the wired `callBuiltin?` EC arms (deliverable 2)

Wave 71 left the `callBuiltin? "ecModReduce"` arm UNWIRED (see Part 2's note).
This wave wires the eight in-scope EC ops into `ANF.Eval.callBuiltin?`, each
routing through the concrete `Crypto.Secp256k1.*` backend defs already exposed
in `ANF/Eval.lean` (`Crypto.ecAdd` … `Crypto.ecPointY`).  `ecMul` / `ecMulGen`
stay UNWIRED (scoped out — kept as named codegen-discharge axioms).

The arm lemmas below pin each arm's reduction by `rfl` (the peer of
`AgreesCrypto.callBuiltin_sha256_arm`).  Together with the Part-1 Stack-side
transport they close the M2 leg for `ecModReduce`: the ANF side now COMPUTES
`Crypto.ecModReduce value m` instead of returning `.ok none` → `crypto_call`.
No new axiom: the backend defs are concrete. -/

open RunarVerification.ANF.Eval (callBuiltin?) in
/-- The `ecModReduce` arm now fires on a two-int argument list, returning the
backend reduction.  Pins the ANF half of the `ecModReduce` M2 agreement. -/
theorem callBuiltin_ecModReduce_arm (a m : Int) :
    callBuiltin? "ecModReduce" [.vBigint a, .vBigint m]
      = .ok (some (.vBigint (RunarVerification.ANF.Eval.Crypto.ecModReduce a m))) := rfl

open RunarVerification.ANF.Eval (callBuiltin?) in
/-- The `ecAdd` arm fires on two byte-valued points. -/
theorem callBuiltin_ecAdd_arm (p q : ByteArray) :
    callBuiltin? "ecAdd" [.vBytes p, .vBytes q]
      = .ok (some (.vBytes (RunarVerification.ANF.Eval.Crypto.ecAdd p q))) := rfl

open RunarVerification.ANF.Eval (callBuiltin?) in
/-- The `ecNegate` arm fires on one byte-valued point. -/
theorem callBuiltin_ecNegate_arm (p : ByteArray) :
    callBuiltin? "ecNegate" [.vBytes p]
      = .ok (some (.vBytes (RunarVerification.ANF.Eval.Crypto.ecNegate p))) := rfl

open RunarVerification.ANF.Eval (callBuiltin?) in
/-- The `ecOnCurve` arm fires on one byte-valued point, returning a Bool. -/
theorem callBuiltin_ecOnCurve_arm (p : ByteArray) :
    callBuiltin? "ecOnCurve" [.vBytes p]
      = .ok (some (.vBool (RunarVerification.ANF.Eval.Crypto.ecOnCurve p))) := rfl

open RunarVerification.ANF.Eval (callBuiltin?) in
/-- The `ecEncodeCompressed` arm fires on one byte-valued point. -/
theorem callBuiltin_ecEncodeCompressed_arm (p : ByteArray) :
    callBuiltin? "ecEncodeCompressed" [.vBytes p]
      = .ok (some (.vBytes (RunarVerification.ANF.Eval.Crypto.ecEncodeCompressed p))) := rfl

open RunarVerification.ANF.Eval (callBuiltin?) in
/-- The `ecMakePoint` arm fires on two ints. -/
theorem callBuiltin_ecMakePoint_arm (x y : Int) :
    callBuiltin? "ecMakePoint" [.vBigint x, .vBigint y]
      = .ok (some (.vBytes (RunarVerification.ANF.Eval.Crypto.ecMakePoint x y))) := rfl

open RunarVerification.ANF.Eval (callBuiltin?) in
/-- The `ecPointX` arm fires on one byte-valued point, returning an Int. -/
theorem callBuiltin_ecPointX_arm (p : ByteArray) :
    callBuiltin? "ecPointX" [.vBytes p]
      = .ok (some (.vBigint (RunarVerification.ANF.Eval.Crypto.ecPointX p))) := rfl

open RunarVerification.ANF.Eval (callBuiltin?) in
/-- The `ecPointY` arm fires on one byte-valued point, returning an Int. -/
theorem callBuiltin_ecPointY_arm (p : ByteArray) :
    callBuiltin? "ecPointY" [.vBytes p]
      = .ok (some (.vBigint (RunarVerification.ANF.Eval.Crypto.ecPointY p))) := rfl

/-- SMOKE (deliverable 2, ANF arm anti-vacuity).  The wired `ecModReduce` arm,
applied to the same concrete pair `(23, 7)`, computes the spec value `2` — the
ANF half now AGREES with the Stack-side transport (`smoke_ecModReduce_value_concrete`).
`native_decide` is legitimate: the EC spec is a closed-form computable `Int`. -/
theorem smoke_callBuiltin_ecModReduce_arm :
    (match callBuiltin? "ecModReduce" [.vBigint 23, .vBigint 7] with
     | .ok (some (.vBigint n)) => n == 2
     | _ => false) = true := by native_decide

/-- SMOKE (deliverable 2).  A NOT-wired op (`ecMul`, scoped out) still returns
`.ok none` — confirming the scope boundary: only the eight in-scope arms route
through the backend; `ecMul` / `ecMulGen` keep falling through to `crypto_call`. -/
theorem smoke_callBuiltin_ecMul_unwired :
    callBuiltin? "ecMul" [.vBytes (ByteArray.mk #[0x00]), .vBigint 1] = .ok none := rfl

/-! ## Part 5 — the `reverse32` loop transport (deliverable 3)

`Stack.Ec.emitReverse32Step` is the 7-op fragment

```text
[ .push (.bigint 1), .opcode "OP_SPLIT", .rot, .rot, .swap, .opcode "OP_CAT", .swap ]
```

Run on `stack = vBytes value :: vBytes acc :: rest` (value on TOS, with
`1 ≤ value.size`), it peels the FIRST byte off `value` and PREPENDS it to `acc`,
leaving `stack = vBytes (value.extract 1 value.size) :: vBytes (value.extract 0 1 ++ acc) :: rest`.
The loop `emitReverse32Loop n` iterates this `n` times; over a full-size value it
reverses the byte order into the accumulator (verified empirically: a length-3
value `[10,20,30]` with acc `[99]` becomes `[30,20,10,99]`).

**UNBLOCKED (the OP_0 wrapper).** `emitReverse32Ops = [.opcode "OP_0", .swap] ++ loop ++ [.drop]`
initializes the accumulator with `OP_0`. The Stack VM models `OP_0` as `.vBigint 0`
(`Stack.Eval.runOpcode "OP_0" = s.push (.vBigint 0)`); the parser likewise turns the
wire byte `0x00` into `vBigint 0`. Wave 72 BLOCKED here because the first loop step's
`OP_CAT` rejected the `vBigint 0` accumulator. That was a Bitcoin-faithfulness GAP in
`asBytes?`: on a real Script stack the number 0 IS the empty byte vector
(`encodeMinimalLE 0 = ByteArray.empty`) and `OP_CAT(empty, x) = x`. This wave closes
the gap by making `Stack.Eval.asBytes? (.vBigint 0) = some ByteArray.empty` (the narrow,
fully-faithful zero coercion; see `Stack/Eval.lean`). The wrapper transport
`reverse32_ops_transport` below is now a THEOREM (proved via
`reverse32_step_transport_accV` for the seeded first step + `reverse32_loop_transport`
for the rest + `drop`), with a concrete 32-byte success smoke. No new axiom. -/

/-- **reverse32 single-step transport.**  One `emitReverse32Step` on
`[value, acc] ++ rest` (value on TOS, `1 ≤ value.size`) peels the head byte of
`value` onto the front of `acc`. -/
theorem reverse32_step_transport
    (s : StackState) (value acc : ByteArray) (rest : List Value)
    (hStk : s.stack = .vBytes value :: .vBytes acc :: rest)
    (hSize : 1 ≤ value.size) :
    runOps Stack.Ec.emitReverse32Step s
      = .ok { s with
              stack := .vBytes (value.extract 1 value.size)
                        :: .vBytes (value.extract 0 1 ++ acc) :: rest } := by
  obtain ⟨stk, alt, out, props, pre⟩ := s
  subst hStk
  have niRot : ∀ t e, StackOp.rot ≠ .ifOp t e := by intro t e h; cases h
  have niSwap : ∀ t e, StackOp.swap ≠ .ifOp t e := by intro t e h; cases h
  have niOp : ∀ (c : String) t e, StackOp.opcode c ≠ .ifOp t e := by
    intro c t e h; cases h
  have niPush : ∀ (pv : PushVal) t e, StackOp.push pv ≠ .ifOp t e := by
    intro pv t e h; cases h
  have stepNonIf_rot : ∀ (st : StackState), stepNonIf .rot st = applyRot st := by
    intro st; rfl
  -- emitReverse32Step is the literal 7-op list.
  show runOps
      ([ StackOp.push (.bigint 1), StackOp.opcode "OP_SPLIT", StackOp.rot,
         StackOp.rot, StackOp.swap, StackOp.opcode "OP_CAT", StackOp.swap ])
      { stack := .vBytes value :: .vBytes acc :: rest, altstack := alt,
        outputs := out, props := props, preimage := pre } = _
  -- Step 1: push 1.
  rw [runOps_cons_nonIf_eq _ _ _ (niPush (.bigint 1)), stepNonIf_push_bigint]
  simp only [match_Except_ok_runOps, StackState.push]
  -- Step 2: OP_SPLIT at index 1.  Guard discharged by hSize.
  rw [runOps_cons_nonIf_eq _ _ _ (niOp "OP_SPLIT"), stepNonIf_opcode]
  rw [show runOpcode "OP_SPLIT"
        { stack := .vBigint 1 :: .vBytes value :: .vBytes acc :: rest, altstack := alt,
          outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBytes (value.extract 1 value.size)
                          :: .vBytes (value.extract 0 1) :: .vBytes acc :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } by
      unfold runOpcode
      simp only [popN, StackState.pop?, asBytes?, asNonNegativeNat?, asInt?,
                 StackState.push, Int.reduceLT, reduceIte, Int.toNat_one]
      rw [if_neg (by omega : ¬ (1 : Nat) > value.size)] ]
  simp only [match_Except_ok_runOps]
  -- Step 3: rot.
  rw [runOps_cons_nonIf_eq _ _ _ niRot, stepNonIf_rot]
  rw [show applyRot
        { stack := .vBytes (value.extract 1 value.size) :: .vBytes (value.extract 0 1)
                    :: .vBytes acc :: rest, altstack := alt, outputs := out,
          props := props, preimage := pre }
        = .ok { stack := .vBytes acc :: .vBytes (value.extract 1 value.size)
                          :: .vBytes (value.extract 0 1) :: rest, altstack := alt,
                outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps]
  -- Step 4: rot.
  rw [runOps_cons_nonIf_eq _ _ _ niRot, stepNonIf_rot]
  rw [show applyRot
        { stack := .vBytes acc :: .vBytes (value.extract 1 value.size)
                    :: .vBytes (value.extract 0 1) :: rest, altstack := alt,
          outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBytes (value.extract 0 1) :: .vBytes acc
                          :: .vBytes (value.extract 1 value.size) :: rest, altstack := alt,
                outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps]
  -- Step 5: swap.
  rw [runOps_cons_nonIf_eq _ _ _ niSwap, stepNonIf_swap]
  rw [show applySwap
        { stack := .vBytes (value.extract 0 1) :: .vBytes acc
                    :: .vBytes (value.extract 1 value.size) :: rest, altstack := alt,
          outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBytes acc :: .vBytes (value.extract 0 1)
                          :: .vBytes (value.extract 1 value.size) :: rest, altstack := alt,
                outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps]
  -- Step 6: OP_CAT → extract 0 1 ++ acc.
  rw [runOps_cons_nonIf_eq _ _ _ (niOp "OP_CAT"), stepNonIf_opcode]
  rw [show runOpcode "OP_CAT"
        { stack := .vBytes acc :: .vBytes (value.extract 0 1)
                    :: .vBytes (value.extract 1 value.size) :: rest, altstack := alt,
          outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBytes (value.extract 0 1 ++ acc)
                          :: .vBytes (value.extract 1 value.size) :: rest, altstack := alt,
                outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps]
  -- Step 7: swap → final layout.
  rw [runOps_cons_nonIf_eq _ _ _ niSwap, stepNonIf_swap]
  rw [show applySwap
        { stack := .vBytes (value.extract 0 1 ++ acc)
                    :: .vBytes (value.extract 1 value.size) :: rest, altstack := alt,
          outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBytes (value.extract 1 value.size)
                          :: .vBytes (value.extract 0 1 ++ acc) :: rest, altstack := alt,
                outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps, runOps_nil]

/-- **reverse32 single-step transport with a coercible non-`vBytes` accumulator.**
Identical to `reverse32_step_transport` but the accumulator slot holds an arbitrary
`accV : Value` whose Bitcoin-faithful byte view is `acc` (`asBytes? accV = some acc`).
This is what lets the FIRST loop step run against the `OP_0`-initialized accumulator
(`accV = .vBigint 0`, `acc = ByteArray.empty`): on a real Script stack `OP_0` is the
empty byte vector, and `OP_CAT(x, empty) = x`.  Only step 6 (`OP_CAT`) differs from
the `vBytes` form — every other op (`OP_SPLIT`, `rot`, `swap`) is value-agnostic. -/
theorem reverse32_step_transport_accV
    (s : StackState) (value acc : ByteArray) (accV : Value) (rest : List Value)
    (hStk : s.stack = .vBytes value :: accV :: rest)
    (hAcc : asBytes? accV = some acc)
    (hSize : 1 ≤ value.size) :
    runOps Stack.Ec.emitReverse32Step s
      = .ok { s with
              stack := .vBytes (value.extract 1 value.size)
                        :: .vBytes (value.extract 0 1 ++ acc) :: rest } := by
  obtain ⟨stk, alt, out, props, pre⟩ := s
  subst hStk
  have niRot : ∀ t e, StackOp.rot ≠ .ifOp t e := by intro t e h; cases h
  have niSwap : ∀ t e, StackOp.swap ≠ .ifOp t e := by intro t e h; cases h
  have niOp : ∀ (c : String) t e, StackOp.opcode c ≠ .ifOp t e := by
    intro c t e h; cases h
  have niPush : ∀ (pv : PushVal) t e, StackOp.push pv ≠ .ifOp t e := by
    intro pv t e h; cases h
  have stepNonIf_rot : ∀ (st : StackState), stepNonIf .rot st = applyRot st := by
    intro st; rfl
  show runOps
      ([ StackOp.push (.bigint 1), StackOp.opcode "OP_SPLIT", StackOp.rot,
         StackOp.rot, StackOp.swap, StackOp.opcode "OP_CAT", StackOp.swap ])
      { stack := .vBytes value :: accV :: rest, altstack := alt,
        outputs := out, props := props, preimage := pre } = _
  -- Step 1: push 1.
  rw [runOps_cons_nonIf_eq _ _ _ (niPush (.bigint 1)), stepNonIf_push_bigint]
  simp only [match_Except_ok_runOps, StackState.push]
  -- Step 2: OP_SPLIT at index 1.  Guard discharged by hSize.
  rw [runOps_cons_nonIf_eq _ _ _ (niOp "OP_SPLIT"), stepNonIf_opcode]
  rw [show runOpcode "OP_SPLIT"
        { stack := .vBigint 1 :: .vBytes value :: accV :: rest, altstack := alt,
          outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBytes (value.extract 1 value.size)
                          :: .vBytes (value.extract 0 1) :: accV :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } by
      unfold runOpcode
      simp only [popN, StackState.pop?, asBytes?, asNonNegativeNat?, asInt?,
                 StackState.push, Int.reduceLT, reduceIte, Int.toNat_one]
      rw [if_neg (by omega : ¬ (1 : Nat) > value.size)] ]
  simp only [match_Except_ok_runOps]
  -- Step 3: rot.
  rw [runOps_cons_nonIf_eq _ _ _ niRot, stepNonIf_rot]
  rw [show applyRot
        { stack := .vBytes (value.extract 1 value.size) :: .vBytes (value.extract 0 1)
                    :: accV :: rest, altstack := alt, outputs := out,
          props := props, preimage := pre }
        = .ok { stack := accV :: .vBytes (value.extract 1 value.size)
                          :: .vBytes (value.extract 0 1) :: rest, altstack := alt,
                outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps]
  -- Step 4: rot.
  rw [runOps_cons_nonIf_eq _ _ _ niRot, stepNonIf_rot]
  rw [show applyRot
        { stack := accV :: .vBytes (value.extract 1 value.size)
                    :: .vBytes (value.extract 0 1) :: rest, altstack := alt,
          outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBytes (value.extract 0 1) :: accV
                          :: .vBytes (value.extract 1 value.size) :: rest, altstack := alt,
                outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps]
  -- Step 5: swap.
  rw [runOps_cons_nonIf_eq _ _ _ niSwap, stepNonIf_swap]
  rw [show applySwap
        { stack := .vBytes (value.extract 0 1) :: accV
                    :: .vBytes (value.extract 1 value.size) :: rest, altstack := alt,
          outputs := out, props := props, preimage := pre }
        = .ok { stack := accV :: .vBytes (value.extract 0 1)
                          :: .vBytes (value.extract 1 value.size) :: rest, altstack := alt,
                outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps]
  -- Step 6: OP_CAT → extract 0 1 ++ acc.  This is the only arm that inspects the
  -- accumulator value; the coercion `asBytes? accV = some acc` feeds `liftBytesBin`.
  rw [runOps_cons_nonIf_eq _ _ _ (niOp "OP_CAT"), stepNonIf_opcode]
  rw [show runOpcode "OP_CAT"
        { stack := accV :: .vBytes (value.extract 0 1)
                    :: .vBytes (value.extract 1 value.size) :: rest, altstack := alt,
          outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBytes (value.extract 0 1 ++ acc)
                          :: .vBytes (value.extract 1 value.size) :: rest, altstack := alt,
                outputs := out, props := props, preimage := pre } by
      unfold runOpcode liftBytesBin
      simp only [popN, StackState.pop?]
      rw [hAcc]
      simp only [asBytes?, StackState.push]]
  simp only [match_Except_ok_runOps]
  -- Step 7: swap → final layout.
  rw [runOps_cons_nonIf_eq _ _ _ niSwap, stepNonIf_swap]
  rw [show applySwap
        { stack := .vBytes (value.extract 0 1 ++ acc)
                    :: .vBytes (value.extract 1 value.size) :: rest, altstack := alt,
          outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBytes (value.extract 1 value.size)
                          :: .vBytes (value.extract 0 1 ++ acc) :: rest, altstack := alt,
                outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps, runOps_nil]

/-! ### The loop spec and transport (by induction on the iteration count)

`reverseTail`/`reverseAcc` recursively model the value-residue and accumulator
that `emitReverse32Loop n` leaves on the stack: each iteration peels the head
byte (`extract 0 1`) onto the front of the accumulator and recurses on the tail
(`extract 1 size`).  `reverse32_loop_transport` then proves the loop's `runOps`
matches these specs, threaded by `n` honest applications of the step lemma.

These are closed-form `ByteArray` functions (no axiom).  For a full-size value
the residue is empty and the accumulator is the byte-reversed value prefixed onto
the original `acc` — the byte-reversal the medium EC ops need (witnessed by the
concrete smoke below). -/

/-- The value-residue after `n` reverse-loop iterations. -/
def reverseTail : Nat → ByteArray → ByteArray
  | 0,     v => v
  | k + 1, v => reverseTail k (v.extract 1 v.size)

/-- The accumulator after `n` reverse-loop iterations: each step prepends the
current head byte (`extract 0 1`) to the front of the running accumulator. -/
def reverseAcc : Nat → ByteArray → ByteArray → ByteArray
  | 0,     _, acc => acc
  | k + 1, v, acc => reverseAcc k (v.extract 1 v.size) (v.extract 0 1 ++ acc)

/-- **reverse32 loop transport.**  Running `emitReverse32Loop n` on
`[value, acc] ++ rest` (value on TOS, `n ≤ value.size`) leaves
`[reverseTail n value, reverseAcc n value acc] ++ rest`.  Proved by induction on
`n` via `reverse32_step_transport`.  The `n ≤ value.size` precondition keeps every
intermediate `OP_SPLIT` index in range. -/
theorem reverse32_loop_transport
    (n : Nat) :
    ∀ (s : StackState) (value acc : ByteArray) (rest : List Value),
      s.stack = .vBytes value :: .vBytes acc :: rest →
      n ≤ value.size →
      runOps (Stack.Ec.emitReverse32Loop n) s
        = .ok { s with
                stack := .vBytes (reverseTail n value)
                          :: .vBytes (reverseAcc n value acc) :: rest } := by
  induction n with
  | zero =>
      intro s value acc rest hStk _
      show runOps [] s = _
      rw [runOps_nil]
      obtain ⟨stk, alt, out, props, pre⟩ := s
      simp only at hStk
      subst hStk
      rfl
  | succ k ih =>
      intro s value acc rest hStk hLe
      -- emitReverse32Loop (k+1) = emitReverse32Step ++ emitReverse32Loop k
      have hUnfold : Stack.Ec.emitReverse32Loop (k + 1)
          = Stack.Ec.emitReverse32Step ++ Stack.Ec.emitReverse32Loop k := rfl
      rw [hUnfold, runOps_append]
      -- One step peels the head byte.
      rw [reverse32_step_transport s value acc rest hStk (by omega)]
      simp only [match_Except_ok_runOps]
      -- Recurse on the tail.  `(value.extract 1 value.size).size = value.size - 1 ≥ k`.
      have hTailSize : (value.extract 1 value.size).size = value.size - 1 := by
        rw [ByteArray.size_extract]
        omega
      rw [ih { s with stack := .vBytes (value.extract 1 value.size)
                        :: .vBytes (value.extract 0 1 ++ acc) :: rest }
            (value.extract 1 value.size) (value.extract 0 1 ++ acc) rest rfl
            (by rw [hTailSize]; omega)]
      rfl

/-! ### MANDATORY smokes for the loop transport (deliverable 3) -/

/-- Concrete value `[10,20,30]` (TOS), accumulator `[99]`. -/
private def smokeRevStk : StackState :=
  { (default : StackState) with
    stack := [.vBytes (ByteArray.mk #[10, 20, 30]), .vBytes (ByteArray.mk #[99])] }

/-- SMOKE (step, anti-vacuity).  One step on `[[10,20,30],[99]]` peels `10`:
result `[[20,30], [10,99]]`. -/
theorem smoke_reverse32_step :
    runOps Stack.Ec.emitReverse32Step smokeRevStk
      = .ok { smokeRevStk with
              stack := [.vBytes ((ByteArray.mk #[10, 20, 30]).extract 1 3),
                        .vBytes ((ByteArray.mk #[10, 20, 30]).extract 0 1
                                  ++ ByteArray.mk #[99])] } :=
  reverse32_step_transport smokeRevStk (ByteArray.mk #[10, 20, 30]) (ByteArray.mk #[99]) []
    rfl (by decide)

/-- SMOKE (loop, the headline).  Running the 3-iteration loop on `[[10,20,30],[99]]`
reverses the value into the accumulator: the result accumulator byte-list is
`[30, 20, 10, 99]` and the residue is empty.  `native_decide` is legitimate —
`reverseTail` / `reverseAcc` are closed-form computable `ByteArray` functions. -/
theorem smoke_reverse32_loop_value_concrete :
    (reverseAcc 3 (ByteArray.mk #[10, 20, 30]) (ByteArray.mk #[99])).toList
        = [30, 20, 10, 99]
      ∧ (reverseTail 3 (ByteArray.mk #[10, 20, 30])).toList = [] := by
  native_decide

/-- SMOKE (loop transport fires).  The loop `runOps` on the concrete stack
succeeds and lands the reversed accumulator — the step lemma really composes. -/
theorem smoke_reverse32_loop_succeeds :
    (runOps (Stack.Ec.emitReverse32Loop 3) smokeRevStk).toOption.isSome = true := by
  rw [reverse32_loop_transport 3 smokeRevStk (ByteArray.mk #[10, 20, 30])
        (ByteArray.mk #[99]) [] rfl (by decide)]
  rfl

/-! ### The `emitReverse32Ops` wrapper transport (UNBLOCKED by the faithful `asBytes?`)

`emitReverse32Ops = [OP_0, swap] ++ emitReverse32Loop 32 ++ [drop]`.  Wave-72 BLOCKED
here because `OP_0` pushes `vBigint 0` and the first loop step's `OP_CAT` rejected the
non-`vBytes` accumulator.  With the Bitcoin-faithful `asBytes? (vBigint 0) = some empty`
(the number 0 IS the empty byte vector; `OP_CAT(empty, x) = x`) the wrapper now RUNS:
* `OP_0` seeds `vBigint 0`, `swap` puts it under the value;
* the FIRST loop step runs via `reverse32_step_transport_accV` (accumulator `vBigint 0`,
  byte view `empty`), turning the accumulator into `.vBytes (value.extract 0 1 ++ empty)`;
* the remaining 31 steps run via `reverse32_loop_transport`;
* `drop` removes the empty value residue, leaving `.vBytes (reverseAcc 32 value empty)`
  — the byte-reversed `value`.  This is the substrate the 5 medium EC ops consume. -/
theorem reverse32_ops_transport
    (s : StackState) (value : ByteArray) (rest : List Value)
    (hStk : s.stack = .vBytes value :: rest)
    (hSize : 32 ≤ value.size) :
    runOps Stack.Ec.emitReverse32Ops s
      = .ok { s with stack := .vBytes (reverseAcc 32 value ByteArray.empty) :: rest } := by
  have niSwap : ∀ t e, StackOp.swap ≠ .ifOp t e := by intro t e h; cases h
  have niDrop : ∀ t e, StackOp.drop ≠ .ifOp t e := by intro t e h; cases h
  have niOp : ∀ (c : String) t e, StackOp.opcode c ≠ .ifOp t e := by
    intro c t e h; cases h
  -- emitReverse32Ops = [OP_0, swap] ++ (emitReverse32Loop 32 ++ [drop]).
  have hUnfold : Stack.Ec.emitReverse32Ops
      = StackOp.opcode "OP_0" :: StackOp.swap
          :: (Stack.Ec.emitReverse32Loop 32 ++ [StackOp.drop]) := rfl
  rw [hUnfold]
  -- Step A: OP_0 pushes vBigint 0.
  rw [runOps_cons_nonIf_eq _ _ _ (niOp "OP_0"), stepNonIf_opcode]
  rw [show runOpcode "OP_0" s = .ok (s.push (.vBigint 0)) from rfl]
  simp only [match_Except_ok_runOps]
  -- Step B: swap → [value, vBigint 0] ++ rest.
  rw [runOps_cons_nonIf_eq _ _ _ niSwap, stepNonIf_swap]
  obtain ⟨stk, alt, out, props, pre⟩ := s
  simp only [StackState.push] at hStk ⊢
  subst hStk
  rw [show applySwap
        { stack := .vBigint 0 :: .vBytes value :: rest, altstack := alt,
          outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBytes value :: .vBigint 0 :: rest, altstack := alt,
                outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps]
  -- The loop+drop on [value, vBigint 0].  Split the loop's first step out.
  rw [runOps_append]
  -- emitReverse32Loop 32 = emitReverse32Step ++ emitReverse32Loop 31.
  have hLoop : Stack.Ec.emitReverse32Loop 32
      = Stack.Ec.emitReverse32Step ++ Stack.Ec.emitReverse32Loop 31 := rfl
  rw [hLoop, runOps_append]
  -- First step against the vBigint-0 accumulator (byte view = empty).
  rw [reverse32_step_transport_accV
        { stack := .vBytes value :: .vBigint 0 :: rest, altstack := alt,
          outputs := out, props := props, preimage := pre }
        value ByteArray.empty (.vBigint 0) rest rfl asBytes?_vBigint_zero (by omega)]
  simp only [match_Except_ok_runOps]
  -- Remaining 31 steps via the bytes-accumulator loop transport.
  have hTailSize : (value.extract 1 value.size).size = value.size - 1 := by
    rw [ByteArray.size_extract]; omega
  rw [reverse32_loop_transport 31
        { stack := .vBytes (value.extract 1 value.size)
                    :: .vBytes (value.extract 0 1 ++ ByteArray.empty) :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        (value.extract 1 value.size) (value.extract 0 1 ++ ByteArray.empty) rest rfl
        (by rw [hTailSize]; omega)]
  simp only [match_Except_ok_runOps]
  -- drop removes the residue (reverseTail 32 value).
  rw [runOps_cons_nonIf_eq _ _ _ niDrop, stepNonIf_drop]
  rw [show applyDrop
        { stack := .vBytes (reverseTail 31 (value.extract 1 value.size))
                    :: .vBytes (reverseAcc 31 (value.extract 1 value.size)
                                  (value.extract 0 1 ++ ByteArray.empty)) :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBytes (reverseAcc 31 (value.extract 1 value.size)
                                    (value.extract 0 1 ++ ByteArray.empty)) :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps, runOps_nil]
  -- reverseAcc 32 value empty = reverseAcc 31 (extract 1..) (extract 0 1 ++ empty)
  -- by one unfold of reverseAcc.
  rfl

/-- SMOKE (the headline — UNBLOCKED).  On a concrete 32-byte input the full
production `emitReverse32Ops` wrapper now SUCCEEDS (was BLOCKED in wave 72) and
lands the byte-reversed value.  The reversed bytes match the closed-form
`reverseAcc` spec, confirmed by `native_decide`.  `OP_0`'s `vBigint 0` is now
consumed by `OP_CAT` exactly as the empty byte vector on a real Script stack. -/
private def smokeRev32Val : ByteArray :=
  ByteArray.mk #[ 1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15, 16,
                 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]

private def smokeRev32Stk : StackState :=
  { (default : StackState) with stack := [.vBytes smokeRev32Val] }

theorem smoke_reverse32_ops_succeeds :
    runOps Stack.Ec.emitReverse32Ops smokeRev32Stk
      = .ok { smokeRev32Stk with
              stack := [.vBytes (reverseAcc 32 smokeRev32Val ByteArray.empty)] } :=
  reverse32_ops_transport smokeRev32Stk smokeRev32Val [] rfl (by decide)

/-- SMOKE (anti-vacuity).  The reversed accumulator really is `value` byte-reversed:
`[32, 31, …, 2, 1]`.  `reverseAcc` is a closed-form computable `ByteArray` function,
so `native_decide` legitimately runs it. -/
theorem smoke_reverse32_ops_value_concrete :
    (reverseAcc 32 smokeRev32Val ByteArray.empty).toList
      = [32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17,
         16, 15, 14, 13, 12, 11, 10,  9,  8,  7,  6,  5,  4,  3,  2,  1] := by
  native_decide

/-! ## Part 6 — DISCHARGED `Crypto/Spec.lean §7` axioms (this wave)

Two of the ten `emitEc*_runOps_eq` codegen-to-spec links (`Crypto/Spec.lean §7`)
move here from `axiom` to `theorem`:

* `emitEcModReduce_runOps_eq` — the 8-op `OP_2DUP/OP_MOD/…` fragment.  The
  `Crypto/Spec` axiom carried NO precondition and so was FALSE at `m = 0`
  (Stack `OP_MOD` errors with `divByZero`; the spec returns `0`).  Restated
  **with `m ≠ 0`** (the honest fix — the axiom had no consumers, so
  strengthening the hypothesis is harmless) and discharged directly off the
  wave-71 `ecModReduce_step_transport`.

* `emitEcEncodeCompressed_runOps_eq` — the `OP_SPLIT/OP_SIZE/OP_SUB/OP_BIN2NUM/
  OP_MOD/OP_CAT` + `.ifOp` fragment.  Proved by an honest 14-op step-chain
  (`ec_encode_op_transport`) that lands the codegen output expressed in `p`'s
  byte extracts, then lifted to the spec `Crypto.Secp256k1.ecEncodeCompressed`
  under explicit input-level well-formedness:

  - `hSplit : 32 ≤ p.size` and `hY : 1 ≤ (p.extract 32 p.size).size` keep both
    `OP_SPLIT` indices in range (a 64-byte point satisfies both);
  - `hX` — the x-half of `p` is the canonical 32-byte big-endian encoding of the
    spec x-coordinate (`p` round-trips its x);
  - `hPar` — the parity the codegen reads off the LAST byte of the y-half equals
    the spec's `pointY p % 2` (the LSB of a big-endian coordinate carries its
    parity).

  Both `hX`/`hPar` are honest invariants of every canonically-encoded point the
  EC codegen emits (witnessed by `smoke_ecEncodeCompressed_*`).  They are NOT
  assumptions about the OUTPUT — they constrain only the input `p`.

No new axiom (the spec defs and the Stack VM are USED, not introduced); both
theorems `#print axioms`-clean (only the inherited backend/`propext`/`Quot.sound`
TCB, never `sorryAx` and never the axioms they replace). -/

/-- **DISCHARGED (deliverable 1).**  `Stack.Ec.emitEcModReduce` agrees with the
spec `Crypto.Secp256k1.ecModReduce`, under the divByZero guard `m ≠ 0`.  This is
the theorem that replaces the `Crypto.Spec.emitEcModReduce_runOps_eq` axiom. -/
theorem emitEcModReduce_runOps_eq
    (stkSt : StackState) (value m : Int) (rest : List Value)
    (hStk : stkSt.stack = .vBigint m :: .vBigint value :: rest)
    (hM : m ≠ 0) :
    runOps Stack.Ec.emitEcModReduce stkSt
      = .ok { stkSt with
              stack := .vBigint (RunarVerification.Crypto.Secp256k1.ecModReduce value m)
                        :: rest } :=
  ecModReduce_step_transport stkSt value m rest hStk hM

/-- **Operational transport for `emitEcEncodeCompressed`.**  Running the 14-op
fragment on `[p] ++ rest` (p on TOS) lands `prefix ++ p.extract 0 32`, where the
`prefix` byte is `0x03` iff the last byte of the y-half (`p.extract 32 p.size`)
decodes to an odd parity, else `0x02`.  Preconditions keep both `OP_SPLIT`
indices in range.  Proof: 14 honest step reductions (`runOps_cons_nonIf_eq` for
the non-`.ifOp` ops; a `pop?`/`asBool?` branch split for the `.ifOp`). -/
theorem ec_encode_op_transport
    (s : StackState) (p : ByteArray) (rest : List Value)
    (hStk : s.stack = .vBytes p :: rest)
    (hSplit : (32 : Nat) ≤ p.size)
    (hY : (1 : Nat) ≤ (p.extract 32 p.size).size) :
    runOps Stack.Ec.emitEcEncodeCompressed s
      = .ok { s with
          stack :=
            .vBytes
              ((if decodeMinimalLE
                    ((p.extract 32 p.size).extract ((p.extract 32 p.size).size - 1)
                      (p.extract 32 p.size).size) % 2 ≠ 0
                then ByteArray.mk #[0x03] else ByteArray.mk #[0x02])
                ++ p.extract 0 32) :: rest } := by
  obtain ⟨stk, alt, out, props, pre⟩ := s
  subst hStk
  have niOp : ∀ (c : String) t e, StackOp.opcode c ≠ .ifOp t e := by
    intro c t e h; cases h
  have niSwap : ∀ t e, StackOp.swap ≠ .ifOp t e := by intro t e h; cases h
  have niDrop : ∀ t e, StackOp.drop ≠ .ifOp t e := by intro t e h; cases h
  have niPush : ∀ (pv : PushVal) t e, StackOp.push pv ≠ .ifOp t e := by
    intro pv t e h; cases h
  -- emitEcEncodeCompressed is the literal op list.
  show runOps
      ([ StackOp.push (.bigint 32), StackOp.opcode "OP_SPLIT", StackOp.opcode "OP_SIZE",
         StackOp.push (.bigint 1), StackOp.opcode "OP_SUB", StackOp.opcode "OP_SPLIT",
         StackOp.opcode "OP_BIN2NUM", StackOp.push (.bigint 2), StackOp.opcode "OP_MOD",
         StackOp.swap, StackOp.drop,
         StackOp.ifOp [StackOp.push (.bytes (ByteArray.mk #[0x03]))]
                      (some [StackOp.push (.bytes (ByteArray.mk #[0x02]))]),
         StackOp.swap, StackOp.opcode "OP_CAT" ])
      { stack := .vBytes p :: rest, altstack := alt,
        outputs := out, props := props, preimage := pre } = _
  -- Step 1: push 32.
  rw [runOps_cons_nonIf_eq _ _ _ (niPush (.bigint 32)), stepNonIf_push_bigint]
  simp only [match_Except_ok_runOps, StackState.push]
  -- Step 2: OP_SPLIT at index 32 → [yb, xb].
  rw [runOps_cons_nonIf_eq _ _ _ (niOp "OP_SPLIT"), stepNonIf_opcode]
  rw [show runOpcode "OP_SPLIT"
        { stack := .vBigint 32 :: .vBytes p :: rest, altstack := alt,
          outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBytes (p.extract 32 p.size) :: .vBytes (p.extract 0 32) :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } by
      unfold runOpcode
      simp only [popN, StackState.pop?, asBytes?, asNonNegativeNat?, asInt?,
                 StackState.push, Int.reduceLT, reduceIte]
      rw [if_neg (by omega : ¬ (32 : Int).toNat > p.size)]
      rfl ]
  simp only [match_Except_ok_runOps]
  -- Step 3: OP_SIZE → size of yb on top.
  rw [runOps_cons_nonIf_eq _ _ _ (niOp "OP_SIZE"), stepNonIf_opcode]
  rw [show runOpcode "OP_SIZE"
        { stack := .vBytes (p.extract 32 p.size) :: .vBytes (p.extract 0 32) :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBigint (p.extract 32 p.size).size
                          :: .vBytes (p.extract 32 p.size) :: .vBytes (p.extract 0 32) :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps]
  -- Step 4: push 1.
  rw [runOps_cons_nonIf_eq _ _ _ (niPush (.bigint 1)), stepNonIf_push_bigint]
  simp only [match_Except_ok_runOps, StackState.push]
  -- Step 5: OP_SUB → (yb.size) - 1.
  rw [runOps_cons_nonIf_eq _ _ _ (niOp "OP_SUB"), stepNonIf_opcode]
  rw [show runOpcode "OP_SUB"
        { stack := .vBigint 1 :: .vBigint (p.extract 32 p.size).size
                    :: .vBytes (p.extract 32 p.size) :: .vBytes (p.extract 0 32) :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBigint (((p.extract 32 p.size).size : Int) - 1)
                          :: .vBytes (p.extract 32 p.size) :: .vBytes (p.extract 0 32) :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps]
  -- Step 6: OP_SPLIT at index (yb.size - 1).
  rw [runOps_cons_nonIf_eq _ _ _ (niOp "OP_SPLIT"), stepNonIf_opcode]
  rw [show runOpcode "OP_SPLIT"
        { stack := .vBigint (((p.extract 32 p.size).size : Int) - 1)
                    :: .vBytes (p.extract 32 p.size) :: .vBytes (p.extract 0 32) :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBytes ((p.extract 32 p.size).extract ((p.extract 32 p.size).size - 1)
                                    (p.extract 32 p.size).size)
                          :: .vBytes ((p.extract 32 p.size).extract 0 ((p.extract 32 p.size).size - 1))
                          :: .vBytes (p.extract 0 32) :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } by
      unfold runOpcode
      simp only [popN, StackState.pop?, asBytes?, asNonNegativeNat?, asInt?,
                 StackState.push, reduceIte]
      rw [if_neg (show ¬ ((p.extract 32 p.size).size : Int) - 1 < 0 by omega)]
      have htn : (((p.extract 32 p.size).size : Int) - 1).toNat = (p.extract 32 p.size).size - 1 := by omega
      rw [htn]
      dsimp only
      rw [if_neg (show ¬ (p.extract 32 p.size).size - 1 > (p.extract 32 p.size).size by omega)] ]
  simp only [match_Except_ok_runOps]
  -- Step 7: OP_BIN2NUM → decodeMinimalLE last_byte.
  rw [runOps_cons_nonIf_eq _ _ _ (niOp "OP_BIN2NUM"), stepNonIf_opcode]
  rw [show runOpcode "OP_BIN2NUM"
        { stack := .vBytes ((p.extract 32 p.size).extract ((p.extract 32 p.size).size - 1)
                              (p.extract 32 p.size).size)
                    :: .vBytes ((p.extract 32 p.size).extract 0 ((p.extract 32 p.size).size - 1))
                    :: .vBytes (p.extract 0 32) :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBigint (decodeMinimalLE ((p.extract 32 p.size).extract
                            ((p.extract 32 p.size).size - 1) (p.extract 32 p.size).size))
                          :: .vBytes ((p.extract 32 p.size).extract 0 ((p.extract 32 p.size).size - 1))
                          :: .vBytes (p.extract 0 32) :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps]
  -- Step 8: push 2.
  rw [runOps_cons_nonIf_eq _ _ _ (niPush (.bigint 2)), stepNonIf_push_bigint]
  simp only [match_Except_ok_runOps, StackState.push]
  -- Step 9: OP_MOD → parity = num % 2.
  rw [runOps_cons_nonIf_eq _ _ _ (niOp "OP_MOD"), stepNonIf_opcode]
  rw [show runOpcode "OP_MOD"
        { stack := .vBigint 2
                    :: .vBigint (decodeMinimalLE ((p.extract 32 p.size).extract
                          ((p.extract 32 p.size).size - 1) (p.extract 32 p.size).size))
                    :: .vBytes ((p.extract 32 p.size).extract 0 ((p.extract 32 p.size).size - 1))
                    :: .vBytes (p.extract 0 32) :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBigint (decodeMinimalLE ((p.extract 32 p.size).extract
                            ((p.extract 32 p.size).size - 1) (p.extract 32 p.size).size) % 2)
                          :: .vBytes ((p.extract 32 p.size).extract 0 ((p.extract 32 p.size).size - 1))
                          :: .vBytes (p.extract 0 32) :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } by
      show (if (2 : Int) == 0 then (Except.error EvalError.divByZero : EvalResult StackState)
            else .ok _) = _
      rw [if_neg (by decide)]; rfl ]
  simp only [match_Except_ok_runOps]
  -- Step 10: swap → [y_prefix, parity, xb].
  rw [runOps_cons_nonIf_eq _ _ _ niSwap, stepNonIf_swap]
  rw [show applySwap
        { stack := .vBigint (decodeMinimalLE ((p.extract 32 p.size).extract
                      ((p.extract 32 p.size).size - 1) (p.extract 32 p.size).size) % 2)
                    :: .vBytes ((p.extract 32 p.size).extract 0 ((p.extract 32 p.size).size - 1))
                    :: .vBytes (p.extract 0 32) :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBytes ((p.extract 32 p.size).extract 0 ((p.extract 32 p.size).size - 1))
                          :: .vBigint (decodeMinimalLE ((p.extract 32 p.size).extract
                                ((p.extract 32 p.size).size - 1) (p.extract 32 p.size).size) % 2)
                          :: .vBytes (p.extract 0 32) :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps]
  -- Step 11: drop → [parity, xb].
  rw [runOps_cons_nonIf_eq _ _ _ niDrop, stepNonIf_drop]
  rw [show applyDrop
        { stack := .vBytes ((p.extract 32 p.size).extract 0 ((p.extract 32 p.size).size - 1))
                    :: .vBigint (decodeMinimalLE ((p.extract 32 p.size).extract
                          ((p.extract 32 p.size).size - 1) (p.extract 32 p.size).size) % 2)
                    :: .vBytes (p.extract 0 32) :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBigint (decodeMinimalLE ((p.extract 32 p.size).extract
                            ((p.extract 32 p.size).size - 1) (p.extract 32 p.size).size) % 2)
                          :: .vBytes (p.extract 0 32) :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps]
  -- Step 12: ifOp — pops parity, picks prefix byte by parity ≠ 0.
  rw [show runOps
        ([ StackOp.ifOp [StackOp.push (.bytes (ByteArray.mk #[0x03]))]
                        (some [StackOp.push (.bytes (ByteArray.mk #[0x02]))]),
           StackOp.swap, StackOp.opcode "OP_CAT" ])
        { stack := .vBigint (decodeMinimalLE ((p.extract 32 p.size).extract
                      ((p.extract 32 p.size).size - 1) (p.extract 32 p.size).size) % 2)
                    :: .vBytes (p.extract 0 32) :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        = runOps ([ StackOp.swap, StackOp.opcode "OP_CAT" ])
            { stack := (if decodeMinimalLE ((p.extract 32 p.size).extract
                            ((p.extract 32 p.size).size - 1) (p.extract 32 p.size).size) % 2 ≠ 0
                        then .vBytes (ByteArray.mk #[0x03]) else .vBytes (ByteArray.mk #[0x02]))
                        :: .vBytes (p.extract 0 32) :: rest,
              altstack := alt, outputs := out, props := props, preimage := pre } by
      rw [runOps]
      by_cases hpar : decodeMinimalLE ((p.extract 32 p.size).extract
                        ((p.extract 32 p.size).size - 1) (p.extract 32 p.size).size) % 2 = 0
      · rw [if_neg (not_not_intro hpar)]
        show (match asBool? (.vBigint (decodeMinimalLE ((p.extract 32 p.size).extract
                ((p.extract 32 p.size).size - 1) (p.extract 32 p.size).size) % 2)) with
              | some true => _ | some false => _ | none => _) = _
        rw [show asBool? (.vBigint (decodeMinimalLE ((p.extract 32 p.size).extract
              ((p.extract 32 p.size).size - 1) (p.extract 32 p.size).size) % 2))
              = some false by simp only [asBool?, ne_eq, hpar, not_true_eq_false, decide_false]]
        simp only []
        rw [runOps_cons_nonIf_eq _ _ _ (niPush (.bytes (ByteArray.mk #[0x02]))),
            stepNonIf_push_bytes]
        simp only [match_Except_ok_runOps, StackState.push, runOps_nil]
      · rw [if_pos hpar]
        show (match asBool? (.vBigint (decodeMinimalLE ((p.extract 32 p.size).extract
                ((p.extract 32 p.size).size - 1) (p.extract 32 p.size).size) % 2)) with
              | some true => _ | some false => _ | none => _) = _
        rw [show asBool? (.vBigint (decodeMinimalLE ((p.extract 32 p.size).extract
              ((p.extract 32 p.size).size - 1) (p.extract 32 p.size).size) % 2))
              = some true by simp only [asBool?, ne_eq, hpar, not_false_eq_true, decide_true]]
        simp only []
        rw [runOps_cons_nonIf_eq _ _ _ (niPush (.bytes (ByteArray.mk #[0x03]))),
            stepNonIf_push_bytes]
        simp only [match_Except_ok_runOps, StackState.push, runOps_nil] ]
  -- Step 13: swap → [xb, prefix].
  rw [runOps_cons_nonIf_eq _ _ _ niSwap, stepNonIf_swap]
  rw [show applySwap
        { stack := (if decodeMinimalLE ((p.extract 32 p.size).extract
                        ((p.extract 32 p.size).size - 1) (p.extract 32 p.size).size) % 2 ≠ 0
                    then .vBytes (ByteArray.mk #[0x03]) else .vBytes (ByteArray.mk #[0x02]))
                    :: .vBytes (p.extract 0 32) :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBytes (p.extract 0 32)
                          :: (if decodeMinimalLE ((p.extract 32 p.size).extract
                                  ((p.extract 32 p.size).size - 1) (p.extract 32 p.size).size) % 2 ≠ 0
                              then .vBytes (ByteArray.mk #[0x03]) else .vBytes (ByteArray.mk #[0x02]))
                          :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps]
  -- Step 14: OP_CAT → prefix ++ xb.
  rw [runOps_cons_nonIf_eq _ _ _ (niOp "OP_CAT"), stepNonIf_opcode]
  rw [show runOpcode "OP_CAT"
        { stack := .vBytes (p.extract 0 32)
                    :: (if decodeMinimalLE ((p.extract 32 p.size).extract
                            ((p.extract 32 p.size).size - 1) (p.extract 32 p.size).size) % 2 ≠ 0
                        then .vBytes (ByteArray.mk #[0x03]) else .vBytes (ByteArray.mk #[0x02]))
                    :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBytes ((if decodeMinimalLE ((p.extract 32 p.size).extract
                              ((p.extract 32 p.size).size - 1) (p.extract 32 p.size).size) % 2 ≠ 0
                            then ByteArray.mk #[0x03] else ByteArray.mk #[0x02]) ++ p.extract 0 32)
                          :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } by
      by_cases hpar : decodeMinimalLE ((p.extract 32 p.size).extract
                        ((p.extract 32 p.size).size - 1) (p.extract 32 p.size).size) % 2 = 0
      · rw [if_neg (not_not_intro hpar), if_neg (not_not_intro hpar)]; rfl
      · rw [if_pos hpar, if_pos hpar]; rfl ]
  simp only [match_Except_ok_runOps, runOps_nil]

open RunarVerification.Crypto.Secp256k1 (ecEncodeCompressed pointX pointY intToBE32) in
/-- **DISCHARGED (deliverable 2).**  `Stack.Ec.emitEcEncodeCompressed` agrees with
the spec `Crypto.Secp256k1.ecEncodeCompressed`, under canonical-encoding
well-formedness on the input point `p` (`hX`, `hPar`) plus the two split-range
preconditions (`hSplit`, `hY`).  This is the theorem that replaces the
`Crypto.Spec.emitEcEncodeCompressed_runOps_eq` axiom (which was missing all four
hypotheses, hence not dischargeable verbatim). -/
theorem emitEcEncodeCompressed_runOps_eq
    (stkSt : StackState) (p : ByteArray) (rest : List Value)
    (hStk : stkSt.stack = .vBytes p :: rest)
    (hSplit : (32 : Nat) ≤ p.size)
    (hY : (1 : Nat) ≤ (p.extract 32 p.size).size)
    (hX : p.extract 0 32 = intToBE32 (pointX p))
    (hPar : decodeMinimalLE ((p.extract 32 p.size).extract ((p.extract 32 p.size).size - 1)
              (p.extract 32 p.size).size) % 2 = pointY p % 2) :
    runOps Stack.Ec.emitEcEncodeCompressed stkSt
      = .ok { stkSt with stack := .vBytes (ecEncodeCompressed p) :: rest } := by
  rw [ec_encode_op_transport stkSt p rest hStk hSplit hY]
  congr 2
  rw [hX]
  unfold ecEncodeCompressed
  simp only []
  rw [hPar]
  by_cases hy : pointY p % 2 = 0
  · rw [if_neg (not_not_intro hy), if_pos hy]
  · rw [if_pos hy, if_neg hy]

/-! ### MANDATORY in-file smokes (deliverable 1 + 2, anti-vacuous, concrete) -/

/-- Concrete two-int stack `[7, 23]` (m = 7 on TOS, value = 23) for the
ecModReduce discharge. -/
private def smokeModStk : StackState :=
  { (default : StackState) with stack := [.vBigint 7, .vBigint 23] }

/-- SMOKE (deliverable 1).  The discharged `emitEcModReduce_runOps_eq` FIRES on
`[7, 23]`, landing `ecModReduce 23 7 = 2`. -/
theorem smoke_emitEcModReduce_runOps_eq :
    runOps Stack.Ec.emitEcModReduce smokeModStk
      = .ok { smokeModStk with
              stack := .vBigint (RunarVerification.Crypto.Secp256k1.ecModReduce 23 7) :: [] } :=
  emitEcModReduce_runOps_eq smokeModStk 23 7 [] rfl (by decide)

/-- A concrete CANONICALLY-ENCODED point `p = makePoint 5 6` (x = 5, y = 6), so
the wf hypotheses `hX`/`hPar` hold by computation, and `p.size = 64`. -/
private def smokeEncPt : ByteArray :=
  RunarVerification.Crypto.Secp256k1.makePoint 5 6

/-- Concrete one-point stack `[p]` for the ecEncodeCompressed discharge. -/
private def smokeEncStk : StackState :=
  { (default : StackState) with stack := [.vBytes smokeEncPt] }

/-- SMOKE (deliverable 2, wf anti-vacuity).  The two well-formedness hypotheses
of `emitEcEncodeCompressed_runOps_eq` are SATISFIABLE — they hold concretely for
the canonically-encoded point `makePoint 5 6`.  `native_decide` is legitimate:
`intToBE32`, `pointX/Y`, `decodeMinimalLE`, `extract` are all closed-form
computable.  This rules out a vacuous discharge. -/
theorem smoke_ecEncodeCompressed_wf_satisfiable :
    (32 : Nat) ≤ smokeEncPt.size
      ∧ (1 : Nat) ≤ (smokeEncPt.extract 32 smokeEncPt.size).size
      ∧ smokeEncPt.extract 0 32
          = RunarVerification.Crypto.Secp256k1.intToBE32
              (RunarVerification.Crypto.Secp256k1.pointX smokeEncPt)
      ∧ decodeMinimalLE ((smokeEncPt.extract 32 smokeEncPt.size).extract
            ((smokeEncPt.extract 32 smokeEncPt.size).size - 1)
            (smokeEncPt.extract 32 smokeEncPt.size).size) % 2
          = RunarVerification.Crypto.Secp256k1.pointY smokeEncPt % 2 := by
  native_decide

/-- SMOKE (deliverable 2, the headline).  The discharged
`emitEcEncodeCompressed_runOps_eq` FIRES on the concrete well-formed point: the
14-op fragment lands exactly `ecEncodeCompressed (makePoint 5 6)`. -/
theorem smoke_emitEcEncodeCompressed_runOps_eq :
    runOps Stack.Ec.emitEcEncodeCompressed smokeEncStk
      = .ok { smokeEncStk with
              stack := .vBytes (RunarVerification.Crypto.Secp256k1.ecEncodeCompressed smokeEncPt)
                        :: [] } :=
  emitEcEncodeCompressed_runOps_eq smokeEncStk smokeEncPt [] rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

/-- SMOKE (deliverable 2, value anti-vacuity).  The deployed compressed encoding
of `makePoint 5 6` is concretely the 33-byte `0x02 ‖ 32-byte BE x` (y = 6 is even
→ prefix `0x02`).  `native_decide` is legitimate (the spec is closed-form). -/
theorem smoke_ecEncodeCompressed_value_concrete :
    (RunarVerification.Crypto.Secp256k1.ecEncodeCompressed smokeEncPt).toList
      = (0x02 :: (List.replicate 31 (0 : UInt8)) ++ [(5 : UInt8)]) := by
  native_decide

/-! ## Part 7 — DISCHARGED `Crypto/Spec.lean §7` axioms: the four
`reverse32`-routed "medium" coordinate ops

`ecPointX`, `ecPointY`, and `ecMakePoint` are plain op-lists whose only
non-trivial sub-block is `emitReverse32Ops` (now a theorem, Part 5).  Each runs:
* a 32-byte `OP_SPLIT` (range-guarded by `32 ≤ p.size`),
* `drop`/`swap+drop` to isolate the wanted half,
* `emitReverse32Ops` to byte-reverse it (LE) — discharged by
  `reverse32_ops_transport`,
* (X/Y) `push 0x00 ; OP_CAT ; OP_BIN2NUM` to decode the LE run as a non-negative
  `Int`, or
* (MakePoint) `push 33 ; OP_NUM2BIN ; push 32 ; OP_SPLIT ; drop ; reverse` per
  coordinate then `OP_CAT`.

Each lands the codegen output expressed in `p`'s byte extracts (or the
`num2binEncode?` of the inputs); the discharge then lifts it to the spec
(`Crypto.Secp256k1.ecPointX / ecPointY / ecMakePoint`) under input-level
canonical-encoding well-formedness — the byte-arith bridge that
`decodeMinimalLE`/`num2binEncode?` round-trip the spec's big-endian `be32At` /
`intToBE32`.  These are NOT output assumptions: they constrain only the input
`p` (or the relation between the `OP_NUM2BIN` encoding and `intToBE32`), exactly
as the wave-73 `hX`/`hPar` did for `ecEncodeCompressed`.  Both `OP_SPLIT` index
guards (`32 ≤ p.size`) are honest input wf (a 64-byte point satisfies them). -/

/-- **Operational transport for `emitEcPointX`.**  Running the
`[push 32, OP_SPLIT, drop] ++ emitReverse32Ops ++ [push 0x00, OP_CAT, OP_BIN2NUM]`
fragment on `[p] ++ rest` lands `decodeMinimalLE (revLE ++ 0x00)`, where
`revLE = reverseAcc 32 (p.extract 0 32) empty` is the byte-reversed (little-endian)
x-half.  Precondition `32 ≤ p.size` keeps the `OP_SPLIT` index in range and makes
the x-half exactly 32 bytes (so `reverse32_ops_transport` applies). -/
theorem ec_pointX_op_transport
    (s : StackState) (p : ByteArray) (rest : List Value)
    (hStk : s.stack = .vBytes p :: rest)
    (hSplit : (32 : Nat) ≤ p.size) :
    runOps Stack.Ec.emitEcPointX s
      = .ok { s with
          stack := .vBigint (decodeMinimalLE
            (reverseAcc 32 (p.extract 0 32) ByteArray.empty ++ ByteArray.mk #[0x00]))
            :: rest } := by
  obtain ⟨stk, alt, out, props, pre⟩ := s
  subst hStk
  have niOp : ∀ (c : String) t e, StackOp.opcode c ≠ .ifOp t e := by
    intro c t e h; cases h
  have niDrop : ∀ t e, StackOp.drop ≠ .ifOp t e := by intro t e h; cases h
  have niPush : ∀ (pv : PushVal) t e, StackOp.push pv ≠ .ifOp t e := by
    intro pv t e h; cases h
  have hXsize : (p.extract 0 32).size = 32 := by rw [ByteArray.size_extract]; omega
  -- emitEcPointX = [push 32, OP_SPLIT, drop] ++ emitReverse32Ops ++ [push 0x00, OP_CAT, OP_BIN2NUM]
  have hUnfold : Stack.Ec.emitEcPointX
      = StackOp.push (.bigint 32) :: StackOp.opcode "OP_SPLIT" :: StackOp.drop
          :: (Stack.Ec.emitReverse32Ops
              ++ [StackOp.push (.bytes (ByteArray.mk #[0x00])), StackOp.opcode "OP_CAT",
                  StackOp.opcode "OP_BIN2NUM"]) := rfl
  rw [hUnfold]
  -- Step 1: push 32.
  rw [runOps_cons_nonIf_eq _ _ _ (niPush (.bigint 32)), stepNonIf_push_bigint]
  simp only [match_Except_ok_runOps, StackState.push]
  -- Step 2: OP_SPLIT at index 32 → [x_high(=p.extract 32 size), p.extract 0 32].
  rw [runOps_cons_nonIf_eq _ _ _ (niOp "OP_SPLIT"), stepNonIf_opcode]
  rw [show runOpcode "OP_SPLIT"
        { stack := .vBigint 32 :: .vBytes p :: rest, altstack := alt,
          outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBytes (p.extract 32 p.size) :: .vBytes (p.extract 0 32) :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } by
      unfold runOpcode
      simp only [popN, StackState.pop?, asBytes?, asNonNegativeNat?, asInt?,
                 StackState.push, Int.reduceLT, reduceIte]
      rw [if_neg (by omega : ¬ (32 : Int).toNat > p.size)]
      rfl ]
  simp only [match_Except_ok_runOps]
  -- Step 3: drop → [p.extract 0 32].
  rw [runOps_cons_nonIf_eq _ _ _ niDrop, stepNonIf_drop]
  rw [show applyDrop
        { stack := .vBytes (p.extract 32 p.size) :: .vBytes (p.extract 0 32) :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBytes (p.extract 0 32) :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps]
  -- emitReverse32Ops ++ tail.
  rw [runOps_append]
  -- The reverse32 wrapper transport on the 32-byte x-half.
  rw [reverse32_ops_transport
        { stack := .vBytes (p.extract 0 32) :: rest, altstack := alt,
          outputs := out, props := props, preimage := pre }
        (p.extract 0 32) rest rfl (by rw [hXsize]; omega)]
  simp only [match_Except_ok_runOps]
  -- Step: push 0x00.
  rw [runOps_cons_nonIf_eq _ _ _ (niPush (.bytes (ByteArray.mk #[0x00]))), stepNonIf_push_bytes]
  simp only [match_Except_ok_runOps, StackState.push]
  -- Step: OP_CAT → revLE ++ 0x00.
  rw [runOps_cons_nonIf_eq _ _ _ (niOp "OP_CAT"), stepNonIf_opcode]
  rw [show runOpcode "OP_CAT"
        { stack := .vBytes (ByteArray.mk #[0x00])
                    :: .vBytes (reverseAcc 32 (p.extract 0 32) ByteArray.empty) :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBytes (reverseAcc 32 (p.extract 0 32) ByteArray.empty
                                    ++ ByteArray.mk #[0x00]) :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps]
  -- Step: OP_BIN2NUM → decodeMinimalLE (revLE ++ 0x00).
  rw [runOps_cons_nonIf_eq _ _ _ (niOp "OP_BIN2NUM"), stepNonIf_opcode]
  rw [show runOpcode "OP_BIN2NUM"
        { stack := .vBytes (reverseAcc 32 (p.extract 0 32) ByteArray.empty
                              ++ ByteArray.mk #[0x00]) :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBigint (decodeMinimalLE (reverseAcc 32 (p.extract 0 32)
                            ByteArray.empty ++ ByteArray.mk #[0x00])) :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps, runOps_nil]

open RunarVerification.Crypto.Secp256k1 (ecPointX) in
/-- **DISCHARGED.**  `Stack.Ec.emitEcPointX` agrees with `Crypto.Secp256k1.ecPointX`,
under the split-range guard `32 ≤ p.size` plus the canonical-decode bridge
`hDec`: the little-endian byte-reversed x-half (with the `0x00` sign byte the
codegen appends) decodes to the spec x-coordinate.  `hDec` is an honest invariant
of every canonically big-endian-encoded 64-byte point the EC codegen emits — it
constrains only the input `p`, not the output, mirroring wave-73's `hX`.  This is
the theorem that replaces the `Crypto.Spec.emitEcPointX_runOps_eq` axiom. -/
theorem emitEcPointX_runOps_eq
    (stkSt : StackState) (pt : ByteArray) (rest : List Value)
    (hStk : stkSt.stack = .vBytes pt :: rest)
    (hSplit : (32 : Nat) ≤ pt.size)
    (hDec : decodeMinimalLE
              (reverseAcc 32 (pt.extract 0 32) ByteArray.empty ++ ByteArray.mk #[0x00])
              = ecPointX pt) :
    runOps Stack.Ec.emitEcPointX stkSt
      = .ok { stkSt with stack := .vBigint (ecPointX pt) :: rest } := by
  rw [ec_pointX_op_transport stkSt pt rest hStk hSplit, hDec]

/-! ### MANDATORY smokes for the ecPointX discharge -/

/-- A concrete canonically-encoded point `p = makePoint 11 22`, so `p.size = 64`
and the decode bridge holds by computation. -/
private def smokePtX : ByteArray :=
  RunarVerification.Crypto.Secp256k1.makePoint 11 22

private def smokePtXStk : StackState :=
  { (default : StackState) with stack := [.vBytes smokePtX] }

/-- SMOKE (wf anti-vacuity).  The split-range and decode-bridge hypotheses of
`emitEcPointX_runOps_eq` are SATISFIABLE — they hold concretely for the
canonically-encoded `makePoint 11 22`.  `native_decide` is legitimate (every
function involved is closed-form computable).  Rules out a vacuous discharge. -/
theorem smoke_ecPointX_wf_satisfiable :
    (32 : Nat) ≤ smokePtX.size
      ∧ decodeMinimalLE
          (reverseAcc 32 (smokePtX.extract 0 32) ByteArray.empty ++ ByteArray.mk #[0x00])
          = RunarVerification.Crypto.Secp256k1.ecPointX smokePtX := by
  native_decide

/-- SMOKE (the headline).  The discharged `emitEcPointX_runOps_eq` FIRES on the
concrete point: the fragment lands exactly `ecPointX (makePoint 11 22) = 11`. -/
theorem smoke_emitEcPointX_runOps_eq :
    runOps Stack.Ec.emitEcPointX smokePtXStk
      = .ok { smokePtXStk with
              stack := .vBigint (RunarVerification.Crypto.Secp256k1.ecPointX smokePtX) :: [] } :=
  emitEcPointX_runOps_eq smokePtXStk smokePtX [] rfl (by native_decide) (by native_decide)

/-- SMOKE (value anti-vacuity).  The extracted x is concretely `11`.
`native_decide` is legitimate (the spec is closed-form). -/
theorem smoke_ecPointX_value_concrete :
    RunarVerification.Crypto.Secp256k1.ecPointX smokePtX = 11 := by
  native_decide

/-- **Operational transport for `emitEcPointY`.**  Running the
`[push 32, OP_SPLIT, swap, drop] ++ emitReverse32Ops ++ [push 0x00, OP_CAT, OP_BIN2NUM]`
fragment on `[p] ++ rest` lands `decodeMinimalLE (revLE ++ 0x00)`, where
`revLE = reverseAcc 32 (p.extract 32 p.size) empty` is the byte-reversed
(little-endian) y-half.  Precondition `64 ≤ p.size` keeps the `OP_SPLIT` index in
range AND makes the y-half ≥ 32 bytes (so `reverse32_ops_transport` applies). -/
theorem ec_pointY_op_transport
    (s : StackState) (p : ByteArray) (rest : List Value)
    (hStk : s.stack = .vBytes p :: rest)
    (hSplit : (64 : Nat) ≤ p.size) :
    runOps Stack.Ec.emitEcPointY s
      = .ok { s with
          stack := .vBigint (decodeMinimalLE
            (reverseAcc 32 (p.extract 32 p.size) ByteArray.empty ++ ByteArray.mk #[0x00]))
            :: rest } := by
  obtain ⟨stk, alt, out, props, pre⟩ := s
  subst hStk
  have niOp : ∀ (c : String) t e, StackOp.opcode c ≠ .ifOp t e := by
    intro c t e h; cases h
  have niDrop : ∀ t e, StackOp.drop ≠ .ifOp t e := by intro t e h; cases h
  have niSwap : ∀ t e, StackOp.swap ≠ .ifOp t e := by intro t e h; cases h
  have niPush : ∀ (pv : PushVal) t e, StackOp.push pv ≠ .ifOp t e := by
    intro pv t e h; cases h
  have hYsize : (p.extract 32 p.size).size = p.size - 32 := by rw [ByteArray.size_extract]; omega
  -- emitEcPointY = [push 32, OP_SPLIT, swap, drop] ++ emitReverse32Ops ++ tail
  have hUnfold : Stack.Ec.emitEcPointY
      = StackOp.push (.bigint 32) :: StackOp.opcode "OP_SPLIT" :: StackOp.swap :: StackOp.drop
          :: (Stack.Ec.emitReverse32Ops
              ++ [StackOp.push (.bytes (ByteArray.mk #[0x00])), StackOp.opcode "OP_CAT",
                  StackOp.opcode "OP_BIN2NUM"]) := rfl
  rw [hUnfold]
  -- Step 1: push 32.
  rw [runOps_cons_nonIf_eq _ _ _ (niPush (.bigint 32)), stepNonIf_push_bigint]
  simp only [match_Except_ok_runOps, StackState.push]
  -- Step 2: OP_SPLIT at index 32 → [p.extract 32 size, p.extract 0 32].
  rw [runOps_cons_nonIf_eq _ _ _ (niOp "OP_SPLIT"), stepNonIf_opcode]
  rw [show runOpcode "OP_SPLIT"
        { stack := .vBigint 32 :: .vBytes p :: rest, altstack := alt,
          outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBytes (p.extract 32 p.size) :: .vBytes (p.extract 0 32) :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } by
      unfold runOpcode
      simp only [popN, StackState.pop?, asBytes?, asNonNegativeNat?, asInt?,
                 StackState.push, Int.reduceLT, reduceIte]
      rw [if_neg (by omega : ¬ (32 : Int).toNat > p.size)]
      rfl ]
  simp only [match_Except_ok_runOps]
  -- Step 3: swap → [p.extract 0 32, p.extract 32 size].
  rw [runOps_cons_nonIf_eq _ _ _ niSwap, stepNonIf_swap]
  rw [show applySwap
        { stack := .vBytes (p.extract 32 p.size) :: .vBytes (p.extract 0 32) :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBytes (p.extract 0 32) :: .vBytes (p.extract 32 p.size) :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps]
  -- Step 4: drop → [p.extract 32 size].
  rw [runOps_cons_nonIf_eq _ _ _ niDrop, stepNonIf_drop]
  rw [show applyDrop
        { stack := .vBytes (p.extract 0 32) :: .vBytes (p.extract 32 p.size) :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBytes (p.extract 32 p.size) :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps]
  -- emitReverse32Ops ++ tail.
  rw [runOps_append]
  rw [reverse32_ops_transport
        { stack := .vBytes (p.extract 32 p.size) :: rest, altstack := alt,
          outputs := out, props := props, preimage := pre }
        (p.extract 32 p.size) rest rfl (by rw [hYsize]; omega)]
  simp only [match_Except_ok_runOps]
  -- Step: push 0x00.
  rw [runOps_cons_nonIf_eq _ _ _ (niPush (.bytes (ByteArray.mk #[0x00]))), stepNonIf_push_bytes]
  simp only [match_Except_ok_runOps, StackState.push]
  -- Step: OP_CAT → revLE ++ 0x00.
  rw [runOps_cons_nonIf_eq _ _ _ (niOp "OP_CAT"), stepNonIf_opcode]
  rw [show runOpcode "OP_CAT"
        { stack := .vBytes (ByteArray.mk #[0x00])
                    :: .vBytes (reverseAcc 32 (p.extract 32 p.size) ByteArray.empty) :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBytes (reverseAcc 32 (p.extract 32 p.size) ByteArray.empty
                                    ++ ByteArray.mk #[0x00]) :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps]
  -- Step: OP_BIN2NUM → decodeMinimalLE (revLE ++ 0x00).
  rw [runOps_cons_nonIf_eq _ _ _ (niOp "OP_BIN2NUM"), stepNonIf_opcode]
  rw [show runOpcode "OP_BIN2NUM"
        { stack := .vBytes (reverseAcc 32 (p.extract 32 p.size) ByteArray.empty
                              ++ ByteArray.mk #[0x00]) :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBigint (decodeMinimalLE (reverseAcc 32 (p.extract 32 p.size)
                            ByteArray.empty ++ ByteArray.mk #[0x00])) :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps, runOps_nil]

open RunarVerification.Crypto.Secp256k1 (ecPointY) in
/-- **DISCHARGED.**  `Stack.Ec.emitEcPointY` agrees with `Crypto.Secp256k1.ecPointY`,
under the split-range guard `64 ≤ p.size` plus the canonical-decode bridge `hDec`:
the little-endian byte-reversed y-half (with the `0x00` sign byte the codegen
appends) decodes to the spec y-coordinate.  `hDec` constrains only the input `p`
(honest invariant of canonically-encoded points), mirroring wave-73's `hX`.
Replaces the `Crypto.Spec.emitEcPointY_runOps_eq` axiom. -/
theorem emitEcPointY_runOps_eq
    (stkSt : StackState) (pt : ByteArray) (rest : List Value)
    (hStk : stkSt.stack = .vBytes pt :: rest)
    (hSplit : (64 : Nat) ≤ pt.size)
    (hDec : decodeMinimalLE
              (reverseAcc 32 (pt.extract 32 pt.size) ByteArray.empty ++ ByteArray.mk #[0x00])
              = ecPointY pt) :
    runOps Stack.Ec.emitEcPointY stkSt
      = .ok { stkSt with stack := .vBigint (ecPointY pt) :: rest } := by
  rw [ec_pointY_op_transport stkSt pt rest hStk hSplit, hDec]

/-! ### MANDATORY smokes for the ecPointY discharge -/

private def smokePtY : ByteArray :=
  RunarVerification.Crypto.Secp256k1.makePoint 11 22

private def smokePtYStk : StackState :=
  { (default : StackState) with stack := [.vBytes smokePtY] }

/-- SMOKE (wf anti-vacuity).  The split-range and decode-bridge hypotheses of
`emitEcPointY_runOps_eq` hold concretely for `makePoint 11 22`. -/
theorem smoke_ecPointY_wf_satisfiable :
    (64 : Nat) ≤ smokePtY.size
      ∧ decodeMinimalLE
          (reverseAcc 32 (smokePtY.extract 32 smokePtY.size) ByteArray.empty ++ ByteArray.mk #[0x00])
          = RunarVerification.Crypto.Secp256k1.ecPointY smokePtY := by
  native_decide

/-- SMOKE (the headline).  The discharged `emitEcPointY_runOps_eq` FIRES,
landing `ecPointY (makePoint 11 22) = 22`. -/
theorem smoke_emitEcPointY_runOps_eq :
    runOps Stack.Ec.emitEcPointY smokePtYStk
      = .ok { smokePtYStk with
              stack := .vBigint (RunarVerification.Crypto.Secp256k1.ecPointY smokePtY) :: [] } :=
  emitEcPointY_runOps_eq smokePtYStk smokePtY [] rfl (by native_decide) (by native_decide)

/-- SMOKE (value anti-vacuity).  The extracted y is concretely `22`. -/
theorem smoke_ecPointY_value_concrete :
    RunarVerification.Crypto.Secp256k1.ecPointY smokePtY = 22 := by
  native_decide

set_option maxRecDepth 8192 in
/-- **Operational transport for `emitEcMakePoint`.**  Input stack `[y, x] ++ rest`
(y on TOS, per the spec arg order — the deepest input is the leftmost spec arg).
Each coordinate is `OP_NUM2BIN`-encoded to 33 LE bytes, split to its low 32 bytes,
then byte-reversed to big-endian; the two BE halves are concatenated `x ‖ y`.
Output: `revBE encX ++ revBE encY`, where `encX`/`encY` are the `num2binEncode?`
images of `x`/`y` at width 33.  Preconditions: both encodings succeed and are ≥32
bytes (honest input wf — every in-field coordinate fits in 33 bytes). -/
theorem ec_makePoint_op_transport
    (s : StackState) (x y : Int) (encX encY : ByteArray) (rest : List Value)
    (hStk : s.stack = .vBigint y :: .vBigint x :: rest)
    (hEncX : num2binEncode? x 33 = some encX)
    (hEncY : num2binEncode? y 33 = some encY)
    (hSzX : (32 : Nat) ≤ encX.size)
    (hSzY : (32 : Nat) ≤ encY.size) :
    runOps Stack.Ec.emitEcMakePoint s
      = .ok { s with
          stack := .vBytes (reverseAcc 32 (encX.extract 0 32) ByteArray.empty
                            ++ reverseAcc 32 (encY.extract 0 32) ByteArray.empty)
            :: rest } := by
  obtain ⟨stk, alt, out, props, pre⟩ := s
  subst hStk
  have niOp : ∀ (c : String) t e, StackOp.opcode c ≠ .ifOp t e := by
    intro c t e h; cases h
  have niDrop : ∀ t e, StackOp.drop ≠ .ifOp t e := by intro t e h; cases h
  have niSwap : ∀ t e, StackOp.swap ≠ .ifOp t e := by intro t e h; cases h
  have niPush : ∀ (pv : PushVal) t e, StackOp.push pv ≠ .ifOp t e := by
    intro pv t e h; cases h
  -- Reusable OP_NUM2BIN reduction at width 33.
  have hNum2Bin : ∀ (n : Int) (enc : ByteArray) (r : List Value),
      num2binEncode? n 33 = some enc →
      runOpcode "OP_NUM2BIN"
        { stack := .vBigint 33 :: .vBigint n :: r, altstack := alt,
          outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBytes enc :: r, altstack := alt,
                outputs := out, props := props, preimage := pre } := by
    intro n enc r hEnc
    unfold runOpcode
    simp only [popN, StackState.pop?, asInt?, StackState.push, Int.reduceLT, reduceIte]
    rw [show (33 : Int).toNat = 33 from rfl, hEnc]
  have hSzXextract : (encX.extract 0 32).size = 32 := by rw [ByteArray.size_extract]; omega
  have hSzYextract : (encY.extract 0 32).size = 32 := by rw [ByteArray.size_extract]; omega
  -- emitEcMakePoint as the literal op list.
  have hUnfold : Stack.Ec.emitEcMakePoint
      = StackOp.push (.bigint 33) :: StackOp.opcode "OP_NUM2BIN" :: StackOp.push (.bigint 32)
          :: StackOp.opcode "OP_SPLIT" :: StackOp.drop
          :: (Stack.Ec.emitReverse32Ops
              ++ (StackOp.swap :: StackOp.push (.bigint 33) :: StackOp.opcode "OP_NUM2BIN"
                  :: StackOp.push (.bigint 32) :: StackOp.opcode "OP_SPLIT" :: StackOp.drop
                  :: (Stack.Ec.emitReverse32Ops
                      ++ [StackOp.swap, StackOp.opcode "OP_CAT"]))) := rfl
  rw [hUnfold]
  -- y-branch.  push 33.
  rw [runOps_cons_nonIf_eq _ _ _ (niPush (.bigint 33)), stepNonIf_push_bigint]
  simp only [match_Except_ok_runOps, StackState.push]
  -- OP_NUM2BIN → encY.
  rw [runOps_cons_nonIf_eq _ _ _ (niOp "OP_NUM2BIN"), stepNonIf_opcode]
  rw [hNum2Bin y encY (.vBigint x :: rest) hEncY]
  simp only [match_Except_ok_runOps]
  -- push 32.
  rw [runOps_cons_nonIf_eq _ _ _ (niPush (.bigint 32)), stepNonIf_push_bigint]
  simp only [match_Except_ok_runOps, StackState.push]
  -- OP_SPLIT at 32.
  rw [runOps_cons_nonIf_eq _ _ _ (niOp "OP_SPLIT"), stepNonIf_opcode]
  rw [show runOpcode "OP_SPLIT"
        { stack := .vBigint 32 :: .vBytes encY :: .vBigint x :: rest, altstack := alt,
          outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBytes (encY.extract 32 encY.size) :: .vBytes (encY.extract 0 32)
                          :: .vBigint x :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } by
      unfold runOpcode
      simp only [popN, StackState.pop?, asBytes?, asNonNegativeNat?, asInt?,
                 StackState.push, Int.reduceLT, reduceIte]
      rw [if_neg (by omega : ¬ (32 : Int).toNat > encY.size)]
      rfl ]
  simp only [match_Except_ok_runOps]
  -- drop → [encY.extract 0 32, x].
  rw [runOps_cons_nonIf_eq _ _ _ niDrop, stepNonIf_drop]
  rw [show applyDrop
        { stack := .vBytes (encY.extract 32 encY.size) :: .vBytes (encY.extract 0 32)
                    :: .vBigint x :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBytes (encY.extract 0 32) :: .vBigint x :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps]
  -- reverse32 (y-half) ++ tail.
  rw [runOps_append]
  rw [reverse32_ops_transport
        { stack := .vBytes (encY.extract 0 32) :: .vBigint x :: rest, altstack := alt,
          outputs := out, props := props, preimage := pre }
        (encY.extract 0 32) (.vBigint x :: rest) rfl (by rw [hSzYextract]; omega)]
  simp only [match_Except_ok_runOps]
  -- swap → [x, revY_be].
  rw [runOps_cons_nonIf_eq _ _ _ niSwap, stepNonIf_swap]
  rw [show applySwap
        { stack := .vBytes (reverseAcc 32 (encY.extract 0 32) ByteArray.empty)
                    :: .vBigint x :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBigint x
                          :: .vBytes (reverseAcc 32 (encY.extract 0 32) ByteArray.empty) :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps]
  -- x-branch.  push 33.
  rw [runOps_cons_nonIf_eq _ _ _ (niPush (.bigint 33)), stepNonIf_push_bigint]
  simp only [match_Except_ok_runOps, StackState.push]
  -- OP_NUM2BIN → encX.
  rw [runOps_cons_nonIf_eq _ _ _ (niOp "OP_NUM2BIN"), stepNonIf_opcode]
  rw [hNum2Bin x encX (.vBytes (reverseAcc 32 (encY.extract 0 32) ByteArray.empty) :: rest) hEncX]
  simp only [match_Except_ok_runOps]
  -- push 32.
  rw [runOps_cons_nonIf_eq _ _ _ (niPush (.bigint 32)), stepNonIf_push_bigint]
  simp only [match_Except_ok_runOps, StackState.push]
  -- OP_SPLIT at 32.
  rw [runOps_cons_nonIf_eq _ _ _ (niOp "OP_SPLIT"), stepNonIf_opcode]
  rw [show runOpcode "OP_SPLIT"
        { stack := .vBigint 32 :: .vBytes encX
                    :: .vBytes (reverseAcc 32 (encY.extract 0 32) ByteArray.empty) :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBytes (encX.extract 32 encX.size) :: .vBytes (encX.extract 0 32)
                          :: .vBytes (reverseAcc 32 (encY.extract 0 32) ByteArray.empty) :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } by
      unfold runOpcode
      simp only [popN, StackState.pop?, asBytes?, asNonNegativeNat?, asInt?,
                 StackState.push, Int.reduceLT, reduceIte]
      rw [if_neg (by omega : ¬ (32 : Int).toNat > encX.size)]
      rfl ]
  simp only [match_Except_ok_runOps]
  -- drop.
  rw [runOps_cons_nonIf_eq _ _ _ niDrop, stepNonIf_drop]
  rw [show applyDrop
        { stack := .vBytes (encX.extract 32 encX.size) :: .vBytes (encX.extract 0 32)
                    :: .vBytes (reverseAcc 32 (encY.extract 0 32) ByteArray.empty) :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBytes (encX.extract 0 32)
                          :: .vBytes (reverseAcc 32 (encY.extract 0 32) ByteArray.empty) :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps]
  -- reverse32 (x-half) ++ [swap, OP_CAT].
  rw [runOps_append]
  rw [reverse32_ops_transport
        { stack := .vBytes (encX.extract 0 32)
                    :: .vBytes (reverseAcc 32 (encY.extract 0 32) ByteArray.empty) :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        (encX.extract 0 32) (.vBytes (reverseAcc 32 (encY.extract 0 32) ByteArray.empty) :: rest)
        rfl (by rw [hSzXextract]; omega)]
  simp only [match_Except_ok_runOps]
  -- swap → [revY_be, revX_be].
  rw [runOps_cons_nonIf_eq _ _ _ niSwap, stepNonIf_swap]
  rw [show applySwap
        { stack := .vBytes (reverseAcc 32 (encX.extract 0 32) ByteArray.empty)
                    :: .vBytes (reverseAcc 32 (encY.extract 0 32) ByteArray.empty) :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBytes (reverseAcc 32 (encY.extract 0 32) ByteArray.empty)
                          :: .vBytes (reverseAcc 32 (encX.extract 0 32) ByteArray.empty) :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps]
  -- OP_CAT → revX_be ++ revY_be (popN gives [top, below] = [revY_be, revX_be]; f a b = a++b).
  rw [runOps_cons_nonIf_eq _ _ _ (niOp "OP_CAT"), stepNonIf_opcode]
  rw [show runOpcode "OP_CAT"
        { stack := .vBytes (reverseAcc 32 (encY.extract 0 32) ByteArray.empty)
                    :: .vBytes (reverseAcc 32 (encX.extract 0 32) ByteArray.empty) :: rest,
          altstack := alt, outputs := out, props := props, preimage := pre }
        = .ok { stack := .vBytes (reverseAcc 32 (encX.extract 0 32) ByteArray.empty
                                    ++ reverseAcc 32 (encY.extract 0 32) ByteArray.empty) :: rest,
                altstack := alt, outputs := out, props := props, preimage := pre } from rfl]
  simp only [match_Except_ok_runOps, runOps_nil]

set_option maxRecDepth 8192 in
open RunarVerification.Crypto.Secp256k1 (ecMakePoint intToBE32) in
/-- **DISCHARGED.**  `Stack.Ec.emitEcMakePoint` agrees with
`Crypto.Secp256k1.ecMakePoint`, under the two `OP_NUM2BIN`-encoding hypotheses
(`hEncX`/`hEncY` — the coordinates fit in 33 bytes), the two size guards, and the
canonical-encoding bridges `hBeX`/`hBeY`: each byte-reversed low-32 `OP_NUM2BIN`
half equals the spec's big-endian `intToBE32`.  All hypotheses constrain only the
INPUTS `x`/`y` (and their canonical encodings), not the output — honest invariants
of every in-field coordinate.  Replaces the `Crypto.Spec.emitEcMakePoint_runOps_eq`
axiom. -/
theorem emitEcMakePoint_runOps_eq
    (stkSt : StackState) (x y : Int) (encX encY : ByteArray) (rest : List Value)
    (hStk : stkSt.stack = .vBigint y :: .vBigint x :: rest)
    (hEncX : num2binEncode? x 33 = some encX)
    (hEncY : num2binEncode? y 33 = some encY)
    (hSzX : (32 : Nat) ≤ encX.size)
    (hSzY : (32 : Nat) ≤ encY.size)
    (hBeX : reverseAcc 32 (encX.extract 0 32) ByteArray.empty = intToBE32 x)
    (hBeY : reverseAcc 32 (encY.extract 0 32) ByteArray.empty = intToBE32 y) :
    runOps Stack.Ec.emitEcMakePoint stkSt
      = .ok { stkSt with stack := .vBytes (ecMakePoint x y) :: rest } := by
  rw [ec_makePoint_op_transport stkSt x y encX encY rest hStk hEncX hEncY hSzX hSzY,
      hBeX, hBeY]
  rfl

/-! ### MANDATORY smokes for the ecMakePoint discharge -/

private def smokeMkX : Int := 11
private def smokeMkY : Int := 22

private def smokeMkStk : StackState :=
  { (default : StackState) with stack := [.vBigint smokeMkY, .vBigint smokeMkX] }

/-- Concrete `OP_NUM2BIN` encodings of the two coordinates at width 33. -/
private def smokeMkEncX : ByteArray :=
  (num2binEncode? smokeMkX 33).getD ByteArray.empty
private def smokeMkEncY : ByteArray :=
  (num2binEncode? smokeMkY 33).getD ByteArray.empty

/-- SMOKE (wf anti-vacuity).  All six discharge hypotheses are SATISFIABLE for
`x = 11, y = 22`: both coordinates encode at width 33 (size 33 ≥ 32) and each
byte-reversed low-32 half equals the spec `intToBE32`.  `native_decide` is
legitimate (every function is closed-form). -/
theorem smoke_ecMakePoint_wf_satisfiable :
    num2binEncode? smokeMkX 33 = some smokeMkEncX
      ∧ num2binEncode? smokeMkY 33 = some smokeMkEncY
      ∧ (32 : Nat) ≤ smokeMkEncX.size
      ∧ (32 : Nat) ≤ smokeMkEncY.size
      ∧ reverseAcc 32 (smokeMkEncX.extract 0 32) ByteArray.empty
          = RunarVerification.Crypto.Secp256k1.intToBE32 smokeMkX
      ∧ reverseAcc 32 (smokeMkEncY.extract 0 32) ByteArray.empty
          = RunarVerification.Crypto.Secp256k1.intToBE32 smokeMkY := by
  native_decide

/-- SMOKE (the headline).  The discharged `emitEcMakePoint_runOps_eq` FIRES on
`[22, 11]`, landing exactly `ecMakePoint 11 22 = makePoint 11 22`. -/
theorem smoke_emitEcMakePoint_runOps_eq :
    runOps Stack.Ec.emitEcMakePoint smokeMkStk
      = .ok { smokeMkStk with
              stack := .vBytes
                (RunarVerification.Crypto.Secp256k1.ecMakePoint smokeMkX smokeMkY) :: [] } :=
  emitEcMakePoint_runOps_eq smokeMkStk smokeMkX smokeMkY smokeMkEncX smokeMkEncY [] rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

/-- SMOKE (value anti-vacuity).  The packed point round-trips: its x-coordinate is
`11` and y-coordinate is `22`. -/
theorem smoke_ecMakePoint_value_concrete :
    RunarVerification.Crypto.Secp256k1.ecPointX
        (RunarVerification.Crypto.Secp256k1.ecMakePoint smokeMkX smokeMkY) = 11
      ∧ RunarVerification.Crypto.Secp256k1.ecPointY
        (RunarVerification.Crypto.Secp256k1.ecMakePoint smokeMkX smokeMkY) = 22 := by
  native_decide

/-! ## Part 8 — the Tracker simulation invariant + model substrate (deliverable 1)

`emitEcNegate` / `emitEcOnCurve` are produced by RUNNING the `Stack.Ec.Tracker`
state machine: their `.roll d` / `.pickStruct d` ops carry depths `d =
Tracker.findDepth nm name`, picked at codegen time against the threaded name array
`nm`.  An honest `runOps` transport for either op list needs a *Tracker-to-runtime
simulation invariant*: the runtime stack `stk` (head = TOS) must mirror the
tracker name array `nm` (bottom→top) slot-for-slot, so that each `.roll`/`.pick`
depth lands on the value of the named slot it addresses.

This Part lands that invariant (`TrackerSim`) plus the reusable model substrate it
needs — all `sorry`-free, all axiom-clean (`propext`/`Quot.sound` only).  See the
BLOCK note in Part 9 for the ONE remaining kernel-level obstacle that gates the
final per-op discharge (`Tracker.findDepth` is built on the `partial`
`Lean.Loop.forIn`, which the kernel cannot reduce or induct over, so the bridge
`Tracker.findDepth = findDepthList ∘ reverse` cannot be proven without editing
`Stack/Ec.lean` — explicitly out of scope). -/

/-- Resolve a tracker slot against valuation `σ`; `none` slots are unconstrained. -/
def slotAgrees (σ : String → Value) (slot : Option String) (v : Value) : Prop :=
  match slot with
  | some n => v = σ n
  | none   => True

/-- **Tracker simulation invariant (deliverable 1).**  Runtime stack `stk`
(head = TOS) mirrors the tracker name array `nm` (bottom→top).  Reversing `nm` to
top→bottom, every named slot holds its `σ`-value; `none` slots are free.  Lengths
agree (so every `findDepth` depth lands in range).  `Tracker.findDepth nm name`
(the codegen `.roll`/`.pick` depth) is asserted-equal to the runtime structural
depth of `name`'s slot via the `findDepthList` model below (`findDepthList_sim`). -/
def TrackerSim (nm : Array (Option String)) (σ : String → Value) (stk : List Value) : Prop :=
  stk.length = nm.size ∧
  ∀ i (h : i < nm.size), slotAgrees σ (nm[i]) (stk[nm.size - 1 - i]!)

/-- Recursive model of `Tracker.findDepth` over the TOP-first name list
(`nm.toList.reverse`): index of the first matching name, else list length.  This
is the kernel-reducible counterpart the opaque `Loop.forIn`-based
`Tracker.findDepth` lacks (see Part 9). -/
def findDepthList (name : String) : List (Option String) → Nat
  | []      => 0
  | x :: xs => if x = some name then 0 else findDepthList name xs + 1

/-- The model depth is `< length` when the name is present. -/
theorem findDepthList_lt (name : String) :
    ∀ (l : List (Option String)), some name ∈ l → findDepthList name l < l.length := by
  intro l
  induction l with
  | nil => intro h; cases h
  | cons x xs ih =>
      intro hmem
      unfold findDepthList
      by_cases hx : x = some name
      · simp [hx]
      · simp only [hx, if_false]
        rw [List.length_cons]
        have hmem' : some name ∈ xs := by
          rcases List.mem_cons.mp hmem with h | h
          · exact absurd h.symm hx
          · exact h
        have := ih hmem'
        omega

/-- The model depth points at a slot actually named `name` (in the TOP-first list). -/
theorem findDepthList_get (name : String) :
    ∀ (l : List (Option String)), some name ∈ l →
      l[findDepthList name l]! = some name := by
  intro l
  induction l with
  | nil => intro h; cases h
  | cons x xs ih =>
      intro hmem
      unfold findDepthList
      by_cases hx : x = some name
      · simp [hx]
      · simp only [hx, if_false]
        have hmem' : some name ∈ xs := by
          rcases List.mem_cons.mp hmem with h | h
          · exact absurd h.symm hx
          · exact h
        rw [show findDepthList name xs + 1 = (findDepthList name xs).succ from rfl]
        rw [List.getElem!_cons_succ]
        exact ih hmem'

/-- Reverse-index bridge: the `d`-th element (top-first) of `nm.toList.reverse`
is the `(size-1-d)`-th element of `nm` (bottom-first), for `d < size`. -/
theorem reverse_getElem_bridge (nm : Array (Option String)) (d : Nat) (hd : d < nm.size) :
    (nm.toList.reverse)[d]! = nm[nm.size - 1 - d]! := by
  have hlen : nm.toList.length = nm.size := by simp
  have hd' : d < nm.toList.reverse.length := by rw [List.length_reverse, hlen]; omega
  rw [getElem!_pos (nm.toList.reverse) d hd', List.getElem_reverse]
  rw [getElem!_pos nm (nm.size - 1 - d) (show nm.size - 1 - d < nm.size by omega)]
  rw [← Array.getElem_toList]
  congr 1

/-- **`findDepthAux`-to-`findDepthList` agreement (wave-77).**  The structural
`Stack.Ec.Tracker.findDepthAux` (the kernel-reducible scan introduced by the
`Stack/Ec.lean` `findDepth` refactor) returns `some (findDepthList name l)`
whenever `name` is present in the top-first list `l`.  The two differ only in the
NOT-found case (`findDepthAux ⇒ none`, `findDepthList ⇒ l.length`); under presence
they coincide.  Proven by structural induction, `propext`/`Quot.sound`-clean. -/
theorem findDepthAux_eq_findDepthList (name : String) :
    ∀ (l : List (Option String)), some name ∈ l →
      Ec.Tracker.findDepthAux name l = some (findDepthList name l) := by
  intro l
  induction l with
  | nil => intro h; cases h
  | cons x xs ih =>
      intro hmem
      unfold Ec.Tracker.findDepthAux findDepthList
      by_cases hx : x = some name
      · simp [hx]
      · have hbeq : (x == some name) = false := by
          simp [beq_eq_false_iff_ne, hx]
        rw [hbeq]
        simp only [Bool.false_eq_true, if_false, hx]
        have hmem' : some name ∈ xs := by
          rcases List.mem_cons.mp hmem with h | h
          · exact absurd h.symm hx
          · exact h
        rw [ih hmem']
        rfl

/-- **The Part-9 BRIDGE (wave-77, was the wave-76 BLOCKER).**
`Tracker.findDepth t name = findDepthList name t.nm.toList.reverse` whenever
`name` is present in the (top-first) name list.  This is the one-line bridge the
wave-76 substrate was gated on.  It is now provable — NOT by `native_decide` — but
by unfolding the refactored structural `Stack.Ec.Tracker.findDepth`
(`(findDepthAux name t.nm.toList.reverse).getD 0`) and discharging via
`findDepthAux_eq_findDepthList` (structural induction).  This rewrites every
codegen-emitted `.roll (Tracker.findDepth …)` / `.pickStruct (Tracker.findDepth …)`
into the `findDepthList` form the wave-76 preservation lemmas
(`applyRoll_findDepth_sim` / `applyPick_findDepth_sim`) address. -/
theorem findDepth_eq_findDepthList (t : Ec.Tracker) (name : String)
    (hmem : some name ∈ t.nm.toList.reverse) :
    t.findDepth name = findDepthList name t.nm.toList.reverse := by
  unfold Ec.Tracker.findDepth
  rw [findDepthAux_eq_findDepthList name t.nm.toList.reverse hmem]
  rfl

/-- **`findDepth` model correctness under `TrackerSim` (keystone).**  When `name`
is present in the tracker, the runtime stack value at structural depth
`d := findDepthList name nm.toList.reverse` is exactly `σ name`, and `d` is in
range.  This is the lemma that — once a kernel-reducible
`Tracker.findDepth = findDepthList ∘ reverse` bridge exists (Part 9) — lets every
`toTop`/`copyToTop` step land on the correctly-named runtime slot. -/
theorem findDepthList_sim (nm : Array (Option String)) (σ : String → Value)
    (stk : List Value) (name : String)
    (hSim : TrackerSim nm σ stk)
    (hmem : some name ∈ nm.toList.reverse) :
    let d := findDepthList name nm.toList.reverse
    d < stk.length ∧ stk[d]! = σ name := by
  intro d
  obtain ⟨hlen, hslot⟩ := hSim
  have hrevlen : nm.toList.reverse.length = nm.size := by rw [List.length_reverse]; simp
  have hd_lt : d < nm.size := by
    have := findDepthList_lt name nm.toList.reverse hmem
    rwa [hrevlen] at this
  refine ⟨by omega, ?_⟩
  have hget : nm.toList.reverse[d]! = some name := findDepthList_get name nm.toList.reverse hmem
  rw [reverse_getElem_bridge nm d hd_lt] at hget
  have hidx : nm.size - 1 - d < nm.size := by omega
  have hslotd := hslot (nm.size - 1 - d) hidx
  have heq : nm.size - 1 - (nm.size - 1 - d) = d := by omega
  rw [heq] at hslotd
  have hgetbang : nm[nm.size - 1 - d] = some name := by
    rw [← hget, getElem!_pos nm (nm.size - 1 - d) hidx]
  unfold slotAgrees at hslotd
  rw [hgetbang] at hslotd
  exact hslotd

/-- Updating the valuation at a fresh name preserves agreement at all OTHER names. -/
theorem slotAgrees_update_ne (σ : String → Value) (name : String) (v : Value)
    (slot : Option String) (w : Value) (hne : slot ≠ some name) :
    slotAgrees σ slot w → slotAgrees (fun s => if s = name then v else σ s) slot w := by
  intro h
  cases slot with
  | none => exact h
  | some n =>
      unfold slotAgrees at h ⊢
      have : n ≠ name := by intro hc; exact hne (by rw [hc])
      simp only [this, if_false]
      exact h

/-- **Push preservation.**  Pushing a value `v` for a fresh `some name` slot
(`nm.push (some name)`, runtime `v :: stk`) preserves `TrackerSim` under the
valuation updated to map `name ↦ v`, PROVIDED `name` does not already occur in
`nm` (the codegen always pushes fresh intermediate names — `pushInt`/`pushBytes`).
This is the `push`/`rawBlock`-produce preservation lemma the helpers compose. -/
theorem TrackerSim_push (nm : Array (Option String)) (σ : String → Value)
    (stk : List Value) (name : String) (v : Value)
    (hSim : TrackerSim nm σ stk)
    (hfresh : some name ∉ nm.toList) :
    TrackerSim (nm.push (some name)) (fun s => if s = name then v else σ s) (v :: stk) := by
  obtain ⟨hlen, hslot⟩ := hSim
  constructor
  · simp [hlen]
  · intro i hi
    rw [Array.size_push] at hi
    by_cases htop : i = nm.size
    · subst htop
      have hidx : (nm.push (some name))[nm.size] = some name := by
        simp [Array.getElem_push_eq]
      rw [hidx]
      have : (nm.push (some name)).size - 1 - nm.size = 0 := by rw [Array.size_push]; omega
      rw [this]
      show slotAgrees _ (some name) ((v :: stk)[0]!)
      unfold slotAgrees
      simp
    · have hi' : i < nm.size := by omega
      have hpushlow : (nm.push (some name))[i] = nm[i]'hi' := by
        rw [Array.getElem_push_lt]
      rw [hpushlow]
      have hszp : (nm.push (some name)).size = nm.size + 1 := by rw [Array.size_push]
      rw [hszp]
      have hcons : (nm.size + 1 - 1 - i) = (nm.size - 1 - i) + 1 := by omega
      rw [hcons]
      rw [List.getElem!_cons_succ]
      have horig := hslot i hi'
      have hne : nm[i]'hi' ≠ some name := by
        intro hc
        exact hfresh (by rw [← hc]; exact Array.getElem_mem_toList hi')
      exact slotAgrees_update_ne σ name v (nm[i]'hi') (stk[nm.size - 1 - i]!) hne horig

/-- **`applyRoll`-at-model-depth transport (`roll`/`toTop` preservation).**  Under
`TrackerSim`, rolling the slot named `name` (at structural depth
`d := findDepthList name nm.toList.reverse`) to the top puts exactly `σ name` on
top — the runtime witness of `Tracker.toTop name`.  The remaining stack is
`s.stack.eraseIdx d`.  This is the `roll` preservation lemma the field-arith
helpers (`fieldMod`/`fieldAdd`/`fieldSub`/`fieldMul`/`fieldSqr`) compose, once the
kernel `findDepth = findDepthList` bridge (Part 9) lands. -/
theorem applyRoll_findDepth_sim (s : StackState) (nm : Array (Option String))
    (σ : String → Value) (name : String)
    (hSim : TrackerSim nm σ s.stack)
    (hmem : some name ∈ nm.toList.reverse) :
    applyRoll s (findDepthList name nm.toList.reverse)
      = .ok { s with stack := σ name :: s.stack.eraseIdx (findDepthList name nm.toList.reverse) } := by
  obtain ⟨hlt, hval⟩ := findDepthList_sim nm σ s.stack name hSim hmem
  unfold applyRoll
  rw [if_neg (by omega : ¬ findDepthList name nm.toList.reverse ≥ s.stack.length)]
  rw [hval]

/-- **`applyPick`-at-model-depth transport (`pick`/`copyToTop` preservation).**
Under `TrackerSim`, structurally picking the slot named `name` (at depth
`d := findDepthList name nm.toList.reverse`) COPIES exactly `σ name` to the top
without removing it — the runtime witness of `Tracker.copyToTop name`. -/
theorem applyPick_findDepth_sim (s : StackState) (nm : Array (Option String))
    (σ : String → Value) (name : String)
    (hSim : TrackerSim nm σ s.stack)
    (hmem : some name ∈ nm.toList.reverse) :
    applyPick s (findDepthList name nm.toList.reverse)
      = .ok (s.push (σ name)) := by
  obtain ⟨hlt, hval⟩ := findDepthList_sim nm σ s.stack name hSim hmem
  unfold applyPick
  rw [if_neg (by omega : ¬ findDepthList name nm.toList.reverse ≥ s.stack.length)]
  rw [hval]

/-! ### MANDATORY smokes for the Tracker simulation substrate (deliverable 1) -/

/-- Concrete tracker name array `[some "a", some "b", some "c"]` (bottom→top). -/
private def simNm : Array (Option String) := #[some "a", some "b", some "c"]

/-- Concrete valuation. -/
private def simσ : String → Value
  | "a" => .vBigint 10
  | "b" => .vBigint 20
  | "c" => .vBigint 30
  | _   => .vBigint 0

/-- Runtime stack mirroring `simNm` (TOS = c = 30). -/
private def simStk : List Value := [.vBigint 30, .vBigint 20, .vBigint 10]

/-- SMOKE (invariant satisfiability — anti-vacuity).  `TrackerSim` is inhabited:
the concrete stack `[c,b,a]` mirrors the name array `[a,b,c]` under `simσ`. -/
theorem smoke_TrackerSim_satisfiable : TrackerSim simNm simσ simStk := by
  refine ⟨by decide, ?_⟩
  intro i hi
  rw [getElem!_pos simNm i hi |>.symm]
  have hsz : simNm.size = 3 := by decide
  have h3 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  clear hi
  unfold slotAgrees
  rcases h3 with rfl | rfl | rfl <;>
    (unfold simNm simStk simσ; rfl)

/-- SMOKE (keystone fires).  Under the concrete `TrackerSim`, the model depth of
`"a"` is 2 and the runtime stack value there is `σ "a" = 10`. -/
theorem smoke_findDepthList_sim :
    (findDepthList "a" simNm.toList.reverse = 2)
      ∧ simStk[findDepthList "a" simNm.toList.reverse]! = simσ "a" := by
  refine ⟨by decide, ?_⟩
  exact (findDepthList_sim simNm simσ simStk "a" smoke_TrackerSim_satisfiable (by decide)).2

/-- SMOKE (roll transport fires).  Rolling `"a"` (depth 2) to the top of the
concrete state lands `σ "a" = 10` on top, with that slot erased from the rest. -/
theorem smoke_applyRoll_findDepth_sim :
    applyRoll { (default : StackState) with stack := simStk }
        (findDepthList "a" simNm.toList.reverse)
      = .ok { (default : StackState) with
              stack := simσ "a"
                :: simStk.eraseIdx (findDepthList "a" simNm.toList.reverse) } := by
  apply applyRoll_findDepth_sim
  · exact smoke_TrackerSim_satisfiable
  · decide

/-- SMOKE (pick transport fires).  Picking `"a"` (depth 2) COPIES `σ "a" = 10` to
the top, leaving the rest intact. -/
theorem smoke_applyPick_findDepth_sim :
    applyPick { (default : StackState) with stack := simStk }
        (findDepthList "a" simNm.toList.reverse)
      = .ok (({ (default : StackState) with stack := simStk }).push (simσ "a")) := by
  apply applyPick_findDepth_sim
  · exact smoke_TrackerSim_satisfiable
  · decide

/-- SMOKE (push preservation fires).  Pushing a fresh `"d" ↦ 40` extends the
concrete `TrackerSim`. -/
theorem smoke_TrackerSim_push :
    TrackerSim (simNm.push (some "d"))
      (fun s => if s = "d" then .vBigint 40 else simσ s) (.vBigint 40 :: simStk) :=
  TrackerSim_push simNm simσ simStk "d" (.vBigint 40) smoke_TrackerSim_satisfiable (by decide)

/-- Concrete tracker whose name array is `simNm = [a, b, c]` (bottom→top). -/
private def simTracker : Ec.Tracker := Ec.Tracker.init [some "a", some "b", some "c"]

/-- SMOKE (bridge fires — anti-vacuity).  On the concrete `simTracker`, the
refactored structural `Tracker.findDepth "a"` equals the model
`findDepthList "a" simTracker.nm.toList.reverse` (both `= 2`).  Discharged via the
BRIDGE THEOREM `findDepth_eq_findDepthList` (proved by structural induction, never
`native_decide`); the only `decide` is the concrete membership side-goal. -/
theorem smoke_findDepth_eq_findDepthList :
    simTracker.findDepth "a" = findDepthList "a" simTracker.nm.toList.reverse := by
  apply findDepth_eq_findDepthList
  decide

/-- SMOKE (bridge produces the right concrete value).  The bridged depth on
`simTracker` is exactly `2`, matching the topmost match's depth-from-TOS. -/
theorem smoke_findDepth_bridge_value :
    simTracker.findDepth "a" = 2 := by
  rw [smoke_findDepth_eq_findDepthList]; decide

/-! ### Per-helper transports (wave-77 deliverable 3)

The wave-76 substrate (`TrackerSim`, `findDepthList_sim`, `applyRoll/applyPick`
preservation) + the wave-77 bridge (`findDepth_eq_findDepthList`) compose into the
reusable per-helper transports below.  Three families are landed here, each with a
smoke:

* **`pickStruct` peer** — `applyPickStruct_findDepth_sim` (the codegen emits
  `.pickStruct d`, not the `.pick d` the substrate addressed; the two ops are
  in-bounds-equivalent, so the substrate's `applyPick_findDepth_sim` lifts).
* **`fieldMod` opcode-sequence transport** — `fieldModOps_transport`.  The 8-op
  `fieldModOps` block is byte-identical to `emitEcModReduce`, so the wave-71
  `ecModReduce_step_transport` lifts to `Secp256k1.fieldMod` (divisor `fieldP ≠ 0`).
* **`fieldAdd/fieldSub/fieldMul` opcode-tail transports** — the
  `[OP_BINOP, push fieldP] ++ fieldModOps` tail each composing the corresponding
  `runOpcode_{ADD,SUB,MUL}_bigint_local` into `Secp256k1.field{Add,Sub,Mul}`.

These are the field-arith leaves the per-op discharge of `emitEcNegate` /
`emitEcOnCurve` consumes.  See the Part-9 BLOCK note for the remaining whole-program
ops-append scaffolding that gates the final per-op assembly. -/

/-- `applyPickStruct = applyPick` whenever the depth is in range (the two differ
only in the out-of-range error string). -/
theorem applyPickStruct_eq_applyPick (s : StackState) (d : Nat)
    (hd : ¬ d ≥ s.stack.length) :
    applyPickStruct s d = applyPick s d := by
  unfold applyPickStruct applyPick
  rw [if_neg hd, if_neg hd]

/-- **`pickStruct`-at-model-depth transport (the codegen-faithful `copyToTop`
witness).**  Under `TrackerSim`, the `.pickStruct (findDepthList …)` op the Tracker
emits for `pick (k+2)` COPIES exactly `σ name` to the top — the `applyPick` peer for
the op the codegen actually emits. -/
theorem applyPickStruct_findDepth_sim (s : StackState) (nm : Array (Option String))
    (σ : String → Value) (name : String)
    (hSim : TrackerSim nm σ s.stack)
    (hmem : some name ∈ nm.toList.reverse) :
    applyPickStruct s (findDepthList name nm.toList.reverse)
      = .ok (s.push (σ name)) := by
  have hlt := (findDepthList_sim nm σ s.stack name hSim hmem).1
  rw [applyPickStruct_eq_applyPick s _ (by omega)]
  exact applyPick_findDepth_sim s nm σ name hSim hmem

/-- The codegen field modulus `Ec.fieldP` equals the spec modulus
`Secp256k1.FIELD_P` (same literal; kernel-checkable, NOT `native_decide`). -/
theorem ec_fieldP_eq_spec : Ec.fieldP = Crypto.Secp256k1.FIELD_P := rfl

/-- `Ec.fieldP ≠ 0` — the `OP_MOD` divisor guard for every `fieldMod` (kernel
`decide`, NOT `native_decide`, so the transports stay free of `Lean.ofReduceBool`). -/
theorem ec_fieldP_ne_zero : Ec.fieldP ≠ 0 := by decide

/-- `fieldModOps` is the same 8-op list as `emitEcModReduce`. -/
theorem fieldModOps_eq_emitEcModReduce :
    Ec.fieldModOps = Stack.Ec.emitEcModReduce := rfl

/-- **`fieldMod` opcode-sequence transport.**  Running `fieldModOps` on
`[a, fieldP]` (fieldP on TOS) lands `Secp256k1.fieldMod a`.  Lifts the wave-71
`ecModReduce_step_transport` (divisor `fieldP ≠ 0`). -/
theorem fieldModOps_transport
    (s : StackState) (a : Int) (rest : List Value)
    (hStk : s.stack = .vBigint Ec.fieldP :: .vBigint a :: rest) :
    runOps Ec.fieldModOps s
      = .ok { s with stack := .vBigint (Crypto.Secp256k1.fieldMod a) :: rest } := by
  rw [fieldModOps_eq_emitEcModReduce]
  rw [ecModReduce_step_transport s a Ec.fieldP rest hStk ec_fieldP_ne_zero]
  have hSpec : Crypto.Secp256k1.ecModReduce a Ec.fieldP = Crypto.Secp256k1.fieldMod a := by
    unfold Crypto.Secp256k1.ecModReduce Crypto.Secp256k1.fieldMod
    rw [if_neg ec_fieldP_ne_zero, ec_fieldP_eq_spec]
  rw [hSpec]

private theorem niOpcode : ∀ (c : String) t e, StackOp.opcode c ≠ .ifOp t e := by
  intro c t e h; cases h
private theorem niPush : ∀ (v : PushVal) t e, StackOp.push v ≠ .ifOp t e := by
  intro v t e h; cases h

/-- **Generic field-binop opcode-tail transport.**  For a binop opcode reducing the
top-two ints by `f`, the tail `[OP_BINOP, push fieldP] ++ fieldModOps` run on
`[a, b]` (b on TOS) lands `Secp256k1.fieldMod (f a b)`. -/
theorem fieldBinop_optail_transport
    (binop : String) (f : Int → Int → Int)
    (s : StackState) (a b : Int) (rest : List Value)
    (hBinop : runOpcode binop s = .ok ({ s with stack := rest }.push (.vBigint (f a b)))) :
    runOps ([.opcode binop, .push (.bigint Ec.fieldP)] ++ Ec.fieldModOps) s
      = .ok { s with stack := .vBigint (Crypto.Secp256k1.fieldMod (f a b)) :: rest } := by
  rw [show ([.opcode binop, .push (.bigint Ec.fieldP)] ++ Ec.fieldModOps)
        = (.opcode binop :: .push (.bigint Ec.fieldP) :: Ec.fieldModOps) from rfl]
  rw [runOps_cons_nonIf_eq _ _ _ (niOpcode binop), stepNonIf_opcode, hBinop]
  simp only [match_Except_ok_runOps]
  rw [runOps_cons_nonIf_eq _ _ _ (niPush (.bigint Ec.fieldP)), stepNonIf_push_bigint]
  simp only [match_Except_ok_runOps]
  rw [fieldModOps_transport _ (f a b) rest rfl]
  simp only [StackState.push]

/-- `fieldAdd` opcode-tail transport: `(a + b) mod p = Secp256k1.fieldAdd a b`. -/
theorem fieldAdd_optail_transport
    (s : StackState) (a b : Int) (rest : List Value)
    (hStk : s.stack = .vBigint b :: .vBigint a :: rest) :
    runOps ([.opcode "OP_ADD", .push (.bigint Ec.fieldP)] ++ Ec.fieldModOps) s
      = .ok { s with stack := .vBigint (Crypto.Secp256k1.fieldAdd a b) :: rest } :=
  fieldBinop_optail_transport "OP_ADD" (· + ·) s a b rest
    (runOpcode_ADD_bigint_local s a b rest hStk)

/-- `fieldSub` opcode-tail transport: `(a - b) mod p = Secp256k1.fieldSub a b`. -/
theorem fieldSub_optail_transport
    (s : StackState) (a b : Int) (rest : List Value)
    (hStk : s.stack = .vBigint b :: .vBigint a :: rest) :
    runOps ([.opcode "OP_SUB", .push (.bigint Ec.fieldP)] ++ Ec.fieldModOps) s
      = .ok { s with stack := .vBigint (Crypto.Secp256k1.fieldSub a b) :: rest } :=
  fieldBinop_optail_transport "OP_SUB" (· - ·) s a b rest
    (runOpcode_SUB_bigint_local s a b rest hStk)

/-- `fieldMul` opcode-tail transport: `(a * b) mod p = Secp256k1.fieldMul a b`. -/
theorem fieldMul_optail_transport
    (s : StackState) (a b : Int) (rest : List Value)
    (hStk : s.stack = .vBigint b :: .vBigint a :: rest) :
    runOps ([.opcode "OP_MUL", .push (.bigint Ec.fieldP)] ++ Ec.fieldModOps) s
      = .ok { s with stack := .vBigint (Crypto.Secp256k1.fieldMul a b) :: rest } :=
  fieldBinop_optail_transport "OP_MUL" (· * ·) s a b rest
    (runOpcode_MUL_bigint_local s a b rest hStk)

/-! ### MANDATORY smokes for the per-helper transports (deliverable 3) -/

/-- Concrete state for the field-helper smokes: `[a=10, b=7]` (b on TOS). -/
private def fieldSmokeStk : StackState :=
  { (default : StackState) with stack := [.vBigint 7, .vBigint 10] }

/-- SMOKE (`fieldMod` fires).  `fieldModOps` on `[42, p]` lands
`Secp256k1.fieldMod 42 = 42`. -/
theorem smoke_fieldModOps_transport :
    runOps Ec.fieldModOps
        { (default : StackState) with stack := [.vBigint Ec.fieldP, .vBigint 42] }
      = .ok { (default : StackState) with
              stack := [.vBigint (Crypto.Secp256k1.fieldMod 42)] } :=
  fieldModOps_transport _ 42 [] rfl

/-- SMOKE (`fieldMod` value anti-vacuity).  The reduced value is concretely `42`. -/
theorem smoke_fieldMod_value : Crypto.Secp256k1.fieldMod 42 = 42 := by native_decide

/-- SMOKE (`fieldAdd` fires).  `[10, 7]` ⇒ `Secp256k1.fieldAdd 10 7 = 17`. -/
theorem smoke_fieldAdd_optail_transport :
    runOps ([.opcode "OP_ADD", .push (.bigint Ec.fieldP)] ++ Ec.fieldModOps) fieldSmokeStk
      = .ok { fieldSmokeStk with stack := [.vBigint (Crypto.Secp256k1.fieldAdd 10 7)] } :=
  fieldAdd_optail_transport fieldSmokeStk 10 7 [] rfl

/-- SMOKE (`fieldSub` fires).  `[10, 7]` ⇒ `Secp256k1.fieldSub 10 7 = 3`. -/
theorem smoke_fieldSub_optail_transport :
    runOps ([.opcode "OP_SUB", .push (.bigint Ec.fieldP)] ++ Ec.fieldModOps) fieldSmokeStk
      = .ok { fieldSmokeStk with stack := [.vBigint (Crypto.Secp256k1.fieldSub 10 7)] } :=
  fieldSub_optail_transport fieldSmokeStk 10 7 [] rfl

/-- SMOKE (`fieldMul` fires).  `[10, 7]` ⇒ `Secp256k1.fieldMul 10 7 = 70`. -/
theorem smoke_fieldMul_optail_transport :
    runOps ([.opcode "OP_MUL", .push (.bigint Ec.fieldP)] ++ Ec.fieldModOps) fieldSmokeStk
      = .ok { fieldSmokeStk with stack := [.vBigint (Crypto.Secp256k1.fieldMul 10 7)] } :=
  fieldMul_optail_transport fieldSmokeStk 10 7 [] rfl

/-- SMOKE (field-arith value anti-vacuity).  The three field ops land `17 / 3 / 70`. -/
theorem smoke_field_values :
    Crypto.Secp256k1.fieldAdd 10 7 = 17
      ∧ Crypto.Secp256k1.fieldSub 10 7 = 3
      ∧ Crypto.Secp256k1.fieldMul 10 7 = 70 := by native_decide

/-- SMOKE (`pickStruct` peer fires).  Under the concrete `TrackerSim`, the
codegen-faithful `.pickStruct (depth "a")` COPIES `σ "a" = 10` to the top. -/
theorem smoke_applyPickStruct_findDepth_sim :
    applyPickStruct { (default : StackState) with stack := simStk }
        (findDepthList "a" simNm.toList.reverse)
      = .ok (({ (default : StackState) with stack := simStk }).push (simσ "a")) := by
  apply applyPickStruct_findDepth_sim
  · exact smoke_TrackerSim_satisfiable
  · decide

/-! ### `toTop` / `copyToTop` runtime transports (wave-78 deliverable 1)

`Tracker.toTop name` emits `Tracker.roll d` and `Tracker.copyToTop name newName`
emits `Tracker.pick d newName`, with `d = Tracker.findDepth name` decided at
codegen time.  Both emit a DEPTH-DEPENDENT op:

  * `roll d` :  0 → nop, 1 → `.swap`, 2 → `.rot`, `n+3` → `.roll (n+3)`.
  * `pick d` :  0 → `.dup`, 1 → `.over`, `k+2` → `.pickStruct (k+2)`.

To thread `runOps` over the whole codegen op-list we need, for each, (a) the
ops-append lemma `(helper t).ops = t.ops ++ extraOps d` and (b) the runtime
transport `runOps (extraOps d) s = applyRoll/applyPick s d` (in range).  Composing
(b) with the wave-76 `applyRoll_findDepth_sim` / `applyPick_findDepth_sim` and the
wave-77 `findDepth_eq_findDepthList` bridge yields the per-step `toTop`/`copyToTop`
transport that lands `σ name` on top under `TrackerSim`. -/

/-- The op-list `Tracker.roll d` appends to `t.ops` (depth-case-uniform). -/
def rollExtraOps (d : Nat) : List StackOp :=
  match d with
  | 0     => []
  | 1     => [.swap]
  | 2     => [.rot]
  | n + 3 => [.roll (n + 3)]

/-- The op-list `Tracker.pick d n` appends to `t.ops` (depth-case-uniform). -/
def pickExtraOps (d : Nat) : List StackOp :=
  match d with
  | 0     => [.dup]
  | 1     => [.over]
  | k + 2 => [.pickStruct (k + 2)]

/-- **`roll` ops-append.**  `(t.roll d).ops = t.ops ++ rollExtraOps d`.  Both
branches of the internal `if L ≥ …` mutate only `nm`, leaving `ops` identical. -/
theorem roll_ops_append (t : Ec.Tracker) (d : Nat) :
    (t.roll d).ops.toList = t.ops.toList ++ rollExtraOps d := by
  unfold Ec.Tracker.roll rollExtraOps
  match d with
  | 0     => simp
  | 1     => simp only []; unfold Ec.Tracker.swap Ec.Tracker.emit; dsimp only; split <;> simp
  | 2     => simp only []; unfold Ec.Tracker.rot Ec.Tracker.emit; dsimp only; split <;> simp
  | n + 3 => simp only []; unfold Ec.Tracker.emit; dsimp only; split <;> simp

/-- **`pick` ops-append.**  `(t.pick d n).ops = t.ops ++ pickExtraOps d`. -/
theorem pick_ops_append (t : Ec.Tracker) (d : Nat) (n : String) :
    (t.pick d n).ops.toList = t.ops.toList ++ pickExtraOps d := by
  unfold Ec.Tracker.pick pickExtraOps
  match d with
  | 0     => unfold Ec.Tracker.dup Ec.Tracker.emit; simp
  | 1     => unfold Ec.Tracker.over Ec.Tracker.emit; simp
  | k + 2 => unfold Ec.Tracker.emit; simp

/-- **`pick` always pushes `some n`** to `nm` (depth-case-uniform).  The runtime
peer pushes the copied value, so `copyToTop` preservation is exactly
`TrackerSim_push`. -/
theorem pick_nm_push (t : Ec.Tracker) (d : Nat) (n : String) :
    (t.pick d n).nm = t.nm.push (some n) := by
  unfold Ec.Tracker.pick
  match d with
  | 0     => unfold Ec.Tracker.dup Ec.Tracker.emit; rfl
  | 1     => unfold Ec.Tracker.over Ec.Tracker.emit; rfl
  | k + 2 => unfold Ec.Tracker.emit; rfl

/-- `applySwap = applyRoll · 1` when the stack has ≥2 elements. -/
theorem applySwap_eq_applyRoll1 (s : StackState) (h : 2 ≤ s.stack.length) :
    applySwap s = applyRoll s 1 := by
  unfold applyRoll applySwap; rw [if_neg (by omega)]
  cases hs : s.stack with
  | nil => rw [hs] at h; simp at h
  | cons a rest =>
    cases hr : rest with
    | nil => rw [hs, hr] at h; simp at h
    | cons b rest2 => simp [List.eraseIdx]

/-- `applyRot = applyRoll · 2` when the stack has ≥3 elements. -/
theorem applyRot_eq_applyRoll2 (s : StackState) (h : 3 ≤ s.stack.length) :
    applyRot s = applyRoll s 2 := by
  unfold applyRoll applyRot; rw [if_neg (by omega)]
  cases hs : s.stack with
  | nil => rw [hs] at h; simp at h
  | cons a rest =>
    cases hr : rest with
    | nil => rw [hs, hr] at h; simp at h
    | cons b rest2 =>
      cases hr2 : rest2 with
      | nil => rw [hs, hr, hr2] at h; simp at h
      | cons c rest3 => simp [List.eraseIdx]

/-- `applyDup = applyPick · 0` when the stack is nonempty. -/
theorem applyDup_eq_applyPick0 (s : StackState) (h : 1 ≤ s.stack.length) :
    applyDup s = applyPick s 0 := by
  unfold applyPick applyDup StackState.push; rw [if_neg (by omega)]
  cases hs : s.stack with
  | nil => rw [hs] at h; simp at h
  | cons a rest => simp

/-- `applyOver = applyPick · 1` when the stack has ≥2 elements. -/
theorem applyOver_eq_applyPick1 (s : StackState) (h : 2 ≤ s.stack.length) :
    applyOver s = applyPick s 1 := by
  unfold applyPick applyOver StackState.push; rw [if_neg (by omega)]
  cases hs : s.stack with
  | nil => rw [hs] at h; simp at h
  | cons a rest =>
    cases hr : rest with
    | nil => rw [hs, hr] at h; simp at h
    | cons b rest2 => simp

private theorem niSwap' : ∀ t e, StackOp.swap ≠ .ifOp t e := by intro t e h; cases h
private theorem niRot' : ∀ t e, StackOp.rot ≠ .ifOp t e := by intro t e h; cases h
private theorem niRoll' : ∀ d t e, StackOp.roll d ≠ .ifOp t e := by intro d t e h; cases h
private theorem niDup' : ∀ t e, StackOp.dup ≠ .ifOp t e := by intro t e h; cases h
private theorem niOver' : ∀ t e, StackOp.over ≠ .ifOp t e := by intro t e h; cases h
private theorem niPickStruct' : ∀ d t e, StackOp.pickStruct d ≠ .ifOp t e := by
  intro d t e h; cases h

/-- **`roll` runtime transport.**  Running the depth-`d` op-list `Tracker.roll`
emits equals `applyRoll s d` whenever `d` is in range — the depth-0/1/2 special
cases (`nop`/`.swap`/`.rot`) collapse to `applyRoll · d` via the conditional
`applySwap/applyRot = applyRoll` bridges; the `≥3` case is the bare `.roll d`. -/
theorem runOps_rollExtraOps (s : StackState) (d : Nat) (h : d < s.stack.length) :
    runOps (rollExtraOps d) s = applyRoll s d := by
  unfold rollExtraOps
  match d with
  | 0 =>
    simp only [runOps_nil]
    unfold applyRoll; rw [if_neg (by omega)]
    cases hs : s.stack with
    | nil => rw [hs] at h; simp at h
    | cons a rest =>
      simp only [hs, List.getElem!_cons_zero, List.eraseIdx_cons_zero]
      cases s; simp_all
  | 1 =>
    rw [runOps_cons_nonIf_eq _ _ _ niSwap',
        show stepNonIf .swap s = applySwap s from rfl, applySwap_eq_applyRoll1 s (by omega)]
    cases happ : applyRoll s 1 with
    | error e => exfalso; unfold applyRoll at happ; rw [if_neg (by omega)] at happ; simp at happ
    | ok s' => simp [runOps_nil]
  | 2 =>
    rw [runOps_cons_nonIf_eq _ _ _ niRot',
        show stepNonIf .rot s = applyRot s from rfl, applyRot_eq_applyRoll2 s (by omega)]
    cases happ : applyRoll s 2 with
    | error e => exfalso; unfold applyRoll at happ; rw [if_neg (by omega)] at happ; simp at happ
    | ok s' => simp [runOps_nil]
  | n + 3 =>
    rw [runOps_cons_nonIf_eq _ _ _ (niRoll' (n+3)),
        show stepNonIf (.roll (n+3)) s = applyRoll s (n+3) from rfl]
    cases happ : applyRoll s (n+3) with
    | error e => exfalso; unfold applyRoll at happ; rw [if_neg (by omega)] at happ; simp at happ
    | ok s' => simp [runOps_nil]

/-- **`pick` runtime transport.**  Running the depth-`d` op-list `Tracker.pick`
emits equals `applyPick s d` whenever `d` is in range — depth-0/1 (`.dup`/`.over`)
collapse to `applyPick · d` via the conditional bridges; `≥2` is `.pickStruct d`
(= `applyPick` in range, the wave-77 `applyPickStruct_eq_applyPick`). -/
theorem runOps_pickExtraOps (s : StackState) (d : Nat) (h : d < s.stack.length) :
    runOps (pickExtraOps d) s = applyPick s d := by
  unfold pickExtraOps
  match d with
  | 0 =>
    rw [runOps_cons_nonIf_eq _ _ _ niDup',
        show stepNonIf .dup s = applyDup s from rfl, applyDup_eq_applyPick0 s (by omega)]
    cases happ : applyPick s 0 with
    | error e => exfalso; unfold applyPick at happ; rw [if_neg (by omega)] at happ; simp at happ
    | ok s' => simp [runOps_nil]
  | 1 =>
    rw [runOps_cons_nonIf_eq _ _ _ niOver',
        show stepNonIf .over s = applyOver s from rfl, applyOver_eq_applyPick1 s (by omega)]
    cases happ : applyPick s 1 with
    | error e => exfalso; unfold applyPick at happ; rw [if_neg (by omega)] at happ; simp at happ
    | ok s' => simp [runOps_nil]
  | k + 2 =>
    rw [runOps_cons_nonIf_eq _ _ _ (niPickStruct' (k+2)),
        show stepNonIf (.pickStruct (k+2)) s = applyPickStruct s (k+2) from rfl,
        applyPickStruct_eq_applyPick s (k+2) (by omega)]
    cases happ : applyPick s (k+2) with
    | error e => exfalso; unfold applyPick at happ; rw [if_neg (by omega)] at happ; simp at happ
    | ok s' => simp [runOps_nil]

/-- **`toTop` per-step runtime transport (deliverable 1).**  Under `TrackerSim`,
running the op-list `Tracker.toTop name` emits (= `rollExtraOps (findDepthList …)`,
via the wave-77 bridge) brings exactly `σ name` to the top of the runtime stack,
leaving the rest as `s.stack.eraseIdx d`.  This is the runtime witness of
`Tracker.toTop` the field-arith helpers compose. -/
theorem runOps_toTop_extraOps_sim (s : StackState) (nm : Array (Option String))
    (σ : String → Value) (name : String)
    (hSim : TrackerSim nm σ s.stack)
    (hmem : some name ∈ nm.toList.reverse) :
    runOps (rollExtraOps (findDepthList name nm.toList.reverse)) s
      = .ok { s with
              stack := σ name :: s.stack.eraseIdx (findDepthList name nm.toList.reverse) } := by
  have hlt := (findDepthList_sim nm σ s.stack name hSim hmem).1
  rw [runOps_rollExtraOps s _ (by omega)]
  exact applyRoll_findDepth_sim s nm σ name hSim hmem

/-- **`copyToTop` per-step runtime transport (deliverable 1).**  Under
`TrackerSim`, running the op-list `Tracker.copyToTop name newName` emits
(= `pickExtraOps (findDepthList …)`) COPIES exactly `σ name` to the top, without
removing it.  Runtime witness of `Tracker.copyToTop`. -/
theorem runOps_copyToTop_extraOps_sim (s : StackState) (nm : Array (Option String))
    (σ : String → Value) (name : String)
    (hSim : TrackerSim nm σ s.stack)
    (hmem : some name ∈ nm.toList.reverse) :
    runOps (pickExtraOps (findDepthList name nm.toList.reverse)) s
      = .ok (s.push (σ name)) := by
  have hlt := (findDepthList_sim nm σ s.stack name hSim hmem).1
  rw [runOps_pickExtraOps s _ (by omega)]
  exact applyPick_findDepth_sim s nm σ name hSim hmem

/-- **`copyToTop` `TrackerSim` preservation (deliverable 1).**  After
`Tracker.copyToTop name newName`, the tracker pushes `some newName` to `nm` and the
runtime pushes `σ name`.  Provided `newName` is fresh (the codegen always picks
fresh copy-target names) the invariant is preserved under the valuation updated to
`newName ↦ σ name`.  Reduces to `TrackerSim_push`. -/
theorem TrackerSim_copyToTop (s : StackState) (nm : Array (Option String))
    (σ : String → Value) (name newName : String)
    (hSim : TrackerSim nm σ s.stack)
    (hfresh : some newName ∉ nm.toList) :
    TrackerSim (nm.push (some newName))
      (fun t => if t = newName then σ name else σ t) (σ name :: s.stack) :=
  TrackerSim_push nm σ s.stack newName (σ name) hSim hfresh

/-! ### THE KEYSTONE — `toTop` nm-side `TrackerSim` preservation (deliverable 1)

The wave-78 hand-off (Part-9 sub-goal (a)) named this as the ONE remaining
model-preservation lemma: the `copyToTop` peer is `TrackerSim_copyToTop`
(= `TrackerSim_push`); the `toTop` peer (`Tracker.roll`) erases the slot at array
index `nm.size-1-d` and pushes it back on top, while the runtime erases the slot at
structural depth `d` and conses `σ name` on top.  The genuine content is the
slot-reindexing across "array-erase-then-push vs list-cons-after-erase" under the
`size-1-i ↔ i` reverse correspondence, split at the erase point `d`
(`TrackerSim_canonical`); the per-`roll`-branch reduction to that canonical
erase-push array shape is `roll_nm_canonical` (the `d=0` identity-of-`eraseLast`,
`d=1` swap-as-erase-push, `d=2`/`d≥3` definitional cases).  All `propext`/
`Quot.sound`-clean, NO `native_decide`, NO `sorry`, NO new axiom. -/

/-- `getElem!` peer of `List.getElem_set`. -/
private theorem getElemBang_set {α : Type} [Inhabited α] (l : List α) (i j : Nat) (v : α)
    (hj : j < l.length) :
    (l.set i v)[j]! = if i = j then v else l[j]! := by
  rw [getElem!_pos (l.set i v) j (by rw [List.length_set]; exact hj),
      getElem!_pos l j hj, List.getElem_set]

/-- `getElem!`-level list extensionality (equal lengths + per-index `[·]!` agreement). -/
private theorem list_ext_getElemBang {α : Type} [Inhabited α] (a b : List α)
    (hlen : a.length = b.length) (h : ∀ n, n < a.length → a[n]! = b[n]!) : a = b := by
  apply List.ext_getElem hlen
  intro n h1 h2
  have := h n h1
  rwa [getElem!_pos a n h1, getElem!_pos b n h2] at this

/-- `getElem!` of `eraseIdx` below the erase point. -/
private theorem getElemBang_eraseIdx_lt {α : Type} [Inhabited α] (l : List α) (e j : Nat)
    (hj : j < e) (he : e < l.length) :
    (l.eraseIdx e)[j]! = l[j]! := by
  have hjlen : j < (l.eraseIdx e).length := by rw [List.length_eraseIdx_of_lt he]; omega
  rw [getElem!_pos (l.eraseIdx e) j hjlen, getElem!_pos l j (by omega)]
  exact List.getElem_eraseIdx_of_lt hjlen hj

/-- `getElem!` of `eraseIdx` at/above the erase point (shifts the index up by one). -/
private theorem getElemBang_eraseIdx_ge {α : Type} [Inhabited α] (l : List α) (e j : Nat)
    (hge : e ≤ j) (he : e < l.length) (hjlen : j < (l.eraseIdx e).length) :
    (l.eraseIdx e)[j]! = l[j+1]! := by
  rw [getElem!_pos (l.eraseIdx e) j hjlen]
  have hj1 : j + 1 < l.length := by rw [List.length_eraseIdx_of_lt he] at hjlen; omega
  rw [getElem!_pos l (j+1) hj1]
  exact List.getElem_eraseIdx_of_ge hjlen hge

/-- `getElem!` of `xs ++ [x]` strictly inside the `xs` part. -/
private theorem getElemBang_append_left {α : Type} [Inhabited α] (xs : List α) (x : α)
    (i : Nat) (h : i < xs.length) :
    (xs ++ [x])[i]! = xs[i]! := by
  rw [getElem!_pos (xs ++ [x]) i (by simp; omega), getElem!_pos xs i h, List.getElem_append_left h]

/-- `getElem!` of `xs ++ [x]` at the appended slot. -/
private theorem getElemBang_append_right {α : Type} [Inhabited α] (xs : List α) (x : α) :
    (xs ++ [x])[xs.length]! = x := by
  rw [getElem!_pos (xs ++ [x]) xs.length (by simp)]; simp

/-- `getElem!` bridge `Array → toList`, in range. -/
private theorem arr_getElemBang_toList {α : Type} [Inhabited α] (a : Array α) (i : Nat)
    (h : i < a.size) : a[i]! = a.toList[i]! := by
  rw [getElem!_pos a i h, getElem!_pos a.toList i (by rw [Array.length_toList]; exact h),
      Array.getElem_toList]

/-- The `d=1` swap nm-update at the list level is exactly the canonical
erase-second-then-append (`e = length-2`): both produce the same list pointwise
(proved by `getElem!` extensionality, three index cases). -/
private theorem swap_toList_canonical {α : Type} [Inhabited α] (l : List α) (h : 2 ≤ l.length) :
    (l.set (l.length - 1) (l[l.length - 2]!)).set (l.length - 2) (l[l.length - 1]!)
      = (l.eraseIdx (l.length - 2)) ++ [l[l.length - 2]!] := by
  have herasel : (l.eraseIdx (l.length - 2)).length = l.length - 1 := by
    rw [List.length_eraseIdx_of_lt (by omega)]
  apply list_ext_getElemBang
  · rw [List.length_set, List.length_set, List.length_append, List.length_singleton, herasel]
    omega
  · intro n hn
    rw [List.length_set, List.length_set] at hn
    rw [getElemBang_set (l.set (l.length - 1) (l[l.length - 2]!)) (l.length - 2) n
          (l[l.length - 1]!) (by rw [List.length_set]; exact hn)]
    rw [getElemBang_set l (l.length - 1) n (l[l.length - 2]!) hn]
    by_cases h2 : l.length - 2 = n
    · subst h2
      simp only [if_pos]
      have hbelow : l.length - 2 < (l.eraseIdx (l.length - 2)).length := by rw [herasel]; omega
      rw [getElemBang_append_left (l.eraseIdx (l.length - 2)) (l[l.length - 2]!) (l.length - 2)
            hbelow]
      rw [getElemBang_eraseIdx_ge l (l.length - 2) (l.length - 2) (Nat.le_refl _) (by omega)
            (by rw [herasel]; omega)]
      congr 1; omega
    · by_cases h1 : l.length - 1 = n
      · subst h1
        rw [if_neg h2, if_pos rfl]
        have hidx : l.length - 1 = (l.eraseIdx (l.length - 2)).length := by rw [herasel]
        rw [hidx]
        exact (getElemBang_append_right (l.eraseIdx (l.length - 2)) (l[l.length - 2]!)).symm
      · simp only [if_neg h2, if_neg h1]
        have hnlt : n < l.length - 2 := by omega
        have hbelow : n < (l.eraseIdx (l.length - 2)).length := by rw [herasel]; omega
        rw [getElemBang_append_left (l.eraseIdx (l.length - 2)) (l[l.length - 2]!) n hbelow]
        rw [getElemBang_eraseIdx_lt l (l.length - 2) n hnlt (by omega)]

/-- The `d=0` nm-update is identity: erasing the last slot and pushing it back
yields the original list. -/
private theorem eraseLast_append {α : Type} [Inhabited α] (l : List α) (h : 0 < l.length) :
    (l.eraseIdx (l.length - 1)) ++ [l[l.length - 1]!] = l := by
  rw [List.eraseIdx_length_sub_one]
  have hne : l ≠ [] := by intro hc; rw [hc] at h; simp at h
  have hgl : l[l.length - 1]! = l.getLast hne := by
    rw [List.getLast_eq_getElem, getElem!_pos l (l.length - 1) (by omega)]
  rw [hgl, List.dropLast_concat_getLast]

/-- **Canonical erase-push `TrackerSim` preservation (the slot-reindexing core).**
Erasing the array slot at index `nm.size-1-d` and pushing it on top mirrors the
runtime erasing structural depth `d` and consing `stk[d]!` on top.  Length: off
`Array.toList_eraseIdxIfInBounds` + `List.length_eraseIdx`.  Slots: per-index
reindexing across array-erase-then-push vs list-cons-after-erase, split at the
erase point `d` (top slot / below-`d` / at-or-above-`d`). -/
private theorem TrackerSim_canonical (nm : Array (Option String)) (σ : String → Value)
    (stk : List Value) (d : Nat) (hd : d < nm.size) (hSim : TrackerSim nm σ stk) :
    TrackerSim ((nm.eraseIdxIfInBounds (nm.size - 1 - d)).push (nm[nm.size - 1 - d]!))
      σ (stk[d]! :: stk.eraseIdx d) := by
  obtain ⟨hlen, hslot⟩ := hSim
  generalize he_def : nm.size - 1 - d = e at *
  have he_lt : e < nm.size := by omega
  have herase_tl : (nm.eraseIdxIfInBounds e).toList = nm.toList.eraseIdx e :=
    Array.toList_eraseIdxIfInBounds
  have hnm_tllen : nm.toList.length = nm.size := Array.length_toList
  have herase_size : (nm.eraseIdxIfInBounds e).size = nm.size - 1 := by
    rw [← Array.length_toList, herase_tl,
        List.length_eraseIdx_of_lt (by rw [hnm_tllen]; exact he_lt), hnm_tllen]
  have hnm'_size : ((nm.eraseIdxIfInBounds e).push (nm[e]!)).size = nm.size := by
    rw [Array.size_push, herase_size]; omega
  have hnm'_tl : ((nm.eraseIdxIfInBounds e).push (nm[e]!)).toList
      = nm.toList.eraseIdx e ++ [nm[e]!] := by rw [Array.toList_push, herase_tl]
  refine ⟨?_, ?_⟩
  · rw [List.length_cons, List.length_eraseIdx_of_lt (by omega : d < stk.length), hnm'_size]
    omega
  · intro i hi
    have hi' : i < nm.size := by rwa [hnm'_size] at hi
    have hnm'_get : ((nm.eraseIdxIfInBounds e).push (nm[e]!))[i]
        = ((nm.eraseIdxIfInBounds e).push (nm[e]!)).toList[i]! :=
      Eq.symm (getElem!_pos ((nm.eraseIdxIfInBounds e).push (nm[e]!)).toList i
        (by rw [Array.length_toList, hnm'_size]; exact hi'))
    rw [hnm'_get, hnm'_tl, hnm'_size]
    have herasel : (nm.toList.eraseIdx e).length = nm.size - 1 := by
      rw [List.length_eraseIdx_of_lt (by rw [hnm_tllen]; exact he_lt), hnm_tllen]
    by_cases htop : i = nm.size - 1
    · subst htop
      have hsizeerasel : (nm.toList.eraseIdx e).length = nm.size - 1 := herasel
      have happend_top : (nm.toList.eraseIdx e ++ [nm[e]!])[nm.size - 1]! = nm[e]! := by
        rw [← hsizeerasel]; exact getElemBang_append_right (nm.toList.eraseIdx e) (nm[e]!)
      rw [happend_top]
      have hidx0 : nm.size - 1 - (nm.size - 1) = 0 := by omega
      rw [hidx0, List.getElem!_cons_zero]
      have horig := hslot e he_lt
      have hed : nm.size - 1 - e = d := by omega
      rw [hed] at horig
      have hnmebang : nm[e]! = nm[e]'he_lt := by rw [getElem!_pos nm e he_lt]
      rw [hnmebang]
      exact horig
    · have hilt : i < nm.size - 1 := by omega
      have happend_low : (nm.toList.eraseIdx e ++ [nm[e]!])[i]! = (nm.toList.eraseIdx e)[i]! :=
        getElemBang_append_left (nm.toList.eraseIdx e) (nm[e]!) i (by rw [herasel]; omega)
      rw [happend_low]
      have hrt_succ : nm.size - 1 - i = (nm.size - 2 - i) + 1 := by omega
      rw [hrt_succ, List.getElem!_cons_succ]
      have he_lt_tl : e < nm.toList.length := by rw [hnm_tllen]; exact he_lt
      by_cases hsplit : i < e
      · rw [getElemBang_eraseIdx_lt nm.toList e i hsplit he_lt_tl]
        have hnmi : nm.toList[i]! = nm[i]'hi' := by
          rw [getElem!_pos nm.toList i (by rw [hnm_tllen]; exact hi'), Array.getElem_toList]
        rw [hnmi]
        have horig := hslot i hi'
        have hge_d : d ≤ nm.size - 2 - i := by omega
        have hd_stk : d < stk.length := by omega
        have herasestk : (stk.eraseIdx d)[nm.size - 2 - i]! = stk[(nm.size - 2 - i) + 1]! := by
          apply getElemBang_eraseIdx_ge stk d (nm.size - 2 - i) hge_d hd_stk
          rw [List.length_eraseIdx_of_lt hd_stk]; omega
        rw [herasestk]
        have hh : (nm.size - 2 - i) + 1 = nm.size - 1 - i := by omega
        rw [hh]
        exact horig
      · have hsplit' : e ≤ i := Nat.le_of_not_lt hsplit
        rw [getElemBang_eraseIdx_ge nm.toList e i hsplit' he_lt_tl
              (by rw [List.length_eraseIdx_of_lt he_lt_tl, hnm_tllen]; omega)]
        have hi1 : i + 1 < nm.size := by omega
        have hnmi1 : nm.toList[i+1]! = nm[i+1]'hi1 := by
          rw [getElem!_pos nm.toList (i+1) (by rw [hnm_tllen]; exact hi1), Array.getElem_toList]
        rw [hnmi1]
        have horig := hslot (i+1) hi1
        have hlt_d : nm.size - 2 - i < d := by omega
        have hd_stk : d < stk.length := by omega
        have herasestk : (stk.eraseIdx d)[nm.size - 2 - i]! = stk[nm.size - 2 - i]! :=
          getElemBang_eraseIdx_lt stk d (nm.size - 2 - i) hlt_d hd_stk
        rw [herasestk]
        have hidxeq : nm.size - 1 - (i + 1) = nm.size - 2 - i := by omega
        rw [hidxeq] at horig
        exact horig

/-- **`Tracker.roll d` nm = the canonical erase-push form**, all four `roll`
branches (`d=0` identity, `d=1` swap, `d=2` rot, `d≥3` bare roll), for `d` in
range.  Bridges the concrete `roll`/`swap`/`rot` nm-updates to the single
`TrackerSim_canonical` shape. -/
private theorem roll_nm_canonical (t : Ec.Tracker) (d : Nat) (hd : d < t.nm.size) :
    (t.roll d).nm = (t.nm.eraseIdxIfInBounds (t.nm.size - 1 - d)).push (t.nm[t.nm.size - 1 - d]!) := by
  match d with
  | 0 =>
    show t.nm = _
    apply Array.ext'
    rw [Array.toList_push, Array.toList_eraseIdxIfInBounds]
    have ht : t.nm.size - 1 - 0 = t.nm.toList.length - 1 := by rw [Array.length_toList]; omega
    rw [ht, arr_getElemBang_toList t.nm (t.nm.toList.length - 1)
          (by rw [Array.length_toList] at *; omega)]
    exact (eraseLast_append t.nm.toList (by rw [Array.length_toList]; omega)).symm
  | 1 =>
    unfold Ec.Tracker.roll Ec.Tracker.swap
    simp only [Ec.Tracker.emit]
    rw [if_pos (by omega : t.nm.size ≥ 2)]
    apply Array.ext'
    rw [Array.toList_push, Array.toList_eraseIdxIfInBounds]
    show ((t.nm.set! (t.nm.size - 1) (t.nm[t.nm.size - 2]!)).set! (t.nm.size - 2)
            (t.nm[t.nm.size - 1]!)).toList = _
    rw [Array.set!, Array.set!, Array.toList_setIfInBounds, Array.toList_setIfInBounds]
    have hl : t.nm.toList.length = t.nm.size := Array.length_toList
    rw [arr_getElemBang_toList t.nm (t.nm.size - 2) (by omega),
        arr_getElemBang_toList t.nm (t.nm.size - 1) (by omega),
        arr_getElemBang_toList t.nm (t.nm.size - 1 - 1) (by omega)]
    have he1 : t.nm.size - 1 = t.nm.toList.length - 1 := by rw [hl]
    have he2 : t.nm.size - 2 = t.nm.toList.length - 2 := by rw [hl]
    have he3 : t.nm.size - 1 - 1 = t.nm.toList.length - 2 := by rw [hl]; omega
    rw [he3, he2, he1]
    exact swap_toList_canonical t.nm.toList (by rw [hl]; omega)
  | 2 =>
    unfold Ec.Tracker.roll Ec.Tracker.rot
    simp only [Ec.Tracker.emit]
    rw [if_pos (by omega : t.nm.size ≥ 3)]
    have he : t.nm.size - 1 - 2 = t.nm.size - 3 := by omega
    rw [he]
  | n + 3 =>
    unfold Ec.Tracker.roll
    simp only [Ec.Tracker.emit]
    rw [if_pos (by omega : t.nm.size ≥ (n + 3) + 1)]

/-- **THE KEYSTONE (deliverable 1) — `toTop` nm-side `TrackerSim` preservation.**
After `Tracker.toTop name` (= `roll (findDepth name)`), the tracker's name array and
the runtime stack stay in lock-step: the runtime brings `σ name` to the top
(remainder `stk.eraseIdx d`, the `runOps_toTop_extraOps_sim` witness), and the
tracker's `nm` becomes the canonical erase-push form (`roll_nm_canonical`), which
preserves `TrackerSim` by the slot-reindexing core (`TrackerSim_canonical`), since
`stk[d]! = σ name` (`findDepthList_sim`).  `d := findDepthList name nm.toList.reverse`
is the codegen depth via the wave-77 bridge `findDepth_eq_findDepthList`.  This is
the `toTop` peer of `TrackerSim_copyToTop` and the last model-preservation lemma the
Part-9 hand-off named. -/
theorem TrackerSim_toTop (t : Ec.Tracker) (σ : String → Value) (stk : List Value)
    (name : String)
    (hSim : TrackerSim t.nm σ stk)
    (hmem : some name ∈ t.nm.toList.reverse) :
    TrackerSim (t.toTop name).nm σ
      (σ name :: stk.eraseIdx (findDepthList name t.nm.toList.reverse)) := by
  have hbridge : t.findDepth name = findDepthList name t.nm.toList.reverse :=
    findDepth_eq_findDepthList t name hmem
  have hsim := findDepthList_sim t.nm σ stk name hSim hmem
  obtain ⟨hlt, hval⟩ := hsim
  have hd_lt : findDepthList name t.nm.toList.reverse < t.nm.size := by
    obtain ⟨hlen, _⟩ := hSim; omega
  unfold Ec.Tracker.toTop
  rw [hbridge, roll_nm_canonical t (findDepthList name t.nm.toList.reverse) hd_lt]
  have hcanon := TrackerSim_canonical t.nm σ stk (findDepthList name t.nm.toList.reverse) hd_lt hSim
  rwa [hval] at hcanon

/-! ### MANDATORY smokes for the `toTop`/`copyToTop` transports (deliverable 1) -/

/-- SMOKE (`roll` ops-append fires).  `(simTracker.roll 2).ops = simTracker.ops ++ [.rot]`. -/
theorem smoke_roll_ops_append :
    (simTracker.roll 2).ops.toList = simTracker.ops.toList ++ [StackOp.rot] := by
  rw [roll_ops_append]; rfl

/-- SMOKE (`pick` ops-append fires).  `(simTracker.pick 3 "z").ops = … ++ [.pickStruct 3]`. -/
theorem smoke_pick_ops_append :
    (simTracker.pick 3 "z").ops.toList = simTracker.ops.toList ++ [StackOp.pickStruct 3] := by
  rw [pick_ops_append]; rfl

/-- SMOKE (`pick` nm-push fires).  `(simTracker.pick 3 "z").nm = simTracker.nm.push (some "z")`. -/
theorem smoke_pick_nm_push :
    (simTracker.pick 3 "z").nm = simTracker.nm.push (some "z") := by
  rw [pick_nm_push]

/-- SMOKE (`roll` runtime transport fires).  `rollExtraOps 1 = [.swap]` on
`[30, 20, 10]` swaps the top two: `[20, 30, 10]` = `applyRoll · 1`. -/
theorem smoke_runOps_rollExtraOps :
    runOps (rollExtraOps 1) { (default : StackState) with stack := simStk }
      = applyRoll { (default : StackState) with stack := simStk } 1 := by
  apply runOps_rollExtraOps; decide

/-- SMOKE (`pick` runtime transport fires).  `pickExtraOps 2 = [.pickStruct 2]` on
`[30, 20, 10]` copies depth-2 (= 10): `[10, 30, 20, 10]` = `applyPick · 2`. -/
theorem smoke_runOps_pickExtraOps :
    runOps (pickExtraOps 2) { (default : StackState) with stack := simStk }
      = applyPick { (default : StackState) with stack := simStk } 2 := by
  apply runOps_pickExtraOps; decide

/-- SMOKE (`toTop` transport fires under the concrete `TrackerSim`).  Bringing
`"a"` (depth 2) to the top lands `σ "a" = 10` over the erased remainder. -/
theorem smoke_runOps_toTop_extraOps_sim :
    runOps (rollExtraOps (findDepthList "a" simNm.toList.reverse))
        { (default : StackState) with stack := simStk }
      = .ok { (default : StackState) with
              stack := simσ "a"
                :: simStk.eraseIdx (findDepthList "a" simNm.toList.reverse) } := by
  apply runOps_toTop_extraOps_sim
  · exact smoke_TrackerSim_satisfiable
  · decide

/-- SMOKE (`copyToTop` transport fires under the concrete `TrackerSim`).  Copying
`"a"` (depth 2) lands `σ "a" = 10` on top without removing it. -/
theorem smoke_runOps_copyToTop_extraOps_sim :
    runOps (pickExtraOps (findDepthList "a" simNm.toList.reverse))
        { (default : StackState) with stack := simStk }
      = .ok (({ (default : StackState) with stack := simStk }).push (simσ "a")) := by
  apply runOps_copyToTop_extraOps_sim
  · exact smoke_TrackerSim_satisfiable
  · decide

/-- SMOKE (`copyToTop` preservation fires).  Copying `"a"` to a fresh `"d"` extends
the concrete `TrackerSim` with `"d" ↦ σ "a" = 10`. -/
theorem smoke_TrackerSim_copyToTop :
    TrackerSim (simNm.push (some "d"))
      (fun t => if t = "d" then simσ "a" else simσ t) (simσ "a" :: simStk) := by
  apply TrackerSim_copyToTop { (default : StackState) with stack := simStk }
  · exact smoke_TrackerSim_satisfiable
  · decide

/-- SMOKE (the KEYSTONE fires — anti-vacuity).  `simTracker.nm = [a,b,c]`; bringing
`"a"` (codegen depth 2) to the top via `toTop` keeps `TrackerSim`: the new name
array is `[b,c,a]` and the runtime is `σ "a" :: simStk.eraseIdx 2 = [10, 30, 20]`.
Discharged through the keystone `TrackerSim_toTop` on the concrete tracker. -/
theorem smoke_TrackerSim_toTop :
    TrackerSim (simTracker.toTop "a").nm simσ
      (simσ "a" :: simStk.eraseIdx (findDepthList "a" simTracker.nm.toList.reverse)) := by
  apply TrackerSim_toTop simTracker simσ simStk "a"
  · refine ⟨by decide, ?_⟩
    intro i hi
    rw [getElem!_pos simTracker.nm i hi |>.symm]
    have hsz : simTracker.nm.size = 3 := by decide
    have h3 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    clear hi
    unfold slotAgrees
    rcases h3 with rfl | rfl | rfl <;> (unfold simTracker simStk simσ; rfl)
  · decide

/-! ### Per-helper ops-append lemmas (wave-78 deliverable 2)

Each Tracker helper APPENDS a determined op-list to `t.ops`, so `runOps_append`
decomposes the 945/518-op codegen list helper-by-helper.  The leaf primitives —
`rawBlock`, `pushInt`/`pushBytes`/`pushFieldP`, `toTop`, `copyToTop` — append a
list expressible via `rollExtraOps`/`pickExtraOps` (D1) at the depth the codegen
decides (`Tracker.findDepth`).  The field helpers compose those leaves; we ship
`fieldMod` as the worked non-nested example (the binop helpers nest a second
`toTop` whose depth is taken against the post-first-`toTop` tracker — provable by
the same `rw` chain, but the conclusion is a nested-tracker term, so we leave the
binop expansions to the assembly site rather than pre-baking a verbose lemma). -/

/-- **Id-monad `forIn`-push fold = append.**  The `rawBlock` ops loop folds
`Array.push` over the extra-ops list; its `toList` is `arr.toList ++ e`. -/
theorem forIn_id_push_toList :
    ∀ (e : List StackOp) (arr : Array StackOp),
      (forIn (m := Id) e arr fun op r => ForInStep.yield (r.push op)).toList
        = arr.toList ++ e := by
  intro e
  induction e with
  | nil => intro arr; rw [List.forIn_nil]; show arr.toList = arr.toList ++ []; simp
  | cons hd tl ih =>
    intro arr
    rw [List.forIn_cons]
    show (forIn (m := Id) tl (arr.push hd) fun op r => ForInStep.yield (r.push op)).toList = _
    rw [ih (arr.push hd)]; simp

/-- The `.ops` field of `rawBlock` is the `forIn`-push fold of the extra ops over
`t.ops`, independent of `produce` and the (ops-irrelevant) `nm` pop loop. -/
theorem rawBlock_ops_eq (t : Ec.Tracker) (c : Nat) (p : Option String) (e : List StackOp) :
    (t.rawBlock c p e).ops
      = forIn (m := Id) e t.ops fun op r => ForInStep.yield (r.push op) := by
  unfold Ec.Tracker.rawBlock; cases p <;> rfl

/-- **`rawBlock` ops-append.**  `(t.rawBlock c p e).ops = t.ops ++ e`. -/
theorem rawBlock_ops_append (t : Ec.Tracker) (c : Nat) (p : Option String) (e : List StackOp) :
    (t.rawBlock c p e).ops.toList = t.ops.toList ++ e := by
  rw [rawBlock_ops_eq]; exact forIn_id_push_toList e t.ops

/-- **`pushInt` ops-append.** -/
theorem pushInt_ops_append (t : Ec.Tracker) (n : String) (v : Int) :
    (t.pushInt n v).ops.toList = t.ops.toList ++ [.push (.bigint v)] := by
  unfold Ec.Tracker.pushInt Ec.Tracker.emit; simp

/-- **`pushBytes` ops-append.** -/
theorem pushBytes_ops_append (t : Ec.Tracker) (n : String) (v : ByteArray) :
    (t.pushBytes n v).ops.toList = t.ops.toList ++ [.push (.bytes v)] := by
  unfold Ec.Tracker.pushBytes Ec.Tracker.emit; simp

/-- **`pushFieldP` ops-append.**  Pushes the field prime literal. -/
theorem pushFieldP_ops_append (t : Ec.Tracker) (n : String) :
    (Ec.pushFieldP t n).ops.toList = t.ops.toList ++ [.push (.bigint Ec.fieldP)] := by
  unfold Ec.pushFieldP; exact pushInt_ops_append t n Ec.fieldP

/-- **`toTop` ops-append.**  `(t.toTop name).ops = t.ops ++ rollExtraOps (findDepth name)`.
The appended op is the depth-`Tracker.findDepth name` `roll` op (D1 `rollExtraOps`). -/
theorem toTop_ops_append (t : Ec.Tracker) (name : String) :
    (t.toTop name).ops.toList = t.ops.toList ++ rollExtraOps (t.findDepth name) := by
  unfold Ec.Tracker.toTop; exact roll_ops_append t (t.findDepth name)

/-- **`copyToTop` ops-append.**  `(t.copyToTop name newName).ops = t.ops ++
pickExtraOps (findDepth name)` (D1 `pickExtraOps`, depth-`Tracker.findDepth name`). -/
theorem copyToTop_ops_append (t : Ec.Tracker) (name newName : String) :
    (t.copyToTop name newName).ops.toList = t.ops.toList ++ pickExtraOps (t.findDepth name) := by
  unfold Ec.Tracker.copyToTop; exact pick_ops_append t (t.findDepth name) newName

/-- **`fieldMod` ops-append (worked field-helper example).**  `fieldMod` is
`toTop a → pushFieldP → rawBlock 2 r fieldModOps`; its ops append in that order. -/
theorem fieldMod_ops_append (t : Ec.Tracker) (a r : String) :
    (Ec.fieldMod t a r).ops.toList
      = t.ops.toList ++ rollExtraOps (t.findDepth a)
        ++ [.push (.bigint Ec.fieldP)] ++ Ec.fieldModOps := by
  unfold Ec.fieldMod
  rw [rawBlock_ops_append, pushFieldP_ops_append, toTop_ops_append]

/-- **Generic field-binop ops-append (deliverable 2 — the nested helper template).**
`fieldAdd`/`fieldSub`/`fieldMul` all share the shape `toTop a → toTop b →
rawBlock 2 prod [binop] → fieldMod prod r`.  Each nested `toTop`/`fieldMod` depth
is `Tracker.findDepth` against the *cumulative* tracker at that step, so the
appended op-blocks name the intermediate trackers explicitly (`t1 = toTop a`,
`t2 = toTop b t1`, `t3 = rawBlock … t2`).  This is the leaf-level decomposition the
whole-program assembly threads, mirroring the codegen's left-to-right helper order. -/
theorem fieldBinop_ops_append (t : Ec.Tracker) (a b prod r : String) (binop : StackOp) :
    (Ec.fieldMod (((t.toTop a).toTop b).rawBlock 2 (some prod) [binop]) prod r).ops.toList
      = t.ops.toList ++ rollExtraOps (t.findDepth a)
        ++ rollExtraOps ((t.toTop a).findDepth b)
        ++ [binop]
        ++ rollExtraOps ((((t.toTop a).toTop b).rawBlock 2 (some prod) [binop]).findDepth prod)
        ++ [.push (.bigint Ec.fieldP)] ++ Ec.fieldModOps := by
  rw [fieldMod_ops_append, rawBlock_ops_append, toTop_ops_append, toTop_ops_append]

/-- **`fieldMul` ops-append.**  Instantiates `fieldBinop_ops_append` at `OP_MUL`. -/
theorem fieldMul_ops_append (t : Ec.Tracker) (a b r : String) :
    (Ec.fieldMul t a b r).ops.toList
      = t.ops.toList ++ rollExtraOps (t.findDepth a)
        ++ rollExtraOps ((t.toTop a).findDepth b)
        ++ [.opcode "OP_MUL"]
        ++ rollExtraOps ((((t.toTop a).toTop b).rawBlock 2 (some "_fmul_prod")
              [.opcode "OP_MUL"]).findDepth "_fmul_prod")
        ++ [.push (.bigint Ec.fieldP)] ++ Ec.fieldModOps := by
  unfold Ec.fieldMul
  exact fieldBinop_ops_append t a b "_fmul_prod" r (.opcode "OP_MUL")

/-- **`fieldAdd` ops-append.**  Instantiates `fieldBinop_ops_append` at `OP_ADD`. -/
theorem fieldAdd_ops_append (t : Ec.Tracker) (a b r : String) :
    (Ec.fieldAdd t a b r).ops.toList
      = t.ops.toList ++ rollExtraOps (t.findDepth a)
        ++ rollExtraOps ((t.toTop a).findDepth b)
        ++ [.opcode "OP_ADD"]
        ++ rollExtraOps ((((t.toTop a).toTop b).rawBlock 2 (some "_fadd_sum")
              [.opcode "OP_ADD"]).findDepth "_fadd_sum")
        ++ [.push (.bigint Ec.fieldP)] ++ Ec.fieldModOps := by
  unfold Ec.fieldAdd
  exact fieldBinop_ops_append t a b "_fadd_sum" r (.opcode "OP_ADD")

/-! ### MANDATORY smokes for the per-helper ops-append lemmas (deliverable 2) -/

/-- SMOKE (`rawBlock` ops-append fires).  Appending `[OP_ADD]` to `simTracker.ops`. -/
theorem smoke_rawBlock_ops_append :
    (simTracker.rawBlock 2 (some "s") [.opcode "OP_ADD"]).ops.toList
      = simTracker.ops.toList ++ [StackOp.opcode "OP_ADD"] := by
  rw [rawBlock_ops_append]

/-- SMOKE (`pushFieldP` ops-append fires).  Appends the field-prime push. -/
theorem smoke_pushFieldP_ops_append :
    (Ec.pushFieldP simTracker "p").ops.toList
      = simTracker.ops.toList ++ [StackOp.push (.bigint Ec.fieldP)] := by
  rw [pushFieldP_ops_append]

/-- SMOKE (`toTop` ops-append fires + concrete depth).  `simTracker` has `nm =
[a,b,c]`; `toTop "a"` rolls depth 2, appending `rollExtraOps 2 = [.rot]`. -/
theorem smoke_toTop_ops_append :
    (simTracker.toTop "a").ops.toList = simTracker.ops.toList ++ [StackOp.rot] := by
  rw [toTop_ops_append]
  have : simTracker.findDepth "a" = 2 := by decide
  rw [this]; rfl

/-- SMOKE (`copyToTop` ops-append fires + concrete depth).  `copyToTop "a"` picks
depth 2, appending `pickExtraOps 2 = [.pickStruct 2]`. -/
theorem smoke_copyToTop_ops_append :
    (simTracker.copyToTop "a" "z").ops.toList
      = simTracker.ops.toList ++ [StackOp.pickStruct 2] := by
  rw [copyToTop_ops_append]
  have : simTracker.findDepth "a" = 2 := by decide
  rw [this]; rfl

/-- SMOKE (`fieldMod` ops-append fires).  Full decomposition of `fieldMod "a" "r"`
on `simTracker`: `toTop` (depth 2 → `.rot`), push prime, then `fieldModOps`. -/
theorem smoke_fieldMod_ops_append :
    (Ec.fieldMod simTracker "a" "r").ops.toList
      = simTracker.ops.toList ++ rollExtraOps (simTracker.findDepth "a")
        ++ [StackOp.push (.bigint Ec.fieldP)] ++ Ec.fieldModOps := by
  rw [fieldMod_ops_append]

/-- SMOKE (`fieldMul` ops-append fires).  Full nested decomposition of
`fieldMul "a" "b" "r"` on `simTracker`: two `toTop`s (against the cumulative
trackers), `OP_MUL`, the result `toTop`, push prime, then `fieldModOps`. -/
theorem smoke_fieldMul_ops_append :
    (Ec.fieldMul simTracker "a" "b" "r").ops.toList
      = simTracker.ops.toList ++ rollExtraOps (simTracker.findDepth "a")
        ++ rollExtraOps ((simTracker.toTop "a").findDepth "b")
        ++ [StackOp.opcode "OP_MUL"]
        ++ rollExtraOps ((((simTracker.toTop "a").toTop "b").rawBlock 2 (some "_fmul_prod")
              [.opcode "OP_MUL"]).findDepth "_fmul_prod")
        ++ [StackOp.push (.bigint Ec.fieldP)] ++ Ec.fieldModOps := by
  rw [fieldMul_ops_append]

/-- SMOKE (`fieldAdd` ops-append fires).  Same nested shape at `OP_ADD`. -/
theorem smoke_fieldAdd_ops_append :
    (Ec.fieldAdd simTracker "a" "b" "r").ops.toList
      = simTracker.ops.toList ++ rollExtraOps (simTracker.findDepth "a")
        ++ rollExtraOps ((simTracker.toTop "a").findDepth "b")
        ++ [StackOp.opcode "OP_ADD"]
        ++ rollExtraOps ((((simTracker.toTop "a").toTop "b").rawBlock 2 (some "_fadd_sum")
              [.opcode "OP_ADD"]).findDepth "_fadd_sum")
        ++ [StackOp.push (.bigint Ec.fieldP)] ++ Ec.fieldModOps := by
  rw [fieldAdd_ops_append]

/-! ## Part 9 — BLOCKED `Crypto/Spec.lean §7` axioms: `ecNegate`, `ecOnCurve`

The remaining two "medium" EC ops are NOT plain op-lists.  Unlike `ecPointX/Y`
and `ecMakePoint` (whose only non-trivial sub-block is `emitReverse32Ops`), both
`emitEcNegate` and `emitEcOnCurve` are produced by RUNNING the `Stack.Ec.Tracker`
state machine: their op lists are `t.ops.toList` after a chain of
`decomposePoint` / `composePoint` / `fieldSub` / `fieldSqr` / `fieldMul` /
`fieldAdd`, each of which interleaves `t.toTop` / `t.copyToTop` operations that
emit `.roll d` / `.pickStruct d` whose depth `d = Tracker.findDepth name` is
computed at CODEGEN TIME against the threaded name array `nm`.

* `emitEcNegate`  : 945 ops — 257 `.rot`, 2 `OP_MOD` (one `fieldSub`, no
  `OP_MUL`), routed through two `emitReverse32Ops` blocks in `decompose`/`compose`.
* `emitEcOnCurve` : 518 ops — 1 `.roll`, 1 `.pickStruct`, 132 `.rot`, 8 `OP_MOD`,
  3 `OP_MUL` (two `fieldSqr`, one `fieldMul`, one `fieldAdd`) + a final `OP_EQUAL`.

**SUBSTRATE LANDED (Part 8).**  The Tracker-to-runtime simulation invariant
`TrackerSim` and its model substrate are now in place, all `sorry`-free /
axiom-clean:

  * `TrackerSim nm σ stk` — the runtime stack mirrors the tracker name array.
  * `findDepthList` — the kernel-reducible recursive model of `Tracker.findDepth`,
    with `findDepthList_lt`, `findDepthList_get`, `reverse_getElem_bridge`.
  * `findDepthList_sim` (KEYSTONE) — under `TrackerSim`, the runtime stack value at
    structural depth `findDepthList name (nm.toList.reverse)` is exactly `σ name`.
  * `TrackerSim_push` (push/rawBlock-produce preservation),
    `applyRoll_findDepth_sim` (`roll`/`toTop` preservation),
    `applyPick_findDepth_sim` (`pick`/`copyToTop` preservation).

**WAVE-76 BLOCKER CLEARED (wave-77).**  The wave-76 BLOCK was the kernel wall that
`Tracker.findDepth` was an `Id.run do … while …` (→ `Lean.Loop.forIn`, a
`partial def` with no equational lemma / no `.induct` / no kernel reduction), so
the bridge `Tracker.findDepth t name = findDepthList name t.nm.toList.reverse` was
unprovable without editing `Stack/Ec.lean`.  Wave-77 PERFORMS that sanctioned,
OUTPUT-PRESERVING refactor: `findDepth` is now a structural fold
(`(Ec.Tracker.findDepthAux name t.nm.toList.reverse).getD 0`), kernel-reducible,
computing byte-identical depths (verified: the EC conformance goldens
`convergence-proof`/`ec-demo`/`ec-primitives`/`ec-unit` recompile byte-exact via
the Lean `compileHex`; `schnorr-zkp` overflows the macOS 64 MB native stack in the
DOWNSTREAM peephole pass identically under both the old and new `findDepth`, i.e.
the overflow is pre-existing and independent of this change).  The bridge
`findDepth_eq_findDepthList` (above) is now proved by structural induction
(`findDepthAux_eq_findDepthList`), NOT `native_decide`, `propext`/`Quot.sound`-clean.

**LANDED WAVE-77 (the bridge + field-helper transports).**
  * The `findDepth` refactor (output-preserving) + the bridge.
  * The per-helper transports: `fieldModOps_transport`,
    `fieldBinop_optail_transport` + `fieldAdd/fieldSub/fieldMul_optail_transport`
    (each → `Crypto.Secp256k1.field*`, divisor `fieldP ≠ 0` via kernel `decide`),
    and `applyPickStruct_findDepth_sim` (the codegen-emitted-op peer of the
    substrate's `applyPick_findDepth_sim`).  All `propext`/`Quot.sound`-clean (plus
    the pre-existing `authBackend`/`hashBackend` opaques inherited via
    `ecModReduce_step_transport`), each with an anti-vacuity smoke.

**LANDED THIS WAVE (wave-78 — deliverables 1 & 2, the per-op assembly scaffolding).**
The two scaffolding pieces the wave-77 hand-off named as the remaining gap are now
in place above, all `propext`/`Quot.sound`-clean (plus the inherited
`authBackend`/`hashBackend` opaques on the `runOps`-bearing transports), each with
an anti-vacuity smoke:

  1. **`toTop` / `copyToTop` runtime transports** — `rollExtraOps`/`pickExtraOps`
     model the depth-dependent op the Tracker emits; `runOps_rollExtraOps` /
     `runOps_pickExtraOps` collapse the depth-0/1/2 special cases (`nop`/`.swap`/
     `.rot` and `.dup`/`.over`) to `applyRoll`/`applyPick` via the conditional
     bridges `applySwap_eq_applyRoll1` / `applyRot_eq_applyRoll2` /
     `applyDup_eq_applyPick0` / `applyOver_eq_applyPick1` (the `applySwap`/`applyRot`/
     `applyDup`/`applyOver` peers the hand-off asked for), and the `≥3`/`≥2` cases to
     the bare `.roll d`/`.pickStruct d`.  Composed with the wave-76 model lemmas +
     the wave-77 bridge: `runOps_toTop_extraOps_sim` brings `σ name` to the TOS
     (remainder `eraseIdx d`), `runOps_copyToTop_extraOps_sim` copies it.
     `TrackerSim_copyToTop` (= `TrackerSim_push`) is the copyToTop invariant
     preservation.

  2. **Per-helper ops-append lemmas** — `forIn_id_push_toList` →
     `rawBlock_ops_eq`/`rawBlock_ops_append`, `pushInt`/`pushBytes`/`pushFieldP_ops_append`,
     `toTop_ops_append` (`= … ++ rollExtraOps (findDepth name)`),
     `copyToTop_ops_append` (`= … ++ pickExtraOps (findDepth name)`), and the worked
     `fieldMod_ops_append`.  These let `runOps_append` decompose the 945/518-op list
     helper-by-helper at the leaf level.

**LANDED THIS WAVE (wave-79 — THE KEYSTONE + field-binop ops-append template).**
The Part-9 sub-goal (a) the wave-78 hand-off named as "the one remaining
model-preservation lemma" is now CLOSED, all `propext`/`Classical.choice`/
`Quot.sound`-clean, NO `sorry`, NO `native_decide` (only in the concrete smokes),
NO new axiom:

  (a) **`toTop` `nm`-side `TrackerSim` preservation — `TrackerSim_toTop`** (the
      slot-reindexing keystone).  Proved via `TrackerSim_canonical` (the genuine
      slot-reindexing core: length off `Array.toList_eraseIdxIfInBounds` +
      `List.length_eraseIdx`; slots a three-way index split — top / below-`d` /
      at-or-above-`d` — across array-erase-then-push vs list-cons-after-erase under
      the `size-1-i ↔ i` reverse correspondence) + `roll_nm_canonical` (the four
      `roll` branches reduced to the single canonical erase-push array shape:
      `d=0` via `eraseLast_append`, `d=1` via `swap_toList_canonical`, `d=2`/`d≥3`
      definitional).  Composed with `findDepth_eq_findDepthList` (bridge) +
      `findDepthList_sim` (`stk[d]! = σ name`).  This is the `toTop` peer of
      `TrackerSim_copyToTop`.  Smoke: `smoke_TrackerSim_toTop`
      (`[a,b,c]`, `toTop "a"` → `[b,c,a]` / runtime `[10,30,20]`).

  Plus the field-binop ops-append template `fieldBinop_ops_append` and its
  instances `fieldMul_ops_append` / `fieldAdd_ops_append` (the nested-`toTop`
  decomposition the wave-78 note left to the assembly site), each with a smoke.

**PRECISE REMAINING SUB-GOAL (deliverable 3 — the whole-program assembly, BLOCKED).**
With (1)+(2)+(a)+the field-binop ops-append now landed, the model-preservation
layer is COMPLETE; what remains is the genuine multi-helper RUNTIME assembly, NOT a
kernel wall:

  (b) **Whole-program symbolic-`nm` threading.**  `emitEcOnCurve` (518 ops) /
      `emitEcNegate` (945 ops) are `t_final.ops.toList` after ~12–30 helper calls;
      with `runOps_append` chunking the op-list via the ops-append lemmas, each
      `toTop`/`copyToTop` step is now transported by `TrackerSim_toTop` /
      `TrackerSim_copyToTop` — but each step's `findDepth` must still be evaluated
      against the concrete *cumulative* `nm` at that step (membership + the wave-77
      bridge per step), threaded under a single rolling `TrackerSim`, with the
      field-arith leaves (`fieldAdd/Sub/Mul`-`optail` transports) composed to match
      the spec closed form `Crypto.Secp256k1.ecOnCurve` (`x:=pointX`, `y:=pointY`,
      `lhs:=fieldMul y y`, `rhs:=fieldAdd (fieldMul (fieldMul x x) x) 7`, then
      `OP_EQUAL` ↔ `decide (lhs = rhs)`).  The unfinished helper-step is the FIRST
      one: `decomposePoint`'s runtime ↔ `(pointX p, pointY p)` (see (c)) — once that
      lands as the base `TrackerSim` over `[_x, _y]`, the keystone + field transports
      thread the remaining `fieldSqr`/`fieldMul`/`fieldAdd`/`OP_EQUAL` steps
      mechanically.

  (c) **`decomposePoint` ↔ `(pointX p, pointY p)` (the unfinished base step).**
      `decomposePoint t "_pt" "_x" "_y"` runs `toTop _pt` → `rawBlock 1 none
      [push 32, OP_SPLIT]` → manual `nm.push _dp_xb/_dp_yb` → `rawBlock 1 (some _y)
      (emitReverse32Ops ++ [push 0x00, OP_CAT, OP_BIN2NUM])` → `toTop _dp_xb` →
      `rawBlock 1 (some _x) (same conv)` → `swap`.  Its 2× `emitReverse32Ops`
      reuse `reverse32_ops_transport`, and the `OP_SPLIT`/`OP_CAT`/`OP_BIN2NUM`
      legs need fresh BE-decode bridges to `Secp256k1.pointX`/`pointY` carrying the
      INPUT-side wf hypotheses (64-byte point ⇒ 32-byte coords; on-curve;
      `OP_MOD` divisors `fieldP ≠ 0`).  This is the same shape as the DISCHARGED
      `emitEcPointX_runOps_eq`/`emitEcPointY_runOps_eq` but for `decomposePoint`'s
      single-split-convert-both ordering rather than split-drop.  It is the one
      remaining helper-step whose `TrackerSim`-bearing runtime transport is unwritten.

The discharge is all-or-nothing per axiom (partial threading discharges neither
axiom), so per the task BLOCK protocol the two axioms are LEFT IN PLACE and the
drift stays `76 → 76` (0 axioms discharged this wave; THE KEYSTONE landed).  The
same model-preservation layer ((1)+(2)+(a)) immediately unblocks
`emitEcAdd`/`emitEcMul` (the wave-76 hand-off). -/

end RunarVerification.Stack.AgreesEC
