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

/-! ## Part 8 — BLOCKED `Crypto/Spec.lean §7` axioms: `ecNegate`, `ecOnCurve`

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

**PRECISE BLOCKER (the missing substrate).**  An honest `runOps` transport for
either op list requires a *Tracker-to-runtime-stack simulation invariant* that
does NOT exist in the base:

  for every codegen step, `Tracker.findDepth nm name` (the `while`-loop search the
  codegen used to pick each `.roll`/`.pickStruct` depth) must equal the runtime
  structural depth of that named value on `StackState.stack`, and this invariant
  must be PRESERVED across `roll` / `pickStruct` / `rot` / `swap` / `drop` /
  `over` / `rawBlock` — through the ~15–20 named field intermediates each op
  threads.  No `decomposePoint_transport`, `composePoint_transport`,
  `fieldSub_transport`, `fieldMul_transport`, `fieldSqr_transport`,
  `fieldAdd_transport`, nor any `Tracker.findDepth`/runtime-depth agreement lemma
  is present in the wave-74 base.  The wave-73/74 substrate
  (`reverse32_ops_transport`, the `ec_encode_op_transport` step-chain) covers
  ONLY plain op-lists; it does not lift the Tracker's `nm`-driven addressing.

Building that simulation library (a `Tracker.findDepth`↔runtime-depth invariant +
per-helper transports for `decompose`/`compose`/`fieldMod`/`fieldAdd`/`fieldSub`/
`fieldMul`/`fieldSqr`) is a standalone multi-hundred-line effort, well beyond
"compose `reverse32_ops_transport` with the field-arith opcode reductions".  Per
the task's BLOCK protocol these two are reported with the precise sub-goal above
and their `Crypto/Spec.lean §7` axioms are LEFT IN PLACE (the field-arith opcode
reductions are individually fine — `OP_MOD` by the positive constant `fieldP` ≠ 0,
`OP_MUL`/`OP_ADD`/`OP_SUB` are total — but the codegen-output op LIST cannot be
run without the Tracker addressing invariant). -/

end RunarVerification.Stack.AgreesEC
