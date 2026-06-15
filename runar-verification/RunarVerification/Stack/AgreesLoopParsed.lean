import RunarVerification.Stack.AgreesLoopBridge

/-! # Loop Tier 4c — the general accumulator `acceptAgrees` over PARSED BYTES

This file closes the documented Tier 4b/4c wall at the end of
`RunarVerification/Stack/AgreesLoopBridge.lean`: it lifts the bridge's
`runOps`-surface accumulator agreement to the **parsed-bytes** surface
`runParsedBytes (compileSafe loopOkProg)`, GENERAL over the entry `start`.

The bridge proved a real `acceptAgrees` over the *peepholed-method op*
surface (`runOps loopOkPeepChain …`), but the lift to the actual parsed
bytes was pinned only OPERATIONALLY at the concrete entries `start = 0` /
`start = 7`, because the deployed bytes contain the
`.pick`/`.roll`/`.nip`/`.placeholder`/`OP_0` instruction mix that every
`Parse.AreRunarEmittable*` round-trip allowlist EXCLUDES (no general
parse-correctness theorem covers it). This file discharges the *general*
statement WITHOUT a general parse theorem — `compileSafe loopOkProg` is a
FIXED closed `ByteArray`, so its parse is a closed computation:

1. **Fixed parse (`loopOk_parseScript_eq`).** `parseScript` of the
   deployed bytes equals an explicit op list `loopOkParsedOps`, read off
   by `native_decide` on the closed bytes (a legitimate fixed-input
   computation — no symbolic `start`). The parser re-decodes each
   `.pickStruct d` of `loopOkPeepChain` to `.pick d` (`[push d, OP_PICK]`),
   and the epilogue `.placeholder 0 "expectedSum"` (wire byte `0x00`) to
   `.push (.bigint 0)`.

2. **Symbolic-start runtime equivalence (`scriptAccepts_parsedOps_eq_peepChain`).**
   `loopOkParsedOps` and `loopOkPeepChain` differ ONLY by
   `.pickStruct d`↔`.pick d` (definitionally identical `applyPick`/
   `applyPickStruct` on the success branch; both reject on the same
   out-of-bounds condition — `scriptAccepts` collapses the two differing
   error strings to `false`) and `.placeholder 0 n`↔`.push (.bigint 0)`
   (identical `stepNonIf`). So they run scriptAccepts-equivalently from
   ANY state. Proven by three suffix-swaps via `scriptAccepts_runOps_prefix_cong`.

3. **General parsed-bytes `scriptAccepts` (`scriptAccepts_loopOk_parsedBytes`).**
   Compose (1)+(2) with the bridge's `scriptAccepts_loopOkPeepChain_iff`:
   the actual parsed bytes are ACCEPTED from `start :: rest` iff
   `3 * start = 0`, GENERAL over `start`.

4. **General ANF half (`anf_isSome_iff`).** The accumulator's ANF
   evaluation succeeds iff `3 * start = 0`, proven by a symbolic-`start`
   walk of `evalBindingsP`/`runLoopP`/`evalBinOp "==="` (the loop count is
   the fixed `3`, so the only symbolic dependency is `start`'s value;
   `sum = start + start + start` and the terminal `assert (sum === 0)`
   succeeds iff that is `0`). NOT a `native_decide` pin — fully symbolic.

5. **The genuine accumulator consume theorem (`loopOk_acceptAgrees_parsedBytes`).**
   `acceptAgrees` of the ANF evaluation against the run of the ACTUAL
   PARSED BYTES, GENERAL over `start`, with NO keyed premise. Subsumes the
   concrete pin `Pipeline.loopOk_acceptAgrees` (its `start = 0` instance)
   and the bridge's operational `start = 0` / `start = 7` pins.

This is add-only and touches NOTHING in the omnibus / dispatch cascade /
`tests/OmnibusInstantiation.lean`. It is the loop consume theorem the
eventual `hNoLoop` lift routes the omnibus to. -/

namespace RunarVerification.Stack.LoopBridge

open RunarVerification.Stack (StackOp)
open RunarVerification.Stack.Eval (StackState runOps scriptAccepts runOps_cons_nonIf_eq acceptAgrees)
open RunarVerification.ANF

/-! ## (a) Per-op scriptAccepts-equivalences and prefix congruence -/

/-- `.pickStruct d` and `.pick d` are scriptAccepts-equivalent as a cons
head: they push the same value when in-bounds (identical `.ok` state,
`applyPick`/`applyPickStruct` are definitionally equal there), and both
error (scriptAccepts = false) when out-of-bounds — the two differing error
strings are invisible to `scriptAccepts`. -/
theorem scriptAccepts_pickStruct_pick_cons (d : Nat) (rest : List StackOp) (s : StackState) :
    scriptAccepts (runOps (.pickStruct d :: rest) s)
      = scriptAccepts (runOps (.pick d :: rest) s) := by
  rw [runOps_cons_nonIf_eq (.pickStruct d) rest s (by intro _ _ h; cases h)]
  rw [runOps_cons_nonIf_eq (.pick d) rest s (by intro _ _ h; cases h)]
  show scriptAccepts (match Stack.Eval.applyPickStruct s d with
        | .error e => .error e | .ok s' => runOps rest s')
      = scriptAccepts (match Stack.Eval.applyPick s d with
        | .error e => .error e | .ok s' => runOps rest s')
  unfold Stack.Eval.applyPickStruct Stack.Eval.applyPick
  by_cases h : d ≥ s.stack.length
  · simp [h]
  · simp [h]

/-- `.placeholder 0 n` and `.push (.bigint 0)` step identically (`rfl`):
both push `vBigint 0`. -/
theorem scriptAccepts_placeholder_push_cons (n : String) (rest : List StackOp) (s : StackState) :
    scriptAccepts (runOps (.placeholder 0 n :: rest) s)
      = scriptAccepts (runOps (.push (.bigint 0) :: rest) s) := by
  rw [runOps_cons_nonIf_eq (.placeholder 0 n) rest s (by intro _ _ h; cases h)]
  rw [runOps_cons_nonIf_eq (.push (.bigint 0)) rest s (by intro _ _ h; cases h)]
  rfl

/-- Prefix congruence under `scriptAccepts`: replacing the suffix of an op
list by a scriptAccepts-equivalent suffix preserves acceptance. -/
theorem scriptAccepts_runOps_prefix_cong (pre tail1 tail2 : List StackOp)
    (hcong : ∀ s', scriptAccepts (runOps tail1 s') = scriptAccepts (runOps tail2 s'))
    (s : StackState) :
    scriptAccepts (runOps (pre ++ tail1) s) = scriptAccepts (runOps (pre ++ tail2) s) := by
  rw [Stack.Sim.runOps_append, Stack.Sim.runOps_append]
  cases h : runOps pre s with
  | error e => simp
  | ok s' => simp [hcong s']

/-! ## (b) The explicit parsed op list + the fixed parse pin -/

/-- The explicit op list that `Parse.parseScript` produces from the deployed
bytes of `compileSafe loopOkProg`. Each `.pickStruct d` of `loopOkPeepChain`
re-decodes to `.pick d`, and the epilogue `.placeholder 0 "expectedSum"`
(wire byte `0x00`) re-decodes to `.push (.bigint 0)`. -/
def loopOkParsedOps : List StackOp :=
  [ StackOp.push (.bigint 0), StackOp.push (.bigint 0)
  , StackOp.pick 2, StackOp.rot, StackOp.swap, StackOp.opcode "OP_ADD"
  , StackOp.push (.bigint 1)
  , StackOp.pick 3, StackOp.rot, StackOp.swap, StackOp.opcode "OP_ADD"
  , StackOp.push (.bigint 2)
  , StackOp.roll 4, StackOp.rot, StackOp.swap, StackOp.opcode "OP_ADD"
  , StackOp.push (.bigint 0), StackOp.opcode "OP_NUMEQUAL"
  , StackOp.nip, StackOp.nip, StackOp.nip ]

/-- Fixed-bytes parse pin (closed computation, `native_decide` legitimate —
no symbolic input). The parsed op list (defaulting to `[]` on any
compile/parse error) equals `loopOkParsedOps`. -/
theorem loopOk_parse_pin :
    (match Pipeline.compileSafe loopOkProg with
     | .ok b =>
        match RunarVerification.Script.Parse.parseScript b with
        | .ok ops => ops
        | .error _ => []
     | .error _ => []) = loopOkParsedOps := by
  native_decide

/-- On the deployed bytes, the parse SUCCEEDS with exactly `loopOkParsedOps`. -/
theorem loopOk_parseScript_eq (bytes : ByteArray)
    (hSafe : Pipeline.compileSafe loopOkProg = .ok bytes) :
    RunarVerification.Script.Parse.parseScript bytes = .ok loopOkParsedOps := by
  have h := loopOk_parse_pin
  rw [hSafe] at h
  simp only at h
  cases hp : RunarVerification.Script.Parse.parseScript bytes with
  | error e => rw [hp] at h; simp only at h; exact absurd h.symm (by decide)
  | ok ops => rw [hp] at h; simp only at h; rw [h]

/-! ## (c) parsedOps ≡ peepChain under scriptAccepts (symbolic start) -/

/-- The explicit unfolded form of `loopOkPeepChain` (the bridge's peephole
RHS, literal). -/
theorem loopOkPeepChain_explicit :
    loopOkPeepChain =
      [ StackOp.push (.bigint 0), StackOp.push (.bigint 0)
      , StackOp.pickStruct 2, StackOp.rot, StackOp.swap, StackOp.opcode "OP_ADD"
      , StackOp.push (.bigint 1)
      , StackOp.pickStruct 3, StackOp.rot, StackOp.swap, StackOp.opcode "OP_ADD"
      , StackOp.push (.bigint 2)
      , StackOp.roll 4, StackOp.rot, StackOp.swap, StackOp.opcode "OP_ADD"
      , StackOp.placeholder 0 "expectedSum", StackOp.opcode "OP_NUMEQUAL"
      , StackOp.nip, StackOp.nip, StackOp.nip ] := by
  native_decide

/-- The two intermediate op lists between `loopOkPeepChain` (explicit) and
`loopOkParsedOps`, each differing from its neighbour by ONE op-swap. -/
private def chain0 : List StackOp :=  -- = loopOkPeepChain (explicit)
  [ StackOp.push (.bigint 0), StackOp.push (.bigint 0)
  , StackOp.pickStruct 2, StackOp.rot, StackOp.swap, StackOp.opcode "OP_ADD"
  , StackOp.push (.bigint 1)
  , StackOp.pickStruct 3, StackOp.rot, StackOp.swap, StackOp.opcode "OP_ADD"
  , StackOp.push (.bigint 2)
  , StackOp.roll 4, StackOp.rot, StackOp.swap, StackOp.opcode "OP_ADD"
  , StackOp.placeholder 0 "expectedSum", StackOp.opcode "OP_NUMEQUAL"
  , StackOp.nip, StackOp.nip, StackOp.nip ]

private def chain1 : List StackOp :=  -- placeholder → push 0
  [ StackOp.push (.bigint 0), StackOp.push (.bigint 0)
  , StackOp.pickStruct 2, StackOp.rot, StackOp.swap, StackOp.opcode "OP_ADD"
  , StackOp.push (.bigint 1)
  , StackOp.pickStruct 3, StackOp.rot, StackOp.swap, StackOp.opcode "OP_ADD"
  , StackOp.push (.bigint 2)
  , StackOp.roll 4, StackOp.rot, StackOp.swap, StackOp.opcode "OP_ADD"
  , StackOp.push (.bigint 0), StackOp.opcode "OP_NUMEQUAL"
  , StackOp.nip, StackOp.nip, StackOp.nip ]

private def chain2 : List StackOp :=  -- pickStruct 3 → pick 3
  [ StackOp.push (.bigint 0), StackOp.push (.bigint 0)
  , StackOp.pickStruct 2, StackOp.rot, StackOp.swap, StackOp.opcode "OP_ADD"
  , StackOp.push (.bigint 1)
  , StackOp.pick 3, StackOp.rot, StackOp.swap, StackOp.opcode "OP_ADD"
  , StackOp.push (.bigint 2)
  , StackOp.roll 4, StackOp.rot, StackOp.swap, StackOp.opcode "OP_ADD"
  , StackOp.push (.bigint 0), StackOp.opcode "OP_NUMEQUAL"
  , StackOp.nip, StackOp.nip, StackOp.nip ]
-- the final list (pickStruct 2 → pick 2) is `loopOkParsedOps`.

/-- **Step 2 crux (symbolic start).** The parsed op list and the
peepholed-method op list run scriptAccepts-equivalently from ANY state. -/
theorem scriptAccepts_parsedOps_eq_peepChain (s : StackState) :
    scriptAccepts (runOps loopOkParsedOps s)
      = scriptAccepts (runOps loopOkPeepChain s) := by
  rw [loopOkPeepChain_explicit]
  show scriptAccepts (runOps loopOkParsedOps s) = scriptAccepts (runOps chain0 s)
  have h01 : ∀ s', scriptAccepts (runOps chain0 s') = scriptAccepts (runOps chain1 s') := by
    intro s'
    exact scriptAccepts_runOps_prefix_cong
      [ StackOp.push (.bigint 0), StackOp.push (.bigint 0)
      , StackOp.pickStruct 2, StackOp.rot, StackOp.swap, StackOp.opcode "OP_ADD"
      , StackOp.push (.bigint 1)
      , StackOp.pickStruct 3, StackOp.rot, StackOp.swap, StackOp.opcode "OP_ADD"
      , StackOp.push (.bigint 2)
      , StackOp.roll 4, StackOp.rot, StackOp.swap, StackOp.opcode "OP_ADD" ]
      (StackOp.placeholder 0 "expectedSum" :: [ StackOp.opcode "OP_NUMEQUAL", StackOp.nip, StackOp.nip, StackOp.nip ])
      (StackOp.push (.bigint 0) :: [ StackOp.opcode "OP_NUMEQUAL", StackOp.nip, StackOp.nip, StackOp.nip ])
      (fun s'' => scriptAccepts_placeholder_push_cons "expectedSum" _ s'') s'
  have h12 : ∀ s', scriptAccepts (runOps chain1 s') = scriptAccepts (runOps chain2 s') := by
    intro s'
    exact scriptAccepts_runOps_prefix_cong
      [ StackOp.push (.bigint 0), StackOp.push (.bigint 0)
      , StackOp.pickStruct 2, StackOp.rot, StackOp.swap, StackOp.opcode "OP_ADD"
      , StackOp.push (.bigint 1) ]
      (StackOp.pickStruct 3 :: [ StackOp.rot, StackOp.swap, StackOp.opcode "OP_ADD"
        , StackOp.push (.bigint 2), StackOp.roll 4, StackOp.rot, StackOp.swap, StackOp.opcode "OP_ADD"
        , StackOp.push (.bigint 0), StackOp.opcode "OP_NUMEQUAL", StackOp.nip, StackOp.nip, StackOp.nip ])
      (StackOp.pick 3 :: [ StackOp.rot, StackOp.swap, StackOp.opcode "OP_ADD"
        , StackOp.push (.bigint 2), StackOp.roll 4, StackOp.rot, StackOp.swap, StackOp.opcode "OP_ADD"
        , StackOp.push (.bigint 0), StackOp.opcode "OP_NUMEQUAL", StackOp.nip, StackOp.nip, StackOp.nip ])
      (fun s'' => scriptAccepts_pickStruct_pick_cons 3 _ s'') s'
  have h23 : ∀ s', scriptAccepts (runOps chain2 s') = scriptAccepts (runOps loopOkParsedOps s') := by
    intro s'
    exact scriptAccepts_runOps_prefix_cong
      [ StackOp.push (.bigint 0), StackOp.push (.bigint 0) ]
      (StackOp.pickStruct 2 :: [ StackOp.rot, StackOp.swap, StackOp.opcode "OP_ADD"
        , StackOp.push (.bigint 1), StackOp.pick 3, StackOp.rot, StackOp.swap, StackOp.opcode "OP_ADD"
        , StackOp.push (.bigint 2), StackOp.roll 4, StackOp.rot, StackOp.swap, StackOp.opcode "OP_ADD"
        , StackOp.push (.bigint 0), StackOp.opcode "OP_NUMEQUAL", StackOp.nip, StackOp.nip, StackOp.nip ])
      (StackOp.pick 2 :: [ StackOp.rot, StackOp.swap, StackOp.opcode "OP_ADD"
        , StackOp.push (.bigint 1), StackOp.pick 3, StackOp.rot, StackOp.swap, StackOp.opcode "OP_ADD"
        , StackOp.push (.bigint 2), StackOp.roll 4, StackOp.rot, StackOp.swap, StackOp.opcode "OP_ADD"
        , StackOp.push (.bigint 0), StackOp.opcode "OP_NUMEQUAL", StackOp.nip, StackOp.nip, StackOp.nip ])
      (fun s'' => scriptAccepts_pickStruct_pick_cons 2 _ s'') s'
  exact ((h01 s).trans ((h12 s).trans (h23 s))).symm

/-! ## (d) General parsed-bytes `scriptAccepts` -/

/-- **Tier 4c headline (parsed-bytes `scriptAccepts`), GENERAL over `start`.**
Running the ACTUAL PARSED BYTES of `compileSafe loopOkProg` from the deployed
entry `start :: rest` is ACCEPTED iff `3 * start = 0`. -/
theorem scriptAccepts_loopOk_parsedBytes (bytes : ByteArray)
    (hSafe : Pipeline.compileSafe loopOkProg = .ok bytes)
    (start : Int) (rest : List RunarVerification.ANF.Eval.Value) (s : StackState) :
    scriptAccepts (Pipeline.Soundness.runParsedBytes bytes
        { s with stack := (.vBigint start) :: rest }) = true
      ↔ (0 : Int) + ((3 : Nat) : Int) * start = 0 := by
  unfold Pipeline.Soundness.runParsedBytes
  rw [loopOk_parseScript_eq bytes hSafe]
  show scriptAccepts (runOps loopOkParsedOps { s with stack := (.vBigint start) :: rest }) = true ↔ _
  rw [scriptAccepts_parsedOps_eq_peepChain { s with stack := (.vBigint start) :: rest }]
  exact scriptAccepts_loopOkPeepChain_iff start rest s

/-! ## (e) General ANF half (symbolic start, no `native_decide`) -/

/-- The accumulator's ANF evaluation success bit equals the decision of the
accumulated sum being zero. The loop count is the fixed `3`, so the only
symbolic dependency is `start`'s value; `sum = start + start + start` and
the terminal `assert (sum === expectedSum)` succeeds iff that is `0`. -/
theorem anf_isSome_eq (start : Int) :
    (RunarVerification.ANF.Eval.evalBindingsP loopOkProg.methods
      { params := [("start", .vBigint start)]
      , props := [("expectedSum", .vBigint 0)] } loopOkM.body).toOption.isSome
      = decide ((start : Int) + start + start = 0) := by
  unfold loopOkM
  simp only [RunarVerification.ANF.Eval.evalBindingsP, RunarVerification.ANF.Eval.evalValueP,
    RunarVerification.ANF.Eval.runLoopP, RunarVerification.Stack.Agrees.A7.loopOkBody,
    RunarVerification.ANF.Eval.lookupRef, RunarVerification.ANF.Eval.State.resolveRef,
    RunarVerification.ANF.Eval.State.lookupBinding, RunarVerification.ANF.Eval.State.lookupParam,
    RunarVerification.ANF.Eval.State.lookupProp, RunarVerification.ANF.Eval.State.addBinding,
    RunarVerification.ANF.Eval.evalBinOp,
    bind, Except.bind, pure, Except.pure]
  simp only [List.find?, beq_self_eq_true, Option.map]
  by_cases h : (start : Int) + start + start = 0 <;> simp [h, Except.toOption]

/-- The general ANF completion biconditional: the accumulator succeeds iff
`3 * start = 0`. -/
theorem anf_isSome_iff (start : Int) :
    (RunarVerification.ANF.Eval.evalBindingsP loopOkProg.methods
      { params := [("start", .vBigint start)]
      , props := [("expectedSum", .vBigint 0)] } loopOkM.body).toOption.isSome
      ↔ (0 : Int) + ((3 : Nat) : Int) * start = 0 := by
  rw [show ((RunarVerification.ANF.Eval.evalBindingsP loopOkProg.methods
      { params := [("start", .vBigint start)]
      , props := [("expectedSum", .vBigint 0)] } loopOkM.body).toOption.isSome = true)
      = ((start : Int) + start + start = 0) from by rw [anf_isSome_eq]; simp]
  omega

/-! ## (f) The genuine accumulator consume theorem over PARSED BYTES -/

/-- **Tier 4c — the genuine accumulator consume theorem over the ACTUAL
PARSED BYTES, GENERAL over `start`, with NO keyed premise.** The ANF
evaluation of the canonical accumulator body AGREES (under the consensus
acceptance bit) with the run of the bytes of `compileSafe loopOkProg` from
the deployed entry `start :: rest`: the ANF completes exactly when the
parsed bytes are accepted, both iff `3 * start = 0`. -/
theorem loopOk_acceptAgrees_parsedBytes (bytes : ByteArray)
    (hSafe : Pipeline.compileSafe loopOkProg = .ok bytes)
    (start : Int) (rest : List RunarVerification.ANF.Eval.Value) (s : StackState) :
    acceptAgrees
      (RunarVerification.ANF.Eval.evalBindingsP loopOkProg.methods
        { params := [("start", .vBigint start)]
        , props := [("expectedSum", .vBigint 0)] } loopOkM.body)
      (Pipeline.Soundness.runParsedBytes bytes { s with stack := (.vBigint start) :: rest }) := by
  unfold acceptAgrees
  rw [scriptAccepts_loopOk_parsedBytes bytes hSafe start rest s]
  exact anf_isSome_iff start

/-! ## (g) Subsuming the concrete `Pipeline.loopOk_acceptAgrees` pin

The pin `Pipeline.loopOk_acceptAgrees` is the `start = 0` instance over the
parsed-bytes surface with the deployed entry `[.vBigint 0]` (i.e. `rest = []`,
`s = {}`). The general theorem above subsumes it directly. -/

/-- The exact shape of `Pipeline.loopOk_acceptAgrees` (the `start = 0`
parsed-bytes agreement), RE-DERIVED as a corollary of the general
parsed-bytes consume theorem — confirming the general theorem genuinely
SUBSUMES the pin. -/
theorem loopOk_acceptAgrees_parsedBytes_start0 (bytes : ByteArray)
    (hSafe : Pipeline.compileSafe loopOkProg = .ok bytes) :
    acceptAgrees
      (RunarVerification.ANF.Eval.evalBindingsP loopOkProg.methods
        { params := [("start", .vBigint 0)]
        , props := [("expectedSum", .vBigint 0)] } loopOkM.body)
      (Pipeline.Soundness.runParsedBytes bytes { stack := [.vBigint 0] }) :=
  loopOk_acceptAgrees_parsedBytes bytes hSafe 0 [] { stack := [.vBigint 0] }

/-- The historical falsifier entry `start = 7` (subsumes the bridge's
operational `loopOk_start7_bytes_rejected` polarity): the ANF FAILS and the
parsed bytes are REJECTED, agreeing under the acceptance bit. -/
theorem loopOk_acceptAgrees_parsedBytes_start7 (bytes : ByteArray)
    (hSafe : Pipeline.compileSafe loopOkProg = .ok bytes) :
    acceptAgrees
      (RunarVerification.ANF.Eval.evalBindingsP loopOkProg.methods
        { params := [("start", .vBigint 7)]
        , props := [("expectedSum", .vBigint 0)] } loopOkM.body)
      (Pipeline.Soundness.runParsedBytes bytes { stack := [.vBigint 7] }) :=
  loopOk_acceptAgrees_parsedBytes bytes hSafe 7 [] { stack := [.vBigint 7] }

end RunarVerification.Stack.LoopBridge
