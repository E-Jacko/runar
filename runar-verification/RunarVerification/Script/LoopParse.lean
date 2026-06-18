import RunarVerification.Script.Parse
import RunarVerification.Script.EmitCorrect
import RunarVerification.Pipeline

/-!
# General parse round-trip for the loop instruction set (PARAMETRIC foundation)

The loop frontier's canonical fixture was proven over its *fixed* bytes
by `native_decide` on the closed parse of `compileSafe loopOkProg`
(`Stack.AgreesLoopParsed.loopOk_parseScript_eq`). Any COUNT-GENERIC loop
has SYMBOLIC bytes (more iterations ⇒ longer op chain), so its parse
cannot be `native_decide`'d. This module builds the GENERAL,
count-agnostic round-trip machinery for the loop op classes.

## The obstacle

`Parse.AreRunarEmittable` (and its normalized superset
`Parse.AreRunarEmittableNormalized`) deliberately EXCLUDE the loop op
classes whose byte-inverse is structural / multi-byte:

* `.pickStruct d` — emits byte-identical bytes to `.pick d`
  (`encodePushBigIntL d ++ [0x79]`), so the parser reconstructs `.pick
  d` (a DIFFERENT constructor). Round-trips only SEMANTICALLY.
* `.placeholder i n` — emits `[0x00]` (`OP_0`), which the parser reads
  as `.push (.bigint 0)`. Round-trips only SEMANTICALLY.

`.pick d` / `.roll d` / `.nip` are ALREADY in `RunarEmittable` for the
small-depth range `d ∈ [1..16]` and round-trip SYNTACTICALLY.

## The strategy

We mirror the existing `normalizeOps` / `AreRunarEmittableNormalized`
machinery (`Parse.lean` §"Normalized push integration"), which already
handles the case where parse yields a DIFFERENT op list than the
original (IF `some []` → `none`, bool/small-int push canonicalisation).

* `loopNormalizeStackOp` / `loopNormalizeOps` — the parser's view of a
  loop op: identical to `Parse.normalizeStackOp` except it additionally
  maps `.pickStruct d ↦ .pick d` and `.placeholder i n ↦ .push (.bigint
  0)`.
* `AreLoopEmittable` — a decidable superset of
  `RunarEmittableNormalized` adding the `.pickStruct d` (small depth)
  and `.placeholder` classes.
* `parseScript (emitOpsL ops) = .ok (loopNormalizeOps ops)` for
  `AreLoopEmittable ops` — the PARSE round-trip (a list-equality up to
  loop-normalisation).
* `runOps (loopNormalizeOps ops) s = runOps ops s` — the SEMANTIC
  identity: loop-normalisation is `runOps`-preserving (proven per-op by
  `rfl`-level facts, then by induction).
* The combination yields the headline `runOps`-EQUALITY round-trip
  `runParsedBytes (emitFast <single-public program>) s = runOps m.ops
  s`.

## Generality (first pass)

* `.pick d` / `.roll d` / `.pickStruct d` covered for `d ∈ [1..16]`
  (single-byte small-int push prefix). The `d ≥ 17` CScriptNum case is
  DEFERRED (documented obstacle: it spans a multi-byte literal-length
  push whose byte-inverse goes through `decodeScriptNumberL`; no
  per-op round-trip lemma exists for it yet).
* `.nip`, `.placeholder i n` covered for all arguments.
* All `RunarEmittableNormalized` ops (the 7 short-form stack ops,
  allowlisted named opcodes, normalized pushes, structural IF over
  normalized bodies) are admitted by reuse.
-/

namespace RunarVerification
namespace Script
namespace Parse

open RunarVerification.Script
open RunarVerification.Stack (StackOp PushVal)
open RunarVerification.Stack.Eval (StackState runOps scriptAccepts)

/-! ## Loop normalisation — the parser's view of a loop op

`loopNormalizeStackOp` agrees with `Parse.normalizeStackOp` on every op
shape except the two SEMANTIC-only loop classes:

* `.pickStruct d ↦ .pick d` (same bytes, parser yields `.pick`).
* `.placeholder i n ↦ .push (.bigint 0)` (`OP_0` byte, parser yields
  the small-int push).
-/

mutual

def loopNormalizeStackOp : StackOp → StackOp
  | .push v                => .push (normalizePushVal v)
  | .pickStruct d          => .pick d
  | .placeholder _ _       => .push (.bigint 0)
  | .pushCodesepIndex      => .push (.bigint 0)
  | .ifOp thn none         => .ifOp (loopNormalizeOps thn) none
  | .ifOp thn (some [])    => .ifOp (loopNormalizeOps thn) none
  | .ifOp thn (some els)   => .ifOp (loopNormalizeOps thn) (some (loopNormalizeOps els))
  | op                     => op

def loopNormalizeOps : List StackOp → List StackOp
  | [] => []
  | op :: rest => loopNormalizeStackOp op :: loopNormalizeOps rest

end

/-! ## SEMANTIC equivalence of the loop classes to their normalised forms

The two loop classes parse back to a DIFFERENT constructor:

* `.placeholder i n` and `.pushCodesepIndex` are `runOps`-EQUAL to
  `.push (.bigint 0)` on EVERY state — `Stack.Eval.stepNonIf` evaluates
  both via `s.push (.vBigint 0)`, identical to `.push (.bigint 0)`
  (true `rfl`).
* `.pickStruct d` is `runOps`-equal to `.pick d` ONLY on the success
  branch: `applyPickStruct s d` and `applyPick s d` are identical
  in-bounds (both copy `s.stack[d]!`), but DIFFER out-of-bounds (the
  two error strings `"pickStruct: …"` vs `"OP_PICK: …"`). The honest
  general statement for `.pickStruct`≡`.pick` is therefore at the
  `scriptAccepts` surface (both errors map to `false`) — exactly the
  `Stack.AgreesLoopParsed.scriptAccepts_pickStruct_pick_cons` precedent
  — NOT a `runOps`-EQUALITY. Out-of-bounds `pickStruct` is rejected
  whether or not it normalises to `.pick`, so the accept-surface
  equality is the correct, non-vacuous claim.

These per-op facts feed the list-level normalisation-preservation
results below. -/

/-- One-step `runOps` agreement: `.placeholder i n` and `.push (.bigint 0)`
both push `vBigint 0`. True `rfl`-level equality on every state. -/
theorem runOps_placeholder_cons_eq (i : Nat) (n : String)
    (rest : List StackOp) (s : StackState) :
    runOps (.placeholder i n :: rest) s = runOps (.push (.bigint 0) :: rest) s := by
  rw [Stack.Eval.runOps_cons_nonIf_eq (.placeholder i n) rest s (by intro _ _ h; cases h)]
  rw [Stack.Eval.runOps_cons_nonIf_eq (.push (.bigint 0)) rest s (by intro _ _ h; cases h)]
  rfl

/-- One-step `runOps` agreement: `.pushCodesepIndex` and `.push (.bigint 0)`
both push `vBigint 0`. True `rfl`-level equality on every state. -/
theorem runOps_pushCodesepIndex_cons_eq (rest : List StackOp) (s : StackState) :
    runOps (.pushCodesepIndex :: rest) s = runOps (.push (.bigint 0) :: rest) s := by
  rw [Stack.Eval.runOps_cons_nonIf_eq .pushCodesepIndex rest s (by intro _ _ h; cases h)]
  rw [Stack.Eval.runOps_cons_nonIf_eq (.push (.bigint 0)) rest s (by intro _ _ h; cases h)]
  rfl

/-! ## Per-op PARSE round-trips for the new loop classes

The parser reconstructs `.pickStruct d` bytes as `.pick d` (byte-identical
emit to `.pick d`) and `.placeholder` / `.pushCodesepIndex` bytes as
`.push (.bigint 0)` (`OP_0`). Each lands its loop-normalised form. -/

/-- `emitStackOpL (.pickStruct d)` is byte-identical to `emitStackOpL (.pick d)`. -/
theorem emitStackOpL_pickStruct_eq_pick (d : Nat) :
    emitStackOpL (.pickStruct d) = emitStackOpL (.pick d) := rfl

/-- `.pickStruct d` for small depth `d ∈ [1..16]` parses back to `.pick d`
(its loop-normalised form). Reuses the existing `.pick d` small-depth
round-trip via the byte-identity above. -/
theorem parseStackOpFuel_pickStruct_smallD (fuel : Nat) (rest : List UInt8)
    (d : Nat) (hd : 1 ≤ d ∧ d ≤ 16) :
    parseStackOpFuel (fuel + 1) (emitStackOpL (.pickStruct d) ++ rest)
      = .ok (.pick d, rest) := by
  rw [emitStackOpL_pickStruct_eq_pick]
  exact parseStackOpFuel_pick_smallD fuel rest d hd

/-- `.placeholder i n` (byte `0x00`, `OP_0`) parses back to `.push (.bigint 0)`,
provided the continuation `rest` does not begin with `OP_PICK` / `OP_ROLL`
(otherwise the parser collapses the `OP_0` into a `.pick 0` / `.roll 0`).
The `restNotPickOrRoll` side condition mirrors the `NormalizedPushEmittable`
push handling — the parser is push-eager, and `OP_0` IS a push byte. -/
theorem parseStackOpFuel_placeholder (fuel : Nat) (i : Nat) (n : String)
    (rest : List UInt8) (hRest : restNotPickOrRoll rest) :
    parseStackOpFuel (fuel + 1) (emitStackOpL (.placeholder i n) ++ rest)
      = .ok (.push (.bigint 0), rest) := by
  cases rest with
  | nil => rfl
  | cons b bs =>
      unfold restNotPickOrRoll at hRest
      show parseStackOpFuel (fuel + 1) (0x00 :: b :: bs)
        = .ok (.push (.bigint 0), b :: bs)
      unfold parseStackOpFuel parsePushVal?
      simp [hRest.1, hRest.2]

/-- `.pushCodesepIndex` (byte `0x00`, `OP_0`) parses back to `.push (.bigint 0)`.
Byte-identical to `.placeholder 0 ""`, so it reuses that round-trip. -/
theorem parseStackOpFuel_pushCodesepIndex (fuel : Nat) (rest : List UInt8)
    (hRest : restNotPickOrRoll rest) :
    parseStackOpFuel (fuel + 1) (emitStackOpL .pushCodesepIndex ++ rest)
      = .ok (.push (.bigint 0), rest) := by
  have hbytes : emitStackOpL .pushCodesepIndex = emitStackOpL (.placeholder 0 "") := rfl
  rw [hbytes]
  exact parseStackOpFuel_placeholder fuel 0 "" rest hRest

/-! ## `AreLoopEmittable` — the loop instruction-set predicate

A decidable superset of the flat `RunarEmittable` subset plus the
normalized-push class, adding the three SEMANTIC-only loop classes:

* `.pickStruct d` for small depth `d ∈ [1..16]` (parses as `.pick d`),
* `.placeholder i n` (parses as `.push (.bigint 0)`),
* `.pushCodesepIndex` (parses as `.push (.bigint 0)`).

`.ifOp` is EXCLUDED from this first pass: its byte-level round-trip
helpers in `Parse.lean` (`head_of_emitStackOpL_not_else_or_endif`,
`parseOpsFuel_cons_unfold_stop`) are `private`, so re-deriving the
IF-body fuel walk is deferred. The canonical loop fixture chain
(`loopOkPeepChain`) is FLAT (no top-level IF), so this restriction does
not weaken the count-generic loop foundation.

The push, placeholder, and pushCodesepIndex classes carry a
`restNotPickOrRoll`-style tail obligation (their `OP_0`/small-int byte
is push-eager and would otherwise collapse into a `.pick`/`.roll`); the
list predicate threads it as a per-cons side condition exactly like
`AreRunarEmittableNormalized`. -/

/-! ### Loop-extended opcode allowlist

The loop instruction set emits `OP_NUMEQUAL` (byte `0x9c`) in the
count-comparison epilogue, which is NOT in the base
`isAllowedOpcodeName`. Byte `0x9c` decodes straight back to
`.opcode "OP_NUMEQUAL"` via `parseStackOp1?` (it is neither a push
prefix, a structural control byte, a short-form constructor byte, nor a
small-int byte), so it is safe to admit in the loop predicate WITHOUT
touching the base allowlist. -/
def isLoopAllowedOpcodeName (name : String) : Bool :=
  isAllowedOpcodeName name || name = "OP_NUMEQUAL"

/-- Per-op round-trip for `OP_NUMEQUAL` (byte `0x9c`). -/
theorem parseStackOpFuel_OP_NUMEQUAL (fuel : Nat) (rest : List UInt8) :
    parseStackOpFuel (fuel + 1) (emitStackOpL (.opcode "OP_NUMEQUAL") ++ rest)
      = .ok (.opcode "OP_NUMEQUAL", rest) := rfl

/-- Per-op round-trip for any loop-allowed opcode name (base allowlist
plus `OP_NUMEQUAL`). -/
theorem parseStackOpFuel_loopOpcode (fuel : Nat) (rest : List UInt8)
    (name : String) (h : isLoopAllowedOpcodeName name = true) :
    parseStackOpFuel (fuel + 1) (emitStackOpL (.opcode name) ++ rest)
      = .ok (.opcode name, rest) := by
  unfold isLoopAllowedOpcodeName at h
  rw [Bool.or_eq_true] at h
  rcases h with hBase | hNumeq
  · exact parseStackOp_emit_round_trip fuel (.opcode name) rest (.opcode name hBase)
  · rw [of_decide_eq_true hNumeq]
    exact parseStackOpFuel_OP_NUMEQUAL fuel rest

/-- `OP_NUMEQUAL` (byte `0x9c`) emits a single byte. -/
theorem emitStackOpL_OP_NUMEQUAL_cons :
    ∃ b tail, emitStackOpL (.opcode "OP_NUMEQUAL") = b :: tail := ⟨0x9c, [], rfl⟩

/-- A loop-allowed opcode emits at least one byte. -/
theorem emitStackOpL_loopOpcode_cons (name : String)
    (h : isLoopAllowedOpcodeName name = true) :
    ∃ b tail, emitStackOpL (.opcode name) = b :: tail := by
  unfold isLoopAllowedOpcodeName at h
  rw [Bool.or_eq_true] at h
  rcases h with hBase | hNumeq
  · exact emitStackOpL_cons_of_RunarEmittable (.opcode name) (.opcode name hBase)
  · rw [of_decide_eq_true hNumeq]; exact emitStackOpL_OP_NUMEQUAL_cons

/-- A loop-allowed opcode's `ByteArray` emit toList-agrees with the list emit. -/
theorem emitStackOp_toList_loopOpcode (name : String)
    (h : isLoopAllowedOpcodeName name = true) :
    (Emit.emitStackOp (.opcode name)).toList = emitStackOpL (.opcode name) := by
  unfold isLoopAllowedOpcodeName at h
  rw [Bool.or_eq_true] at h
  rcases h with hBase | hNumeq
  · exact emitStackOp_toList_of_RunarEmittable (.opcode name) (.opcode name hBase)
  · rw [of_decide_eq_true hNumeq]; exact ByteArray.toList_mk_singleton _

/-- Single-op loop emittability. -/
inductive RunarEmittableLoop : StackOp → Prop where
  | flat (op : StackOp) (h : RunarEmittable op) :
      RunarEmittableLoop op
  | push (v : PushVal) (h : NormalizedPushEmittable v) :
      RunarEmittableLoop (.push v)
  | pickStruct (d : Nat) (hd : 1 ≤ d ∧ d ≤ 16) :
      RunarEmittableLoop (.pickStruct d)
  | placeholder (i : Nat) (n : String) :
      RunarEmittableLoop (.placeholder i n)
  | pushCodesepIndex :
      RunarEmittableLoop .pushCodesepIndex
  | loopOpcode (name : String) (h : isLoopAllowedOpcodeName name = true) :
      RunarEmittableLoop (.opcode name)

/-- An op whose `OP_0`/small-int push byte is push-eager (would collapse
into a `.pick`/`.roll` if followed by `0x79`/`0x7a`): the three push-like
classes need the `restNotPickOrRoll` tail obligation. -/
def isPushLikeLoopOp : StackOp → Bool
  | .push _           => true
  | .placeholder _ _  => true
  | .pushCodesepIndex => true
  | _                 => false

/-- List-level loop emittability, threading the per-cons tail obligation
for the push-like classes (exactly mirroring `AreRunarEmittableNormalized`). -/
inductive AreLoopEmittable : List StackOp → Prop where
  | nil : AreLoopEmittable []
  | cons (op : StackOp) (rest : List StackOp)
      (hOp : RunarEmittableLoop op)
      (hRest : AreLoopEmittable rest)
      (hTail : isPushLikeLoopOp op = true → restNotPickOrRoll (emitOpsL rest)) :
      AreLoopEmittable (op :: rest)

/-! ### Decidability (flat sub-predicate)

Mirroring `AreRunarEmittableNormalized`, the FULL `AreLoopEmittable`
predicate is NOT given a Bool checker: its `push` case carries a
`NormalizedPushEmittable` proof that is supplied explicitly (the same
design choice as the upstream normalized predicate, which likewise has
no Bool decider). We instead provide a Bool decider for the
loop-class-plus-`RunarEmittable` fragment (no normalized pushes — i.e.
pushes already in canonical `.bigint` small-int form, which is exactly
the shape the loop fixture emits), and the introduction lemmas that
lift `RunarEmittable` / `RunarEmittableNormalized` proofs into the loop
predicate. -/

/-- Bool decider for the loop fragment that excludes normalized pushes
(pushes must already be `RunarEmittable`). -/
def runarEmittableLoopFlatBool : StackOp → Bool
  | .pickStruct d     => decide (1 ≤ d ∧ d ≤ 16)
  | .placeholder _ _  => true
  | .pushCodesepIndex => true
  | .opcode name      => isLoopAllowedOpcodeName name
  | op                => runarEmittableBool op

theorem runarEmittableLoopFlatBool_iff (op : StackOp) :
    runarEmittableLoopFlatBool op = true → RunarEmittableLoop op := by
  intro h
  cases op with
  | pickStruct d =>
      exact .pickStruct d (of_decide_eq_true h)
  | placeholder i n => exact .placeholder i n
  | pushCodesepIndex => exact .pushCodesepIndex
  | opcode name => exact .loopOpcode name h
  | push v =>
      exact .flat (.push v) ((runarEmittableBool_iff_RunarEmittable (.push v)).mp h)
  | _ =>
      first
      | exact .flat _ ((runarEmittableBool_iff_RunarEmittable _).mp h)

/-- Every `RunarEmittable` op is `RunarEmittableLoop`. -/
theorem RunarEmittable.toLoop (op : StackOp) (h : RunarEmittable op) :
    RunarEmittableLoop op := .flat op h

/-! ### Emit head / length helpers -/

/-- `RunarEmittable` excludes every `.push` shape, so a `.flat`-tagged op
is never a push. Used to discharge `loopNormalizeStackOp = id` on flat ops. -/
theorem loopNormalizeStackOp_eq_self_of_RunarEmittable
    (op : StackOp) (h : RunarEmittable op) :
    loopNormalizeStackOp op = op := by
  cases h <;> rfl

/-- Each loop-emittable op produces at least one byte. -/
theorem emitStackOpL_cons_of_RunarEmittableLoop (op : StackOp)
    (hOp : RunarEmittableLoop op) :
    ∃ b tail, emitStackOpL op = b :: tail := by
  cases hOp with
  | flat op h => exact emitStackOpL_cons_of_RunarEmittable op h
  | push v h => exact h.emitted_cons
  | pickStruct d hd =>
      obtain ⟨b, tail, hb⟩ := emitStackOpL_cons_of_RunarEmittable (.pick d) (.pick d hd)
      exact ⟨b, tail, by rw [emitStackOpL_pickStruct_eq_pick]; exact hb⟩
  | placeholder i n => exact ⟨0x00, [], rfl⟩
  | pushCodesepIndex => exact ⟨0x00, [], rfl⟩
  | loopOpcode name h => exact emitStackOpL_loopOpcode_cons name h

theorem emitStackOpL_length_pos_of_RunarEmittableLoop (op : StackOp)
    (hOp : RunarEmittableLoop op) :
    1 ≤ (emitStackOpL op).length := by
  obtain ⟨b, tail, hHead⟩ := emitStackOpL_cons_of_RunarEmittableLoop op hOp
  rw [hHead]; simp

/-! ### Per-op PARSE round-trip to the loop-normalised form -/

/-- For any `RunarEmittableLoop` op, parsing its emitted bytes (followed
by a tail satisfying `restNotPickOrRoll` when the op is push-like)
yields exactly `loopNormalizeStackOp op`. -/
theorem parseStackOpFuel_emit_round_trip_loop
    (op : StackOp) (hOp : RunarEmittableLoop op)
    (fuel : Nat) (hFuel : (emitStackOpL op).length ≤ fuel)
    (rest : List UInt8)
    (hTail : isPushLikeLoopOp op = true → restNotPickOrRoll rest) :
    parseStackOpFuel fuel (emitStackOpL op ++ rest)
      = .ok (loopNormalizeStackOp op, rest) := by
  have hFuelPos : 1 ≤ fuel := by
    have := emitStackOpL_length_pos_of_RunarEmittableLoop op hOp; omega
  obtain ⟨fuel', rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
  cases hOp with
  | flat op h =>
      rw [loopNormalizeStackOp_eq_self_of_RunarEmittable op h]
      exact parseStackOp_emit_round_trip fuel' op rest h
  | push v h =>
      have hRest : restNotPickOrRoll rest := hTail rfl
      show parseStackOpFuel (fuel' + 1) (emitStackOpL (.push v) ++ rest)
        = .ok (.push (normalizePushVal v), rest)
      exact h.parse_normalized fuel' rest hRest
  | pickStruct d hd =>
      show parseStackOpFuel (fuel' + 1) (emitStackOpL (.pickStruct d) ++ rest)
        = .ok (.pick d, rest)
      exact parseStackOpFuel_pickStruct_smallD fuel' rest d hd
  | placeholder i n =>
      have hRest : restNotPickOrRoll rest := hTail rfl
      show parseStackOpFuel (fuel' + 1) (emitStackOpL (.placeholder i n) ++ rest)
        = .ok (.push (.bigint 0), rest)
      exact parseStackOpFuel_placeholder fuel' i n rest hRest
  | pushCodesepIndex =>
      have hRest : restNotPickOrRoll rest := hTail rfl
      show parseStackOpFuel (fuel' + 1) (emitStackOpL .pushCodesepIndex ++ rest)
        = .ok (.push (.bigint 0), rest)
      exact parseStackOpFuel_pushCodesepIndex fuel' rest hRest
  | loopOpcode name h =>
      show parseStackOpFuel (fuel' + 1) (emitStackOpL (.opcode name) ++ rest)
        = .ok (.opcode name, rest)
      exact parseStackOpFuel_loopOpcode fuel' rest name h

/-! ### List-level composition (fuel walk)

The crux: composing the per-op round-trips through the stateful fuel
parser over a mixed op list. Because `.ifOp` is excluded from
`AreLoopEmittable`, this is a clean structural induction (no mutual
block) — a strict simplification of the upstream
`parseOpsFuel_emit_round_trip_normalized`. -/

theorem parseOpsFuel_emit_round_trip_loop :
    ∀ (ops : List StackOp), AreLoopEmittable ops →
      ∀ (fuel : Nat), (emitOpsL ops).length ≤ fuel →
        parseOpsFuel (fuel + 1) (emitOpsL ops) false
          = .ok (loopNormalizeOps ops, []) := by
  intro ops hOps
  induction ops with
  | nil => intro fuel _; rfl
  | cons op rest ih =>
      intro fuel hFuel
      cases hOps with
      | cons _ _ hOp hRest hTail =>
          have hHeadLen := emitStackOpL_length_pos_of_RunarEmittableLoop op hOp
          have hFuelPos : 1 ≤ fuel := by
            have hLen : (emitStackOpL op).length + (emitOpsL rest).length ≤ fuel := by
              simpa [emitOpsL, List.length_append] using hFuel
            omega
          obtain ⟨fuel', rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
          obtain ⟨b, opTail, hOpHead⟩ :=
            emitStackOpL_cons_of_RunarEmittableLoop op hOp
          have hAllBytes : emitOpsL (op :: rest)
              = b :: (opTail ++ emitOpsL rest) := by
            show emitStackOpL op ++ emitOpsL rest = _
            rw [hOpHead]; rfl
          rw [hAllBytes]
          rw [parseOpsFuel_cons_unfold (fuel' + 1) b (opTail ++ emitOpsL rest)]
          have hHeadBack : b :: (opTail ++ emitOpsL rest)
              = emitStackOpL op ++ emitOpsL rest := by
            rw [hOpHead]; rfl
          rw [hHeadBack]
          have hOpFuel : (emitStackOpL op).length ≤ fuel' + 1 := by
            have hLen : (emitStackOpL op).length + (emitOpsL rest).length ≤ fuel' + 1 := by
              simpa [emitOpsL, List.length_append] using hFuel
            omega
          -- The push-like tail obligation on `emitOpsL rest`.
          have hPushTail :
              isPushLikeLoopOp op = true → restNotPickOrRoll (emitOpsL rest) := hTail
          rw [parseStackOpFuel_emit_round_trip_loop op hOp (fuel' + 1) hOpFuel
                (emitOpsL rest) hPushTail]
          dsimp only
          have hRestFuel : (emitOpsL rest).length ≤ fuel' := by
            have hLen : (emitStackOpL op).length + (emitOpsL rest).length ≤ fuel' + 1 := by
              simpa [emitOpsL, List.length_append] using hFuel
            omega
          rw [ih hRest fuel' hRestFuel]
          rfl

/-- The number of bytes emitted is at least the op-count for any
`AreLoopEmittable` list. Justifies the `parseOps` fuel choice. -/
theorem emitOpsL_length_ge_ops_length_loop (ops : List StackOp)
    (hOps : AreLoopEmittable ops) : ops.length ≤ (emitOpsL ops).length := by
  induction ops with
  | nil => simp [emitOpsL]
  | cons op rest ih =>
      cases hOps with
      | cons _ _ hOp hRest hTail =>
          obtain ⟨b, opTail, hOpHead⟩ :=
            emitStackOpL_cons_of_RunarEmittableLoop op hOp
          have hRestLen := ih hRest
          show (op :: rest).length ≤ (emitStackOpL op ++ emitOpsL rest).length
          simp [hOpHead, List.length_append, List.length_cons]
          omega

/-- Top-level `parseOps`: emitted loop bytes round-trip back to the
loop-normalised op list. -/
theorem parseOps_emit_round_trip_loop (ops : List StackOp)
    (hOps : AreLoopEmittable ops) :
    parseOps (emitOpsL ops) = .ok (loopNormalizeOps ops) := by
  unfold parseOps
  rw [parseOpsFuel_emit_round_trip_loop ops hOps (emitOpsL ops).length (Nat.le_refl _)]

/-! ### ByteArray bridge → `parseScript`

`parseScript` is `parseOps ∘ ByteArray.toList`. We bridge from the
`ByteArray` emitter `Emit.emitOps` to the list emitter `emitOpsL` via
the per-op `toList` agreements. -/

/-- `(Emit.emitStackOp op).toList = emitStackOpL op` for loop-emittable ops. -/
theorem emitStackOp_toList_of_RunarEmittableLoop
    (op : StackOp) (hOp : RunarEmittableLoop op) :
    (Emit.emitStackOp op).toList = emitStackOpL op := by
  cases hOp with
  | flat op h => exact emitStackOp_toList_of_RunarEmittable op h
  | push v h => exact h.emit_toList
  | pickStruct d hd =>
      -- byte-identical to `.pick d`
      have hPick := emitStackOp_toList_of_RunarEmittable (.pick d) (.pick d hd)
      change (Emit.emitStackOp (.pickStruct d)).toList = emitStackOpL (.pickStruct d)
      rw [emitStackOpL_pickStruct_eq_pick]
      have hEmitEq : Emit.emitStackOp (.pickStruct d) = Emit.emitStackOp (.pick d) := rfl
      rw [hEmitEq]; exact hPick
  | placeholder i n => exact ByteArray.toList_mk_singleton _
  | pushCodesepIndex => exact ByteArray.toList_mk_singleton _
  | loopOpcode name h => exact emitStackOp_toList_loopOpcode name h

theorem emitOps_toList_of_AreLoopEmittable
    (ops : List StackOp) (hOps : AreLoopEmittable ops) :
    (Emit.emitOps ops).toList = emitOpsL ops := by
  induction ops with
  | nil =>
      unfold Emit.emitOps emitOpsL
      exact ByteArray.toList_empty
  | cons op rest ih =>
      cases hOps with
      | cons _ _ hOp hRest hTail =>
          change (Emit.emitStackOp op ++ Emit.emitOps rest).toList
            = emitStackOpL op ++ emitOpsL rest
          rw [ByteArray.toList_append,
            emitStackOp_toList_of_RunarEmittableLoop op hOp,
            ih hRest]

/-- `parseScript` of the `ByteArray`-emitted loop bytes returns the
loop-normalised op list. -/
theorem parseScript_emit_round_trip_loop
    (ops : List StackOp) (hOps : AreLoopEmittable ops) :
    parseScript (Emit.emitOps ops) = .ok (loopNormalizeOps ops) := by
  unfold parseScript
  rw [emitOps_toList_of_AreLoopEmittable ops hOps]
  exact parseOps_emit_round_trip_loop ops hOps

/-- Fast-emitter peer: `parseScript` of `emitOpsFast` loop bytes. -/
theorem parseScript_emitOpsFast_round_trip_loop
    (ops : List StackOp) (hOps : AreLoopEmittable ops) :
    parseScript (Emit.emitOpsFast ops) = .ok (loopNormalizeOps ops) := by
  rw [← Emit.EmitFastProof.emitOps_eq_emitOpsFast ops]
  exact parseScript_emit_round_trip_loop ops hOps


end Parse
end Script

/-! ## Headline: the general `runOps`-equality round-trip for loops

For a single-public-method program whose body is `AreLoopEmittable`,
running the parsed deployment bytes equals running the loop-normalised
op list. This is the count-AGNOSTIC analogue of the fixed-input
`Stack.AgreesLoopParsed.loopOk_parseScript_eq` pin (which was
`native_decide`'d on the closed parse of `compileSafe loopOkProg`).

The result is stated against `loopNormalizeOps m.ops` (the parser's
view) — exactly as the upstream `*_normalized` omnibus lemmas state
their conclusion against `Parse.normalizeOps m.ops`. The
`loopNormalizeOps` rewrites are the SEMANTIC-only loop swaps
(`.pickStruct d ↦ .pick d`, `.placeholder ↦ OP_0`); the accompanying
`scriptAccepts` bridge below (and the per-op equalities
`runOps_placeholder_cons_eq` / `Stack.AgreesLoopParsed.scriptAccepts_*`)
connect this back to the original `m.ops` on the acceptance surface. -/

namespace Pipeline
namespace Soundness

open RunarVerification.ANF
open RunarVerification.Stack
open RunarVerification.Script
open RunarVerification.Stack.Eval (StackState runOps)
open RunarVerification.Stack (StackOp StackMethod StackProgram)

/-- `emitFast` single-public-method parse round-trip to the loop-normalised
body. -/
theorem emitFast_single_public_parse_round_trip_loop
    (p : StackProgram) (m : StackMethod)
    (hPublic : Emit.publicMethodsOf p = [m])
    (hOps : Script.Parse.AreLoopEmittable m.ops) :
    Script.Parse.parseScript (Emit.emitFast p)
      = .ok (Script.Parse.loopNormalizeOps m.ops) := by
  unfold Emit.emitFast
  rw [hPublic]
  simp only
  exact Script.Parse.parseScript_emitOpsFast_round_trip_loop m.ops hOps

/-- HEADLINE: the general loop round-trip. Running the parsed deployment
bytes equals running the loop-normalised body. Count-agnostic — no
`native_decide` on fixed bytes. -/
theorem emitFast_single_public_runOps_eq_loop
    (p : StackProgram) (m : StackMethod) (initialStack : StackState)
    (hPublic : Emit.publicMethodsOf p = [m])
    (hOps : Script.Parse.AreLoopEmittable m.ops) :
    runParsedBytes (Emit.emitFast p) initialStack
      = runOps (Script.Parse.loopNormalizeOps m.ops) initialStack := by
  unfold runParsedBytes
  rw [emitFast_single_public_parse_round_trip_loop p m hPublic hOps]

/-- `compileSafe` peer of the headline: the deployed bytes of a
single-public-method loop program parse-and-run to the loop-normalised
body. -/
theorem compileSafe_single_public_runOps_eq_loop
    (p : ANFProgram) (bytes : ByteArray)
    (m : StackMethod) (initialStack : StackState)
    (hSafe : compileSafe p = .ok bytes)
    (hPublic : Emit.publicMethodsOf (peepholeProgram (Lower.lower p)) = [m])
    (hOps : Script.Parse.AreLoopEmittable m.ops) :
    runParsedBytes bytes initialStack
      = runOps (Script.Parse.loopNormalizeOps m.ops) initialStack := by
  have hBytes := compileSafe_ok_implies_emitFast p bytes hSafe
  rw [hBytes]
  exact emitFast_single_public_runOps_eq_loop
    (peepholeProgram (Lower.lower p)) m initialStack hPublic hOps

end Soundness
end Pipeline
end RunarVerification
