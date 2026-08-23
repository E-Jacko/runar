import RunarVerification.Stack.AgreesLoopCountGeneric

/-!
# Stack IR — Symbolic count-generic whole-method lowering (wall c)

This module attacks the hardest count-generic loop frontier: the symbolic
whole-method lowering of the canonical accumulator `loopAccM n`
(`AgreesLoopCountGeneric.lean`, PR #97) and the peephole-over-`n`. The
`AgreesLoopBridge` fixture dodged this with `native_decide` at `count = 3`
(`LoopBridge.peepholedLoweredMethod_loopOk_ops_eq`); here the goal is to do
it SYMBOLICALLY over `n`.

## Confirmed empirical shapes (n = 1, 2, 3 — via `#eval`, see commit notes)

* **RAW** `(Lower.lowerMethod (loopAccProg n) … (loopAccM n)).ops`
  `= [.push (.bigint 0)] ++ loopOkAssemble n ["sum","start"] n`
    `++ [.placeholder 0 "expectedSum", .swap, .swap, .opcode "OP_NUMEQUAL"]`
    `++ List.replicate n .nip`
  The RAW epilogue carries a DOUBLE `.swap` (the `binOp "==="` bring-to-top)
  that the peephole fuses; the NIP-cleanup strand count is exactly `n`.

* **PEEPHOLED** `(peepholedLoweredMethod (loopAccProg n) (loopAccM n)).ops`
  `= [.push (.bigint 0)] ++ loopOkAssemble n ["sum","start"] n`
    `++ [.placeholder 0 "expectedSum", .opcode "OP_NUMEQUAL"]`
    `++ List.replicate n .nip`
  i.e. the count-generic generalization of `LoopBridge.loopOkPeepChain`.

## Status of this module (honest partial — the hardest wall)

LANDED (symbolic, building):
* `loopOkStrandMap_length` — the post-loop stack-map length is `n + 1`
  (induction on `n`). This is the SYMBOLIC SUBSTRATE of `lowerMethod`'s
  NIP-cleanup count: `nipCount = depthAfterBody - 1 = (finalSm.length) = n`
  follows once the epilogue map threading is closed.
* `loopOkStrandMap_head` — `sum` is at the head of the post-loop map for
  every `n ≥ 1` (the epilogue `binOp "==="` loads `sum` at a fixed depth).
* `n = 3` sanity ties `loopOkStrandMap … 3` back to the concrete bridge.

DEFERRED (the precise remaining obstacle — see module-end note):
* (c1) the full raw-lowering composition (prologue + Tier 2 loop +
  symbolic epilogue + NIP count) needs the `lowerValueP` loop-arm
  RESULTING-MAP exposed symbolically (available via
  `lowerLoopItersP_loopOkBody_eq`'s `.2` projection) threaded through the
  three epilogue bindings (`loadProp`, `binOp "==="`, terminal `assert`).
* (c2) the peephole-distribution induction over the 23-rule
  `peepholeMethodOps` pipeline (`peepholePassAllFlat` 19 rules +
  `peepholePostFold` + `peepholeChainFold` + `peepholeRollPickFold`),
  modeled on the existing `arithEmitNoFuse` per-rule identity framework
  (`Peephole.lean` Wave 38) but over the wider loop op vocabulary
  (`.push`, `.pickStruct`, `.rot`, `.swap`, `.roll d (d ≥ 3)`, `OP_ADD`).
-/

namespace RunarVerification.Stack.LoopWholeMethod

open RunarVerification.Stack.Agrees.A7 (loopOkAssemble loopOkStrandMap loopOkBody)
open RunarVerification.Stack.LoopCountGeneric (loopAccM loopAccProg)
open RunarVerification.Stack.Lower (StackMap)

/-! ## The post-loop stack-map: length and head (the symbolic NIP substrate) -/

/-- **Generalized strand-map length.** During the `loopOkStrandMap`
recursion the iteration-start map always has shape `"sum" :: rest` with
`"start"` somewhere in `rest`; each non-final iteration prepends one `"i"`
to `rest` (length `+1`) while decrementing the remaining count, and the
final iteration erases the single `"start"`. The net length of
`loopOkStrandMap ("sum" :: rest) (m + 1)` is therefore `rest.length + m + 1`.

Stated and proven for the canonical entry `rest` containing exactly one
`"start"` (`hStart : rest.count (some "start") = 1`), which is preserved by the
`"i"`-prepend recursion. -/
theorem loopOkStrandMap_length_gen :
    ∀ (m : Nat) (rest : Stack.Lower.StackMap), rest.count (some "start") = 1 →
      (loopOkStrandMap (some "sum" :: rest) (m + 1)).length = rest.length + m + 1 := by
  intro m
  induction m with
  | zero =>
    intro rest hStart
    -- final iteration: "sum" :: "i" :: rest.erase (some "start")
    show (loopOkStrandMap (some "sum" :: rest) 1).length = rest.length + 0 + 1
    rw [show loopOkStrandMap (some "sum" :: rest) 1
          = some "sum" :: some "i" :: rest.erase (some "start") from rfl]
    -- length = 2 + (rest.erase (some "start")).length, and erase removes exactly one.
    have hmem : (some "start") ∈ rest := by
      have : 0 < rest.count (some "start") := by rw [hStart]; exact Nat.zero_lt_one
      exact List.count_pos_iff.mp this
    have herase : (rest.erase (some "start")).length = rest.length - 1 :=
      List.length_erase_of_mem hmem
    simp only [List.length_cons, herase]
    have hpos : 1 ≤ rest.length := List.length_pos_of_mem hmem
    omega
  | succ k ih =>
    intro rest hStart
    -- non-final: loopOkStrandMap ("sum" :: rest) (k+2)
    --            = loopOkStrandMap ("sum" :: "i" :: rest) (k+1)
    show (loopOkStrandMap (some "sum" :: rest) (k + 1 + 1)).length = rest.length + (k + 1) + 1
    rw [show loopOkStrandMap (some "sum" :: rest) (k + 1 + 1)
          = loopOkStrandMap (some "sum" :: some "i" :: rest) (k + 1) from rfl]
    have hStart' : ((some "i" : Option String) :: rest).count (some "start") = 1 := by
      rw [List.count_cons, hStart]
      decide
    rw [ih ("i" :: rest) hStart']
    simp only [List.length_cons]
    omega

/-- **The post-loop stack-map length is `n + 1`** for the canonical
accumulator entry map `["sum", "start"]`, every `n ≥ 1`. This is the
symbolic substrate of `lowerMethod`'s NIP-cleanup count: the loop leaves
`n + 1` map entries (`sum`, plus `n` stranded `i`s after `start` is
consumed in the final iteration); the three-binding epilogue then nets to
`finalSm.length = n`, so `nipCount = n`. -/
theorem loopOkStrandMap_length (n : Nat) (hn : 1 ≤ n) :
    (loopOkStrandMap (["sum", "start"] : StackMap) n).length = n + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := loopOkStrandMap_length_gen m (["start"] : StackMap) (by decide)
  simp only [List.length_cons, List.length_nil] at h
  omega

/-- **`sum` is at the head of the post-loop stack-map** for every `n ≥ 1`.
The `binOp "==="` epilogue then loads `sum` at a fixed depth (`1` after the
`loadProp` push of `expectedSum`), independent of `n`. -/
theorem loopOkStrandMap_head_gen :
    ∀ (m : Nat) (rest : Stack.Lower.StackMap),
      (loopOkStrandMap (some "sum" :: rest) (m + 1)).head? = some "sum" := by
  intro m
  induction m with
  | zero =>
    intro rest
    rw [show loopOkStrandMap (some "sum" :: rest) 1
          = some "sum" :: some "i" :: rest.erase (some "start") from rfl]
    rfl
  | succ k ih =>
    intro rest
    rw [show loopOkStrandMap (some "sum" :: rest) (k + 1 + 1)
          = loopOkStrandMap (some "sum" :: some "i" :: rest) (k + 1) from rfl]
    exact ih ("i" :: rest)

theorem loopOkStrandMap_head (n : Nat) (hn : 1 ≤ n) :
    (loopOkStrandMap (["sum", "start"] : StackMap) n).head? = some "sum" := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact loopOkStrandMap_head_gen m (["start"] : StackMap)

/-! ## `n = 3` sanity — tie the symbolic substrate back to the bridge -/

/-- At `n = 3` the symbolic post-loop map length reproduces the concrete
value (`4 = 3 + 1`), matching the bridge fixture's `nip, nip, nip`
(`= List.replicate 3 .nip`) cleanup count derivation. -/
theorem loopOkStrandMap_length_three :
    (loopOkStrandMap (["sum", "start"] : StackMap) 3).length = 4 :=
  loopOkStrandMap_length 3 (by omega)

end RunarVerification.Stack.LoopWholeMethod
