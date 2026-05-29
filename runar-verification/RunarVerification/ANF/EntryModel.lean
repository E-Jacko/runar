import RunarVerification.ANF.WellTyped
import RunarVerification.ANF.TypeCheck   -- for TypeEnv.ofParamsProps

/-!
# ANF IR — Type-directed entry model (WS0a Task 8, piece 1)

This module closes the §11.5 "wall crack": it makes `EntryBigintTyped`
(and its `EntryBytesTyped` / `StateWellTyped` siblings) a **theorem**
rather than a free assumption on an arbitrary runtime `State`.

## Why this is needed

The omnibus quantifies the initial ANF state `initialAnf : State`
FREELY, and `State.params : List (String × Value)` carry *untyped*
`Value`s.  So `EntryBigintTyped Γ initialAnf` (every `.bigint`-declared
slot holds a `.vBigint`) cannot be derived from the omnibus alone — an
arbitrary `State` could put a `.vBool` in a bigint slot.

The *real* system never does that.  The unlocking-witness parser
(`packages/runar-sdk/**` deserializers; on-chain, the Script that pushes
the spend witness) produces, for each method parameter, a value of that
parameter's **declared type**: a `bigint` param is decoded as a number,
a `ByteString` param as bytes, a `bool` param as a 0/1 flag, etc.  We
model that decode step as a *type-directed entry constructor*
`coerceToType` and prove the resulting entry is well-typed **by
construction**.

## Faithfulness note (documented modeling choice)

`coerceToType ty raw` is a *model* of the unlocking-witness parser, in
exactly the same spirit as the eval backends (`Crypto.hashBackend`,
`Crypto.sha256Compress`, …) are models of their external primitives.
Its byte-level faithfulness to any *specific* SDK deserializer is NOT
claimed here and is NOT load-bearing for this module's purpose.  The
single property that matters — and that this module proves — is the
**kind invariant**:

    coerceToType .bigint     raw  is always  `.vBigint _`
    coerceToType .bool       raw  is always  `.vBool _`
    coerceToType .byteString raw  is always  `.vBytes _`   (and the byte family)

That invariant is what flips `EntryBigintTyped` from a hypothesis the
omnibus must be GIVEN into a fact provable from the construction: an
entry built by `mkEntryState` over a `coerceToType`-coerced witness
*cannot* put the wrong runtime tag in a typed slot, because the
constructor is type-directed.  The point is structural, not empirical:
the model is type-directed, therefore the entry is well-typed.

## On the props side (scoping)

`TypeEnv.ofParamsProps` builds the method's typing context from the
contract *properties* AND the method *parameters* (params shadow props).
The entry's **parameter** slots are type-directed by `coerceToType`, so
their well-typedness is unconditional.  The entry's **property** slots
(`propsVals`) come from the deserialized contract state and are passed
through verbatim — their well-typedness is a *separate* fact about
state-deserialization, which we take as the explicit `hPropsWT`
hypothesis on the general theorem (and which is discharged trivially in
the no-property smoke test).  This is the documented props scoping the
task anticipated.

This module is self-contained (a NEW file) and does NOT touch the
omnibus.  It is the substrate the discharge bridge (Task 8 piece 2) will
compose with to retire the free `EntryBigintTyped` premise.
-/

namespace RunarVerification.ANF.EntryModel

open RunarVerification.ANF (ANFType ANFParam ANFProperty)
open RunarVerification.ANF.Eval (Value State)
open RunarVerification.ANF.WellTyped (EntryBigintTyped EntryBytesTyped StateWellTyped
  ValueHasKind)
open RunarVerification.ANF.Typed (TypeEnv)
open RunarVerification.ANF.TypeCheck (TypeEnv.ofParamsProps)

/-! ## General list helpers (reusable, no axioms) -/

/-- If `(k, t) ∈ xs` and the keys `xs.map Prod.fst` are `Nodup`, then
`xs.find? (·.fst == k) = some (k, t)`.  (`String` has `LawfulBEq`, so the
`==` predicate is exactly key-equality.) -/
theorem find_eq_of_mem_nodup_fst {T : Type}
    (xs : List (String × T)) (k : String) (t : T)
    (hmem : (k, t) ∈ xs) (hnd : (xs.map Prod.fst).Nodup) :
    xs.find? (·.fst == k) = some (k, t) := by
  induction xs with
  | nil => simp at hmem
  | cons hd tl ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hHdNotIn, hTlNd⟩ := hnd
    rw [List.find?_cons]
    rcases List.mem_cons.mp hmem with hEq | hInTl
    · subst hEq; simp only [beq_self_eq_true]
    · have hkInTl : k ∈ tl.map Prod.fst := by
        have : (k, t).fst ∈ tl.map Prod.fst := List.mem_map_of_mem (f := Prod.fst) hInTl
        simpa using this
      have hHdNe : (hd.fst == k) = false := by
        rw [beq_eq_false_iff_ne]; intro hHdEq; exact hHdNotIn (hHdEq ▸ hkInTl)
      rw [hHdNe]; exact ih hInTl hTlNd

/-- An element paired in `zipIdx` is a member of the original list (the
forward projection: `(x, i) ∈ xs.zipIdx → x ∈ xs`). -/
theorem mem_of_mem_zipIdx {α : Type} {xs : List α} {x : α} {i : Nat}
    (h : (x, i) ∈ xs.zipIdx) : x ∈ xs := by
  obtain ⟨_hk, hlt, hx⟩ := List.mem_zipIdx h
  simp only [Nat.zero_add, Nat.sub_zero] at *
  rw [hx]
  exact List.getElem_mem (by omega)

/-- Membership of an element in a list yields an index pairing it in
`zipIdx` (the reverse of `mem_of_mem_zipIdx`'s forward projection). -/
theorem mem_zipIdx_of_mem {α : Type} (l : List α) (a : α) (k : Nat) (h : a ∈ l) :
    ∃ i, (a, i) ∈ l.zipIdx k := by
  induction l generalizing k with
  | nil => simp at h
  | cons hd tl ih =>
    rw [List.zipIdx_cons]
    rcases List.mem_cons.mp h with hHd | hTl
    · subst hHd; exact ⟨k, List.mem_cons_self⟩
    · obtain ⟨i, hi⟩ := ih (k + 1) hTl
      exact ⟨i, List.mem_cons_of_mem _ hi⟩

/-! ## The type-directed coercion -/

/--
Type-directed coercion of a raw witness `Value` to the canonical runtime
representation of an `ANFType`.  This is the model of the
unlocking-witness parser's per-parameter decode (see the module
doc-comment for the faithfulness discussion).

The three scalar runtime kinds are produced via the strict ANF
coercions (`Value.asInt?` / `Value.asBool?` / `Value.asBytes?`) with a
total canonical fallback, so the result is ALWAYS the kind the type
demands:

* `.bigint` ⇒ `.vBigint` (fallback `0`),
* `.bool` ⇒ `.vBool` (fallback `false`),
* every byte-family type (`.byteString`, `.pubKey`, `.sig`, hashes,
  addr, preimage, EC points) ⇒ `.vBytes` (fallback empty).

The two `bigint`-family-but-int-encoded subtypes (`.rabinSig`,
`.rabinPubKey`) live on the stack as integers, so they coerce to
`.vBigint` (matching `TypeCheck.isBigintFamily`).  `array` types coerce
to a canonical `.vBytes` placeholder (no conformance fixture carries an
array-typed *param* or *property* — see `Syntax.lean`'s `ANFType.array`
note — so this arm is never exercised by a real entry; it only keeps the
function total).
-/
def coerceToType (ty : ANFType) (raw : Value) : Value :=
  match ty with
  | .bigint          => .vBigint (raw.asInt?.getD 0)
  | .bool            => .vBool (raw.asBool?.getD false)
  | .byteString      => .vBytes (raw.asBytes?.getD ByteArray.empty)
  | .pubKey          => .vBytes (raw.asBytes?.getD ByteArray.empty)
  | .sig             => .vBytes (raw.asBytes?.getD ByteArray.empty)
  | .sha256          => .vBytes (raw.asBytes?.getD ByteArray.empty)
  | .ripemd160       => .vBytes (raw.asBytes?.getD ByteArray.empty)
  | .addr            => .vBytes (raw.asBytes?.getD ByteArray.empty)
  | .sigHashPreimage => .vBytes (raw.asBytes?.getD ByteArray.empty)
  | .point           => .vBytes (raw.asBytes?.getD ByteArray.empty)
  | .p256Point       => .vBytes (raw.asBytes?.getD ByteArray.empty)
  | .p384Point       => .vBytes (raw.asBytes?.getD ByteArray.empty)
  -- Rabin subtypes live as stack integers (see TypeCheck.isBigintFamily).
  | .rabinSig        => .vBigint (raw.asInt?.getD 0)
  | .rabinPubKey     => .vBigint (raw.asInt?.getD 0)
  -- `array` never reaches a real entry slot (no fixture has array params /
  -- props); a canonical empty-bytes placeholder keeps the function total.
  | .array _         => .vBytes (raw.asBytes?.getD ByteArray.empty)

/-! ## Kind invariants (the load-bearing facts, proved BY CONSTRUCTION)

These say `coerceToType` produces exactly the runtime kind each `Entry`
predicate expects.  They are pure `rfl` facts — no hypothesis on
`raw`. -/

/-- `coerceToType .bigint raw` is always a `.vBigint`. -/
theorem coerceToType_bigint_isBigint (raw : Value) :
    ∃ i : Int, coerceToType .bigint raw = .vBigint i :=
  ⟨raw.asInt?.getD 0, rfl⟩

/-- `coerceToType .bool raw` is always a `.vBool`. -/
theorem coerceToType_bool_isBool (raw : Value) :
    ∃ b : Bool, coerceToType .bool raw = .vBool b :=
  ⟨raw.asBool?.getD false, rfl⟩

/-- `coerceToType .byteString raw` is always a `.vBytes`. -/
theorem coerceToType_byteString_isBytes (raw : Value) :
    ∃ b : ByteArray, coerceToType .byteString raw = .vBytes b :=
  ⟨raw.asBytes?.getD ByteArray.empty, rfl⟩

/-- The `Value.IsBigint` form of the bigint kind invariant. -/
theorem coerceToType_bigint_IsBigint (raw : Value) :
    WellTyped.Value.IsBigint (coerceToType .bigint raw) :=
  coerceToType_bigint_isBigint raw

/-- The `Value.IsBool` form of the bool kind invariant. -/
theorem coerceToType_bool_IsBool (raw : Value) :
    WellTyped.Value.IsBool (coerceToType .bool raw) :=
  coerceToType_bool_isBool raw

/-- The `Value.IsBytes` form of the byteString kind invariant. -/
theorem coerceToType_byteString_IsBytes (raw : Value) :
    WellTyped.Value.IsBytes (coerceToType .byteString raw) :=
  coerceToType_byteString_isBytes raw

/-- **Master kind invariant.**  For EVERY `ANFType`, `coerceToType ty raw`
has the runtime kind `ValueHasKind · ty` expects.  This is the single
fact that drives every entry-well-typedness theorem below: a slot built
by `coerceToType ty` always satisfies `ValueHasKind v ty`.  For the three
scalar kinds it unfolds to the `IsBigint`/`IsBool`/`IsBytes` invariants;
for every other (crypto / point / array) type `ValueHasKind` is `True`. -/
theorem coerceToType_valueHasKind (ty : ANFType) (raw : Value) :
    ValueHasKind (coerceToType ty raw) ty := by
  cases ty with
  | bigint     => exact coerceToType_bigint_IsBigint raw
  | bool       => exact coerceToType_bool_IsBool raw
  | byteString => exact coerceToType_byteString_IsBytes raw
  -- every other type maps `ValueHasKind · ty` to `True`.
  | _          => trivial

/-! ## The type-directed entry constructor

`mkEntryParams` zips each declared param with the `coerceToType`-decode
of the corresponding witness value (or a `default` raw when the witness
is short, which the bigint/bool/bytes arms still map to a canonical
typed value).  `mkEntryState` packages those params with the contract's
property slots into a `State`. -/

/-- Build the typed parameter slots from the declared `params` and a raw
`witness` value list.  Param `i` gets `coerceToType params[i].type
(witness[i])`, with a `default` raw value when the witness is shorter
than the parameter list. -/
def mkEntryParams (params : List ANFParam) (witness : List Value) :
    List (String × Value) :=
  params.zipIdx.map (fun pi => (pi.1.name, coerceToType pi.1.type (witness.getD pi.2 default)))

/-- Build the type-directed entry `State`: typed params from
`mkEntryParams`, property slots `propsVals` passed through verbatim, no
bindings, no outputs. -/
def mkEntryState (params : List ANFParam) (propsVals : List (String × Value))
    (witness : List Value) : State :=
  { params := mkEntryParams params witness, props := propsVals }

/-- Every slot in `mkEntryParams params witness` has the form
`(p.name, coerceToType p.type raw)` for some param `p ∈ params`.  (`find?`
returns a member, so this transports to whatever `lookupParam` finds — no
name-uniqueness needed for the *value* side.) -/
theorem mem_mkEntryParams_shape
    {params : List ANFParam} {witness : List Value}
    {e : String × Value} (hmem : e ∈ mkEntryParams params witness) :
    ∃ (p : ANFParam) (raw : Value), p ∈ params ∧
      e = (p.name, coerceToType p.type raw) := by
  unfold mkEntryParams at hmem
  rw [List.mem_map] at hmem
  obtain ⟨pi, hpi, he⟩ := hmem
  obtain ⟨p, i⟩ := pi
  exact ⟨p, witness.getD i default, mem_of_mem_zipIdx hpi, he.symm⟩

/-- Two params with the same name in a `Nodup`-names list are equal.  This
is the *only* place parameter-name uniqueness is used; it is exactly the
real-system invariant (a method cannot declare two params of one name). -/
theorem param_eq_of_nodup_name
    {params : List ANFParam} (hnd : (params.map ANFParam.name).Nodup)
    {p q : ANFParam} (hp : p ∈ params) (hq : q ∈ params)
    (hname : p.name = q.name) : p = q := by
  induction params with
  | nil => simp at hp
  | cons hd tl ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hHdNotIn, hTlNd⟩ := hnd
    rcases List.mem_cons.mp hp with hpHd | hpTl
    · rcases List.mem_cons.mp hq with hqHd | hqTl
      · rw [hpHd, hqHd]
      · exfalso; apply hHdNotIn; rw [hpHd] at hname; rw [hname]
        exact List.mem_map_of_mem (f := ANFParam.name) hqTl
    · rcases List.mem_cons.mp hq with hqHd | hqTl
      · exfalso; apply hHdNotIn; rw [hqHd] at hname; rw [← hname]
        exact List.mem_map_of_mem (f := ANFParam.name) hpTl
      · exact ih hTlNd hpTl hqTl

/-! ## Resolution facts about `mkEntryState`

`resolveRef = lookupBinding <|> lookupParam <|> lookupProp`; `mkEntryState`
has no bindings, so resolution is `lookupParam <|> lookupProp`. -/

/-- **Param-slot resolution.**  For a param `p ∈ params` with distinct
names, `mkEntryState` resolves `p.name` to the `coerceToType`-coerced
witness value of THAT param.  By construction this value is
`coerceToType p.type _`, so it has kind `p.type` (the master invariant).
This is the by-construction core: the resolved value's runtime tag is
fixed by the param's declared type, never by the raw witness. -/
theorem resolveRef_mkEntryState_param
    {params : List ANFParam} {propsVals : List (String × Value)} {witness : List Value}
    (hnd : (params.map ANFParam.name).Nodup)
    {p : ANFParam} (hp : p ∈ params) :
    ∃ v : Value, (mkEntryState params propsVals witness).resolveRef p.name = some v ∧
      ValueHasKind v p.type := by
  -- A concrete member of `mkEntryParams` keyed at `p.name`.
  obtain ⟨i, hpi⟩ := mem_zipIdx_of_mem params p 0 hp
  have hMemMk : (p.name, coerceToType p.type (witness.getD i default))
      ∈ mkEntryParams params witness := by
    unfold mkEntryParams; rw [List.mem_map]; exact ⟨(p, i), hpi, rfl⟩
  -- Hence `find? (·.fst == p.name)` succeeds.
  have hSome : ((mkEntryParams params witness).find? (·.fst == p.name)).isSome = true := by
    rw [List.find?_isSome]; exact ⟨_, hMemMk, by simp⟩
  obtain ⟨e', hf⟩ := Option.isSome_iff_exists.mp hSome
  have he'mem : e' ∈ mkEntryParams params witness := List.mem_of_find?_eq_some hf
  have he'pred : ((·.fst == p.name) e' : Bool) = true :=
    @List.find?_some _ (·.fst == p.name) e' _ hf
  have he'name : e'.1 = p.name := eq_of_beq he'pred
  -- The found slot's shape: `(q.name, coerceToType q.type raw)` with `q.name = p.name`.
  obtain ⟨q, raw, hqmem, hqe⟩ := mem_mkEntryParams_shape he'mem
  have hqname : q.name = p.name := by rw [← he'name, hqe]
  have hqp : q = p := param_eq_of_nodup_name hnd hqmem hp hqname
  refine ⟨e'.2, ?_, ?_⟩
  · -- `resolveRef` stops at the (successful) param leg; bindings are empty.
    unfold State.resolveRef State.lookupBinding State.lookupParam mkEntryState
    simp only [List.find?_nil, Option.map_none]
    rw [hf]; simp
  · -- value kind: `e'.2 = coerceToType q.type raw`, and `q.type = p.type`.
    rw [hqe]; simp only; rw [hqp]; exact coerceToType_valueHasKind p.type raw

/-! ## The lookup ⇒ resolution bridge through `ofParamsProps`

`StateWellTyped` is keyed by `ofParamsProps`-lookups.  We split a
`lookup n = some ty` into the param case (handled by construction above)
and the props case (the `hPropsWT` hypothesis).  The structural lemma is
the `ofParamsProps` bindings characterization. -/

/-- `ofParamsProps`'s binding list is `params.reverse ++ props.reverse`
(each entry the `(name, type)` projection).  Direct from the
`foldl extend` definition. -/
theorem ofParamsProps_bindings (props : List ANFProperty) (params : List ANFParam) :
    (TypeEnv.ofParamsProps props params).bindings
      = params.reverse.map (fun p => (p.name, p.type))
        ++ props.reverse.map (fun p => (p.name, p.type)) := by
  unfold TypeEnv.ofParamsProps
  have key : ∀ {S : Type} (proj : S → (String × ANFType)) (l : List S) (Γ₀ : TypeEnv),
      (l.foldl (fun Γ x => Γ.extend (proj x).1 (proj x).2) Γ₀).bindings
        = l.reverse.map proj ++ Γ₀.bindings := by
    intro S proj l Γ₀
    induction l generalizing Γ₀ with
    | nil => simp [TypeEnv.empty]
    | cons x xs ih =>
        simp only [List.foldl_cons, List.reverse_cons, List.map_append, List.map_cons,
          List.map_nil]
        rw [ih]; simp [TypeEnv.extend]
  rw [key (fun pp : ANFParam => (pp.name, pp.type)) params]
  rw [key (fun pp : ANFProperty => (pp.name, pp.type)) props]
  simp [TypeEnv.empty]

/-- **Param-side lookup.**  For a param `p ∈ params` with distinct names,
`ofParamsProps` looks `p.name` up to `p.type` (params shadow props, and
`Nodup` makes the found param unique). -/
theorem ofParamsProps_lookup_param
    (props : List ANFProperty) (params : List ANFParam)
    (hnd : (params.map ANFParam.name).Nodup)
    {p : ANFParam} (hp : p ∈ params) :
    (TypeEnv.ofParamsProps props params).lookup p.name = some p.type := by
  unfold TypeEnv.lookup
  rw [ofParamsProps_bindings, List.find?_append]
  have hmemSeg : (p.name, p.type)
      ∈ params.reverse.map (fun q : ANFParam => (q.name, q.type)) :=
    List.mem_map_of_mem (f := fun q : ANFParam => (q.name, q.type)) (List.mem_reverse.mpr hp)
  have hndSeg :
      ((params.reverse.map (fun q : ANFParam => (q.name, q.type))).map Prod.fst).Nodup := by
    rw [List.map_map]
    show (params.reverse.map (fun q : ANFParam => q.name)).Nodup
    rw [List.map_reverse]
    exact (List.reverse_perm _).nodup_iff.mpr hnd
  rw [find_eq_of_mem_nodup_fst _ p.name p.type hmemSeg hndSeg]
  rfl

/-! ## The props-side hypothesis

The entry's **property** slots (`propsVals`) come from the deserialized
contract state, NOT from `coerceToType`, so their well-typedness is a
separate fact we take as a hypothesis.  `EntryPropsWellTyped` says: every
name `ofParamsProps` looks up that is NOT a parameter name (i.e. a genuine
property name) resolves, in the entry state, to a value of its declared
kind.  This is exactly the obligation the param-side construction does
*not* discharge, and it is **vacuously true whenever the contract has no
unshadowed property slots** (e.g. `props = []`), which is the
stateless-contract case the smoke test exercises. -/

/-- The props-side well-typedness hypothesis for `mkEntryState`.  For every
non-parameter name `n` that `ofParamsProps` declares at type `ty`, the
entry state resolves `n` to a value of kind `ty`.  (Param names are
excluded — they are handled by construction via `coerceToType`.) -/
def EntryPropsWellTyped
    (props : List ANFProperty) (params : List ANFParam)
    (propsVals : List (String × Value)) (witness : List Value) : Prop :=
  ∀ (n : String) (ty : ANFType),
    (TypeEnv.ofParamsProps props params).lookup n = some ty →
    (∀ p : ANFParam, p ∈ params → p.name ≠ n) →
    ∃ v : Value, (mkEntryState params propsVals witness).resolveRef n = some v ∧
      ValueHasKind v ty

/-- When there are no property declarations, the props-side hypothesis is
vacuous: a non-parameter name cannot be looked up at all (the prop segment
of `ofParamsProps`'s bindings is empty), so the antecedent is unsatisfiable.
This discharges `EntryPropsWellTyped` for every stateless contract. -/
theorem entryPropsWellTyped_of_noProps
    (params : List ANFParam) (propsVals : List (String × Value)) (witness : List Value) :
    EntryPropsWellTyped [] params propsVals witness := by
  intro n ty hLk hNotParam
  exfalso
  -- A successful lookup means `n` is a binding name; with no props every
  -- binding is a parameter name — contradicting `hNotParam`.
  obtain ⟨e, hmem, hename, _⟩ := WellTyped.lookup_mem_name _ n ty hLk
  rw [ofParamsProps_bindings] at hmem
  simp only [List.reverse_nil, List.map_nil, List.append_nil] at hmem
  rw [List.mem_map] at hmem
  obtain ⟨q, hqmem, hqe⟩ := hmem
  exact hNotParam q (List.mem_reverse.mp hqmem) (by rw [← hename, ← hqe])

/-! ## Headline theorems — entry well-typedness BY CONSTRUCTION

The master result is `mkEntryState_stateWellTyped`: under
parameter-name distinctness (`hnd`) and the props-side hypothesis
(`hProps`), the type-directed entry satisfies `StateWellTyped` for the
method's full typing context `ofParamsProps props params`.  The
`EntryBigintTyped` / `EntryBytesTyped` headlines fall out as the
`.bigint` / `.byteString` specializations. -/

/-- **Master theorem — the entry is well-typed by construction.**

Under parameter-name distinctness and the props-side hypothesis, the
type-directed entry `mkEntryState params propsVals witness` satisfies
`StateWellTyped (ofParamsProps props params)`: every name the typing
context declares resolves, in the entry, to a value of its declared kind.

The parameter names are handled BY CONSTRUCTION (`coerceToType` fixes the
runtime tag from the declared type — `resolveRef_mkEntryState_param`); the
property names are handled by `hProps`. -/
theorem mkEntryState_stateWellTyped
    (props : List ANFProperty) (params : List ANFParam)
    (propsVals : List (String × Value)) (witness : List Value)
    (hnd : (params.map ANFParam.name).Nodup)
    (hProps : EntryPropsWellTyped props params propsVals witness) :
    StateWellTyped (TypeEnv.ofParamsProps props params)
      (mkEntryState params propsVals witness) := by
  intro n ty hLk
  by_cases hParam : ∃ p : ANFParam, p ∈ params ∧ p.name = n
  · -- Param case: handled by construction.
    obtain ⟨p, hp, hpn⟩ := hParam
    -- `lookup n = some ty` and `lookup p.name = some p.type` (param-side), with
    -- `p.name = n`, force `ty = p.type`.
    have hLkP : (TypeEnv.ofParamsProps props params).lookup p.name = some p.type :=
      ofParamsProps_lookup_param props params hnd hp
    rw [hpn] at hLkP
    have htyEq : ty = p.type := by rw [hLkP] at hLk; exact (Option.some.inj hLk).symm
    subst htyEq
    -- resolve `n = p.name` to the coerced value of `p`, kind `p.type`.
    obtain ⟨v, hres, hvk⟩ := resolveRef_mkEntryState_param (propsVals := propsVals)
      (witness := witness) hnd hp
    rw [hpn] at hres
    exact ⟨v, hres, hvk⟩
  · -- Props case: `n` is not a param name; defer to `hProps`.
    have hNotParam : ∀ p : ANFParam, p ∈ params → p.name ≠ n := by
      intro p hp hpn; exact hParam ⟨p, hp, hpn⟩
    exact hProps n ty hLk hNotParam

/-- **Headline 1 — `EntryBigintTyped` by construction.**

Every `.bigint`-declared name (param OR property) in the method's typing
context resolves, in the type-directed entry, to a `.vBigint`.  This is
the `.bigint` specialization of `mkEntryState_stateWellTyped` (via
`ValueHasKind v .bigint = Value.IsBigint v`).  It is the fact the omnibus
quantified as a free premise — now a theorem. -/
theorem mkEntryState_entryBigintTyped
    (props : List ANFProperty) (params : List ANFParam)
    (propsVals : List (String × Value)) (witness : List Value)
    (hnd : (params.map ANFParam.name).Nodup)
    (hProps : EntryPropsWellTyped props params propsVals witness) :
    EntryBigintTyped (TypeEnv.ofParamsProps props params)
      (mkEntryState params propsVals witness) := by
  intro n hLk
  obtain ⟨v, hres, hvk⟩ :=
    mkEntryState_stateWellTyped props params propsVals witness hnd hProps n .bigint hLk
  -- `ValueHasKind v .bigint` definitionally is `Value.IsBigint v`.
  exact ⟨v, hres, hvk⟩

/-- **Headline 2 — `EntryBytesTyped` by construction.**

The `.byteString` analogue of `mkEntryState_entryBigintTyped`: every
`.byteString`-declared name resolves to a `.vBytes` in the type-directed
entry. -/
theorem mkEntryState_entryBytesTyped
    (props : List ANFProperty) (params : List ANFParam)
    (propsVals : List (String × Value)) (witness : List Value)
    (hnd : (params.map ANFParam.name).Nodup)
    (hProps : EntryPropsWellTyped props params propsVals witness) :
    EntryBytesTyped (TypeEnv.ofParamsProps props params)
      (mkEntryState params propsVals witness) := by
  intro n hLk
  obtain ⟨v, hres, hvk⟩ :=
    mkEntryState_stateWellTyped props params propsVals witness hnd hProps n .byteString hLk
  exact ⟨v, hres, hvk⟩

/-! ## Stateless-contract corollaries (no property slots)

For a stateless contract (`props = []`), the props-side hypothesis is
discharged internally by `entryPropsWellTyped_of_noProps`, so the entry's
well-typedness is UNCONDITIONAL given only parameter-name distinctness.
These are the cleanest by-construction statements: a type-directed entry
over distinct-named params is well-typed, full stop. -/

/-- Stateless `StateWellTyped`: no props ⇒ the props hypothesis vanishes. -/
theorem mkEntryState_stateWellTyped_noProps
    (params : List ANFParam) (propsVals : List (String × Value)) (witness : List Value)
    (hnd : (params.map ANFParam.name).Nodup) :
    StateWellTyped (TypeEnv.ofParamsProps [] params)
      (mkEntryState params propsVals witness) :=
  mkEntryState_stateWellTyped [] params propsVals witness hnd
    (entryPropsWellTyped_of_noProps params propsVals witness)

/-- Stateless `EntryBigintTyped`: UNCONDITIONAL by construction (given only
distinct param names). -/
theorem mkEntryState_entryBigintTyped_noProps
    (params : List ANFParam) (propsVals : List (String × Value)) (witness : List Value)
    (hnd : (params.map ANFParam.name).Nodup) :
    EntryBigintTyped (TypeEnv.ofParamsProps [] params)
      (mkEntryState params propsVals witness) :=
  mkEntryState_entryBigintTyped [] params propsVals witness hnd
    (entryPropsWellTyped_of_noProps params propsVals witness)

/-- Stateless `EntryBytesTyped`: UNCONDITIONAL by construction. -/
theorem mkEntryState_entryBytesTyped_noProps
    (params : List ANFParam) (propsVals : List (String × Value)) (witness : List Value)
    (hnd : (params.map ANFParam.name).Nodup) :
    EntryBytesTyped (TypeEnv.ofParamsProps [] params)
      (mkEntryState params propsVals witness) :=
  mkEntryState_entryBytesTyped [] params propsVals witness hnd
    (entryPropsWellTyped_of_noProps params propsVals witness)

/-! ## MANDATORY smoke tests

A concrete stateless contract: params `a : bigint`, `f : bool`, and a raw
witness `[.vBigint 7, .vBool true]`.  We exhibit the type-directed entry
and fire the headline theorems THROUGH the by-construction machinery
(NOT by re-asserting the conclusion): `EntryBigintTyped` holds (the only
`.bigint` name `a` resolves to a `.vBigint`), and the entry is fully
`StateWellTyped`.  We also exercise the `coerceToType` kind invariants on
a deliberately MISMATCHED raw value (`coerceToType .bigint (.vBool true)`
is STILL a `.vBigint`) — demonstrating the entry is type-directed, not a
pass-through of whatever the witness happened to carry. -/

/-- Smoke params: `a : bigint`, `f : bool` (distinct names). -/
private def smokeParams : List ANFParam :=
  [⟨"a", .bigint⟩, ⟨"f", .bool⟩]

/-- Smoke raw witness: a number and a flag, in declaration order. -/
private def smokeWitness : List Value :=
  [.vBigint 7, .vBool true]

/-- The smoke params have distinct names. -/
theorem smoke_params_nodup : (smokeParams.map ANFParam.name).Nodup := by decide

/-- **Smoke — `EntryBigintTyped` holds via the by-construction theorem.**
Every `.bigint`-declared name in `ofParamsProps [] smokeParams` resolves,
in the type-directed entry, to a `.vBigint` — proved through
`mkEntryState_entryBigintTyped_noProps`, NOT re-asserted. -/
theorem smoke_entryBigintTyped :
    EntryBigintTyped (TypeEnv.ofParamsProps [] smokeParams)
      (mkEntryState smokeParams [] smokeWitness) :=
  mkEntryState_entryBigintTyped_noProps smokeParams [] smokeWitness smoke_params_nodup

/-- **Smoke — the full entry is `StateWellTyped`.** -/
theorem smoke_stateWellTyped :
    StateWellTyped (TypeEnv.ofParamsProps [] smokeParams)
      (mkEntryState smokeParams [] smokeWitness) :=
  mkEntryState_stateWellTyped_noProps smokeParams [] smokeWitness smoke_params_nodup

/-- **Smoke — the entry concretely resolves `a` to a `.vBigint` and `f` to a
`.vBool`.**  Sanity check that the construction is non-vacuous: the slots
exist and carry the type-directed runtime values. -/
example :
    (mkEntryState smokeParams [] smokeWitness).resolveRef "a" = some (.vBigint 7) ∧
    (mkEntryState smokeParams [] smokeWitness).resolveRef "f" = some (.vBool true) := by
  constructor <;> rfl

/-- **Smoke — type-directed, not pass-through.**  Even on a raw value of
the WRONG kind, `coerceToType .bigint` still yields a `.vBigint` (here the
fallback `0`, since `(.vBool true).asInt? = none`).  This is exactly why
`EntryBigintTyped` is a theorem and not a hope about the witness. -/
example : coerceToType .bigint (.vBool true) = .vBigint 0 := rfl

end RunarVerification.ANF.EntryModel
