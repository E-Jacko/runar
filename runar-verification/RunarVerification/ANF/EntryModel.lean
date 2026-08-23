import RunarVerification.ANF.WellTyped
import RunarVerification.ANF.TypeCheck   -- for TypeEnv.ofParamsProps
import RunarVerification.Stack.AgreesA3  -- piece 2b: entryTsmArithTyped / tsmCoherent / taggedAllBigint

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
open RunarVerification.Stack.Agrees (SlotKind TaggedStackMap agreesTagged taggedStackAligned
  untagSm lookupAnfByKind entryTsmArithTyped tsmCoherent taggedAllBigint
  taggedAllBigint_of_entryTyped)
open RunarVerification.Stack.Eval (StackState)

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

/-! ## Type-directed PROPERTY slots — `EntryPropsWellTyped` BY CONSTRUCTION
    (WS0a Task 8, props side)

The param-side machinery above leaves `EntryPropsWellTyped` as an explicit
hypothesis: the property slots `propsVals` were taken as GIVEN, so their
well-typedness had to be assumed.  For a STATEFUL contract the on-chain
deserialized state is itself interpreted PER DECLARED PROPERTY TYPE — a
`bigint` property is decoded as a number, a `ByteString` property as
bytes, exactly as for parameters.  We model that decode with the SAME
`coerceToType` and DISCHARGE `EntryPropsWellTyped` by construction.

`mkEntryProps` mirrors `mkEntryParams`: each declared property is zipped
with the `coerceToType`-decode of the corresponding `stateWitness` value.
The headline `entryPropsWellTyped_mkEntryProps` then proves the props-side
obligation outright (no hypothesis on the witness), so the props-bearing
entry headlines below need only parameter- AND property-name distinctness
— no free well-typedness premise survives even for stateful contracts. -/

/-- Build the type-directed PROPERTY slots from the declared `props` and a
raw `stateWitness` value list.  Property `i` gets `coerceToType
props[i].type (stateWitness[i])`, with a `default` raw value when the
witness is shorter than the property list.  Mirror of `mkEntryParams`. -/
def mkEntryProps (props : List ANFProperty) (stateWitness : List Value) :
    List (String × Value) :=
  props.zipIdx.map
    (fun pi => (pi.1.name, coerceToType pi.1.type (stateWitness.getD pi.2 default)))

/-- The names of `mkEntryProps props sw` are exactly `props.map (·.name)`
(the `coerceToType` value side is irrelevant to the key projection).
Mirror of `mkEntryParams_map_fst`. -/
theorem mkEntryProps_map_fst (props : List ANFProperty) (stateWitness : List Value) :
    (mkEntryProps props stateWitness).map (·.1) = props.map ANFProperty.name := by
  unfold mkEntryProps
  rw [List.map_map]
  show (props.zipIdx.map (fun pi => pi.1.name)) = props.map ANFProperty.name
  rw [show (fun pi : ANFProperty × Nat => pi.1.name)
        = (ANFProperty.name ∘ (·.1)) from rfl, ← List.map_map, List.zipIdx_map_fst]

/-- Each slot of `mkEntryProps` is `lookupProp`-findable in the entry
state, given distinct property names.  (`find?` is unique under the
`Nodup` key projection.)  Mirror of `lookupParam_mkEntryState_of_mem`. -/
theorem lookupProp_mkEntryProps_of_mem
    {params : List ANFParam} {props : List ANFProperty}
    {stateWitness witness : List Value}
    (hndP : (props.map ANFProperty.name).Nodup)
    {e : String × Value} (hmem : e ∈ mkEntryProps props stateWitness) :
    (mkEntryState params (mkEntryProps props stateWitness) witness).lookupProp e.1
      = some e.2 := by
  unfold State.lookupProp mkEntryState
  have hndKeys : ((mkEntryProps props stateWitness).map Prod.fst).Nodup := by
    show ((mkEntryProps props stateWitness).map (·.1)).Nodup
    rw [mkEntryProps_map_fst]; exact hndP
  have hpair : e = (e.1, e.2) := rfl
  rw [find_eq_of_mem_nodup_fst (mkEntryProps props stateWitness) e.1 e.2 (hpair ▸ hmem) hndKeys]
  rfl

/-- **Property-side lookup.**  A name that `ofParamsProps` looks up AND that
is NOT a parameter name resolves to its declared PROPERTY type, and pins a
member property `q ∈ props` carrying that name and type.  This is the
delicate step the task flagged: `hNotParam` makes the param segment miss
(`find?_paramSeg_none_of_not_param`), so `find?` falls to the prop segment,
where the looked-up `(n, ty)` is a member — i.e. a property of name `n` and
declared type `ty`. -/
theorem ofParamsProps_lookup_prop
    (props : List ANFProperty) (params : List ANFParam) (n : String) (ty : ANFType)
    (hLk : (TypeEnv.ofParamsProps props params).lookup n = some ty)
    (hNotParam : ∀ p : ANFParam, p ∈ params → p.name ≠ n) :
    ∃ q : ANFProperty, q ∈ props ∧ q.name = n ∧ q.type = ty := by
  -- A looked-up name is a binding member of name `n` and type `ty`.
  obtain ⟨e, hemem, hename, hetype⟩ := WellTyped.lookup_mem_name _ n ty hLk
  -- Split that membership across the param / prop segments of `ofParamsProps`.
  rw [ofParamsProps_bindings, List.mem_append] at hemem
  rcases hemem with hParamSeg | hPropSeg
  · -- Param segment: contradicts `hNotParam` (the member's name is `n = e.1`).
    exfalso
    rw [List.mem_map] at hParamSeg
    obtain ⟨p, hpMem, hpe⟩ := hParamSeg
    have hpName : p.name = n := by rw [← hename, ← hpe]
    exact hNotParam p (List.mem_reverse.mp hpMem) hpName
  · -- Prop segment: the member is a property of name `n` and type `ty`.
    rw [List.mem_map] at hPropSeg
    obtain ⟨q, hqMem, hqe⟩ := hPropSeg
    have hqName : q.name = n := by rw [← hename, ← hqe]
    have hqType : q.type = ty := by rw [← hetype, ← hqe]
    exact ⟨q, List.mem_reverse.mp hqMem, hqName, hqType⟩

/-- **`resolveRef = lookupProp` at entry (for a non-parameter name).**
Because `mkEntryState` has no bindings AND `n` is not a parameter name (so
`lookupParam n = none`), the evaluator's `resolveRef` falls through both
prefixes of the `<|>` chain to `lookupProp`.  Mirror — on the OTHER branch
— of `resolveRef_eq_lookupParam_mkEntryState`. -/
theorem resolveRef_eq_lookupProp_of_not_param
    {params : List ANFParam} {propsVals : List (String × Value)} {witness : List Value}
    {n : String}
    (hNotParam : ∀ p : ANFParam, p ∈ params → p.name ≠ n) :
    (mkEntryState params propsVals witness).resolveRef n
      = (mkEntryState params propsVals witness).lookupProp n := by
  -- `lookupParam n = none`: no param slot is keyed at `n` (param keys are
  -- `params.map name`, and `hNotParam` forbids any equal to `n`).
  have hLPnone : (mkEntryState params propsVals witness).lookupParam n = none := by
    unfold State.lookupParam mkEntryState
    have hfind : (mkEntryParams params witness).find? (·.fst == n) = none := by
      rw [List.find?_eq_none]
      intro x hx hpx
      obtain ⟨p, raw, hpMem, hpe⟩ := mem_mkEntryParams_shape hx
      have hxName : x.fst = p.name := by rw [hpe]
      rw [hxName] at hpx
      exact hNotParam p hpMem (eq_of_beq hpx)
    rw [hfind]; rfl
  -- bindings empty ⇒ lookupBinding = none; then the orElse chain collapses to lookupProp.
  unfold State.resolveRef State.lookupBinding mkEntryState
  simp only [List.find?_nil, Option.map_none]
  show (none <|> (mkEntryState params propsVals witness).lookupParam n <|>
      (mkEntryState params propsVals witness).lookupProp n)
    = (mkEntryState params propsVals witness).lookupProp n
  rw [hLPnone]; rfl

/-- **The props-side headline — `EntryPropsWellTyped` BY CONSTRUCTION.**

When the property slots are built type-directed by `mkEntryProps`, the
props-side obligation is DISCHARGED outright (no hypothesis on the witness).
For every non-parameter name `n` that `ofParamsProps` declares at type
`ty`, the entry resolves `n` (through `lookupProp`, since `n` is not a
param) to the `coerceToType ty`-coerced property value — whose runtime
kind is `ty` by the master invariant `coerceToType_valueHasKind`.

Proof: `n` non-param + lookup ⇒ `n` is a property of declared type `ty`
(`ofParamsProps_lookup_prop`); that property's `mkEntryProps` slot is
`lookupProp`-found under `hndP` (`lookupProp_mkEntryProps_of_mem`), and
`resolveRef` reaches it because the param leg misses
(`resolveRef_eq_lookupProp_of_not_param`).  The resolved value is
`coerceToType ty raw`, kind `ty`. -/
theorem entryPropsWellTyped_mkEntryProps
    (props : List ANFProperty) (params : List ANFParam)
    (stateWitness witness : List Value)
    (hndP : (props.map ANFProperty.name).Nodup) :
    EntryPropsWellTyped props params (mkEntryProps props stateWitness) witness := by
  intro n ty hLk hNotParam
  -- `n` is a property name with declared type `ty`.
  obtain ⟨q, hqMem, hqName, hqType⟩ := ofParamsProps_lookup_prop props params n ty hLk hNotParam
  -- Its type-directed slot is in `mkEntryProps`, keyed at `q.name = n`.
  obtain ⟨i, hqi⟩ := mem_zipIdx_of_mem props q 0 hqMem
  have hMemMk : (q.name, coerceToType q.type (stateWitness.getD i default))
      ∈ mkEntryProps props stateWitness := by
    unfold mkEntryProps; rw [List.mem_map]; exact ⟨(q, i), hqi, rfl⟩
  -- `lookupProp` finds that slot (distinct property names).
  have hLP : (mkEntryState params (mkEntryProps props stateWitness) witness).lookupProp n
      = some (coerceToType q.type (stateWitness.getD i default)) := by
    have := lookupProp_mkEntryProps_of_mem (params := params) (witness := witness)
      hndP hMemMk
    -- `e = (q.name, …)`, and `q.name = n`.
    simpa only [hqName] using this
  -- `resolveRef n = lookupProp n` (n is not a param), so resolveRef hits the coerced value.
  refine ⟨coerceToType q.type (stateWitness.getD i default), ?_, ?_⟩
  · rw [resolveRef_eq_lookupProp_of_not_param hNotParam, hLP]
  · -- kind: `coerceToType q.type _` has kind `q.type = ty`.
    rw [hqType] at *
    exact coerceToType_valueHasKind ty (stateWitness.getD i default)

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

/-! ## Stateful-contract headlines (type-directed PROPERTY slots)

These are the full props-bearing analogues: the property slots are built
type-directed by `mkEntryProps`, so the props-side hypothesis is
discharged INTERNALLY by `entryPropsWellTyped_mkEntryProps`.  Given only
parameter-name distinctness (`hnd`) AND property-name distinctness
(`hndP`), a stateful contract's type-directed entry is well-typed — no
free well-typedness premise survives.  This is the props-side counterpart
of the `_noProps` stateless corollaries below. -/

/-- **Stateful `StateWellTyped` by construction.**  With type-directed
property slots, the full method context `ofParamsProps props params` is
satisfied given only param- and property-name distinctness. -/
theorem mkEntryState_stateWellTyped_props
    (props : List ANFProperty) (params : List ANFParam)
    (stateWitness witness : List Value)
    (hnd : (params.map ANFParam.name).Nodup)
    (hndP : (props.map ANFProperty.name).Nodup) :
    StateWellTyped (TypeEnv.ofParamsProps props params)
      (mkEntryState params (mkEntryProps props stateWitness) witness) :=
  mkEntryState_stateWellTyped props params (mkEntryProps props stateWitness) witness hnd
    (entryPropsWellTyped_mkEntryProps props params stateWitness witness hndP)

/-- **Stateful `EntryBigintTyped` by construction.**  Every
`.bigint`-declared name — parameter OR property — resolves to a `.vBigint`
in the type-directed stateful entry.  Discharges the props hypothesis via
`entryPropsWellTyped_mkEntryProps`. -/
theorem mkEntryState_entryBigintTyped_props
    (props : List ANFProperty) (params : List ANFParam)
    (stateWitness witness : List Value)
    (hnd : (params.map ANFParam.name).Nodup)
    (hndP : (props.map ANFProperty.name).Nodup) :
    EntryBigintTyped (TypeEnv.ofParamsProps props params)
      (mkEntryState params (mkEntryProps props stateWitness) witness) :=
  mkEntryState_entryBigintTyped props params (mkEntryProps props stateWitness) witness hnd
    (entryPropsWellTyped_mkEntryProps props params stateWitness witness hndP)

/-- **Stateful `EntryBytesTyped` by construction.**  The `.byteString`
analogue: every `.byteString`-declared name (param OR property) resolves
to a `.vBytes` in the type-directed stateful entry. -/
theorem mkEntryState_entryBytesTyped_props
    (props : List ANFProperty) (params : List ANFParam)
    (stateWitness witness : List Value)
    (hnd : (params.map ANFParam.name).Nodup)
    (hndP : (props.map ANFProperty.name).Nodup) :
    EntryBytesTyped (TypeEnv.ofParamsProps props params)
      (mkEntryState params (mkEntryProps props stateWitness) witness) :=
  mkEntryState_entryBytesTyped props params (mkEntryProps props stateWitness) witness hnd
    (entryPropsWellTyped_mkEntryProps props params stateWitness witness hndP)

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

/-! ## Stack-side entry model — `agreesTagged` BY CONSTRUCTION

This is the wave-25 *alignment* leg.  The omnibus discharge path needs,
alongside the ANF-side well-typedness above, a **stack-side** entry: a
concrete `StackState` whose stack mirrors the type-directed entry, plus
the `agreesTagged` relating the two AND the `hUntag` premise the
`arith_consume` chain consumes.

`mkTsm` is the tagged stack-map for the entry: every parameter is a
`.param` slot, in **stack order** (top = last param).  Because the
Bitcoin Script stack pushes params in declaration order, the *top* of the
stack is the *last*-declared param, so the stack-order list is
`params.reverse`.

`mkStackEntry` is the matching `StackState`: its `.stack` is the coerced
param values in that same reversed order, with `props`/`outputs` shared
with the ANF entry.  `agreesTagged_mkEntry` then proves alignment **by
construction** — no hypothesis beyond parameter-name distinctness. -/

/-- The tagged stack-map for the type-directed entry: each parameter
becomes a `.param` slot, ordered top-of-stack-first (i.e. `params`
reversed, since the last-declared param sits on top of the Script
stack). -/
def mkTsm (params : List ANFParam) : TaggedStackMap :=
  (params.reverse).map (fun p => (p.name, SlotKind.param))

/-- **`hUntag` by construction.**  Stripping the kind tags off `mkTsm`
yields exactly `params.reverse.map (·.name)` — which is the `StackMap`
the codegen lowers parameters to (stack order), and precisely the
`hUntag` premise the `arith_consume` chain requires. -/
theorem untagSm_mkTsm (params : List ANFParam) :
    untagSm (mkTsm params) = List.reverse (params.map (fun p => some p.name)) := by
  unfold mkTsm
  rw [← List.map_reverse]
  -- `untagSm (xs.map (fun p => (p.name, .param))) = xs.map (·.name)`, here `xs = params.reverse`.
  generalize params.reverse = xs
  induction xs with
  | nil => rfl
  | cons hd tl ih => simp only [List.map_cons, untagSm]; rw [ih]

/-- The matching stack-side entry `StackState`.  Its `.stack` holds the
coerced parameter values in `mkTsm` order (reversed, top-first); `props`
and `outputs` are shared with the ANF entry (`mkEntryState` leaves
`outputs := []`, so the stack entry does too).  `altstack`/`preimage`
take their structure defaults — the `SimpleANF` subset does not constrain
them (see `Agrees.agrees` doc). -/
def mkStackEntry (params : List ANFParam) (propsVals : List (String × Value))
    (witness : List Value) : StackState :=
  { stack   := (mkEntryParams params witness).reverse.map (·.2)
    props   := propsVals
    outputs := [] }

/-! ### Alignment plumbing

The general lemma `taggedStackAligned_param_self` aligns a `.param`-tagged
map built from *any* entry-param list with the value-projection of that
same list, given only that each slot is `lookupParam`-findable.  Both
`mkTsm` and `mkStackEntry.stack` come from `(mkEntryParams …).reverse`, so
they instantiate it directly. -/

/-- For a fixed ANF state, if every `(n, v)` in a slot list `sub` is
`lookupParam`-findable (`lookupParam n = some v`), then the
`.param`-tagged map of `sub` aligns with the value-projection of `sub`.
Pure induction on `sub`; the per-slot findability is supplied as a
`∀ _ ∈ sub` hypothesis (so reversal of `sub` is irrelevant). -/
theorem taggedStackAligned_param_self
    (anfSt : State) (sub : List (String × Value))
    (hfind : ∀ e ∈ sub, anfSt.lookupParam e.1 = some e.2) :
    taggedStackAligned (sub.map (fun e => (e.1, SlotKind.param))) anfSt
      (sub.map (·.2)) := by
  induction sub with
  | nil => exact True.intro
  | cons hd tl ih =>
    rw [List.map_cons, List.map_cons]
    refine ⟨?_, ?_⟩
    · -- head slot: `lookupAnfByKind (hd.1, .param) = lookupParam hd.1 = some hd.2`.
      show lookupAnfByKind anfSt (hd.1, SlotKind.param) = some hd.2
      unfold lookupAnfByKind
      exact hfind hd (List.mem_cons_self)
    · exact ih (fun e he => hfind e (List.mem_cons_of_mem _ he))

/-- The names of `mkEntryParams params witness` are exactly
`params.map (·.name)` (the `coerceToType` value side is irrelevant to the
key projection). -/
theorem mkEntryParams_map_fst (params : List ANFParam) (witness : List Value) :
    (mkEntryParams params witness).map (·.1) = params.map ANFParam.name := by
  unfold mkEntryParams
  rw [List.map_map]
  -- `((fun pi => (pi.1.name, …)) >>> (·.1)) = (·.1.name)`, then `zipIdx`'s fst-projection.
  show (params.zipIdx.map (fun pi => pi.1.name)) = params.map ANFParam.name
  rw [show (fun pi : ANFParam × Nat => pi.1.name)
        = (ANFParam.name ∘ (·.1)) from rfl, ← List.map_map, List.zipIdx_map_fst]

/-- Each slot of `mkEntryParams` is `lookupParam`-findable in the entry
state, given distinct parameter names.  (`find?` is unique under the
`Nodup` key projection.) -/
theorem lookupParam_mkEntryState_of_mem
    {params : List ANFParam} {propsVals : List (String × Value)} {witness : List Value}
    (hnd : (params.map ANFParam.name).Nodup)
    {e : String × Value} (hmem : e ∈ mkEntryParams params witness) :
    (mkEntryState params propsVals witness).lookupParam e.1 = some e.2 := by
  unfold State.lookupParam mkEntryState
  -- `find? (·.fst == e.1)` over `mkEntryParams` hits `e` (membership + nodup keys).
  have hndKeys : ((mkEntryParams params witness).map Prod.fst).Nodup := by
    show ((mkEntryParams params witness).map (·.1)).Nodup
    rw [mkEntryParams_map_fst]; exact hnd
  have hpair : e = (e.1, e.2) := rfl
  rw [find_eq_of_mem_nodup_fst (mkEntryParams params witness) e.1 e.2 (hpair ▸ hmem) hndKeys]
  rfl

/-! ### The headline — `agreesTagged` by construction -/

/-- **Headline — the stack-side entry agrees with the ANF entry BY
CONSTRUCTION.**

Under parameter-name distinctness, the type-directed ANF entry
`mkEntryState` and the matching stack entry `mkStackEntry` satisfy
`agreesTagged (mkTsm params)`: the tagged param-stack aligns positionally,
and `props`/`outputs` coincide (both sides share those fields).  No
hypothesis on the witness or on agreement is needed — alignment is fixed
by the shared construction over `(mkEntryParams …).reverse`. -/
theorem agreesTagged_mkEntry
    (params : List ANFParam) (propsVals : List (String × Value)) (witness : List Value)
    (hnd : (params.map ANFParam.name).Nodup) :
    agreesTagged (mkTsm params) (mkEntryState params propsVals witness)
      (mkStackEntry params propsVals witness) := by
  refine ⟨?_, rfl, rfl⟩
  -- Alignment: rewrite `mkTsm` and the stack as `.param`-map / value-map of
  -- the SAME list `sub = (mkEntryParams …).reverse`, then apply the general lemma.
  show taggedStackAligned (mkTsm params) (mkEntryState params propsVals witness)
    ((mkStackEntry params propsVals witness).stack)
  unfold mkStackEntry
  show taggedStackAligned (mkTsm params) (mkEntryState params propsVals witness)
    ((mkEntryParams params witness).reverse.map (·.2))
  -- `mkTsm params = (mkEntryParams …).reverse.map (fun e => (e.1, .param))`.
  have hTsm : mkTsm params
      = (mkEntryParams params witness).reverse.map (fun e => (e.1, SlotKind.param)) := by
    unfold mkTsm
    -- Pull `reverse` outside both maps, then compare the un-reversed maps.
    rw [List.map_reverse, List.map_reverse]
    congr 1
    -- `params.map (fun p => (p.name, .param)) = (mkEntryParams …).map (fun e => (e.1, .param))`.
    rw [show (fun e : String × Value => (e.1, SlotKind.param))
          = (fun n : String => (n, SlotKind.param)) ∘ (·.1) from rfl,
        ← List.map_map, mkEntryParams_map_fst, List.map_map]
    rfl
  rw [hTsm]
  exact taggedStackAligned_param_self (mkEntryState params propsVals witness)
    ((mkEntryParams params witness).reverse)
    (fun e he => lookupParam_mkEntryState_of_mem hnd (List.mem_reverse.mp he))

/-! ## Type-directed `entryTsmArithTyped` + `tsmCoherent` BY CONSTRUCTION
    (WS0a Task 8, piece 2b)

The wave-35 deliverable `successAgrees_arith_consume_unconditional`
(`Stack/AgreesA3.lean`) consumes, alongside the `agreesTagged` /
`hUntag` legs proved above, two further entry premises:

* `Agrees.entryTsmArithTyped Γ tsm` — every slot of the entry tagged
  stack-map is declared `.bigint` in `Γ` (the structural arith-rule
  side), and
* `Agrees.tsmCoherent anfSt tsm` — every slot reads the same value
  through its kind-specific `lookupAnfByKind` as through the
  evaluator's `resolveRef` (SSA head-correspondence).

This section discharges BOTH for the type-directed entry built by
`mkEntryState` / `mkTsm`, closing the last two §11.5-wall entry premises.

The single subtlety the task flagged — `resolveRef = lookupParam` at
entry — is resolved structurally from `State.resolveRef`'s definition
(`lookupBinding <|> lookupParam <|> lookupProp`): `mkEntryState` sets
ONLY `params`/`props`, so `bindings = []` (the structure default),
whence `lookupBinding n = none` and `resolveRef n = lookupParam n <|>
lookupProp n`.  For a parameter name `lookupParam` ALREADY succeeds
(`lookupParam_mkEntryState_of_mem`), so the `<|>` short-circuits to
`lookupParam` — params win over props *because the param leg resolves*,
NOT by any disjointness assumption.  Hence NO prop/param disjointness
hypothesis is needed even if a property shares a parameter's name. -/

/-- Membership in `mkTsm params` is exactly a `.param`-tagged parameter
name: `s ∈ mkTsm params ↔ ∃ p ∈ params, s = (p.name, .param)`.  (The
internal `params.reverse` is erased by `List.mem_reverse`.) -/
theorem mem_mkTsm {params : List ANFParam} {s : String × SlotKind}
    (hs : s ∈ mkTsm params) :
    ∃ p : ANFParam, p ∈ params ∧ s = (p.name, SlotKind.param) := by
  unfold mkTsm at hs
  rw [List.mem_map] at hs
  obtain ⟨p, hpMem, hpe⟩ := hs
  exact ⟨p, List.mem_reverse.mp hpMem, hpe.symm⟩

/-- **`resolveRef = lookupParam` at entry (for a parameter).**  Because
`mkEntryState` has no bindings, and a parameter name resolves under
`lookupParam`, the evaluator's `resolveRef` returns exactly the param
slot — regardless of any property of the same name (the param `<|>` leg
short-circuits before the prop leg is consulted). -/
theorem resolveRef_eq_lookupParam_mkEntryState
    {params : List ANFParam} {propsVals : List (String × Value)} {witness : List Value}
    (hnd : (params.map ANFParam.name).Nodup)
    {p : ANFParam} (hp : p ∈ params) :
    (mkEntryState params propsVals witness).resolveRef p.name
      = (mkEntryState params propsVals witness).lookupParam p.name := by
  -- `p` keys a concrete slot of `mkEntryParams`, so `lookupParam p.name = some _`.
  obtain ⟨i, hpi⟩ := mem_zipIdx_of_mem params p 0 hp
  have hMemMk : (p.name, coerceToType p.type (witness.getD i default))
      ∈ mkEntryParams params witness := by
    unfold mkEntryParams; rw [List.mem_map]; exact ⟨(p, i), hpi, rfl⟩
  have hLP : (mkEntryState params propsVals witness).lookupParam p.name
      = some (coerceToType p.type (witness.getD i default)) :=
    lookupParam_mkEntryState_of_mem hnd hMemMk
  -- Both sides equal `some (coerceToType …)`: the RHS by `hLP`; the LHS because
  -- `mkEntryState` has empty `bindings`, so `lookupBinding = none` and the
  -- `none <|> some _ <|> _` of `resolveRef` reduces (definitionally) to `some _`.
  rw [hLP]
  show (mkEntryState params propsVals witness).resolveRef p.name
    = some (coerceToType p.type (witness.getD i default))
  unfold State.resolveRef State.lookupBinding mkEntryState
  -- `lookupBinding` over `[]` is `none`; rewriting the param leg via `hLP` then
  -- collapses the orElse chain by `rfl`.
  simp only [List.find?_nil, Option.map_none]
  show (none <|> (mkEntryState params propsVals witness).lookupParam p.name <|>
      (mkEntryState params propsVals witness).lookupProp p.name)
    = some (coerceToType p.type (witness.getD i default))
  rw [hLP]; rfl

/-- **Piece 2b (1) — `entryTsmArithTyped` by construction.**  When every
parameter is declared `.bigint`, the type-directed entry's tagged
stack-map `mkTsm params` is `entryTsmArithTyped` over the method's typing
context `ofParamsProps props params`: each slot `(p.name, .param)` looks
up to `some .bigint` (via `ofParamsProps_lookup_param` + the all-bigint
hypothesis).  This is the structural arith-rule premise the wave-35
deliverable consumes. -/
theorem entryTsmArithTyped_mkEntry
    (props : List ANFProperty) (params : List ANFParam)
    (hnd : (params.map ANFParam.name).Nodup)
    (hAllBigint : ∀ p ∈ params, p.type = ANFType.bigint) :
    entryTsmArithTyped (TypeEnv.ofParamsProps props params) (mkTsm params) := by
  intro s hs
  obtain ⟨p, hp, hse⟩ := mem_mkTsm hs
  -- `arithOperandBigint Γ s.fst` is `Γ.lookup s.fst = some .bigint`; `s.fst = p.name`.
  show (TypeEnv.ofParamsProps props params).lookup s.fst = some ANFType.bigint
  rw [hse]
  show (TypeEnv.ofParamsProps props params).lookup p.name = some ANFType.bigint
  rw [ofParamsProps_lookup_param props params hnd hp, hAllBigint p hp]

/-- **Piece 2b (2) — `tsmCoherent` by construction.**  The type-directed
entry's tagged stack-map is coherent with the entry state: every slot
`(p.name, .param)` reads the same value through `lookupAnfByKind` (which
IS `lookupParam` for a `.param` slot) as through `resolveRef`
(`resolveRef_eq_lookupParam_mkEntryState`).  No hypothesis beyond
parameter-name distinctness — in particular NO prop/param disjointness,
since the param leg of `resolveRef` short-circuits. -/
theorem tsmCoherent_mkEntry
    (props : List ANFProperty) (params : List ANFParam)
    (propsVals : List (String × Value)) (witness : List Value)
    (hnd : (params.map ANFParam.name).Nodup) :
    tsmCoherent (mkEntryState params propsVals witness) (mkTsm params) := by
  intro s hs
  obtain ⟨p, hp, hse⟩ := mem_mkTsm hs
  subst hse
  -- `lookupAnfByKind (p.name, .param) = lookupParam p.name`; equate to `resolveRef`.
  show lookupAnfByKind (mkEntryState params propsVals witness) (p.name, SlotKind.param)
    = (mkEntryState params propsVals witness).resolveRef p.name
  unfold lookupAnfByKind
  exact (resolveRef_eq_lookupParam_mkEntryState hnd hp).symm

/-- **Piece 2b (3) — corollary: `taggedAllBigint` at the type-directed
entry.**  Composing piece-1 `mkEntryState_entryBigintTyped_noProps` (the
`EntryBigintTyped` leg, unconditional for a stateless contract) with the
two premises above through `Agrees.taggedAllBigint_of_entryTyped` yields
the whole entry tagged stack-map's `.vBigint` invariant — exactly what
the wave-35 inner walk needs DERIVED rather than assumed.  Holds for an
all-bigint-param stateless entry, given only parameter-name
distinctness. -/
theorem taggedAllBigint_mkEntry_noProps
    (params : List ANFParam) (propsVals : List (String × Value)) (witness : List Value)
    (hnd : (params.map ANFParam.name).Nodup)
    (hAllBigint : ∀ p ∈ params, p.type = ANFType.bigint) :
    taggedAllBigint (mkEntryState params propsVals witness) (mkTsm params) :=
  taggedAllBigint_of_entryTyped (TypeEnv.ofParamsProps [] params)
    (mkEntryState params propsVals witness) (mkTsm params)
    (mkEntryState_entryBigintTyped_noProps params propsVals witness hnd)
    (tsmCoherent_mkEntry [] params propsVals witness hnd)
    (entryTsmArithTyped_mkEntry [] params hnd hAllBigint)

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

/-- **Smoke — `agreesTagged` holds via the by-construction theorem.**  On
the real smoke params/witness, the type-directed ANF entry and the
matching stack entry agree under `mkTsm smokeParams` — proved THROUGH
`agreesTagged_mkEntry`, not re-asserted. -/
theorem smoke_agreesTagged_mkEntry :
    agreesTagged (mkTsm smokeParams) (mkEntryState smokeParams [] smokeWitness)
      (mkStackEntry smokeParams [] smokeWitness) :=
  agreesTagged_mkEntry smokeParams [] smokeWitness smoke_params_nodup

/-- **Smoke — `hUntag` holds concretely.**  `untagSm (mkTsm smokeParams)`
reduces to the reversed parameter-name list `["f", "a"]`, confirming the
`untagSm_mkTsm` shape fires on real data (the stack-order `StackMap`). -/
example : untagSm (mkTsm smokeParams) = (["f", "a"] : Stack.Lower.StackMap) := by decide

/-- **Smoke — the stack entry is non-vacuous.**  Its stack carries the two
coerced param values in stack order (top = last param `f`'s flag, then
`a`'s number).  This is what `agreesTagged` aligns `mkTsm` against. -/
example : (mkStackEntry smokeParams [] smokeWitness).stack
    = [.vBool true, .vBigint 7] := rfl

/-! ### Piece 2b smokes

`entryTsmArithTyped` REQUIRES every param `.bigint`, so it does NOT hold
for `smokeParams` (the `f : bool` param fails the arith rule).  We use an
all-bigint params list `bigintSmokeParams = [a : bigint, b : bigint]` for
the `entryTsmArithTyped` / `taggedAllBigint` smokes; `tsmCoherent` (a pure
resolution fact, type-agnostic) fires on the existing `smokeParams`. -/

/-- All-bigint smoke params: `a : bigint`, `b : bigint` (distinct names). -/
private def bigintSmokeParams : List ANFParam :=
  [⟨"a", .bigint⟩, ⟨"b", .bigint⟩]

/-- All-bigint smoke witness. -/
private def bigintSmokeWitness : List Value :=
  [.vBigint 7, .vBigint 9]

/-- The all-bigint smoke params have distinct names. -/
theorem bigint_smoke_params_nodup : (bigintSmokeParams.map ANFParam.name).Nodup := by decide

/-- Every all-bigint smoke param is declared `.bigint`. -/
theorem bigint_smoke_allBigint :
    ∀ p ∈ bigintSmokeParams, p.type = ANFType.bigint := by decide

/-- **Smoke — `entryTsmArithTyped` holds via the by-construction theorem.**
Every slot of `mkTsm bigintSmokeParams` is declared `.bigint` in
`ofParamsProps [] bigintSmokeParams` — proved THROUGH
`entryTsmArithTyped_mkEntry`, not re-asserted. -/
theorem smoke_entryTsmArithTyped :
    entryTsmArithTyped (TypeEnv.ofParamsProps [] bigintSmokeParams)
      (mkTsm bigintSmokeParams) :=
  entryTsmArithTyped_mkEntry [] bigintSmokeParams bigint_smoke_params_nodup
    bigint_smoke_allBigint

/-- **Smoke — `tsmCoherent` holds via the by-construction theorem.**  On the
original mixed-type `smokeParams` (coherence is type-agnostic), every slot
of `mkTsm smokeParams` reads the same value through `lookupAnfByKind` as
through `resolveRef` — proved THROUGH `tsmCoherent_mkEntry`. -/
theorem smoke_tsmCoherent :
    tsmCoherent (mkEntryState smokeParams [] smokeWitness) (mkTsm smokeParams) :=
  tsmCoherent_mkEntry [] smokeParams [] smokeWitness smoke_params_nodup

/-- **Smoke — `taggedAllBigint` at the type-directed entry, via the
corollary.**  The whole entry tagged stack-map resolves to `.vBigint`s,
DERIVED (not assumed) by composing the piece-1 typed-entry with piece-2b's
two premises through `taggedAllBigint_of_entryTyped`. -/
theorem smoke_taggedAllBigint :
    taggedAllBigint (mkEntryState bigintSmokeParams [] bigintSmokeWitness)
      (mkTsm bigintSmokeParams) :=
  taggedAllBigint_mkEntry_noProps bigintSmokeParams [] bigintSmokeWitness
    bigint_smoke_params_nodup bigint_smoke_allBigint

/-! ### Stateful-contract smokes (type-directed PROPERTY slots)

A concrete STATEFUL contract: one parameter `a : bigint` and one property
`count : bigint` (the canonical counter shape), with a property
state-witness `[.vBigint 42]`.  We fire the props-bearing headline
`mkEntryState_entryBigintTyped_props` THROUGH the by-construction
machinery (NOT by re-asserting), and confirm the `count` PROPERTY slot
concretely resolves to a `.vBigint` — demonstrating the props side is
type-directed and non-vacuous (the env genuinely declares a property name
that is NOT a parameter). -/

/-- Stateful smoke params: a single `a : bigint`. -/
private def statefulSmokeParams : List ANFParam :=
  [⟨"a", .bigint⟩]

/-- Stateful smoke properties: a single mutable `count : bigint`. -/
private def statefulSmokeProps : List ANFProperty :=
  [⟨"count", .bigint, false, none⟩]

/-- Stateful smoke property state-witness (the deserialized `count`). -/
private def statefulSmokeStateWitness : List Value :=
  [.vBigint 42]

/-- Stateful smoke parameter witness. -/
private def statefulSmokeWitness : List Value :=
  [.vBigint 7]

/-- The stateful smoke params have distinct names. -/
theorem stateful_smoke_params_nodup :
    (statefulSmokeParams.map ANFParam.name).Nodup := by decide

/-- The stateful smoke properties have distinct names. -/
theorem stateful_smoke_props_nodup :
    (statefulSmokeProps.map ANFProperty.name).Nodup := by decide

/-- **Smoke — props-side `EntryPropsWellTyped` holds via the
by-construction theorem.**  The `count` property (the only non-parameter
name) is well-typed in the type-directed stateful entry — proved THROUGH
`entryPropsWellTyped_mkEntryProps`, NOT re-asserted. -/
theorem stateful_smoke_entryPropsWellTyped :
    EntryPropsWellTyped statefulSmokeProps statefulSmokeParams
      (mkEntryProps statefulSmokeProps statefulSmokeStateWitness) statefulSmokeWitness :=
  entryPropsWellTyped_mkEntryProps statefulSmokeProps statefulSmokeParams
    statefulSmokeStateWitness statefulSmokeWitness stateful_smoke_props_nodup

/-- **Smoke — stateful `EntryBigintTyped` via the props-bearing headline.**
Every `.bigint`-declared name — the parameter `a` AND the property `count`
— resolves to a `.vBigint` in the type-directed stateful entry, proved
THROUGH `mkEntryState_entryBigintTyped_props` (props hypothesis discharged
internally). -/
theorem stateful_smoke_entryBigintTyped :
    EntryBigintTyped (TypeEnv.ofParamsProps statefulSmokeProps statefulSmokeParams)
      (mkEntryState statefulSmokeParams
        (mkEntryProps statefulSmokeProps statefulSmokeStateWitness) statefulSmokeWitness) :=
  mkEntryState_entryBigintTyped_props statefulSmokeProps statefulSmokeParams
    statefulSmokeStateWitness statefulSmokeWitness
    stateful_smoke_params_nodup stateful_smoke_props_nodup

/-- **Smoke — the full stateful entry is `StateWellTyped`.** -/
theorem stateful_smoke_stateWellTyped :
    StateWellTyped (TypeEnv.ofParamsProps statefulSmokeProps statefulSmokeParams)
      (mkEntryState statefulSmokeParams
        (mkEntryProps statefulSmokeProps statefulSmokeStateWitness) statefulSmokeWitness) :=
  mkEntryState_stateWellTyped_props statefulSmokeProps statefulSmokeParams
    statefulSmokeStateWitness statefulSmokeWitness
    stateful_smoke_params_nodup stateful_smoke_props_nodup

/-- **Smoke — the `count` PROPERTY slot concretely resolves to a
`.vBigint`** (and the parameter `a` to its own `.vBigint`).  This is the
non-vacuity check: the property name is genuinely present in the entry and
carries the type-directed runtime value decoded from the state-witness. -/
example :
    (mkEntryState statefulSmokeParams
        (mkEntryProps statefulSmokeProps statefulSmokeStateWitness)
        statefulSmokeWitness).resolveRef "count" = some (.vBigint 42) ∧
    (mkEntryState statefulSmokeParams
        (mkEntryProps statefulSmokeProps statefulSmokeStateWitness)
        statefulSmokeWitness).resolveRef "a" = some (.vBigint 7) := by
  constructor <;> rfl

/-- **Smoke — props are type-directed, not pass-through.**  A `count`
state-witness of the WRONG kind (`.vBool true`) STILL coerces to a
`.vBigint` (the fallback `0`), exactly as for parameters — so
`EntryPropsWellTyped` is a theorem, not a hope about the deserialized
state. -/
example :
    (mkEntryState statefulSmokeParams
        (mkEntryProps statefulSmokeProps [.vBool true])
        statefulSmokeWitness).resolveRef "count" = some (.vBigint 0) := by
  rfl

end RunarVerification.ANF.EntryModel
