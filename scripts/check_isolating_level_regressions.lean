/-
Regression guard for the family-level isolating theorem
(`InfinitaryLogic/Scott/IsolatingLevel.lean`).

All three public theorems are *applied*, not only listed for their axioms.

* **Pure sets: the level separates exactly.**  The family `Option ℕ → Type` sending `none` to
  `ℕ` and `some n` to `Fin n`, as pure sets (the empty language).  At the level returned by
  `exists_isolating_level`, `BFEquiv0` between two members holds iff the indices are equal: the
  theorem gives `→` up to isomorphism, cardinality turns isomorphism into equality of indices,
  and reflexivity gives `←`.  In particular `ℕ` and `Fin 3`, and `Fin 2` and `Fin 3`, are not
  `BFEquiv0` at that level.
* **Negative: level `0` does not isolate the pure family.**  `ℕ` and `Fin 3` are `BFEquiv0` at
  level `0` (the empty tuple has no atomic formulas over the empty language) but are not
  isomorphic, so no isolating level of this family is `0` (`pure_level_pos`); applied to the
  level returned by `exists_isolating_level`, that level is positive
  (`pure_returned_level_pos`).
* **The empty family.**  `ι := Empty`: the theorem applies, and every level, in particular `0`,
  isolates vacuously.
* **Two isomorphic members.**  The family `Bool → Type` with `ℕ` and `ℤ` as pure sets: at the
  returned level the two members are `BFEquiv0` (isomorphic structures are back-and-forth
  equivalent at every level), and the theorem returns an isomorphism; `exists_isolating_level_iff`
  gives the `BFEquiv0` side directly.
* **A nonempty language, constant carrier.**  The code-form consumer's shape: carrier `ℕ` for
  every index, structures `S : ι → L.Structure ℕ` varying with the index, instance arguments
  passed explicitly (`constant_carrier`, generic `L`).  Concretely, over a language with one
  binary relation symbol, `ℕ` read with `≤` and with `≥` are not isomorphic and are separated at
  the returned level (`order_separated`).
* **The contrapositive.**
  - *Generic-signature plumbing check, not an uncountability test.*  `ladder_not_countable`
    applies `not_countable_of_forall_unisolated` at a generic `L : Language.{u, v}` with generic
    `Type w` carriers, to a family indexed by `{γ // γ < ω₁} × Bool` built from a hypothetical
    ladder of non-isomorphic pairs `BFEquiv0` at each `γ`.  It checks only that the hypothesis
    shape matches: its conclusion holds **without** the ladder hypothesis, as
    `ordinalIndex_not_countable` proves outright.  No concrete family with an unisolated pair at
    every countable level (unbounded back-and-forth rank) is constructed here.
  - *Concrete countable family.*  For the pure family, which is countable, the contrapositive
    shows that some level below `ω₁` has no unisolated pair.
* **A `Type 1` carrier universe.**  The pure family lifted to `ULift.{1}`, with explicit
  universes: the returned level separates `ULift ℕ` from `ULift (Fin 2)`.
* **Import closure.**  The `InfinitaryLogic` closure of the module is exactly the list
  `allowedClosure` below (`[CLOSURE DRIFT]` otherwise); it contains `Karp.PotentialIso` through
  `Scott.Sentence`, which is inherent to `Scott.RefinementCount`, and no `Descriptive`,
  `ModelTheory`, `Methods`, `Admissible`, `Conditional`, `ScottProcess` or `WIP` module
  (`[BROAD CONE]` otherwise).

Every declaration of the module (enumerated from the environment, and a fixed list that must be
present) and every declaration of this guard uses only the standard axioms.  The closure check
and the axiom audit run in one command, so the OK line is printed only when both pass.

Run with: lake env lean scripts/check_isolating_level_regressions.lean
-/
import InfinitaryLogic.Scott.IsolatingLevel

open Lean FirstOrder FirstOrder.Language

universe u v w

noncomputable section

namespace IsolatingLevelGuard

/-! ### Pure sets -/

/-- The pure family: `ℕ` at `none`, `Fin n` at `some n`. -/
def pure : Option ℕ → Type
  | none => ℕ
  | some n => Fin n

instance (i : Option ℕ) : Language.empty.Structure (pure i) := Language.emptyStructure

instance instCountablePure : ∀ i, Countable (pure i)
  | none => inferInstanceAs (Countable ℕ)
  | some n => inferInstanceAs (Countable (Fin n))

/-- Pure sets in the family are isomorphic only at equal indices. -/
theorem pure_eq_of_equiv {i j : Option ℕ} (e : pure i ≃[Language.empty] pure j) : i = j := by
  match i, j, e with
  | none, none, _ => rfl
  | none, some n, e =>
    have e' : ℕ ≃ Fin n := e.toEquiv
    have := Finite.of_equiv _ e'.symm
    exact (not_finite ℕ).elim
  | some n, none, e =>
    have e' : Fin n ≃ ℕ := e.toEquiv
    have := Finite.of_equiv _ e'
    exact (not_finite ℕ).elim
  | some _, some _, e => exact congrArg some (Fin.equiv_iff_eq.mp ⟨e.toEquiv⟩)

/-- **The level separates exactly**: at the returned level, `BFEquiv0` on the pure family is
equality of indices. -/
theorem pure_level :
    ∃ γ : Ordinal.{0}, γ < Ordinal.omega 1 ∧
      ∀ i j, BFEquiv0 (L := Language.empty) (pure i) (pure j) γ ↔ i = j := by
  obtain ⟨γ, hγ, hiso⟩ := exists_isolating_level (L := Language.empty) pure
  refine ⟨γ, hγ, fun i j ↦ ⟨fun h ↦ pure_eq_of_equiv (hiso i j h).some, ?_⟩⟩
  rintro rfl
  exact BFEquiv.refl γ _

/-- At the returned level, `ℕ` is separated from `Fin 3` and `Fin 2` from `Fin 3`. -/
theorem pure_separated :
    ∃ γ : Ordinal.{0}, γ < Ordinal.omega 1 ∧
      ¬ BFEquiv0 (L := Language.empty) (pure none) (pure (some 3)) γ ∧
      ¬ BFEquiv0 (L := Language.empty) (pure (some 2)) (pure (some 3)) γ := by
  obtain ⟨γ, hγ, h⟩ := pure_level
  exact ⟨γ, hγ, fun h' ↦ by simpa using (h _ _).mp h', fun h' ↦ by simpa using (h _ _).mp h'⟩

/-- Over the empty language, any two empty tuples have the same atomic type. -/
theorem sameAtomicType_elim0 (M N : Type) [Language.empty.Structure M]
    [Language.empty.Structure N] :
    SameAtomicType (L := Language.empty) (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) := by
  intro idx
  cases idx with
  | eq i _ => exact i.elim0
  | rel R _ => exact isEmptyElim R

/-- **Negative: level `0` does not isolate the pure family.**  `ℕ` and `Fin 3` are `BFEquiv0` at
level `0` but not isomorphic, so no isolating level of this family is `0`. -/
theorem pure_level_zero_unisolated :
    BFEquiv0 (L := Language.empty) (pure none) (pure (some 3)) (0 : Ordinal.{0}) ∧
      IsEmpty (pure none ≃[Language.empty] pure (some 3)) :=
  ⟨(BFEquiv.zero_iff_sameAtomicType _ _).mpr (sameAtomicType_elim0 _ _),
    ⟨fun e ↦ by simpa using pure_eq_of_equiv e⟩⟩

/-- Every isolating level of the pure family is positive. -/
theorem pure_level_pos :
    ∀ γ : Ordinal.{0}, (∀ i j, BFEquiv0 (L := Language.empty) (pure i) (pure j) γ →
      Nonempty (pure i ≃[Language.empty] pure j)) → 0 < γ := by
  intro γ h
  rw [pos_iff_ne_zero]
  rintro rfl
  exact pure_level_zero_unisolated.2.false (h _ _ pure_level_zero_unisolated.1).some

/-- **The returned level is positive**: `pure_level_pos` applied to the level returned by
`exists_isolating_level`. -/
theorem pure_returned_level_pos :
    ∃ γ : Ordinal.{0}, γ < Ordinal.omega 1 ∧ 0 < γ ∧
      ∀ i j, BFEquiv0 (L := Language.empty) (pure i) (pure j) γ →
        Nonempty (pure i ≃[Language.empty] pure j) := by
  obtain ⟨γ, hγ, h⟩ := exists_isolating_level (L := Language.empty) pure
  exact ⟨γ, hγ, pure_level_pos γ h, h⟩

/-! ### The empty family -/

/-- **The empty family**: the theorem applies, and level `0` isolates it vacuously. -/
theorem empty_family (M : Empty → Type) [∀ i, Language.empty.Structure (M i)]
    [∀ i, Countable (M i)] :
    (∃ γ : Ordinal.{0}, γ < Ordinal.omega 1 ∧
      ∀ i j, BFEquiv0 (L := Language.empty) (M i) (M j) γ →
        Nonempty (M i ≃[Language.empty] M j)) ∧
      ∀ i j, BFEquiv0 (L := Language.empty) (M i) (M j) (0 : Ordinal.{0}) →
        Nonempty (M i ≃[Language.empty] M j) :=
  ⟨exists_isolating_level M, fun i ↦ i.elim⟩

/-- A concrete empty family. -/
def emptyFam (_ : Empty) : Type := ℕ

instance (i : Empty) : Language.empty.Structure (emptyFam i) := Language.emptyStructure

instance (i : Empty) : Countable (emptyFam i) := inferInstanceAs (Countable ℕ)

/-- The empty family, concretely. -/
theorem empty_family_concrete :
    ∃ γ : Ordinal.{0}, γ < Ordinal.omega 1 ∧
      ∀ i j, BFEquiv0 (L := Language.empty) (emptyFam i) (emptyFam j) γ →
        Nonempty (emptyFam i ≃[Language.empty] emptyFam j) :=
  (empty_family emptyFam).1

/-! ### Two isomorphic members -/

/-- The family `ℕ`, `ℤ` as pure sets. -/
def twoInf : Bool → Type
  | false => ℕ
  | true => ℤ

instance (b : Bool) : Language.empty.Structure (twoInf b) := Language.emptyStructure

instance instCountableTwoInf : ∀ b, Countable (twoInf b)
  | false => inferInstanceAs (Countable ℕ)
  | true => inferInstanceAs (Countable ℤ)

/-- `ℕ` and `ℤ` are isomorphic pure sets. -/
def natIntEquiv : twoInf false ≃[Language.empty] twoInf true :=
  { toEquiv := (Equiv.intEquivNat).symm }

/-- **Two isomorphic members**: at the returned level they are `BFEquiv0`, and the theorem
returns an isomorphism. -/
theorem iso_members :
    ∃ γ : Ordinal.{0}, γ < Ordinal.omega 1 ∧
      BFEquiv0 (L := Language.empty) (twoInf false) (twoInf true) γ ∧
      Nonempty (twoInf false ≃[Language.empty] twoInf true) := by
  obtain ⟨γ, hγ, hiso⟩ := exists_isolating_level (L := Language.empty) twoInf
  have hbf : BFEquiv0 (L := Language.empty) (twoInf false) (twoInf true) γ := by
    simpa only [comp_fin_elim0] using equiv_implies_BFEquiv natIntEquiv γ 0 Fin.elim0
  exact ⟨γ, hγ, hbf, hiso false true hbf⟩

/-- **Both directions at the returned level**: `exists_isolating_level_iff` on the isomorphic
members gives `BFEquiv0` at its level from the isomorphism. -/
theorem iso_members_iff :
    ∃ γ : Ordinal.{0}, γ < Ordinal.omega 1 ∧
      BFEquiv0 (L := Language.empty) (twoInf false) (twoInf true) γ := by
  obtain ⟨γ, hγ, h⟩ := exists_isolating_level_iff (L := Language.empty) twoInf
  exact ⟨γ, hγ, (h false true).mpr ⟨natIntEquiv⟩⟩

/-! ### A nonempty language, constant carrier -/

/-- **The code-form consumer's shape**: constant carrier `ℕ`, structures varying with the index,
instance arguments passed explicitly, over a generic countable relational language. -/
theorem constant_carrier {ι : Type} [Countable ι] {L : Language.{u, v}} [L.IsRelational]
    [Countable (Σ l, L.Relations l)] (S : ι → L.Structure ℕ) :
    ∃ γ : Ordinal.{0}, γ < Ordinal.omega 1 ∧
      ∀ i j, @BFEquiv0 L ℕ ℕ (S i) (S j) γ → Nonempty (@Language.Equiv L ℕ ℕ (S i) (S j)) :=
  @exists_isolating_level L _ _ ι _ (fun _ ↦ ℕ) S (fun _ ↦ inferInstance)

/-- One binary relation symbol. -/
inductive LeRel : ℕ → Type
  | le : LeRel 2

/-- The language with one binary relation symbol and no function symbols. -/
def leLang : Language.{0, 0} := ⟨fun _ ↦ Empty, LeRel⟩

instance : leLang.IsRelational := fun _ ↦ inferInstanceAs (IsEmpty Empty)

instance : Countable (Σ l, leLang.Relations l) :=
  Function.Injective.countable (f := fun x : Σ l, LeRel l ↦ x.1)
    (by rintro ⟨_, ⟨⟩⟩ ⟨_, ⟨⟩⟩ _; rfl)

/-- `ℕ` with the relation symbol read as `≤` (`false`) or as `≥` (`true`). -/
@[instance_reducible]
def ordS (b : Bool) : leLang.Structure ℕ where
  RelMap
    | LeRel.le, x => if b then x 1 ≤ x 0 else x 0 ≤ x 1

/-- `(ℕ, ≤)` and `(ℕ, ≥)` are not isomorphic: an isomorphism would send `0` to a greatest
element. -/
theorem ordS_not_equiv : IsEmpty (@Language.Equiv leLang ℕ ℕ (ordS false) (ordS true)) := by
  refine ⟨fun e ↦ ?_⟩
  have key : ∀ x y : ℕ, x ≤ y ↔ e y ≤ e x := fun x y ↦
    (@Language.Equiv.map_rel leLang ℕ ℕ (ordS false) (ordS true) e 2 LeRel.le ![x, y]).symm
  let f : ℕ ≃ ℕ := @Language.Equiv.toEquiv leLang ℕ ℕ (ordS false) (ordS true) e
  have hf : ∀ x, f x = e x := fun _ ↦ rfl
  have h := (key 0 (f.symm (e 0 + 1))).mp (Nat.zero_le _)
  rw [← hf, Equiv.apply_symm_apply] at h
  omega

/-- **A nonempty language**: the returned level separates `(ℕ, ≤)` from `(ℕ, ≥)`, and identifies
each with itself. -/
theorem order_separated :
    ∃ γ : Ordinal.{0}, γ < Ordinal.omega 1 ∧
      ¬ @BFEquiv0 leLang ℕ ℕ (ordS false) (ordS true) γ ∧
      @BFEquiv0 leLang ℕ ℕ (ordS true) (ordS true) γ := by
  obtain ⟨γ, hγ, h⟩ := @exists_isolating_level_iff leLang _ _ Bool _ (fun _ ↦ ℕ) ordS
    (fun _ ↦ inferInstance)
  exact ⟨γ, hγ, fun hb ↦ ordS_not_equiv.false ((h false true).mp hb).some,
    (h true true).mpr ⟨@Language.Equiv.refl leLang ℕ (ordS true)⟩⟩

/-! ### The contrapositive -/

/-- **The index of the plumbing check is uncountable outright**, with no ladder: a countable set
of countable ordinals has a countable supremum, which is not above its own successor. -/
theorem ordinalIndex_not_countable :
    ¬ Countable ({γ : Ordinal.{0} // γ < Ordinal.omega 1} × Bool) := by
  intro h
  have : Countable {γ : Ordinal.{0} // γ < Ordinal.omega 1} :=
    Function.Injective.countable (f := fun x ↦ (x, false)) (fun a b hab ↦ by simpa using hab)
  have hs : ∀ x : {γ : Ordinal.{0} // γ < Ordinal.omega 1}, Order.succ x.1 < Ordinal.omega 1 :=
    fun x ↦ (Cardinal.isSuccLimit_omega 1).succ_lt x.2
  have hle := Ordinal.le_iSup (fun x : {γ : Ordinal.{0} // γ < Ordinal.omega 1} ↦
    Order.succ x.1) ⟨_, Ordinal.iSup_lt_omega_one hs⟩
  exact (Order.lt_succ _).not_ge hle

/-- **Generic-signature plumbing check, not an uncountability test.**  Applies
`not_countable_of_forall_unisolated` at a generic `L` and generic `Type w` carriers, to a family
built from a hypothetical ladder of non-isomorphic pairs that are `BFEquiv0` at each countable
level.  It checks only that the hypothesis shape matches: the conclusion holds without `hP`
(`ordinalIndex_not_countable`). -/
theorem ladder_not_countable {L : Language.{u, v}} [L.IsRelational]
    [Countable (Σ l, L.Relations l)] (P : Ordinal.{0} → Bool → Type w)
    [∀ γ b, L.Structure (P γ b)] [∀ γ b, Countable (P γ b)]
    (hP : ∀ γ : Ordinal.{0}, γ < Ordinal.omega 1 →
      BFEquiv0 (L := L) (P γ false) (P γ true) γ ∧ IsEmpty (P γ false ≃[L] P γ true)) :
    ¬ Countable ({γ : Ordinal.{0} // γ < Ordinal.omega 1} × Bool) :=
  not_countable_of_forall_unisolated (L := L) (fun x ↦ P x.1.1 x.2) fun γ hγ ↦
    ⟨(⟨γ, hγ⟩, false), (⟨γ, hγ⟩, true), hP γ hγ⟩

/-- **Concrete countable family**: on the pure family, some level below `ω₁` has no unisolated
pair, by the contrapositive. -/
theorem pure_not_forall_unisolated :
    ¬ ∀ γ : Ordinal.{0}, γ < Ordinal.omega 1 →
      ∃ i j, BFEquiv0 (L := Language.empty) (pure i) (pure j) γ ∧
        IsEmpty (pure i ≃[Language.empty] pure j) := fun h ↦
  not_countable_of_forall_unisolated (L := Language.empty) pure h inferInstance

/-! ### A `Type 1` carrier universe -/

/-- The pure family lifted to `Type 1`. -/
def pureLift (i : Option ℕ) : Type 1 := ULift.{1} (pure i)

instance (i : Option ℕ) : Language.empty.Structure (pureLift i) := Language.emptyStructure

instance (i : Option ℕ) : Countable (pureLift i) := inferInstanceAs (Countable (ULift (pure i)))

/-- **`Type 1` carriers**, explicit universes: the returned level separates `ULift ℕ` from
`ULift (Fin 2)`. -/
theorem lift_separated :
    ∃ γ : Ordinal.{0}, γ < Ordinal.omega 1 ∧
      ¬ BFEquiv0 (L := Language.empty) (pureLift none) (pureLift (some 2)) γ := by
  obtain ⟨γ, hγ, hiso⟩ :=
    exists_isolating_level.{0, 0, 1, 0} (L := Language.empty) (ι := Option ℕ) pureLift
  refine ⟨γ, hγ, fun h ↦ ?_⟩
  obtain ⟨e⟩ := hiso none (some 2) h
  have : pure none ≃[Language.empty] pure (some 2) :=
    { toEquiv := Equiv.ulift.symm.trans (e.toEquiv.trans Equiv.ulift) }
  simpa using pure_eq_of_equiv this

end IsolatingLevelGuard

/-! ### Import closure and axiom audit -/

/-- The modules transitively imported by `m` (including `m`), read from the environment
header. -/
partial def importClosure (env : Environment) (m : Name) : NameSet :=
  go [m] {}
where
  go : List Name → NameSet → NameSet
    | [], seen => seen
    | m :: rest, seen =>
      if seen.contains m then go rest seen
      else
        let deps := match env.getModuleIdx? m with
          | some idx => (env.header.moduleData[idx.toNat]!).imports.toList.map (·.module)
          | none => []
        go (deps ++ rest) (seen.insert m)

/-- Module-name prefixes no module of the closure may have. -/
def forbiddenPrefixes : List Name :=
  [`InfinitaryLogic.ScottProcess, `InfinitaryLogic.Descriptive, `InfinitaryLogic.Methods,
   `InfinitaryLogic.ModelTheory, `InfinitaryLogic.Admissible, `InfinitaryLogic.Conditional,
   `InfinitaryLogic.WIP]

/-- The exact `InfinitaryLogic` closure of the module: `Karp.PotentialIso` enters through
`Scott.Sentence`, inherently to `Scott.RefinementCount`. -/
def allowedClosure : List Name :=
  [`InfinitaryLogic.Scott.IsolatingLevel, `InfinitaryLogic.Scott.RefinementCount,
   `InfinitaryLogic.Scott.Sentence, `InfinitaryLogic.Scott.Formula,
   `InfinitaryLogic.Scott.BackAndForth, `InfinitaryLogic.Scott.AtomicDiagram,
   `InfinitaryLogic.Karp.PotentialIso, `InfinitaryLogic.Lomega1omega.Syntax,
   `InfinitaryLogic.Lomega1omega.Semantics, `InfinitaryLogic.Lomega1omega.Operations,
   `InfinitaryLogic.Lomega1omega.OpenBoundsSemantics, `InfinitaryLogic.OrdinalUtil,
   `InfinitaryLogic.Util]

/-- The public declarations of the module that must be present. -/
def moduleDecls : List Name :=
  [`exists_isolating_level, `exists_isolating_level_iff,
   `not_countable_of_forall_unisolated].map (`FirstOrder.Language ++ ·)

/-- The guard's own declarations whose axioms are audited. -/
def guardDecls : List Name :=
  [`pure_eq_of_equiv, `pure_level, `pure_separated, `sameAtomicType_elim0,
   `pure_level_zero_unisolated, `pure_level_pos, `pure_returned_level_pos, `empty_family,
   `emptyFam, `empty_family_concrete, `natIntEquiv, `iso_members, `iso_members_iff,
   `constant_carrier, `leLang, `ordS, `ordS_not_equiv, `order_separated,
   `ordinalIndex_not_countable, `ladder_not_countable, `pure_not_forall_unisolated,
   `lift_separated].map (`IsolatingLevelGuard ++ ·)

/-- The standard axioms. -/
def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

-- The closure check and the axiom audit run in one command, so that the final OK line is
-- printed only when both pass.
run_cmd do
  let env ← getEnv
  let target := `InfinitaryLogic.Scott.IsolatingLevel
  let some idx := env.getModuleIdx? target
    | throwError "module {target} is not in the environment"
  let cl := importClosure env target
  let ilModules := cl.toList.filter fun m ↦ (`InfinitaryLogic).isPrefixOf m
  let hits := ilModules.filter fun m ↦ forbiddenPrefixes.any (·.isPrefixOf m)
  unless hits.isEmpty do
    throwError "[BROAD CONE] the closure of {target} reaches {hits}"
  let extra := ilModules.filter fun m ↦ !allowedClosure.contains m
  let missing := allowedClosure.filter fun m ↦ !ilModules.contains m
  unless extra.isEmpty && missing.isEmpty do
    throwError "[CLOSURE DRIFT] the InfinitaryLogic closure of {target} is {ilModules}; \
      update allowedClosure deliberately (extra {extra}, missing {missing})"
  let enumerated := (env.header.moduleData[idx.toNat]!).constNames.toList
  for n in moduleDecls do
    unless enumerated.contains n do throwError "declaration {n} not found in the module"
  for n in enumerated ++ guardDecls do
    unless (env.find? n).isSome do throwError "declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a ↦ !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo m!"Isolating-level regression guard: OK (applied: on the pure family N, Fin n the \
    returned level makes BFEquiv0 equality of indices, separating N from Fin 3 and Fin 2 from \
    Fin 3, while level 0 leaves N and Fin 3 unisolated, so the returned level is positive; \
    the empty family, isolated vacuously at 0; N and Z as isomorphic members, identified at \
    the returned level, also through the iff form; the constant-carrier shape over a generic \
    language, and (N, <=) separated from (N, >=) over a one-relation language; a \
    generic-signature plumbing check of the contrapositive on a ladder-indexed family, whose \
    conclusion also holds outright without the ladder (not an uncountability test); the \
    contrapositive on the countable pure family; Type 1 carriers with explicit universes; \
    exact import closure \
    ({ilModules.length} modules) without Scott-process, descriptive, method, model-theory, \
    admissible, conditional or WIP modules; standard axioms)"
