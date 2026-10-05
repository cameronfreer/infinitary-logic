/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.BFConcentration
-- `Scott.IsolatingLevel` already imports it; listed for the instance's direct uses
-- (`stabilizationOrdinal_spec`, `stabilizationOrdinal_lt_omega1'`,
-- `stabilizationOrdinal_eq_of_equiv`)
import InfinitaryLogic.Scott.RefinementCount
import InfinitaryLogic.Scott.IsolatingLevel
import InfinitaryLogic.OrdinalCountability

/-!
# Counting isomorphism classes of a back-and-forth scattered class through an isolating rank

An **isolating rank** on the codes of countable `L`-structures (`IsIsolatingRank ρ`) is a map
`ρ : StructureSpace L → Ordinal.{0}` that is

* invariant under isomorphism (`iso_invariant`),
* below `ω₁` (`lt_omega1`), and
* isolating at its own value: `CodeBFEquiv (ρ c) c d` implies that `c` and `d` are isomorphic
  (`isolates`).

This module states that contract, instantiates it once, and derives the counting statements
from it alone.

1. **The instance.**  `codeStabilizationOrdinal c` is the stabilization ordinal of the structure
   decoded from `c`; for countably many relation symbols it is an isolating rank
   (`isIsolatingRank_codeStabilizationOrdinal`).
2. **The code form of the isolating level.**  For any isolating rank and any set `S` of codes
   meeting only countably many isomorphism classes, one level `γ < ω₁` decides isomorphism on
   `S` through `CodeBFEquiv γ` (`IsIsolatingRank.exists_isolating_codeLevel`), and the
   contrapositive (`IsIsolatingRank.not_countable_isoClasses_of_forall_unisolated`).  No
   countability of the language is used.
3. **Counting for a back-and-forth scattered class.**  For any isolating rank and any
   `K` with `BFScattered K`, each fibre of the rank on the isomorphism classes of `K` is
   countable (`IsIsolatingRank.countable_fibers`), so `K` meets at most `ℵ₁` isomorphism classes
   (`IsIsolatingRank.mk_isoClasses_le_aleph_one`), exactly `ℵ₁` when it meets uncountably many
   (`IsIsolatingRank.mk_isoClasses_eq_aleph_one`), and countably many iff the rank is bounded
   below `ω₁` on `K` (`IsIsolatingRank.countable_isoClasses_iff_bounded`).  These are
   applications of `OrdinalCountability` to the lifted rank on classes.

## Main declarations

* `IsIsolatingRank`, with `IsIsolatingRank.isolates_of_le`, `IsIsolatingRank.lift`,
  `IsIsolatingRank.lift_mk`, `IsIsolatingRank.lift_lt_omega1` and `IsIsolatingRank.of_le`.
* `IsIsolatingRank.exists_unbounded_of_not_countable` (inflation) and
  `IsIsolatingRank.exists_bound_of_countable`, both with no scatteredness.
* `codeStabilizationOrdinal`, `codeStabilizationOrdinal_def`, `codeStabilizationOrdinal_congr`,
  `isIsolatingRank_codeStabilizationOrdinal`.
* `IsIsolatingRank.exists_isolating_codeLevel`,
  `IsIsolatingRank.not_countable_isoClasses_of_forall_unisolated`, and the bridge
  `exists_isolating_codeLevel_of_family`.
* `IsIsolatingRank.countable_fiber` (one level), `IsIsolatingRank.countable_fibers`,
  `IsIsolatingRank.mk_isoClasses_le_aleph_one`,
  `IsIsolatingRank.mk_isoClasses_eq_aleph_one`, `IsIsolatingRank.countable_isoClasses_iff_bounded`.

## The contract is abstract

* **Three fields only.**  Countable fibres and "countable iff bounded" are *conclusions*
  (`IsIsolatingRank.countable_fibers`, `IsIsolatingRank.countable_isoClasses_iff_bounded`, both
  under `BFScattered K`), not fields of the contract.
* **The contract does not pin the rank.**  `IsIsolatingRank.of_le`: any isomorphism-invariant
  map below `ω₁` lying above an isolating rank is again one.  So the contract has many instances
  (the regression guard exhibits `Order.succ ∘ codeStabilizationOrdinal`, different from the
  instance at every code), every result derived here from the contract applies to each of them,
  and no least isolating rank is asserted.
* **Off countably many classes, the contract does not pin boundedness either.**
  `IsIsolatingRank.exists_unbounded_of_not_countable`: on a set meeting uncountably many
  isomorphism classes, every isolating rank lies below one that is unbounded below `ω₁` there.
  Countably many classes always give a bound (`IsIsolatingRank.exists_bound_of_countable`).  So
  boundedness is rank-independent on such a set exactly when no isolating rank is bounded on it
  (`boundedRankOn_rankIndependent_iff`, proved in
  `scripts/check_minimally_unbounded_regressions.lean`); `BFScattered` forces that
  (`countable_isoClasses_iff_bounded`).  The same guard exhibits a class that is not
  back-and-forth scattered and carries a bounded and an unbounded isolating rank
  (`bfScattered_necessary`).
* **`codeStabilizationOrdinal` is not the least isolating level among codes.**  The
  stabilization ordinal of `c` is the least `α` with `StabilizesAt c α`, and `StabilizesAt`
  quantifies over *all* countable structures `N`, not only over codes; nothing here says that
  it is the least level `α` at which `CodeBFEquiv α c` decides isomorphism with `c` among
  codes.
* **No Scott-rank convention.**  Neither the contract nor the instance is identified with the
  Scott rank of any structure under any convention, or with an internal orbit rank; no
  comparison theorem is stated.

## Where countability of the language enters

`[Countable (Σ l, L.Relations l)]` occurs in exactly two declarations of this module:
`isIsolatingRank_codeStabilizationOrdinal`, through `stabilizationOrdinal_lt_omega1'` and
`stabilizationOrdinal_spec`, and the bridge `exists_isolating_codeLevel_of_family`, through
`exists_isolating_level`.  `codeStabilizationOrdinal`, its congruence lemma, the contract, the
code form of the isolating level and the counting statements are proved for every relational
`Language.{u, v}`.  That countability is necessary for the instance is not claimed, and no
isolating rank is exhibited for uncountably many relation symbols: there the contract's
consequences hold for any isolating rank one is given.

## A countable family of representatives, not a countable set of codes

One isomorphism class of countable structures is presented by uncountably many codes, so a set
of codes meeting countably many isomorphism classes can be uncountable.  The code form of the
isolating level is stated for such sets: its hypothesis is that `Quotient.mk _ '' S` is
countable, not that `S` is.

* **Primary: from the contract.**  `IsIsolatingRank.exists_isolating_codeLevel` takes the level
  to be the supremum of the lifted rank over the countably many classes of `S`.  It uses only
  the contract, so it holds for every relational language.
* **Bridge: through the family form.**  `exists_isolating_codeLevel_of_family` derives the same
  statement from `exists_isolating_level` (`Scott/IsolatingLevel.lean`), applied to the
  countable family of chosen representatives `Quotient.out q` of the classes `q` of `S`, and
  transfers the level back to arbitrary codes of `S` through `CodeBFEquiv.of_iso`.  It needs
  countably many relation symbols (the hypothesis of the family form) and exists only to show
  that the family form in the Scott layer and the code form here agree; nothing else in this
  module depends on it.

## Interpretation choices

* **Arbitrary classes.**  The counting statements are for an arbitrary set `K` of codes with
  `BFScattered K`, with no analyticity, Borel or invariance hypothesis on `K`, and for an
  arbitrary isolating rank.
* **No `ModelsOf` specialisation.**  The counting statements are not restated for the models
  of a sentence; for those, the `ℵ₁` bound `mk_isoSetoid_quotient_le_aleph_one`
  (`ModelTheory/MorleyCounting.lean`) already exists, and this module neither re-derives nor
  imports it.
* **Counting isomorphism classes.**  The classes of `K` are `Quotient.mk (structureIsoSetoid L)
  '' K`, counted with `Set.Countable` and `Cardinal.mk`; no measurable structure is put on the
  quotient.  Levels are `Ordinal.{0}` below `Ordinal.omega 1`, with no lift and no offset, and
  the level-`α` relation is this library's `CodeBFEquiv α`.

## Proofs

* **`countable_fiber`** (one level; `countable_fibers` applies it at every level).  Choose a
  representative `r q ∈ K` of each class `q` of `K`.  On the fibre over `α`, send `q` to the
  `CodeBFEquiv α`-class of `r q` within `K`.  This is injective: equal images give
  `CodeBFEquiv α (r q) (r q')` at `α = ρ (r q)`, hence `r q ≅ r q'` by `isolates`.  So the
  fibre injects into the level-`α` quotient of `K`, which is countable by hypothesis (by
  `BFScattered K` in `countable_fibers`).
* **The cardinal and boundedness statements** are `mk_le_aleph_one_of_countable_fibers`,
  `mk_eq_aleph_one_of_countable_fibers` and `countable_iff_rank_bounded` from
  `OrdinalCountability`, applied to the lifted rank on the classes of `K`.
* **`codeStabilizationOrdinal_congr`** is `stabilizationOrdinal_eq_of_equiv`
  (`Scott/RefinementCount.lean`), which needs no countability.

## Scope

* No least isolating level, no Scott-rank convention, no `ModelsOf` specialisation.
* **Non-vacuity is not shown.**  No class with `BFScattered K` and uncountably many isomorphism
  classes is exhibited here.
* The Silver-side statement that a thin sentence has back-and-forth scattered models is in
  `Conditional/BFScatteredSilver.lean`; it does not use an isolating rank and does not import
  this module, and this module imports nothing from `Conditional`.

## References

* M. Morley, "The number of countable models", *J. Symbolic Logic* 35 (1970), 14–18 (the
  counting argument: a rank below `ω₁` with countable fibres bounds the number of classes by
  `ℵ₁`, and boundedness of the rank gives countably many).
* A. Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, draft, Chapter XII,
  §XII.1 (scattered sentences: countably many classes at every countable level).

The composition was offered for upstreaming by a consumer of this library.
-/

universe u v

open Cardinal Set

namespace FirstOrder.Language

section Contract

variable {L : Language.{u, v}} [L.IsRelational]

/-! ### The contract -/

/-- **An isolating rank on codes.**  A map `ρ` from codes to `Ordinal.{0}` that is invariant
under isomorphism, takes values below `ω₁`, and isolates at its own value: `CodeBFEquiv (ρ c)`
between `c` and `d` implies that they are isomorphic.

Countable fibres on a back-and-forth scattered class and "countable iff bounded" are theorems
(`IsIsolatingRank.countable_fibers`, `IsIsolatingRank.countable_isoClasses_iff_bounded`), not
fields.  The contract does not determine the rank (`IsIsolatingRank.of_le`). -/
structure IsIsolatingRank (ρ : StructureSpace L → Ordinal.{0}) : Prop where
  /-- Isomorphic codes have the same rank. -/
  iso_invariant : ∀ ⦃c d : StructureSpace L⦄, (structureIsoSetoid L).r c d → ρ c = ρ d
  /-- The rank is a countable ordinal. -/
  lt_omega1 : ∀ c, ρ c < Ordinal.omega 1
  /-- Back-and-forth equivalence at the rank of `c` decides isomorphism with `c`. -/
  isolates : ∀ ⦃c d : StructureSpace L⦄, CodeBFEquiv (ρ c) c d → (structureIsoSetoid L).r c d

/-- An uncountable set maps onto the countable ordinals: some `f` with values below `ω₁` takes
every value `β < ω₁` at a point of `S` (`¬ S.Countable` gives `ℵ₁ ≤ #S`, hence an embedding of
`(ω₁).ToType` into `S`). -/
private theorem exists_onto_omega_one_of_not_countable {α : Type*} {S : Set α}
    (hS : ¬ S.Countable) :
    ∃ f : α → Ordinal.{0}, (∀ x, f x < Ordinal.omega 1) ∧
      ∀ β < Ordinal.omega 1, ∃ x ∈ S, f x = β := by
  classical
  have h1 : Cardinal.lift (Cardinal.mk (Ordinal.omega.{0} 1).ToType) ≤
      Cardinal.lift.{0} (Cardinal.mk S) := by
    rw [Cardinal.mk_toType, Ordinal.card_omega, Cardinal.lift_aleph, Cardinal.lift_uzero,
      Ordinal.lift_one, Cardinal.aleph_one_le_iff, ← not_le,
      Cardinal.le_aleph0_iff_set_countable]
    exact hS
  obtain ⟨e⟩ := Cardinal.lift_mk_le'.mp h1
  let f : α → Ordinal.{0} := fun x ↦
    if h : ∃ t, (e t : α) = x then
      Ordinal.typein (α := (Ordinal.omega.{0} 1).ToType) (· < ·) h.choose
    else 0
  refine ⟨f, fun x ↦ ?_, fun β hβ ↦ ?_⟩
  · simp only [f]
    split_ifs
    · exact Ordinal.typein_lt_self _
    · exact Ordinal.omega_pos 1
  · have hβ' : β < Ordinal.type (α := (Ordinal.omega.{0} 1).ToType) (· < ·) := by
      rwa [Ordinal.type_toType]
    let t := Ordinal.enum (α := (Ordinal.omega.{0} 1).ToType) (· < ·) ⟨β, hβ'⟩
    refine ⟨e t, (e t).2, ?_⟩
    have h : ∃ t', (e t' : α) = e t := ⟨t, rfl⟩
    have ht : h.choose = t := e.injective (Subtype.ext h.choose_spec)
    simp only [f, h, ↓reduceDIte, ht, t]
    exact Ordinal.typein_enum _ hβ'

namespace IsIsolatingRank

variable {ρ : StructureSpace L → Ordinal.{0}} {K : Set (StructureSpace L)}

/-- An isolating rank isolates at every level at or above its value. -/
theorem isolates_of_le (hρ : IsIsolatingRank ρ) {c d : StructureSpace L} {γ : Ordinal.{0}}
    (hγ : ρ c ≤ γ) (h : CodeBFEquiv γ c d) : (structureIsoSetoid L).r c d :=
  hρ.isolates (CodeBFEquiv.monotone hγ h)

/-- The rank of an isomorphism class. -/
noncomputable def lift (hρ : IsIsolatingRank ρ) : Quotient (structureIsoSetoid L) → Ordinal.{0} :=
  Quotient.lift ρ fun _ _ h ↦ hρ.iso_invariant h

@[simp] theorem lift_mk (hρ : IsIsolatingRank ρ) (c : StructureSpace L) :
    hρ.lift (Quotient.mk _ c) = ρ c := rfl

/-- The rank of an isomorphism class is a countable ordinal. -/
theorem lift_lt_omega1 (hρ : IsIsolatingRank ρ) (q : Quotient (structureIsoSetoid L)) :
    hρ.lift q < Ordinal.omega 1 :=
  Quotient.inductionOn q hρ.lt_omega1

/-- **The contract does not determine the rank.**  An isomorphism-invariant map below `ω₁` that
lies above an isolating rank is again an isolating rank. -/
theorem of_le (hρ : IsIsolatingRank ρ) {ρ' : StructureSpace L → Ordinal.{0}}
    (hle : ∀ c, ρ c ≤ ρ' c)
    (hinv : ∀ ⦃c d : StructureSpace L⦄, (structureIsoSetoid L).r c d → ρ' c = ρ' d)
    (hlt : ∀ c, ρ' c < Ordinal.omega 1) : IsIsolatingRank ρ' :=
  ⟨hinv, hlt, fun _ _ h ↦ hρ.isolates_of_le (hle _) h⟩

/-- **Boundedness is not pinned off countably many classes either.**  On a set `K` meeting
uncountably many isomorphism classes, every isolating rank lies below an isolating rank that is
unbounded below `ω₁` on `K`: take `max ρ (f ∘ Quotient.mk _)` with `f` a map of the classes onto
the countable ordinals, and apply `of_le`.  No scatteredness and no countability of the language
is assumed; under `BFScattered K` the counting statements below make every isolating rank
unbounded on such a `K`, so the comparison of boundedness across isolating ranks holds there.
The conclusion is the shape of `UnboundedRankOn ρ' K` (`Descriptive/MinimallyUncountable.lean`). -/
theorem exists_unbounded_of_not_countable (hρ : IsIsolatingRank ρ)
    (hK : ¬ (Quotient.mk (structureIsoSetoid L) '' K).Countable) :
    ∃ ρ' : StructureSpace L → Ordinal.{0}, IsIsolatingRank ρ' ∧ (∀ c, ρ c ≤ ρ' c) ∧
      ∀ β < Ordinal.omega 1, ∃ c ∈ K, β ≤ ρ' c := by
  obtain ⟨f, hf, hsurj⟩ := exists_onto_omega_one_of_not_countable hK
  refine ⟨fun c ↦ max (ρ c) (f (Quotient.mk _ c)), hρ.of_le (fun c ↦ le_max_left _ _)
    (fun c d h ↦ by simp only [hρ.iso_invariant h, Quotient.sound h])
    (fun c ↦ max_lt (hρ.lt_omega1 c) (hf _)), fun c ↦ le_max_left _ _, fun β hβ ↦ ?_⟩
  obtain ⟨_, ⟨c, hc, rfl⟩, hcβ⟩ := hsurj β hβ
  exact ⟨c, hc, hcβ ▸ le_max_right _ _⟩

/-- **Countably many classes give a bound**, for any isolating rank and any set of codes, with
no scatteredness: the supremum of the rank over the countably many classes of `K` is below `ω₁`.
This is the forward direction of `countable_isoClasses_iff_bounded` without `BFScattered`.  The
conclusion is the shape of `BoundedRankOn ρ K` (`Descriptive/MinimallyUncountable.lean`). -/
theorem exists_bound_of_countable (hρ : IsIsolatingRank ρ)
    (hK : (Quotient.mk (structureIsoSetoid L) '' K).Countable) :
    ∃ β < Ordinal.omega 1, ∀ c ∈ K, ρ c < β := by
  have := hK.to_subtype
  let f : ↥(Quotient.mk (structureIsoSetoid L) '' K) → Ordinal.{0} := fun q ↦ hρ.lift q.1
  refine ⟨Order.succ (⨆ q, f q), (Cardinal.isSuccLimit_omega 1).succ_lt
    (Ordinal.iSup_lt_omega_one fun q ↦ hρ.lift_lt_omega1 q.1), fun c hc ↦ ?_⟩
  exact Order.lt_succ_iff.mpr
    (le_ciSup (f := f) Ordinal.bddAbove_of_small ⟨Quotient.mk _ c, c, hc, rfl⟩)

/-! ### The code form of the isolating level -/

/-- **A countable isolating level for a set of codes meeting countably many classes**, from any
isolating rank, with no countability of the language.  The set `S` itself may be uncountable;
the level is the supremum of the rank over the countably many classes of `S`. -/
theorem exists_isolating_codeLevel (hρ : IsIsolatingRank ρ) {S : Set (StructureSpace L)}
    (hS : (Quotient.mk (structureIsoSetoid L) '' S).Countable) :
    ∃ γ : Ordinal.{0}, γ < Ordinal.omega 1 ∧
      ∀ x ∈ S, ∀ y ∈ S, CodeBFEquiv γ x y → (structureIsoSetoid L).r x y := by
  have := hS.to_subtype
  let f : ↥(Quotient.mk (structureIsoSetoid L) '' S) → Ordinal.{0} := fun q ↦ hρ.lift q.1
  refine ⟨⨆ q, f q, Ordinal.iSup_lt_omega_one fun q ↦ hρ.lift_lt_omega1 q.1,
    fun x hx y _ h ↦ ?_⟩
  have : ρ x ≤ ⨆ q, f q :=
    le_ciSup (f := f) Ordinal.bddAbove_of_small ⟨Quotient.mk _ x, x, hx, rfl⟩
  exact hρ.isolates_of_le this h

/-- **Unisolated at every countable level forces uncountably many classes**: the contrapositive
of `exists_isolating_codeLevel`, for any isolating rank and any relational language. -/
theorem not_countable_isoClasses_of_forall_unisolated (hρ : IsIsolatingRank ρ)
    {S : Set (StructureSpace L)}
    (h : ∀ γ : Ordinal.{0}, γ < Ordinal.omega 1 →
      ∃ x ∈ S, ∃ y ∈ S, CodeBFEquiv γ x y ∧ ¬ (structureIsoSetoid L).r x y) :
    ¬ (Quotient.mk (structureIsoSetoid L) '' S).Countable := by
  intro hS
  obtain ⟨γ, hγ, hiso⟩ := hρ.exists_isolating_codeLevel hS
  obtain ⟨x, hx, y, hy, hbf, hne⟩ := h γ hγ
  exact hne (hiso x hx y hy hbf)

/-! ### Counting the isomorphism classes of a back-and-forth scattered class -/

/-- **A countable fibre from one countable level.**  If `K` has countably many
`CodeBFEquiv α`-classes, then the fibre over `α` of the rank on the isomorphism classes of `K`
is countable: it injects into the `CodeBFEquiv α`-quotient of `K`. -/
theorem countable_fiber (hρ : IsIsolatingRank ρ) {α : Ordinal.{0}}
    (hα : Countable (Quotient ((codeBFEquivSetoid L α).comap
      (Subtype.val : K → StructureSpace L)))) :
    Countable {q : ↥(Quotient.mk (structureIsoSetoid L) '' K) // hρ.lift q.1 = α} := by
  have hrep : ∀ q : ↥(Quotient.mk (structureIsoSetoid L) '' K),
      ∃ x : K, Quotient.mk (structureIsoSetoid L) x.1 = q.1 :=
    fun q ↦ let ⟨x, hx, h⟩ := q.2; ⟨⟨x, hx⟩, h⟩
  choose r hr using hrep
  refine Function.Injective.countable
    (f := fun q : {q : ↥(Quotient.mk (structureIsoSetoid L) '' K) // hρ.lift q.1 = α} ↦
      (Quotient.mk _ (r q.1) : Quotient ((codeBFEquivSetoid L α).comap
        (Subtype.val : K → StructureSpace L)))) ?_
  rintro ⟨q, hq⟩ ⟨q', hq'⟩ h
  have hbf : CodeBFEquiv α (r q).1 (r q').1 := Quotient.exact h
  have hρq : ρ (r q).1 = α := by rw [← hq, ← hr q, lift_mk]
  have hiso := hρ.isolates (hρq ▸ hbf)
  apply Subtype.ext; apply Subtype.ext
  rw [← hr q, ← hr q']
  exact Quotient.sound hiso

/-- **Countable fibres.**  On a back-and-forth scattered class `K`, each fibre of the rank on the
isomorphism classes of `K` over a countable ordinal is countable (`countable_fiber` at each
level). -/
theorem countable_fibers (hρ : IsIsolatingRank ρ) (hK : BFScattered K) :
    ∀ α < Ordinal.omega 1,
      Countable {q : ↥(Quotient.mk (structureIsoSetoid L) '' K) // hρ.lift q.1 = α} :=
  fun α hα ↦ hρ.countable_fiber (hK α hα)

/-- **At most `ℵ₁` isomorphism classes** in a back-and-forth scattered class. -/
theorem mk_isoClasses_le_aleph_one (hρ : IsIsolatingRank ρ) (hK : BFScattered K) :
    Cardinal.mk ↥(Quotient.mk (structureIsoSetoid L) '' K) ≤ Cardinal.aleph 1 :=
  InfinitaryLogic.mk_le_aleph_one_of_countable_fibers (fun q ↦ hρ.lift q.1)
    (fun q ↦ hρ.lift_lt_omega1 q.1) (hρ.countable_fibers hK)

/-- **Exactly `ℵ₁` isomorphism classes** in a back-and-forth scattered class meeting uncountably
many. -/
theorem mk_isoClasses_eq_aleph_one (hρ : IsIsolatingRank ρ) (hK : BFScattered K)
    (hunc : ¬ (Quotient.mk (structureIsoSetoid L) '' K).Countable) :
    Cardinal.mk ↥(Quotient.mk (structureIsoSetoid L) '' K) = Cardinal.aleph 1 :=
  InfinitaryLogic.mk_eq_aleph_one_of_countable_fibers (fun q ↦ hρ.lift q.1)
    (fun q ↦ hρ.lift_lt_omega1 q.1) (hρ.countable_fibers hK)
    (fun h ↦ hunc (Set.countable_coe_iff.mp h))

/-- **Countably many classes iff the rank is bounded.**  A back-and-forth scattered class meets
countably many isomorphism classes iff the rank is bounded below `ω₁` on it. -/
theorem countable_isoClasses_iff_bounded (hρ : IsIsolatingRank ρ) (hK : BFScattered K) :
    (Quotient.mk (structureIsoSetoid L) '' K).Countable ↔
      ∃ β < Ordinal.omega 1, ∀ x ∈ K, ρ x < β := by
  have key := InfinitaryLogic.countable_iff_rank_bounded
    (fun q : ↥(Quotient.mk (structureIsoSetoid L) '' K) ↦ hρ.lift q.1)
    (fun q ↦ hρ.lift_lt_omega1 q.1) (hρ.countable_fibers hK) Set.univ
  rw [Set.countable_univ_iff, Set.countable_coe_iff] at key
  rw [key]
  refine exists_congr fun β ↦ and_congr_right fun _ ↦ ⟨fun h x hx ↦ ?_, fun h q _ ↦ ?_⟩
  · exact h ⟨_, x, hx, rfl⟩ trivial
  · obtain ⟨_, x, hx, rfl⟩ := q
    exact h x hx

end IsIsolatingRank

/-! ### The stabilization-ordinal instance -/

/-- **The stabilization ordinal of a code**: `stabilizationOrdinal` of the structure on `ℕ`
decoded from `c`.  It is an isolating rank for countably many relation symbols
(`isIsolatingRank_codeStabilizationOrdinal`).  It is not claimed to be the least isolating level
among codes: `StabilizesAt` quantifies over all countable structures, not only codes. -/
noncomputable def codeStabilizationOrdinal (c : StructureSpace L) : Ordinal.{0} :=
  -- the decoded structure is supplied explicitly: it is a definition, not an instance
  @stabilizationOrdinal L ℕ c.toStructure _

/-- The defining equation of `codeStabilizationOrdinal`, for transporting `stabilizationOrdinal`
facts to codes. -/
theorem codeStabilizationOrdinal_def (c : StructureSpace L) :
    codeStabilizationOrdinal c = @stabilizationOrdinal L ℕ c.toStructure _ :=
  rfl

/-- Isomorphic codes have the same stabilization ordinal (`stabilizationOrdinal_eq_of_equiv`), for
every relational language. -/
theorem codeStabilizationOrdinal_congr {c d : StructureSpace L}
    (h : (structureIsoSetoid L).r c d) :
    codeStabilizationOrdinal c = codeStabilizationOrdinal d :=
  let ⟨e⟩ := h
  -- the decoded structures are supplied explicitly: both live on the carrier `ℕ`, so instance
  -- resolution cannot tell them apart
  @stabilizationOrdinal_eq_of_equiv L ℕ ℕ c.toStructure d.toStructure _ _ e

/-- **The stabilization ordinal is an isolating rank** for countably many relation symbols: it
is countable (`stabilizationOrdinal_lt_omega1'`) and decides isomorphism at its own level
(`stabilizationOrdinal_spec`).  Together with the family bridge
`exists_isolating_codeLevel_of_family` (whose countability is forced by the landed
`exists_isolating_level`), this is one of the two declarations of the module that assume
countably many relation symbols. -/
theorem isIsolatingRank_codeStabilizationOrdinal [Countable (Σ l, L.Relations l)] :
    IsIsolatingRank (codeStabilizationOrdinal (L := L)) where
  iso_invariant _ _ h := codeStabilizationOrdinal_congr h
  -- the decoded structures are supplied explicitly: `c.toStructure` and `d.toStructure` are two
  -- structures on the same carrier `ℕ`, so instance resolution cannot tell them apart
  lt_omega1 c := @stabilizationOrdinal_lt_omega1' L _ _ ℕ c.toStructure _
  isolates c d h := (@stabilizationOrdinal_spec L _ _ ℕ c.toStructure _ ℕ d.toStructure _).mp h

/-! ### The bridge to the family form -/

/-- **The code form through the family form.**  The conclusion of
`IsIsolatingRank.exists_isolating_codeLevel`, obtained instead from `exists_isolating_level`
(`Scott/IsolatingLevel.lean`) applied to the countable family of chosen representatives of the
classes of `S`, and transferred back to the codes of `S` by `CodeBFEquiv.of_iso`.  It needs
countably many relation symbols, the hypothesis of the family form.  It records that the two
forms agree (a countable family of representatives versus a set of codes meeting countably many
classes); nothing in this module depends on it. -/
theorem exists_isolating_codeLevel_of_family [Countable (Σ l, L.Relations l)]
    {S : Set (StructureSpace L)}
    (hS : (Quotient.mk (structureIsoSetoid L) '' S).Countable) :
    ∃ γ : Ordinal.{0}, γ < Ordinal.omega 1 ∧
      ∀ x ∈ S, ∀ y ∈ S, CodeBFEquiv γ x y → (structureIsoSetoid L).r x y := by
  have := hS.to_subtype
  obtain ⟨γ, hγ, hiso⟩ := @exists_isolating_level L _ _
    ↥(Quotient.mk (structureIsoSetoid L) '' S) _ (fun _ ↦ ℕ)
    -- the representatives' structures are passed explicitly, all on the carrier `ℕ`
    (fun q ↦ (Quotient.out q.1 : StructureSpace L).toStructure) (fun _ ↦ inferInstance)
  refine ⟨γ, hγ, fun x hx y hy h ↦ ?_⟩
  have hxo : (structureIsoSetoid L).r (Quotient.out (Quotient.mk (structureIsoSetoid L) x)) x :=
    Quotient.mk_out (s := structureIsoSetoid L) x
  have hyo : (structureIsoSetoid L).r (Quotient.out (Quotient.mk (structureIsoSetoid L) y)) y :=
    Quotient.mk_out (s := structureIsoSetoid L) y
  have hbf : CodeBFEquiv γ (Quotient.out (Quotient.mk (structureIsoSetoid L) x))
      (Quotient.out (Quotient.mk (structureIsoSetoid L) y)) :=
    (codeBFEquivSetoid L γ).iseqv.trans (CodeBFEquiv.of_iso hxo γ)
      ((codeBFEquivSetoid L γ).iseqv.trans h
        ((codeBFEquivSetoid L γ).iseqv.symm (CodeBFEquiv.of_iso hyo γ)))
  have := hiso ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩ hbf
  exact (structureIsoSetoid L).iseqv.trans ((structureIsoSetoid L).iseqv.symm hxo)
    ((structureIsoSetoid L).iseqv.trans this hyo)

end Contract

end FirstOrder.Language
