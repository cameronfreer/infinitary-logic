/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.BFConcentration
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
* `codeStabilizationOrdinal`, `codeStabilizationOrdinal_congr`,
  `isIsolatingRank_codeStabilizationOrdinal`.
* `IsIsolatingRank.exists_isolating_codeLevel`,
  `IsIsolatingRank.not_countable_isoClasses_of_forall_unisolated`, and the bridge
  `exists_isolating_codeLevel_of_family`.
* `IsIsolatingRank.countable_fibers`, `IsIsolatingRank.mk_isoClasses_le_aleph_one`,
  `IsIsolatingRank.mk_isoClasses_eq_aleph_one`, `IsIsolatingRank.countable_isoClasses_iff_bounded`.

## The contract is abstract

* **Three fields only.**  Countable fibres and "countable iff bounded" are *conclusions*
  (`IsIsolatingRank.countable_fibers`, `IsIsolatingRank.countable_isoClasses_iff_bounded`, both
  under `BFScattered K`), not fields of the contract.
* **The contract does not pin the rank.**  `IsIsolatingRank.of_le`: any isomorphism-invariant
  map below `ω₁` lying above an isolating rank is again one.  So nothing proved from the
  contract depends on which isolating rank is used, and no least isolating rank is asserted.
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
`Language.{u, v}`.  That countability is necessary for the instance is not claimed.

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

* **`countable_fibers`.**  Choose a representative `r q ∈ K` of each class `q` of `K`.  On the
  fibre over `α`, send `q` to the `CodeBFEquiv α`-class of `r q` within `K`.  This is injective:
  equal images give `CodeBFEquiv α (r q) (r q')` at `α = ρ (r q)`, hence `r q ≅ r q'` by
  `isolates`.  So the fibre injects into the level-`α` quotient of `K`, which is countable by
  `BFScattered K`.
* **The cardinal and boundedness statements** are `mk_le_aleph_one_of_countable_fibers`,
  `mk_eq_aleph_one_of_countable_fibers` and `countable_iff_rank_bounded` from
  `OrdinalCountability`, applied to the lifted rank on the classes of `K`.
* **`codeStabilizationOrdinal_congr`** uses `stabilizesAt_of_equiv`: the set of stabilizing
  levels of isomorphic structures is the same, so their infima agree.

## Scope

* No least isolating level, no Scott-rank convention, no `ModelsOf` specialisation.
* **Non-vacuity is not shown.**  No class with `BFScattered K` and uncountably many isomorphism
  classes is exhibited here.
* The Silver-side statement that a thin sentence has back-and-forth scattered models is in
  `Conditional/BFScatteredSilver.lean`; it does not use an isolating rank and does not import
  this module, and this module imports nothing from `Conditional`.
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

/-- **Countable fibres.**  On a back-and-forth scattered class `K`, each fibre of the rank on the
isomorphism classes of `K` over a countable ordinal is countable: it injects into the
`CodeBFEquiv α`-quotient of `K`. -/
theorem countable_fibers (hρ : IsIsolatingRank ρ) (hK : BFScattered K) :
    ∀ α < Ordinal.omega 1,
      Countable {q : ↥(Quotient.mk (structureIsoSetoid L) '' K) // hρ.lift q.1 = α} := by
  intro α hα
  have := hK α hα
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
  have hρq : ρ (r q).1 = α := by rw [← hq, ← hr q]; rfl
  have hiso := hρ.isolates (hρq ▸ hbf)
  apply Subtype.ext; apply Subtype.ext
  rw [← hr q, ← hr q']
  exact Quotient.sound hiso

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
  @stabilizationOrdinal L ℕ c.toStructure _

/-- Isomorphic codes have the same stabilization ordinal (`stabilizesAt_of_equiv`), for every
relational language. -/
theorem codeStabilizationOrdinal_congr {c d : StructureSpace L}
    (h : (structureIsoSetoid L).r c d) :
    codeStabilizationOrdinal c = codeStabilizationOrdinal d := by
  obtain ⟨e⟩ := h
  have key : ∀ α : Ordinal.{0}, @StabilizesAt L ℕ c.toStructure α ↔
      @StabilizesAt L ℕ d.toStructure α := fun α ↦
    ⟨@stabilizesAt_of_equiv L ℕ ℕ c.toStructure d.toStructure e α,
      @stabilizesAt_of_equiv L ℕ ℕ d.toStructure c.toStructure
        (@Language.Equiv.symm L ℕ ℕ c.toStructure d.toStructure e) α⟩
  simp only [codeStabilizationOrdinal, stabilizationOrdinal]
  exact congrArg sInf (Set.ext key)

/-- **The stabilization ordinal is an isolating rank** for countably many relation symbols: it
is countable (`stabilizationOrdinal_lt_omega1'`) and decides isomorphism at its own level
(`stabilizationOrdinal_spec`).  This is the one place in the contract layer where countability
of the language is used. -/
theorem isIsolatingRank_codeStabilizationOrdinal [Countable (Σ l, L.Relations l)] :
    IsIsolatingRank (codeStabilizationOrdinal (L := L)) where
  iso_invariant _ _ h := codeStabilizationOrdinal_congr h
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
