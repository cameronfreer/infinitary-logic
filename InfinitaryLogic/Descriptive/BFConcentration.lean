/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.BFScattered
import InfinitaryLogic.Scott.BFEquivRelabel

/-!
# Concentration at back-and-forth levels

A set `C` of codes of countable relational structures is **concentrated at back-and-forth
levels** (`ConcentratedAtBFLevels C`) when, at every countable level `α < ω₁`, all but countably
many isomorphism classes of `C` lie in a single `CodeBFEquiv α`-class.  The centre of that class
is a code that may lie outside `C` and may depend on `α`.

This module proves two things about such a class, with no isolating rank anywhere.

1. **Thinness.**  A concentrated class is back-and-forth scattered
   (`ConcentratedAtBFLevels.bfScattered`), so it carries no Cantor antichain for isomorphism and,
   for countably many relation symbols, it is thin.  These two endpoints are one-line corollaries
   of `not_hasCantorAntichainOn_of_bfScattered` and `isThinOn_of_bfScattered`
   (`Descriptive/BFScattered.lean`), which are not re-proved here.
2. **One side of an invariant split has countably many classes.**  If `B ⊆ C` is closed under
   isomorphism within `C` and both `B` and `C \ B` are analytic (for instance `B` relatively
   Borel in an analytic `C`, with countably many relation symbols), then `B` or `C \ B` meets
   only countably many isomorphism classes
   (`ConcentratedAtBFLevels.countable_isoClasses_or_of_analyticSets`; the relatively Borel form
   is `ConcentratedAtBFLevels.countable_isoClasses_or`).

## Main declarations

* `CodeBFEquiv.of_iso`: isomorphic codes are back-and-forth equivalent at every level.
* `ConcentratedAtBFLevels C`, with `ConcentratedAtBFLevels.mono` and
  `concentratedAtBFLevels_of_countable`.
* `ConcentratedAtBFLevels.bfScattered`: the bridge to `BFScattered`; with the endpoints
  `ConcentratedAtBFLevels.not_hasCantorAntichainOn` and `ConcentratedAtBFLevels.isThinOn`.
* `exists_bfLevel_saturated_of_analyticSets`: an isomorphism-invariant split of `C` with analytic
  sides is a union of `CodeBFEquiv β`-classes within `C` for all `β` from some `α < ω₁` on;
  `exists_bfLevel_saturated` is the relatively Borel form in an analytic `C`.
* `invariant_of_bfLevel_saturated`: saturation at any single level forces invariance within `C`.
* `ConcentratedAtBFLevels.countable_isoClasses_or_of_saturatedAt`: the combinatorial core, from
  saturation at one level, with no invariance and no analyticity.
* `ConcentratedAtBFLevels.countable_isoClasses_or_of_analyticSets` and
  `ConcentratedAtBFLevels.countable_isoClasses_or`: one side of an invariant split has countably
  many isomorphism classes.

## The proofs

* **Bridge.**  At level `α`, with centre `k`, send `x ∈ C` to `none` if `x` is
  `CodeBFEquiv α`-equivalent to `k`, and to `some ⟦x⟧` (its isomorphism class) otherwise.  The
  values lie in `insert none (some '' S)` for the countable set `S` of classes off the centre,
  and equal values imply `CodeBFEquiv α`: through the centre by symmetry and transitivity, off it
  because isomorphic codes are equivalent at every level (`CodeBFEquiv.of_iso`).  Then
  `countable_quotient_of_countable_range` gives countably many classes at level `α`.
* **Saturation.**  `exists_uniform_bfSeparation_of_analyticSets`, applied to `B` and `C \ B`
  (which contain no isomorphic pair, by invariance), gives one separating level; monotonicity
  and symmetry of `CodeBFEquiv` give the iff at every higher level.
* **Core.**  At a saturating level `α` take the centre `k`.  If some `x ∈ B` is equivalent to
  `k`, every `y ∈ C` equivalent to `k` is equivalent to `x`, hence lies in `B`; so `C \ B` lies
  off the centre.  Otherwise `B` lies off the centre.  Either way one side has countably many
  classes.

## Interpretation choices

* **Concentration is the stronger premise.**  The one-side-countable result assumes
  `ConcentratedAtBFLevels C`, not `BFScattered C`.  Every concentrated class is back-and-forth
  scattered, and `BFScattered` is the hypothesis of the thinness results; the counting result
  for invariant splits is stated only under concentration, and scatteredness is not substituted
  for it.
* **Counting isomorphism classes.**  The off-centre part is counted through
  `Quotient.mk (structureIsoSetoid L)` with plain `Set.Countable`; no measurable structure is
  put on the quotient.
* **The centre.**  The centre `k` is an arbitrary code, possibly outside `C`, and may change with
  the level.
* **Equivalence convention and levels.**  The level-`α` relation is this library's
  `CodeBFEquiv α` (single-element back-and-forth steps from the empty tuples); levels are
  `Ordinal.{0}` below `Ordinal.omega 1`, with no lift and no offset.
* **Invariance is relative to `C` and necessary.**  Invariance is the hypothesis
  `∀ x ∈ B, ∀ y ∈ C, (structureIsoSetoid L).r x y → y ∈ B`, stated through
  `structureIsoSetoid` and relative to `C`.  It cannot be dropped:
  `invariant_of_bfLevel_saturated` shows that the conclusion of the saturation theorem, at any
  single level, already implies it.  The combinatorial core assumes neither invariance nor
  analyticity; both enter only through saturation.
* **Countability of the language.**  `[Countable (Σ l, L.Relations l)]` occurs in exactly three
  declarations: `ConcentratedAtBFLevels.isThinOn` (through `isThinOn_of_bfScattered`, where a
  perfect antichain yields a Cantor antichain in the Polish space of codes),
  `exists_bfLevel_saturated` and `ConcentratedAtBFLevels.countable_isoClasses_or` (where the
  Polish and Borel structure of the space of codes makes relatively Borel subsets of an
  analytic set analytic).  In the last two the assumption is sufficient for that step; it is
  not shown to be necessary.  The bridge, the Cantor-antichain endpoint, the analytic-sides
  forms and the core need no countability.
* **Dependency on `Scott.BFEquivRelabel`.**  This module adds exactly `Scott.BFEquivRelabel` to
  the import closure of `Descriptive.BFScattered`.  Its only use is `BFEquiv.map_equiv` in
  `CodeBFEquiv.of_iso`, which serves the bridge and the necessity lemma; the saturation theorems
  and the counting results do not use it.

## Scope

* **Non-vacuity is not shown.**  Both counting forms force `C` to be analytic (the relatively
  Borel form assumes it; with `B ⊆ C`, the analytic-sides form gives `C = B ∪ (C \ B)`
  analytic).  No *analytic* concentrated class with uncountably many isomorphism classes is
  exhibited here, so the one-side-countable result is not shown to be non-vacuous.  Such a
  class, and an analytic, back-and-forth scattered, non-concentrated class with an invariant
  relatively Borel split whose two sides both have uncountably many classes, are recorded as
  follow-ups.  With countably many relation symbols, a witness that is Borel and isomorphism
  invariant would be a thin Borel invariant class with uncountably many isomorphism classes,
  which would settle a well-known open problem; witnesses have to be sought among analytic
  classes that are not Borel invariant.  A class of codes of well-orders of unbounded order
  types cannot serve, since it is never analytic (`analytic_wellOrder_type_boundedness`); such a
  class can only illustrate the thinness side, which needs no analyticity.
* No isolating rank, Scott rank or stabilization ordinal is used or defined.

## References

* A. Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, draft, Chapter XII,
  §XII.1 (scattered sentences: countably many classes at every countable level).
* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156,
  Springer, 1995, §31.A (the boundedness theorem behind `exists_uniform_bfSeparation`).

The composition was offered for upstreaming by a consumer of this library.
-/

universe u v

namespace FirstOrder.Language

open Set MeasureTheory

variable {L : Language.{u, v}} [L.IsRelational]

/-! ### Isomorphic codes are back-and-forth equivalent -/

/-- **Isomorphic codes are back-and-forth equivalent at every level**: transport the reflexive
`BFEquiv` of a code along an isomorphism (`BFEquiv.map_equiv`).  This is the only use of
`Scott.BFEquivRelabel` in this module. -/
theorem CodeBFEquiv.of_iso {c d : StructureSpace L} (h : (structureIsoSetoid L).r c d)
    (α : Ordinal.{0}) : CodeBFEquiv α c d := by
  obtain ⟨e⟩ := h
  -- the decoded structures are supplied explicitly: `c.toStructure` and `d.toStructure` are
  -- two structures on the same carrier `ℕ`, so instance resolution cannot tell them apart
  have key := (@BFEquiv.map_equiv L ℕ c.toStructure ℕ c.toStructure ℕ ℕ c.toStructure
    d.toStructure (@Language.Equiv.refl L ℕ c.toStructure) e α 0 Fin.elim0 Fin.elim0).mpr
    (@BFEquiv.refl L ℕ c.toStructure 0 α Fin.elim0)
  unfold CodeBFEquiv
  rwa [comp_fin_elim0, comp_fin_elim0] at key

/-- `CodeBFEquiv α` is symmetric (`codeBFEquivSetoid`).  Kept private: a dot-notation shorthand
for the chains in this module. -/
private theorem CodeBFEquiv.symm {α : Ordinal.{0}} {c d : StructureSpace L}
    (h : CodeBFEquiv α c d) : CodeBFEquiv α d c :=
  (codeBFEquivSetoid L α).iseqv.symm h

/-- `CodeBFEquiv α` is transitive (`codeBFEquivSetoid`).  Kept private, as `CodeBFEquiv.symm`. -/
private theorem CodeBFEquiv.trans {α : Ordinal.{0}} {c d e : StructureSpace L}
    (h₁ : CodeBFEquiv α c d) (h₂ : CodeBFEquiv α d e) : CodeBFEquiv α c e :=
  (codeBFEquivSetoid L α).iseqv.trans h₁ h₂

/-! ### Concentration and the bridge to `BFScattered` -/

/-- `C` is **concentrated at back-and-forth levels**: for every level `α < ω₁` there is a code
`k` (the centre, possibly outside `C`, possibly depending on `α`) such that the members of `C`
not `CodeBFEquiv α`-equivalent to `k` meet only countably many isomorphism classes.  The count is
of classes of `structureIsoSetoid L`, with plain `Set.Countable` and no measurable structure on
the quotient. -/
def ConcentratedAtBFLevels (C : Set (StructureSpace L)) : Prop :=
  ∀ α : Ordinal.{0}, α < Ordinal.omega 1 → ∃ k : StructureSpace L,
    (Quotient.mk (structureIsoSetoid L) '' {x | x ∈ C ∧ ¬ CodeBFEquiv α x k}).Countable

/-- Concentration passes to subsets, with the same centres. -/
theorem ConcentratedAtBFLevels.mono {C C' : Set (StructureSpace L)}
    (hC : ConcentratedAtBFLevels C) (h : C' ⊆ C) : ConcentratedAtBFLevels C' := fun α hα ↦
  let ⟨k, hk⟩ := hC α hα
  ⟨k, hk.mono (image_mono fun _ hx ↦ by exact ⟨h hx.1, hx.2⟩)⟩

/-- A set meeting countably many isomorphism classes is concentrated, with any centre. -/
theorem concentratedAtBFLevels_of_countable {C : Set (StructureSpace L)}
    (hC : (Quotient.mk (structureIsoSetoid L) '' C).Countable) : ConcentratedAtBFLevels C :=
  fun _ _ ↦ ⟨(fun _ ↦ false : StructureSpaceOn L ℕ), hC.mono (image_mono fun _ hx ↦ hx.1)⟩

/-- **Concentration implies back-and-forth scatteredness.**  At level `α` with centre `k`, the
observation `x ↦ none` on the centre's class and `x ↦ some ⟦x⟧` (the isomorphism class) off it
has countably many values on `C`, and equal values imply `CodeBFEquiv α`: on the centre by
symmetry and transitivity, off it by `CodeBFEquiv.of_iso`.  No analyticity of `C` and no
countability of the relation symbols is assumed. -/
theorem ConcentratedAtBFLevels.bfScattered {C : Set (StructureSpace L)}
    (hC : ConcentratedAtBFLevels C) : BFScattered C := by
  intro α hα
  obtain ⟨k, hk⟩ := hC α hα
  classical
  refine countable_quotient_of_countable_range _
    (fun x : C ↦ if CodeBFEquiv α x.1 k then (none : Option (Quotient (structureIsoSetoid L)))
      else some (Quotient.mk _ x.1)) ?_ ?_
  · refine ((hk.image some).insert none).mono ?_
    rintro _ ⟨x, rfl⟩
    by_cases hx : CodeBFEquiv α x.1 k
    · simp [hx]
    · simp only [hx, ite_false]
      exact Or.inr ⟨_, ⟨x.1, ⟨x.2, hx⟩, rfl⟩, rfl⟩
  · intro x y hxy
    -- the pulled-back relation `(codeBFEquivSetoid L α).comap Subtype.val` is, by definition,
    -- `CodeBFEquiv α` on the underlying codes
    change CodeBFEquiv α x.1 y.1
    by_cases hx : CodeBFEquiv α x.1 k <;> by_cases hy : CodeBFEquiv α y.1 k <;>
      simp only [hx, hy, ite_true, ite_false, reduceCtorEq, Option.some.injEq] at hxy
    · exact hx.trans hy.symm
    · exact CodeBFEquiv.of_iso (Quotient.exact hxy) α

/-- **No Cantor antichain on a concentrated class**, for every relational language:
`not_hasCantorAntichainOn_of_bfScattered` through `ConcentratedAtBFLevels.bfScattered`.  No
countability of the relation symbols and no analyticity of `C` is assumed. -/
theorem ConcentratedAtBFLevels.not_hasCantorAntichainOn {C : Set (StructureSpace L)}
    (hC : ConcentratedAtBFLevels C) : ¬ HasCantorAntichainOn (structureIsoSetoid L) C :=
  not_hasCantorAntichainOn_of_bfScattered hC.bfScattered

/-- **A concentrated class is thin**: `isThinOn_of_bfScattered` through
`ConcentratedAtBFLevels.bfScattered`.  Countability of the relation symbols enters only through
`isThinOn_of_bfScattered`; no analyticity of `C` is assumed. -/
theorem ConcentratedAtBFLevels.isThinOn [Countable (Σ l, L.Relations l)]
    {C : Set (StructureSpace L)} (hC : ConcentratedAtBFLevels C) :
    IsThinOn (structureIsoSetoid L) C :=
  isThinOn_of_bfScattered hC.bfScattered

/-! ### Saturation of an invariant split -/

/-- **An invariant split with analytic sides is saturated from some countable level on.**  If
`B` and `C \ B` are analytic and `B` is closed under isomorphism within `C`, then there is
`α < ω₁` such that for every `β ≥ α`, `CodeBFEquiv β`-equivalent members of `C` lie on the same
side of `B`.  This is `exists_uniform_bfSeparation_of_analyticSets` for `B` and `C \ B`, with
monotonicity and symmetry of `CodeBFEquiv`.  No countability of the relation symbols, no
analyticity of `C` and no `B ⊆ C` is assumed. -/
theorem exists_bfLevel_saturated_of_analyticSets {B C : Set (StructureSpace L)}
    (hB : AnalyticSet B) (hCB : AnalyticSet (C \ B))
    (hinv : ∀ x ∈ B, ∀ y ∈ C, (structureIsoSetoid L).r x y → y ∈ B) :
    ∃ α : Ordinal.{0}, α < Ordinal.omega 1 ∧ ∀ β : Ordinal.{0}, α ≤ β →
      ∀ x ∈ C, ∀ y ∈ C, CodeBFEquiv β x y → (x ∈ B ↔ y ∈ B) := by
  obtain ⟨α, hα, hsep⟩ := exists_uniform_bfSeparation_of_analyticSets hB hCB
    fun x hx y hy hxy ↦ hy.2 (hinv x hx y hy.1 hxy)
  refine ⟨α, hα, fun β hβ x hx y hy hxy ↦ ⟨fun hxB ↦ ?_, fun hyB ↦ ?_⟩⟩
  · by_contra hyB
    exact hsep x hxB y ⟨hy, hyB⟩ (CodeBFEquiv.monotone hβ hxy)
  · by_contra hxB
    exact hsep y hyB x ⟨hx, hxB⟩ (CodeBFEquiv.monotone hβ hxy.symm)

/-- **Saturation, relatively Borel form**: `exists_bfLevel_saturated_of_analyticSets` for
`B = C ∩ D` with `D` Borel and `C` analytic.  Countably many relation symbols make the space of
codes Polish with its Borel structure, so both `C ∩ D` and `C \ (C ∩ D) = C ∩ Dᶜ` are analytic;
this is the only use of countability.  The assumption is sufficient for this step; it is not
shown to be necessary. -/
theorem exists_bfLevel_saturated [Countable (Σ l, L.Relations l)]
    {B C : Set (StructureSpace L)} (hC : AnalyticSet C)
    (hB : ∃ D : Set (StructureSpace L), MeasurableSet D ∧ B = C ∩ D)
    (hinv : ∀ x ∈ B, ∀ y ∈ C, (structureIsoSetoid L).r x y → y ∈ B) :
    ∃ α : Ordinal.{0}, α < Ordinal.omega 1 ∧ ∀ β : Ordinal.{0}, α ≤ β →
      ∀ x ∈ C, ∀ y ∈ C, CodeBFEquiv β x y → (x ∈ B ↔ y ∈ B) := by
  obtain ⟨D, hD, rfl⟩ := hB
  refine exists_bfLevel_saturated_of_analyticSets (hC.inter_measurableSet hD) ?_ hinv
  rw [sdiff_self_inter, sdiff_eq]
  exact hC.inter_measurableSet hD.compl

/-- **Invariance is necessary for saturation**: if `B ⊆ C` is a union of `CodeBFEquiv α`-classes
within `C` at any single level `α`, then `B` is closed under isomorphism within `C`, since
isomorphic codes are equivalent at every level (`CodeBFEquiv.of_iso`). -/
theorem invariant_of_bfLevel_saturated {B C : Set (StructureSpace L)} {α : Ordinal.{0}}
    (hsat : ∀ x ∈ C, ∀ y ∈ C, CodeBFEquiv α x y → (x ∈ B ↔ y ∈ B)) (hBC : B ⊆ C) :
    ∀ x ∈ B, ∀ y ∈ C, (structureIsoSetoid L).r x y → y ∈ B :=
  fun x hx y hy h ↦ (hsat x (hBC hx) y hy (CodeBFEquiv.of_iso h α)).mp hx

/-! ### One side has countably many isomorphism classes -/

/-- **The combinatorial core**: if `C` is concentrated, `B ⊆ C`, and `B` is saturated within `C`
at one level `α < ω₁` in the one-sided sense (members of `C` equivalent to a member of `B` lie in
`B`), then `B` or `C \ B` meets only countably many isomorphism classes.  With the centre `k` at
level `α`: if some member of `B` is equivalent to `k`, all of `C \ B` lies off the centre;
otherwise all of `B` does.  No invariance, no analyticity and no countability is assumed. -/
theorem ConcentratedAtBFLevels.countable_isoClasses_or_of_saturatedAt
    {B C : Set (StructureSpace L)} (hC : ConcentratedAtBFLevels C) (hBC : B ⊆ C)
    {α : Ordinal.{0}} (hα : α < Ordinal.omega 1)
    (hsat : ∀ x ∈ B, ∀ y ∈ C, CodeBFEquiv α x y → y ∈ B) :
    (Quotient.mk (structureIsoSetoid L) '' B).Countable ∨
      (Quotient.mk (structureIsoSetoid L) '' (C \ B)).Countable := by
  obtain ⟨k, hk⟩ := hC α hα
  by_cases h : ∃ x ∈ B, CodeBFEquiv α x k
  · obtain ⟨x, hxB, hxk⟩ := h
    refine Or.inr (hk.mono (image_mono ?_))
    rintro y ⟨hyC, hyB⟩
    exact ⟨hyC, fun hyk ↦ hyB (hsat x hxB y hyC (hxk.trans hyk.symm))⟩
  · exact Or.inl (hk.mono (image_mono fun x hx ↦ by exact ⟨hBC hx, fun hxk ↦ h ⟨x, hx, hxk⟩⟩))

/-- **One side of an invariant split with analytic sides has countably many isomorphism
classes**, for a concentrated `C`: the core at the level of
`exists_bfLevel_saturated_of_analyticSets`.  No countability of the relation symbols and no
analyticity of `C` itself is assumed. -/
theorem ConcentratedAtBFLevels.countable_isoClasses_or_of_analyticSets
    {B C : Set (StructureSpace L)} (hC : ConcentratedAtBFLevels C) (hBC : B ⊆ C)
    (hB : AnalyticSet B) (hCB : AnalyticSet (C \ B))
    (hinv : ∀ x ∈ B, ∀ y ∈ C, (structureIsoSetoid L).r x y → y ∈ B) :
    (Quotient.mk (structureIsoSetoid L) '' B).Countable ∨
      (Quotient.mk (structureIsoSetoid L) '' (C \ B)).Countable := by
  obtain ⟨α, hα, hsat⟩ := exists_bfLevel_saturated_of_analyticSets hB hCB hinv
  exact hC.countable_isoClasses_or_of_saturatedAt hBC hα
    fun x hx y hy hxy ↦ (hsat α le_rfl x (hBC hx) y hy hxy).mp hx

/-- **One side of an invariant relatively Borel split has countably many isomorphism classes**:
for a concentrated analytic `C` and `B = C ∩ D` with `D` Borel, closed under isomorphism within
`C`, either `B` or `C \ B` meets only countably many isomorphism classes.  The core at the level
of `exists_bfLevel_saturated`; countability of the relation symbols enters only there, as a
sufficient assumption not shown to be necessary. -/
theorem ConcentratedAtBFLevels.countable_isoClasses_or [Countable (Σ l, L.Relations l)]
    {B C : Set (StructureSpace L)} (hC : ConcentratedAtBFLevels C) (hCa : AnalyticSet C)
    (hB : ∃ D : Set (StructureSpace L), MeasurableSet D ∧ B = C ∩ D)
    (hinv : ∀ x ∈ B, ∀ y ∈ C, (structureIsoSetoid L).r x y → y ∈ B) :
    (Quotient.mk (structureIsoSetoid L) '' B).Countable ∨
      (Quotient.mk (structureIsoSetoid L) '' (C \ B)).Countable := by
  obtain ⟨α, hα, hsat⟩ := exists_bfLevel_saturated hCa hB hinv
  have hBC : B ⊆ C := by obtain ⟨D, -, rfl⟩ := hB; exact inter_subset_left
  exact hC.countable_isoClasses_or_of_saturatedAt hBC hα
    fun x hx y hy hxy ↦ (hsat α le_rfl x (hBC hx) y hy hxy).mp hx

end FirstOrder.Language
