/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.MinimallyUncountable
import InfinitaryLogic.Descriptive.ScatteredCounting

/-!
# Minimally unbounded classes for a rank on codes

This module is the rank-parametric half of an analogue of [Mon, Def XII.4].  For a map
`ρ : StructureSpace L → Ordinal.{0}`, a set `K` of codes is **minimally unbounded**
(`MinimallyUnboundedOn ρ K`) when `ρ` is unbounded below `ω₁` on `K`
(`UnboundedRankOn ρ K`), but every sentence cut `K ∩ ModelsOf θ` / `K \ ModelsOf θ` has a side
on which `ρ` is bounded.  For a sentence `Θ`, `Sentenceω.MinimallyUnbounded ρ Θ` is the case
`K = ModelsOf Θ`, and `Sentenceω.minimallyUnbounded_iff_inf` restates it with the literal
sentences `Θ ⊓ θ` and `Θ ⊓ θ.not`.  The book's definition has no named "cut": it quantifies
over all sentences `θ`, and the pair of sides is `Θ ∧ θ`, `Θ ∧ ¬θ`.

The rank is a parameter.  No Scott rank of the book is identified with any `ρ`; the meaning of
"bounded" depends on `ρ` in general.  The isolating-rank contract `IsIsolatingRank`
(`Descriptive/ScatteredCounting.lean`) removes that dependence on back-and-forth scattered
classes: there, bounded means countably many isomorphism classes, for every isolating rank.

## Main declarations

* `MinimallyUnboundedOn ρ K`, `Sentenceω.MinimallyUnbounded ρ Θ`, and the literal form
  `Sentenceω.minimallyUnbounded_iff_inf`.
* `MinimallyUnboundedOn.bounded_bfClass_or_compl`: the cut by a back-and-forth class below
  `ω₁` has a bounded side.
* `MinimallyUnboundedOn.exists_bfClass_compl_bounded` (the first half of [Mon, Lemma XII.8], in
  this form): at a level `α < ω₁` where `K` has countably many `CodeBFEquiv α`-classes, one class
  is unbounded and its complement in `K` is bounded.  It needs neither an isolating rank nor
  `ρ < ω₁`.  The per-level countability is the scatteredness hypothesis that the book's
  statement omits.
* Rank independence on a back-and-forth scattered class `K` (`BFScattered K` explicit):
  `IsIsolatingRank.boundedRankOn_iff_countable` (bounded iff countably many isomorphism
  classes), `boundedRankOn_iff_of_isIsolatingRank` (two isolating ranks agree on boundedness),
  `minimallyUnboundedOn_iff_minimallyUncountableOn` (minimally unbounded iff minimally
  uncountable, `Descriptive/MinimallyUncountable.lean`) and
  `minimallyUnboundedOn_iff_of_isIsolatingRank`.

## Where hypotheses enter

* `IsIsolatingRank ρ` enters only in the four rank-independence statements, which use the
  contract through its landed counting conclusion
  `IsIsolatingRank.countable_isoClasses_iff_bounded`, not through any instance.
* `[Countable (Σ l, L.Relations l)]` enters only through `scottSentenceAt`, in the two
  statements about back-and-forth classes.

## Import closure

The import closure contains `Karp.PotentialIso`, through `Descriptive.ScatteredCounting` and
`Scott.Sentence` (the module of the stabilization-ordinal instance of the contract).  The proofs
of this module do not use it: the dependency guard checks that their proof cones contain no
`Karp` constant and no stabilization ordinal, and only the abstract contract.  The definition
`MinimallyUnboundedOn` and its two statements about back-and-forth classes need no isolating
rank either; they live here, beside the contract, because only for isolating ranks on
back-and-forth scattered classes is their meaning independent of `ρ`.  The rank-free notion,
the rank definitions and the generic engine are in `Descriptive/MinimallyUncountable.lean`,
whose import closure contains no `Karp` module.

## References

* [Mon] A. Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, draft, Chapter XII,
  §XII.1–XII.2 (Def XII.1, Def XII.4, Lemma XII.8).

The composition was offered for upstreaming by a consumer of this library.
-/

universe u v

namespace FirstOrder.Language

open Cardinal Set

/-! ### Minimal unboundedness -/

section Minimal

variable {L : Language.{u, v}} [L.IsRelational] (ρ : StructureSpace L → Ordinal.{0})

/-- **Minimally unbounded on `K`** (rank-parametric analogue of [Mon, Def XII.4]): `ρ` is
unbounded below `ω₁` on `K`, and every sentence cut `K ∩ ModelsOf θ` / `K \ ModelsOf θ` has a
side on which `ρ` is bounded.  The cut ranges over sentences, not arbitrary invariant
subsets. -/
def MinimallyUnboundedOn (K : Set (StructureSpace L)) : Prop :=
  UnboundedRankOn ρ K ∧
    ∀ θ : L.Sentenceω, BoundedRankOn ρ (K ∩ ModelsOf θ) ∨ BoundedRankOn ρ (K \ ModelsOf θ)

/-- **A minimally unbounded sentence** for `ρ`: its `ℕ`-coded models are minimally
unbounded. -/
def Sentenceω.MinimallyUnbounded (Θ : L.Sentenceω) : Prop :=
  MinimallyUnboundedOn ρ (ModelsOf Θ)

variable {ρ}

/-- **The literal form for a sentence**: `ρ` is unbounded on the models of `Θ`, and for every
sentence `θ` it is bounded on the models of `Θ ⊓ θ` or on those of `Θ ⊓ θ.not`. -/
theorem Sentenceω.minimallyUnbounded_iff_inf (Θ : L.Sentenceω) :
    Θ.MinimallyUnbounded ρ ↔ UnboundedRankOn ρ (ModelsOf Θ) ∧
      ∀ θ : L.Sentenceω, BoundedRankOn ρ (ModelsOf (Θ ⊓ θ)) ∨
        BoundedRankOn ρ (ModelsOf (Θ ⊓ θ.not)) := by
  simp only [Sentenceω.MinimallyUnbounded, MinimallyUnboundedOn, modelsOf_inf, modelsOf_not,
    Set.sdiff_eq]

end Minimal

/-! ### Back-and-forth classes -/

section BFClasses

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ l, L.Relations l)]
  {ρ : StructureSpace L → Ordinal.{0}} {K : Set (StructureSpace L)}

/-- **The cut by a back-and-forth class**: in a minimally unbounded class, `ρ` is bounded on the
class of any code at any level `α < ω₁`, or on its complement. -/
theorem MinimallyUnboundedOn.bounded_bfClass_or_compl (h : MinimallyUnboundedOn ρ K)
    (c : StructureSpace L) {α : Ordinal.{0}} (hα : α < Ordinal.omega 1) :
    BoundedRankOn ρ (K ∩ {d | CodeBFEquiv α c d}) ∨
      BoundedRankOn ρ (K \ {d | CodeBFEquiv α c d}) := by
  rw [← modelsOf_scottSentenceAt c hα]; exact h.2 _

/-- **One unbounded class with a bounded complement** (the first half of [Mon, Lemma XII.8],
in this form): at a level `α < ω₁` where a minimally unbounded `K` has countably many
`CodeBFEquiv α`-classes, `ρ` is unbounded on the class of some `a ∈ K` and bounded on its
complement in `K`.  No isolating rank and no bound `ρ < ω₁` is used; the per-level countability
is the scatteredness hypothesis that the book's statement omits. -/
theorem MinimallyUnboundedOn.exists_bfClass_compl_bounded (h : MinimallyUnboundedOn ρ K)
    {α : Ordinal.{0}} (hα : α < Ordinal.omega 1)
    (hKα : Countable (Quotient ((codeBFEquivSetoid L α).comap
      (Subtype.val : K → StructureSpace L)))) :
    ∃ a ∈ K, UnboundedRankOn ρ (K ∩ {d | CodeBFEquiv α a d}) ∧
      BoundedRankOn ρ (K \ {d | CodeBFEquiv α a d}) := by
  simpa only [unboundedRankOn_iff_not_boundedRankOn] using
    exists_bfClass_compl_of_sentenceCuts (BoundedRankOn ρ) (fun _ _ hJK h ↦ h.mono hJK)
      (fun _ hS h ↦ boundedRankOn_sUnion hS h) (unboundedRankOn_iff_not_boundedRankOn.mp h.1)
      h.2 hα hKα

end BFClasses

/-! ### Rank independence on back-and-forth scattered classes -/

section RankIndependence

variable {L : Language.{u, v}} [L.IsRelational] {ρ ρ' : StructureSpace L → Ordinal.{0}}
  {K : Set (StructureSpace L)}

/-- **Bounded iff countably many classes**, for an isolating rank on a back-and-forth scattered
class: `IsIsolatingRank.countable_isoClasses_iff_bounded`, read backwards. -/
theorem IsIsolatingRank.boundedRankOn_iff_countable (hρ : IsIsolatingRank ρ)
    (hK : BFScattered K) :
    BoundedRankOn ρ K ↔ (Quotient.mk (structureIsoSetoid L) '' K).Countable :=
  (hρ.countable_isoClasses_iff_bounded hK).symm

/-- **Two isolating ranks agree on boundedness** on a back-and-forth scattered class. -/
theorem boundedRankOn_iff_of_isIsolatingRank (hρ : IsIsolatingRank ρ)
    (hρ' : IsIsolatingRank ρ') (hK : BFScattered K) :
    BoundedRankOn ρ K ↔ BoundedRankOn ρ' K :=
  (hρ.boundedRankOn_iff_countable hK).trans (hρ'.boundedRankOn_iff_countable hK).symm

/-- **Minimally unbounded iff minimally uncountable**, for an isolating rank on a
back-and-forth scattered class: both sides of every cut are again back-and-forth scattered
(`BFScattered.mono`). -/
theorem minimallyUnboundedOn_iff_minimallyUncountableOn (hρ : IsIsolatingRank ρ)
    (hK : BFScattered K) : MinimallyUnboundedOn ρ K ↔ MinimallyUncountableOn K := by
  rw [MinimallyUnboundedOn, MinimallyUncountableOn, unboundedRankOn_iff_not_boundedRankOn,
    hρ.boundedRankOn_iff_countable hK]
  refine and_congr_right' (forall_congr' fun θ ↦ or_congr ?_ ?_)
  · exact hρ.boundedRankOn_iff_countable (hK.mono inter_subset_left)
  · exact hρ.boundedRankOn_iff_countable (hK.mono sdiff_subset)

/-- **Two isolating ranks agree on minimal unboundedness** on a back-and-forth scattered
class. -/
theorem minimallyUnboundedOn_iff_of_isIsolatingRank (hρ : IsIsolatingRank ρ)
    (hρ' : IsIsolatingRank ρ') (hK : BFScattered K) :
    MinimallyUnboundedOn ρ K ↔ MinimallyUnboundedOn ρ' K :=
  (minimallyUnboundedOn_iff_minimallyUncountableOn hρ hK).trans
    (minimallyUnboundedOn_iff_minimallyUncountableOn hρ' hK).symm

end RankIndependence

end FirstOrder.Language
