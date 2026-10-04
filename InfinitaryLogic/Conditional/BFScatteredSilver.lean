/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.BFScatteredSentence
import InfinitaryLogic.Conditional.SilverAntichain

/-!
# A thin sentence has back-and-forth scattered models

For a countable relational language, the coded models of a sentence `Θ` are back-and-forth
scattered (`BFScattered (ModelsOf Θ)`: countably many `CodeBFEquiv η`-classes at every level
`η < ω₁`) as soon as `Θ` is thin on its coded models
(`Sentenceω.bfScattered_of_isThinOnNatModels`).  With the converse
`isThinOn_of_bfScattered` (`Descriptive/BFScattered.lean`) this is an equivalence
(`Sentenceω.bfScattered_iff_isThinOnNatModels`), and since a perfect set of pairwise
non-isomorphic models has the cardinality of the continuum, fewer than continuum many
isomorphism classes of coded models also give back-and-forth scatteredness
(`Sentenceω.bfScattered_modelsOf_of_lt_continuum`).

## Main declarations

* `Sentenceω.bfScattered_of_isThinOnNatModels`: thin implies back-and-forth scattered (primary).
* `Sentenceω.bfScattered_iff_isThinOnNatModels`: the two are equivalent.
* `Sentenceω.bfScattered_modelsOf_of_lt_continuum`: fewer than continuum many isomorphism
  classes of coded models imply back-and-forth scattered.

## Proof

At a level `η < ω₁`, `bfEquivSetoid Θ η` is a Borel equivalence relation on the Borel set
`ModelsOf Θ` (`bfEquivSetoid_measurableSet`) that is coarser than isomorphism
(`isoSetoid_refines_bfEquivSetoid`).  Silver's theorem for a Borel subset
(`silver_countable_or_cantorAntichain`) gives countably many classes, which is the level-`η`
clause of `BFScattered` (`bfEquivSetoid_eq_comap`), or a Cantor antichain for isomorphism in
`ModelsOf Θ`, which gives a perfect set of pairwise non-isomorphic models
(`Sentenceω.hasPerfectSet_of_ambient_cantorAntichain`) and contradicts thinness.

The same per-level step is inlined in the proof of `morley_counting_coded_or_perfect`
(`Conditional/MorleyPerfect.lean`).  Extracting it there as one named lemma, used by both, is a
recorded follow-up; `MorleyPerfect.lean` is not changed here.

## Scope

* **Rank-free proof cones (checked).**  The proofs use no isolating rank, Scott rank, Scott
  height or stabilization ordinal: `check_bf_scattered_silver_regressions.lean` walks the proof
  cones of the three theorems and finds none of those constants.  The Scott modules that define
  them (`Scott.RefinementCount`, `Scott.Rank`, `Scott.Height`) are present only in the import
  closure, through `ModelTheory/MorleyCounting.lean`.
* **Composition with an isolating rank.**  From `BFScattered (ModelsOf Θ)` and an
  `IsIsolatingRank ρ`, the counting statements of `Descriptive/ScatteredCounting.lean` give at
  most `ℵ₁` isomorphism classes, exactly `ℵ₁` when uncountably many, and countably many iff the
  rank is bounded.  That composition is left to the consumer: this module does **not** import
  `Descriptive.ScatteredCounting`, and `Descriptive.ScatteredCounting` imports nothing from
  `Conditional`.
* **Countable language.**  `[Countable (Σ l, L.Relations l)]` is used to make the space of codes
  Polish and `bfEquivSetoid` Borel, for Silver's theorem.
* **Why `Conditional`.**  The module consumes Silver's theorem through
  `Conditional/SilverAntichain.lean`.

## References

* M. Morley, "The number of countable models", *J. Symbolic Logic* 35 (1970), 14–18 (the
  level-by-level analysis of the back-and-forth stratification; here each level is handled by
  Silver's dichotomy).
* J. H. Silver, "Counting the number of equivalence classes of Borel and coanalytic equivalence
  relations", *Ann. Math. Logic* 18 (1980), 1–28.

The composition was offered for upstreaming by a consumer of this library.
-/

universe u v

namespace FirstOrder.Language

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

/-- **A thin sentence has back-and-forth scattered models.**  If `Θ` is thin on its coded models,
then at every level `η < ω₁` its coded models fall into countably many `CodeBFEquiv η`-classes.
The per-level step is the one inlined in `morley_counting_coded_or_perfect`. -/
theorem Sentenceω.bfScattered_of_isThinOnNatModels {Θ : L.Sentenceω}
    (h : Θ.IsThinOnNatModels) : BFScattered (ModelsOf Θ) := by
  intro η hη
  rcases silver_countable_or_cantorAntichain (modelsOf_measurableSet Θ) (structureIsoSetoid L)
      (bfEquivSetoid Θ η) (fun _ _ h ↦ isoSetoid_refines_bfEquivSetoid Θ η h)
      (bfEquivSetoid_measurableSet Θ η hη) with hc | hcantor
  · rw [← bfEquivSetoid_eq_comap]; exact hc
  · exact absurd (Sentenceω.hasPerfectSet_of_ambient_cantorAntichain hcantor) h

/-- **Thin iff back-and-forth scattered**, for the coded models of a sentence: the converse
direction is `isThinOn_of_bfScattered`. -/
theorem Sentenceω.bfScattered_iff_isThinOnNatModels {Θ : L.Sentenceω} :
    BFScattered (ModelsOf Θ) ↔ Θ.IsThinOnNatModels :=
  ⟨isThinOn_of_bfScattered, Sentenceω.bfScattered_of_isThinOnNatModels⟩

/-- **Fewer than continuum many classes give back-and-forth scatteredness**: a perfect set of
pairwise non-isomorphic coded models would give continuum many isomorphism classes, so `Θ` is
thin. -/
theorem Sentenceω.bfScattered_modelsOf_of_lt_continuum {Θ : L.Sentenceω}
    (h : Cardinal.mk (Quotient (isoSetoid Θ)) < Cardinal.continuum) :
    BFScattered (ModelsOf Θ) :=
  Sentenceω.bfScattered_of_isThinOnNatModels fun hp ↦
    (Sentenceω.HasPerfectSetOfPairwiseNonisomorphicNatModels.continuum_le hp).not_gt h

end FirstOrder.Language
