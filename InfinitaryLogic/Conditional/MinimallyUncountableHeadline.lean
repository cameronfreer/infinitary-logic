/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Conditional.BFScatteredSilver
import InfinitaryLogic.Descriptive.MinimallyUnbounded
import InfinitaryLogic.Descriptive.MinimallyUncountableThin

/-!
# Minimally uncountable sentences: the headline

For a sentence `Θ` of a countable relational language, the rank-free notion of
`Descriptive/MinimallyUncountable.lean` is back-and-forth scatteredness together with the
rank-parametric analogue of [Mon, Def XII.4] (`Descriptive/MinimallyUnbounded.lean`), for **any**
isolating rank `ρ` (`Sentenceω.minimallyUncountable_iff`).  Equivalently, minimal uncountability
is concentration at back-and-forth levels together with uncountably many isomorphism classes of
coded models (`Sentenceω.minimallyUncountable_iff_concentrated`).

## Main declarations

* `Sentenceω.minimallyUncountable_iff`: for an isolating rank `ρ`,
  `MinimallyUncountableOn (ModelsOf Θ) ↔ BFScattered (ModelsOf Θ) ∧ Θ.MinimallyUnbounded ρ`.
  The right side does not depend on `ρ` among isolating ranks.  The landed instance is
  `codeStabilizationOrdinal` (`isIsolatingRank_codeStabilizationOrdinal`,
  `Descriptive/ScatteredCounting.lean`).
* `Sentenceω.minimallyUncountable_iff_concentrated`: `MinimallyUncountableOn (ModelsOf Θ)` iff
  `ConcentratedAtBFLevels (ModelsOf Θ)` and the coded models meet uncountably many isomorphism
  classes.  No rank occurs.

## Proof

The only step that is not a restatement is that a minimally uncountable model class is
back-and-forth scattered.  It composes `MinimallyUncountableOn.isThinOn`
(`Descriptive/MinimallyUncountableThin.lean`: a minimally uncountable class is thin) with
`Sentenceω.bfScattered_of_isThinOnNatModels` (`Conditional/BFScatteredSilver.lean`: a thin
sentence has back-and-forth scattered models).  Given scatteredness, the first theorem is
`minimallyUnboundedOn_iff_minimallyUncountableOn`, and the second is
`bfScattered_and_minimallyUncountableOn_iff` for the Borel, hence analytic, set
`ModelsOf Θ` (`modelsOf_measurableSet`).  The same composition discharges, for the models of a
minimally uncountable sentence, the per-level countability hypothesis of
`MinimallyUncountableOn.exists_bfClass_compl_countable`.

## Dependencies

* **Why `Conditional`.**  The scatteredness step consumes Silver's theorem, through
  `Sentenceω.bfScattered_of_isThinOnNatModels` and `Conditional/SilverAntichain.lean`.
* **Proof cones.**  The forward directions reach the López–Escobar theorem `lopez_escobar`
  (through `MinimallyUncountableOn.isThinOn`, whose splits criterion uses sentence recovery)
  and the Silver chain (`silver_countable_or_cantorAntichain` and `silver_core_polish`, through
  `Sentenceω.bfScattered_of_isThinOnNatModels`).  Both are asserted positively by
  `check_minimally_uncountable_headline_regressions.lean`, separately from its axiom audit; the
  axioms are the standard `propext`, `Classical.choice` and `Quot.sound`.
* **Conventions.**  The level relation is this library's `BFEquiv` (through `CodeBFEquiv`); it is
  not identified with the book's tuple relations `≡_α`, and no `ρ` is identified with a Scott
  rank of the book.

## Scope

Of [Mon, Lemma XII.8] only the first half is formalized
(`MinimallyUncountableOn.exists_bfClass_compl_countable`), and it enters only the concentrated
form.  No minimally uncountable sentence is exhibited.

## References

* [Mon] A. Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, draft, Chapter XII,
  §XII.2 (Def XII.4, Lemma XII.8).

The composition was offered for upstreaming by a consumer of this library.
-/

universe u v

namespace FirstOrder.Language

open Set MeasureTheory

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

/-- **Minimally uncountable sentences, through any isolating rank**: the models of `Θ` are
minimally uncountable iff they are back-and-forth scattered and `Θ` is minimally unbounded for
`ρ` (the analogue of [Mon, Def XII.4]).  The scatteredness half goes through Silver's theorem
(`Sentenceω.bfScattered_of_isThinOnNatModels`) and López–Escobar
(`MinimallyUncountableOn.isThinOn`). -/
theorem Sentenceω.minimallyUncountable_iff {ρ : StructureSpace L → Ordinal.{0}}
    (hρ : IsIsolatingRank ρ) (Θ : L.Sentenceω) :
    MinimallyUncountableOn (ModelsOf Θ) ↔
      BFScattered (ModelsOf Θ) ∧ Θ.MinimallyUnbounded ρ := by
  refine ⟨fun h ↦ ?_, fun ⟨hK, h⟩ ↦ (minimallyUnboundedOn_iff_minimallyUncountableOn hρ hK).mp h⟩
  have hK := Sentenceω.bfScattered_of_isThinOnNatModels h.isThinOn
  exact ⟨hK, (minimallyUnboundedOn_iff_minimallyUncountableOn hρ hK).mpr h⟩

/-- **Minimally uncountable sentences, through concentration**: the models of `Θ` are minimally
uncountable iff they are concentrated at back-and-forth levels and meet uncountably many
isomorphism classes.  No rank occurs. -/
theorem Sentenceω.minimallyUncountable_iff_concentrated (Θ : L.Sentenceω) :
    MinimallyUncountableOn (ModelsOf Θ) ↔ ConcentratedAtBFLevels (ModelsOf Θ) ∧
      ¬ (Quotient.mk (structureIsoSetoid L) '' ModelsOf Θ).Countable := by
  have hKa : AnalyticSet (ModelsOf Θ) := (modelsOf_measurableSet Θ).analyticSet
  refine ⟨fun h ↦ ?_, fun h ↦ ((bfScattered_and_minimallyUncountableOn_iff hKa).mpr h).2⟩
  exact (bfScattered_and_minimallyUncountableOn_iff hKa).mp
    ⟨Sentenceω.bfScattered_of_isThinOnNatModels h.isThinOn, h⟩

end FirstOrder.Language
