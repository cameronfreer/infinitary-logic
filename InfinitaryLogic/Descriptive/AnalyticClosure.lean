/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Closure properties of analytic sets

Closure properties of analytic sets that Mathlib lacks: finite intersections
(`MeasureTheory.AnalyticSet.inter`, and `MeasureTheory.AnalyticSet.inter_measurableSet` for
intersection with a Borel set), products (`MeasureTheory.AnalyticSet.prod`), and the
off-diagonal of a closed subset of a Polish space (`MeasureTheory.analyticSet_offDiag`).  The
statements are Mathlib-shaped; they are used by the `G₀` dichotomy
(`InfinitaryLogic/Descriptive/G0Dichotomy.lean`), by the back-and-forth separation
(`InfinitaryLogic/Descriptive/BFSeparation.lean`), and by thinness from countably many
back-and-forth classes (`InfinitaryLogic/Descriptive/BFScattered.lean`).
-/

namespace MeasureTheory

variable {α : Type*} [TopologicalSpace α]

protected theorem AnalyticSet.inter [T2Space α] {A B : Set α}
    (hA : AnalyticSet A) (hB : AnalyticSet B) : AnalyticSet (A ∩ B) := by
  rw [Set.inter_eq_iInter]
  exact AnalyticSet.iInter fun b => by cases b <;> simpa

protected theorem AnalyticSet.inter_measurableSet [PolishSpace α] [MeasurableSpace α]
    [BorelSpace α] {A B : Set α} (hA : AnalyticSet A) (hB : MeasurableSet B) :
    AnalyticSet (A ∩ B) :=
  hA.inter hB.analyticSet

protected theorem AnalyticSet.prod {β : Type*} [TopologicalSpace β] {A : Set α} {B : Set β}
    (hA : AnalyticSet A) (hB : AnalyticSet B) : AnalyticSet (A ×ˢ B) := by
  obtain ⟨X, hXt, hXp, f, hf, rfl⟩ := analyticSet_iff_exists_polishSpace_range.mp hA
  obtain ⟨Y, hYt, hYp, g, hg, rfl⟩ := analyticSet_iff_exists_polishSpace_range.mp hB
  let := hXt; have := hXp; let := hYt; have := hYp
  rw [← Set.range_prodMap]
  exact analyticSet_range_of_polishSpace (hf.prodMap hg)

/-- **The off-diagonal of a closed set is analytic** in a Polish space: it is `P ×ˢ P` minus the
diagonal (`Set.prod_sdiff_diagonal`), the intersection of a closed set with the complement of the
closed diagonal, and both are analytic in the Polish space `α × α`. -/
theorem analyticSet_offDiag [PolishSpace α] {P : Set α} (hP : IsClosed P) :
    AnalyticSet P.offDiag := by
  rw [← Set.prod_sdiff_diagonal, Set.sdiff_eq]
  refine (hP.prod hP).analyticSet.inter ?_
  simpa using isClosed_diagonal.isOpen_compl.analyticSet_image continuous_id

end MeasureTheory
