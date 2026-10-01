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
intersection with a Borel set) and products (`MeasureTheory.AnalyticSet.prod`).  The
statements are Mathlib-shaped; they are used by the `G₀` dichotomy
(`InfinitaryLogic/Descriptive/G0Dichotomy.lean`) and by the back-and-forth separation
(`InfinitaryLogic/Descriptive/BFSeparation.lean`).
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

end MeasureTheory
