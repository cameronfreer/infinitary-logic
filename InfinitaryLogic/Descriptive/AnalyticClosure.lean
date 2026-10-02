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
intersection with a Borel set), products (`MeasureTheory.AnalyticSet.prod`), and off-diagonals
in a Hausdorff space (`MeasureTheory.AnalyticSet.offDiag`).  The
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

/-- **The off-diagonal of an analytic set is analytic** in a Hausdorff space: if `P` is the range
of a continuous `f` on a Polish space, then `P.offDiag` is the image under `Prod.map f f` of the
open set of pairs with distinct values. -/
protected theorem AnalyticSet.offDiag [T2Space α] {P : Set α} (hP : AnalyticSet P) :
    AnalyticSet P.offDiag := by
  obtain ⟨β, hβt, hβp, f, hf, rfl⟩ := analyticSet_iff_exists_polishSpace_range.mp hP
  have hopen : IsOpen {q : β × β | f q.1 ≠ f q.2} :=
    (isClosed_eq (hf.comp continuous_fst) (hf.comp continuous_snd)).isOpen_compl
  have : (Set.range f).offDiag = Prod.map f f '' {q | f q.1 ≠ f q.2} := by
    ext ⟨x, y⟩
    constructor
    · rintro ⟨⟨a, rfl⟩, ⟨b, rfl⟩, h⟩
      exact ⟨(a, b), h, rfl⟩
    · rintro ⟨⟨a, b⟩, h, he⟩
      simp only [Prod.map, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨⟨a, rfl⟩, ⟨b, rfl⟩, h⟩
  rw [this]
  exact hopen.analyticSet_image (hf.prodMap hf)

end MeasureTheory
