/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.MetricSpace.Polish

/-!
# A Gδ subset of a Polish space is Polish

The easy half of Alexandrov's theorem, in its subspace topology, with no nonemptiness assumption:

* `IsGδ.polishSpace`: a Gδ subset of a Polish space is Polish.
* `IsGδ.standardBorelSpace`: a Gδ subset of a Polish Borel space is standard Borel.

Mathlib (at the pinned revision) supplies the open, closed, and closed-embedding cases
(`IsOpen.polishSpace`, `IsClosed.polishSpace`, `Topology.IsClosedEmbedding.polishSpace`) but not
the Gδ case.  Proof: write `s = ⋂ n, U n` with each `U n` open (`IsGδ.eq_iInter_nat`, indexed by
`ℕ`, so no case split for a finite or empty family); the diagonal map `s → Π n, U n` is a closed
embedding of `s` into a Polish product, since composing with the coordinate `0` and the inclusion
recovers the subtype inclusion of `s`, and its range `{g | ∀ n, (g n : α) = g 0}` is closed by
Hausdorffness.

Only the implication "Gδ implies Polish" is provided; the converse is a different theorem.
Nothing here refines a topology.  The root names follow Mathlib's `IsOpen.polishSpace`; a later
Mathlib supplying the same theorems will clash at the dependency update, which is the signal to
delete this module.
-/

open Set Topology TopologicalSpace

/-- A Gδ subset of a Polish space is Polish, in its subspace topology. -/
theorem IsGδ.polishSpace {α : Type*} [TopologicalSpace α] [PolishSpace α] {s : Set α}
    (hs : IsGδ s) : PolishSpace s := by
  obtain ⟨U, hUo, rfl⟩ := hs.eq_iInter_nat
  have hU : ∀ n, PolishSpace (U n) := fun n ↦ (hUo n).polishSpace
  have : PolishSpace (∀ n, U n) := PolishSpace.mk
  let f : (⋂ n, U n : Set α) → ∀ n, U n := fun x n ↦ ⟨x, mem_iInter.1 x.2 n⟩
  have hfc : Continuous f :=
    continuous_pi fun n ↦ (continuous_subtype_val.subtype_mk fun x ↦ mem_iInter.1 x.2 n)
  have hg : Continuous fun g : (∀ n, U n) ↦ (g 0 : α) :=
    continuous_subtype_val.comp (continuous_apply 0)
  have hrange : range f = {g | ∀ n, (g n : α) = g 0} := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩ n
      rfl
    · intro hgn
      refine ⟨⟨g 0, mem_iInter.2 fun n ↦ hgn n ▸ (g n).2⟩, funext fun n ↦ ?_⟩
      exact Subtype.ext (hgn n).symm
  refine IsClosedEmbedding.polishSpace (f := f) ⟨IsEmbedding.of_comp hfc hg ?_, ?_⟩
  · exact IsEmbedding.subtypeVal
  · rw [hrange, ofPred_forall]
    exact isClosed_iInter fun n ↦
      isClosed_eq (continuous_subtype_val.comp (continuous_apply n)) hg

/-- A Gδ subset of a Polish Borel space is standard Borel, in the subspace structures. -/
theorem IsGδ.standardBorelSpace {α : Type*} [TopologicalSpace α] [PolishSpace α]
    [MeasurableSpace α] [BorelSpace α] {s : Set α} (hs : IsGδ s) : StandardBorelSpace s :=
  haveI := hs.polishSpace
  inferInstance
