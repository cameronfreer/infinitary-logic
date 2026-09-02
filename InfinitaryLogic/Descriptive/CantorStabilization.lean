/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Metrizable.CompletelyMetrizable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.MetricSpace.Perfect

/-!
# Stabilizing countably many Borel maps on a Cantor subcopy

`CantorStabilization.exists_subcopy_continuous`: given countably many maps
`g i : (ℕ → Bool) → C i` into countable discrete spaces, each with Borel fibres, there is one
continuous injective `e : (ℕ → Bool) → (ℕ → Bool)` along which **all** the composites `g i ∘ e`
are continuous.  (Kechris, CDST 8.38 in spirit: Baire-measurable functions are continuous on a
comeager set; here the comeager set is then thinned to a Cantor copy.)  The conclusion is
continuity of `g i ∘ e`, not continuity of `g i` at the points of `range e`.

This is the natural companion of the Cantor-antichain vocabulary in this directory: a
construction that produces a Cantor antichain and then needs countably many pieces of Borel
data along it to be *continuous* may pass to the subcopy `e` first, uniformly for all of them at
once.

## Route

* Each fibre `g i ⁻¹' {c}` differs from an open set `U` by a meager set — the Baire property of
  Borel sets, `MeasurableSet.residualEq_isOpen`.
* The countably many exceptional sets are absorbed into one comeager set `G` on which every
  fibre is the trace of its open approximant; `G` is Borel.
* `G` is uncountable: a countable subset of Cantor space is meager (Cantor space has no isolated
  points, `cantor_nhdsNE_neBot`), and a residual set is not (`not_isMeagre_of_mem_residual`).
* An uncountable Borel subset of a Polish space contains a continuous injective copy of Cantor
  space (`MeasurableSet.exists_nat_bool_injection_of_not_countable`): pass to a finer Polish
  topology making the set clopen (`MeasurableSet.isClopenable`), apply the closed-set Cantor
  injection there, and note that the injection stays continuous for the coarser topology.
* Along that copy every fibre of `g i ∘ e` is the preimage of an open set.

## Implementation notes

* `PolishSpace (ℕ → Bool)` does not currently synthesize; it is assembled here from the countable-Pi
  second-countability and complete-metrizability instances and kept **local** to this file.
* The Borel-set-contains-Cantor-copy lemma is stated for an arbitrary Polish space; Mathlib has
  only the closed-set form (`IsClosed.exists_nat_bool_injection_of_not_countable`).
-/

open Topology Filter Set Function

namespace CantorStabilization

/-- Cantor space is Polish (second countable + completely metrizable, both from the countable
product instances).  Local to this file. -/
private theorem polishSpace_cantor : PolishSpace (ℕ → Bool) :=
  PolishSpace.mk

attribute [local instance] polishSpace_cantor

/-! ## Cantor space has no isolated points -/

/-- Flipping the `n`-th coordinate converges to `x` while staying away from it. -/
private theorem cantor_nhdsNE_neBot (x : ℕ → Bool) : (𝓝[≠] x).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot]
  refine mem_closure_of_tendsto (b := atTop) (f := fun n : ℕ => Function.update x n (!x n)) ?_ ?_
  · refine tendsto_pi_nhds.2 fun i => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop i] with n hn
    exact (Function.update_of_ne hn.ne _ _).symm
  · refine Eventually.of_forall fun n => ?_
    intro h
    have := congrFun h n
    simp at this

private theorem isMeagre_singleton_cantor (x : ℕ → Bool) : IsMeagre ({x} : Set (ℕ → Bool)) := by
  have := cantor_nhdsNE_neBot x
  exact residual_of_dense_open isOpen_compl_singleton (dense_compl_singleton x)

private theorem isMeagre_of_countable_cantor {s : Set (ℕ → Bool)} (hs : s.Countable) :
    IsMeagre s := by
  rw [← Set.biUnion_of_singleton s]
  exact isMeagre_biUnion hs fun x _ => isMeagre_singleton_cantor x

private theorem not_countable_of_mem_residual_cantor {s : Set (ℕ → Bool)} (hs : s ∈ residual _) :
    ¬ s.Countable :=
  fun h => not_isMeagre_of_mem_residual hs (isMeagre_of_countable_cantor h)

/-! ## Uncountable Borel sets contain Cantor copies -/

/-- An uncountable Borel subset of a Polish space contains a continuous injective copy of Cantor
space.  (Finer Polish topology making the set clopen, then the closed-set Cantor injection; the
injection stays continuous for the original, coarser topology.) -/
theorem _root_.MeasurableSet.exists_nat_bool_injection_of_not_countable
    {α : Type*} [TopologicalSpace α] [PolishSpace α] [MeasurableSpace α] [BorelSpace α]
    {s : Set α} (hs : MeasurableSet s) (hunc : ¬ s.Countable) :
    ∃ f : (ℕ → Bool) → α, range f ⊆ s ∧ Continuous f ∧ Injective f := by
  obtain ⟨t', hle, ht', hclosed, -⟩ := hs.isClopenable
  obtain ⟨f, hrange, hcont, hinj⟩ :=
    @IsClosed.exists_nat_bool_injection_of_not_countable α t' ht' s hclosed hunc
  exact ⟨f, hrange, continuous_le_rng hle hcont, hinj⟩

/-! ## The stabilization theorem -/

/-- **Stabilization on a Cantor subcopy.**  Countably many maps from Cantor space into countable
discrete spaces with Borel fibres become simultaneously continuous after composing with one
continuous injective self-map of Cantor space. -/
theorem exists_subcopy_continuous
    {ι : Type*} [Countable ι] {C : ι → Type*} [∀ i, TopologicalSpace (C i)]
    [∀ i, DiscreteTopology (C i)] [∀ i, Countable (C i)]
    (g : ∀ i, (ℕ → Bool) → C i) (hg : ∀ i (c : C i), MeasurableSet (g i ⁻¹' {c})) :
    ∃ e : (ℕ → Bool) → (ℕ → Bool), Continuous e ∧ Injective e ∧ ∀ i, Continuous (g i ∘ e) := by
  have hU : ∀ p : Σ i, C i, ∃ U : Set (ℕ → Bool), IsOpen U ∧ (g p.1 ⁻¹' {p.2}) =ᵇ U :=
    fun p => (hg p.1 p.2).residualEq_isOpen
  choose U hUo hUeq using hU
  -- the comeager set on which every fibre agrees with its open approximant
  set G : Set (ℕ → Bool) := {x | ∀ p : Σ i, C i, g p.1 x = p.2 ↔ x ∈ U p} with hGdef
  have hGres : G ∈ residual (ℕ → Bool) := by
    have : ∀ᶠ x in residual (ℕ → Bool), ∀ p : Σ i, C i, g p.1 x = p.2 ↔ x ∈ U p :=
      eventually_countable_forall.2 fun p =>
        (eventuallyEq_set.1 (hUeq p)).mono fun x hx => by simpa using hx
    exact this
  have hGmeas : MeasurableSet G := by
    have : G = ⋂ p : Σ i, C i,
        ((g p.1 ⁻¹' {p.2}) ∩ U p) ∪ ((g p.1 ⁻¹' {p.2})ᶜ ∩ (U p)ᶜ) := by
      ext x
      simp only [hGdef, mem_ofPred_eq, mem_iInter, mem_union, mem_inter_iff, mem_preimage,
        mem_singleton_iff, mem_compl_iff]
      refine forall_congr' fun p => ?_
      tauto
    rw [this]
    exact MeasurableSet.iInter fun p =>
      ((hg p.1 p.2).inter (hUo p).measurableSet).union
        ((hg p.1 p.2).compl.inter (hUo p).measurableSet.compl)
  obtain ⟨e, hrange, hcont, hinj⟩ :=
    hGmeas.exists_nat_bool_injection_of_not_countable (not_countable_of_mem_residual_cantor hGres)
  refine ⟨e, hcont, hinj, fun i => ?_⟩
  refine continuous_discrete_rng.2 fun c => ?_
  have : (g i ∘ e) ⁻¹' {c} = e ⁻¹' U ⟨i, c⟩ := by
    ext x
    have hx : e x ∈ G := hrange ⟨x, rfl⟩
    simp only [mem_preimage, comp_apply, mem_singleton_iff]
    exact hx ⟨i, c⟩
  rw [this]
  exact (hUo ⟨i, c⟩).preimage hcont

end CantorStabilization
