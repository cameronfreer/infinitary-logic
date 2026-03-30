/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.CountingDichotomy
import Mathlib.Topology.MetricSpace.Perfect
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Architect

/-!
# Silver-Burgess Dichotomy: Foundations

This file establishes the foundational lemmas needed for the Silver-Burgess
dichotomy for Borel equivalence relations on standard Borel spaces.

## Main Results (Stage 1)

- `Perfect.mk_eq_continuum`: A nonempty perfect subset of a Polish space has
  cardinality exactly 2^ℵ₀.
- `continuum_classes_of_perfect_transversal`: If an equivalence relation has a
  perfect set of pairwise inequivalent elements, it has continuum classes.
-/

open Cardinal Set

universe u

/-! ### Perfect set cardinality -/

/-- A nonempty perfect subset of a Polish space has cardinality = continuum.
Lower bound via `Perfect.exists_nat_bool_injection`; upper bound via
second-countability of Polish spaces. -/
theorem Perfect.mk_eq_continuum {α : Type u} [MetricSpace α] [CompleteSpace α]
    [SecondCountableTopology α]
    {C : Set α} (hperf : Perfect C) (hne : C.Nonempty) :
    #C = Cardinal.continuum := by
  apply le_antisymm
  · -- Upper bound: #C ≤ 𝔠
    calc #C ≤ #α := mk_set_le C
      _ ≤ Cardinal.continuum := by
        haveI : Nonempty α := let ⟨x, _⟩ := hne; ⟨x⟩
        obtain ⟨f, _, hf_surj⟩ := PolishSpace.exists_nat_nat_continuous_surjective α
        have h1 := lift_mk_le_lift_mk_of_surjective hf_surj
        simp only [lift_uzero] at h1
        exact h1.trans (by simp [aleph0_power_aleph0])
  · -- Lower bound: 𝔠 ≤ #C
    obtain ⟨f, hf_range, _, hf_inj⟩ := hperf.exists_nat_bool_injection hne
    let g : (ℕ → Bool) → C := fun x => ⟨f x, hf_range (mem_range_self x)⟩
    have hg_inj : Function.Injective g := fun a b hab => hf_inj (Subtype.mk.inj hab)
    have h1 := lift_mk_le_lift_mk_of_injective hg_inj
    simp only [lift_uzero] at h1
    rw [show lift.{u} #(ℕ → Bool) = Cardinal.continuum from by simp] at h1
    exact h1

/-! ### Perfect transversal → continuum classes -/

/-- If an equivalence relation on a Polish space has a perfect set of
pairwise inequivalent elements, it has at least continuum classes. -/
theorem continuum_classes_of_perfect_transversal {α : Type u}
    [MetricSpace α] [CompleteSpace α] [SecondCountableTopology α]
    (r : Setoid α) {C : Set α} (hperf : Perfect C) (hne : C.Nonempty)
    (hinequiv : ∀ x ∈ C, ∀ y ∈ C, r.r x y → x = y) :
    Cardinal.continuum ≤ #(Quotient r) := by
  have hcard := hperf.mk_eq_continuum hne
  rw [← hcard]
  -- The quotient map restricted to C is injective
  exact Cardinal.mk_le_of_injective (f := fun ⟨x, hx⟩ => Quotient.mk r x)
    (fun ⟨x, hx⟩ ⟨y, hy⟩ hq => by
      exact Subtype.ext (hinequiv x hx y hy (Quotient.exact hq)))

/-- If an equivalence relation on a Polish space has a perfect set of
pairwise inequivalent elements, it has exactly continuum classes
(assuming the ambient space has cardinality ≤ continuum). -/
theorem eq_continuum_classes_of_perfect_transversal {α : Type u}
    [MetricSpace α] [CompleteSpace α] [SecondCountableTopology α]
    (r : Setoid α) {C : Set α} (hperf : Perfect C) (hne : C.Nonempty)
    (hinequiv : ∀ x ∈ C, ∀ y ∈ C, r.r x y → x = y)
    (hle : #α ≤ Cardinal.continuum) :
    #(Quotient r) = Cardinal.continuum := by
  apply le_antisymm
  · calc #(Quotient r) ≤ #α := Cardinal.mk_le_of_surjective (Quotient.mk_surjective)
      _ ≤ Cardinal.continuum := hle
  · exact continuum_classes_of_perfect_transversal r hperf hne hinequiv
