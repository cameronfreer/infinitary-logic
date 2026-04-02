/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.SilverBurgess
import Mathlib.Topology.Defs.Induced

/-!
# Gandy-Harrington Reduction and Silver's Theorem for Borel Relations

This file provides:
1. The Borel-to-closed reduction (`borel_to_closed_reduction`): if a Borel
   equivalence relation on a Polish space has uncountably many classes, there
   exists a Polish space Y with a continuous injective map to α on which the
   pulled-back relation is closed and still has uncountably many classes.
2. `silver_core_polish`: Silver's theorem for Borel equivalence relations,
   derived from the reduction + `silver_core_closed`.
3. `silverBurgessDichotomy`: the full dichotomy for standard Borel spaces.

## Status

`borel_to_closed_reduction` requires the Gandy-Harrington topology
construction (sorry). Once filled, `silver_core_polish` and
`silverBurgessDichotomy` become sorry-free, making `morley_counting`
fully unconditional.
-/

universe u v

open Set Cardinal Topology

/-- **Gandy-Harrington reduction**: A Borel equivalence relation on a Polish
space with uncountably many classes admits a Polish space Y with a continuous
injective map to α on which the pulled-back relation is closed and still has
uncountably many classes.

The proof requires the Gandy-Harrington topology construction (refining
the topology on α so that analytic sets become open in a Polish core). -/
theorem borel_to_closed_reduction {α : Type u}
    [MetricSpace α] [CompleteSpace α] [SecondCountableTopology α]
    [MeasurableSpace α] [BorelSpace α]
    (r : Setoid α) (hr : MeasurableSet {p : α × α | r.r p.1 p.2})
    (hunc : ¬ Countable (Quotient r)) :
    ∃ (Y : Type u) (_ : MetricSpace Y) (_ : CompleteSpace Y)
      (_ : SecondCountableTopology Y) (i : Y → α),
      Continuous i ∧ Function.Injective i ∧
      IsClosed {p : Y × Y | r.r (i p.1) (i p.2)} ∧
      ¬ Countable (Quotient (Setoid.comap i r)) := by
  sorry

/-- **Silver's theorem** for Borel equivalence relations on Polish spaces.
Reduces to the closed case via `borel_to_closed_reduction`, then applies
`silver_core_closed` on the subspace and composes with the embedding. -/
theorem silver_core_polish {α : Type u}
    [MetricSpace α] [CompleteSpace α] [SecondCountableTopology α]
    [MeasurableSpace α] [BorelSpace α]
    (r : Setoid α) (hr : MeasurableSet {p : α × α | r.r p.1 p.2}) :
    Countable (Quotient r) ∨
      ∃ f : (ℕ → Bool) → α,
        Continuous f ∧ Function.Injective f ∧
        ∀ a b, a ≠ b → ¬ r.r (f a) (f b) := by
  by_cases hcount : Countable (Quotient r)
  · exact Or.inl hcount
  · right
    -- Apply the Borel-to-closed reduction
    obtain ⟨Y, instM, instC, instS, i, hi_cont, hi_inj, hi_closed, hi_unc⟩ :=
      borel_to_closed_reduction r hr hcount
    -- Apply silver_core_closed on Y
    have hY := @silver_core_closed Y instM instC instS (Setoid.comap i r) hi_closed
    rcases hY with hY_count | ⟨f, hf_cont, hf_inj, hf_ineq⟩
    · exact absurd hY_count hi_unc
    · -- Compose f with i
      exact ⟨i ∘ f,
        hi_cont.comp hf_cont,
        hi_inj.comp hf_inj,
        fun a b hab h => hf_ineq a b hab (by rwa [Setoid.comap_rel])⟩

/-! ### Silver-Burgess dichotomy -/

namespace FirstOrder.Language

/-- The Silver-Burgess dichotomy for Borel equivalence relations on standard Borel
spaces, derived from `silver_core_polish`. -/
theorem silverBurgessDichotomy : SilverBurgessDichotomy.{v} := by
  intro X _ _ r hr
  -- Upgrade the standard Borel space to a Polish topology
  letI := upgradeStandardBorel X
  -- Further upgrade to a compatible complete metric
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable X
  rcases silver_core_polish r hr with h_count | ⟨f, hf_cont, hf_inj, hf_ineq⟩
  · left; exact mk_le_aleph0
  · right
    apply le_antisymm
    · haveI : Nonempty X := ⟨f (fun _ => false)⟩
      exact mk_quotient_le_continuum_of_polish r
    · have hinj : Function.Injective (fun x : ULift.{v} (ℕ → Bool) =>
          Quotient.mk r (f x.down)) := by
        intro ⟨a⟩ ⟨b⟩ h
        apply ULift.ext
        by_contra hab
        exact hf_ineq a b hab (Quotient.exact h)
      calc Cardinal.continuum
          = lift.{v} #(ℕ → Bool) := by
            rw [show #(ℕ → Bool) = Cardinal.continuum from
              (Cardinal.power_def Bool ℕ).symm.trans (by rw [Cardinal.mk_bool, Cardinal.mk_nat,
                Cardinal.two_power_aleph0])
            , Cardinal.lift_continuum]
        _ = #(ULift.{v} (ℕ → Bool)) := (Cardinal.mk_uLift _).symm
        _ ≤ #(Quotient r) := mk_le_of_injective hinj

end FirstOrder.Language
