/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Conditional.SilverBurgess

/-!
# Silver's Theorem for Borel Equivalence Relations

This file provides:
1. `gandy_harrington_for_relation`: Silver's theorem for Borel equivalence
   relations on Polish spaces — a Borel equivalence relation with uncountably
   many classes contains a perfect set of pairwise-inequivalent points.
2. `silver_core_polish`: the dichotomy form (countable quotient or perfect
   set of inequivalent points), derived as a thin wrapper.
3. `silverBurgessDichotomy`: the full dichotomy for standard Borel spaces.

## Status

`gandy_harrington_for_relation` currently carries a sorry. The statement is
a classical ZFC theorem (Silver, 1980), but its proof requires
descriptive-set-theory infrastructure not yet in mathlib: either
Kuratowski–Ulam + Banach–Mazur games (Kechris, CDST Ch 21) or lightface
Gandy–Harrington (Harrington 1985). Once filled, `silver_core_polish`,
`silverBurgessDichotomy`, and `morley_counting` become unconditional.
-/

universe u v

open Set Cardinal Topology MeasureTheory

/-- **Silver's theorem for Borel equivalence relations.** A Borel equivalence
relation on a Polish space with uncountably many classes contains a perfect set
of pairwise-inequivalent points: there is a continuous injection
`f : (ℕ → Bool) → α` such that distinct inputs produce r-inequivalent outputs.

Provable via Kuratowski–Ulam + Banach–Mazur games (Kechris CDST Ch 21) or via
lightface Gandy–Harrington; neither DST infrastructure is currently in mathlib. -/
theorem gandy_harrington_for_relation {α : Type u}
    [MetricSpace α] [CompleteSpace α] [SecondCountableTopology α]
    [MeasurableSpace α] [BorelSpace α]
    (r : Setoid α) (hr : MeasurableSet {p : α × α | r.r p.1 p.2})
    (hunc : ¬ Countable (Quotient r)) :
    ∃ f : (ℕ → Bool) → α,
      Continuous f ∧ Function.Injective f ∧
      ∀ a b, a ≠ b → ¬ r.r (f a) (f b) := by
  sorry

/-- **Silver's theorem** (dichotomy form) for Borel equivalence relations on
Polish spaces. Either the quotient is countable, or there exists a perfect set
of pairwise-inequivalent points. -/
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
  · exact Or.inr (gandy_harrington_for_relation r hr hcount)

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
