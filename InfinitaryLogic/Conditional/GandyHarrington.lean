/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Conditional.SilverBurgess
import InfinitaryLogic.Conditional.SilverCategoryRoute

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

**PROVED (2026-06-10).** `gandy_harrington_for_relation` is now sorry-free: it is the
endpoint of Miller's classical category route, fully formalized in this project
(see `docs/silver-phase2-route.md` for the development record):

* `G0Fusion.exists_gsGraph_hom` — the classical Kechris–Solecki–Todorcevic
  `G₀`-dichotomy construction (positivity ideals, Lusin separation, fusion);
* `gSGraphHomHypothesis_holds` — the homomorphism input, in `SilverCategoryRoute.lean`;
* `isMeagre_pullback_class_of_gSGraph_hom` (Miller Prop. 6), `isMeagre_of_isMeagre_sections`
  (Kuratowski–Ulam), and `mycielski_cantor` (Mycielski) — the category glue;
* `gandy_harrington_of_gSGraphHom` — the assembly used below.

Consequently `silver_core_polish`, `silverBurgessDichotomy`, and the instantiation of
`morley_counting` are unconditional, with axioms exactly
`[propext, Classical.choice, Quot.sound]`.

The **equality case** `gandy_harrington_for_eq` (via Cantor–Bendixson) is kept as a simple
direct proof of the smooth end of the dichotomy.

**Why there was no easy reduction to a "closed relation" case.** A tempting plan is to refine
the Polish topology so the Borel relation becomes *closed* and then run a Cantor scheme. This
is invalid in general: a closed equivalence relation on a Polish space is *smooth* (the class
map `x ↦ [x]` into the Effros–Borel space is Borel), so "potentially closed ⟹ smooth". But
`E₀` (eventual equality on `2^ℕ`) is a Borel equivalence relation with continuum-many classes
— so Silver applies — that is **not** smooth (Glimm–Effros), hence not potentially closed. So
the hard core of Silver is exactly the non-smooth relations — the `G₀`-dichotomy content of
the category route.
-/

universe u v

open Set Cardinal Topology MeasureTheory

/-! ### Status

Audited invariant (axioms confirmed via `#print axioms`): the project's descriptive-set-theory
chain is **sorry-free**. `gandy_harrington_for_relation`, `silver_core_polish`,
`silverBurgessDichotomy`, and the unconditional instantiation of `morley_counting` all report
exactly `[propext, Classical.choice, Quot.sound]`. -/

/-- **Silver's theorem for Borel equivalence relations.** A Borel equivalence
relation on a Polish space with uncountably many classes contains a perfect set
of pairwise-inequivalent points: there is a continuous injection
`f : (ℕ → Bool) → α` such that distinct inputs produce r-inequivalent outputs.

Proved via Miller's classical category route: the `G₀`-dichotomy homomorphism
(`gSGraphHomHypothesis_holds`, by the fusion construction `G0Fusion.exists_gsGraph_hom`),
Miller's independence lemma, Kuratowski–Ulam, and Mycielski's theorem, assembled by
`gandy_harrington_of_gSGraphHom`. -/
theorem gandy_harrington_for_relation {α : Type u}
    [MetricSpace α] [CompleteSpace α] [SecondCountableTopology α]
    [MeasurableSpace α] [BorelSpace α]
    (r : Setoid α) (hr : MeasurableSet {p : α × α | r.r p.1 p.2})
    (hunc : ¬ Countable (Quotient r)) :
    ∃ f : (ℕ → Bool) → α,
      Continuous f ∧ Function.Injective f ∧
      ∀ a b, a ≠ b → ¬ r.r (f a) (f b) :=
  gandy_harrington_of_gSGraphHom gSGraphHomHypothesis_holds r hr hunc

/-- **[Equality case, unconditional]** Silver's theorem when the relation is *equality*
(`r = ⊥`): an uncountable Polish space already contains a continuous injection
`(ℕ → Bool) → α`, so distinct inputs give distinct (hence `⊥`-inequivalent) outputs.

This is exactly `gandy_harrington_for_relation` instantiated at `r = ⊥` — but, unlike the
general Borel case, it needs no descriptive-set-theory machinery beyond mathlib's
Cantor–Bendixson theorem (`IsClosed.exists_nat_bool_injection_of_not_countable` applied to
`Set.univ`). It is the *smooth* end of the dichotomy; the hard content of Silver lives
entirely in the non-smooth relations (see the `E₀` note on `gandy_harrington_for_relation`). -/
theorem gandy_harrington_for_eq {α : Type u}
    [MetricSpace α] [CompleteSpace α] [SecondCountableTopology α]
    [MeasurableSpace α] [BorelSpace α]
    (hunc : ¬ Countable α) :
    ∃ f : (ℕ → Bool) → α,
      Continuous f ∧ Function.Injective f ∧ ∀ a b, a ≠ b → f a ≠ f b := by
  have hnc : ¬ (Set.univ : Set α).Countable := by
    rwa [Set.countable_univ_iff]
  obtain ⟨f, _, hcont, hinj⟩ :=
    isClosed_univ.exists_nat_bool_injection_of_not_countable hnc
  exact ⟨f, hcont, hinj, fun _ _ hab => hinj.ne hab⟩

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
