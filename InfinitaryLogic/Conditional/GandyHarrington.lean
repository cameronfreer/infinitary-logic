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

`gandy_harrington_for_relation` (general Borel relations) currently carries a sorry. The
statement is a classical ZFC theorem (Silver, 1980), but its proof requires
descriptive-set-theory infrastructure not yet in mathlib: either Kuratowski–Ulam +
Banach–Mazur games (Kechris, CDST Ch 21) or lightface Gandy–Harrington (Harrington 1985).
Once filled, `silver_core_polish`, `silverBurgessDichotomy`, and `morley_counting` become
unconditional.

The **equality case** is unconditional: see `gandy_harrington_for_eq` (axiom-clean, via
Cantor–Bendixson).

**Why there is no easy reduction to a "closed relation" case.** A tempting plan is to refine
the Polish topology so the Borel relation becomes *closed* and then run a Cantor scheme. This
is invalid in general: a closed equivalence relation on a Polish space is *smooth* (the class
map `x ↦ [x]` into the Effros–Borel space is Borel), so "potentially closed ⟹ smooth". But
`E₀` (eventual equality on `2^ℕ`) is a Borel equivalence relation with continuum-many classes
— so Silver applies — that is **not** smooth (Glimm–Effros), hence not potentially closed. So
the hard core of Silver is exactly the non-smooth relations, which cannot be made closed by a
change of topology; the effective (Gandy–Harrington) or games content is irreducible here.
-/

universe u v

open Set Cardinal Topology MeasureTheory

/-! ### Frontier status

Invariant for this development (audited; axioms confirmed via `#print axioms`):

* **All active infinitary-logic results are proved**, and the only active descriptive-set-
  theory frontier is Silver / Gandy–Harrington, namely `gandy_harrington_for_relation` below
  — the single non-legacy `sorry` in the project.
* **Conditional endpoints** chain through exactly that one `sorry` and nothing else
  (`[propext, Classical.choice, Quot.sound, sorryAx]`): `silver_core_polish`,
  `silverBurgessDichotomy`, and the *unconditional* instantiation of `morley_counting`.
  `morley_counting` itself takes the dichotomy as a hypothesis, so the parametrized form is
  axiom-clean — the `sorry` enters only when one supplies `silverBurgessDichotomy`.
* **The false "potentially closed" reduction is explicitly ruled out** (`E₀`; see the `## Status`
  note and the `gandy_harrington_for_relation` docstring). No declaration depends on it.
* `gandy_harrington_for_eq` is a small axiom-clean sanity check (the `r = ⊥` case), **not** a
  step toward the general theorem — it does not shorten the route to `gandy_harrington_for_relation`.

Do not add smooth / potentially-closed Silver variants unless deliberately building DST
infrastructure: the missing content is exactly the non-smooth case, which is the core theorem. -/

/-- **Silver's theorem for Borel equivalence relations.** A Borel equivalence
relation on a Polish space with uncountably many classes contains a perfect set
of pairwise-inequivalent points: there is a continuous injection
`f : (ℕ → Bool) → α` such that distinct inputs produce r-inequivalent outputs.

Provable via Kuratowski–Ulam + Banach–Mazur games (Kechris CDST Ch 21) or via
lightface Gandy–Harrington; neither DST infrastructure is currently in mathlib.

**`E₀` obstruction (do not try to reduce to a closed relation).** One cannot prove this by
refining the topology to make `r` closed and running a Cantor scheme: that route only works
for *smooth* (potentially closed) relations, and `E₀` — eventual equality on `2^ℕ`, a Borel
relation with continuum-many classes — is not smooth, so it is not potentially closed. The
hard content is precisely these non-smooth relations. The equality case (`r = ⊥`) *is*
unconditional: see `gandy_harrington_for_eq`. (See the module `## Status` note for detail.) -/
theorem gandy_harrington_for_relation {α : Type u}
    [MetricSpace α] [CompleteSpace α] [SecondCountableTopology α]
    [MeasurableSpace α] [BorelSpace α]
    (r : Setoid α) (hr : MeasurableSet {p : α × α | r.r p.1 p.2})
    (hunc : ¬ Countable (Quotient r)) :
    ∃ f : (ℕ → Bool) → α,
      Continuous f ∧ Function.Injective f ∧
      ∀ a b, a ≠ b → ¬ r.r (f a) (f b) := by
  sorry

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
