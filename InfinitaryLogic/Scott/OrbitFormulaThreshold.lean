/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Scott.OrbitRank
import InfinitaryLogic.Karp.CarrierTheorem
import InfinitaryLogic.Lomega1omega.QuantifierRank

/-!
# Orbit formulas give back-and-forth thresholds

An **orbit formula** for a tuple `a : Fin n → M` is a formula whose realizations in `M` are
exactly the automorphic images of `a`:
`∀ b, φ.Realize b ↔ ∃ e : M ≃[L] M, ⇑e ∘ a = b`.
Over a relational language, back-and-forth equivalence to `a` at the (lifted) quantifier rank of
`φ` preserves `φ` (the forward Karp lemma `BFEquiv_implies_agreeQR`), so it already forces an
automorphism carrying `a` to `b`.

The file has two layers.

* **Infinitary orbit formulas.**  For `φ : L.Formulaω (Fin n)` an orbit formula of `a`, the orbit
  of `a` is determined at level `Ordinal.lift.{w, 0} φ.qrank`, so `orbitRank a` is at most that
  lifted rank.  If every tuple has an infinitary orbit formula of rank strictly below a fixed
  `α`, the semantic upper bound `internalScottRank_le_of_orbits_determined` gives
  `internalScottRank M ≤ Ordinal.lift.{w, 0} α`.
* **First-order orbit formulas.**  For `φ : L.Formula (Fin n)` an ordinary first-order formula of
  `L` itself, the infinitary results apply to `φ.toLω`, whose rank is finite
  (`BoundedFormula.qrank_toLω_lt_omega0`): the orbit of `a` is determined at a finite level.  If
  every tuple has a first-order orbit formula, `internalScottRank M ≤ ω`.

## Main declarations

* `orbit_determined_of_infinitaryOrbitFormula`: equivalence to `a` at
  `Ordinal.lift.{w, 0} φ.qrank` gives an automorphism carrying `a` to `b`.
* `orbitRank_le_lift_qrank_of_infinitaryOrbitFormula`: a tuple with an infinitary orbit formula
  `φ` has orbit rank at most `Ordinal.lift.{w, 0} φ.qrank`.
* `internalScottRank_le_of_infinitaryOrbitFormulas`: if every tuple has an infinitary orbit
  formula of rank `< α`, then `internalScottRank M ≤ Ordinal.lift.{w, 0} α`.
* `orbit_determined_of_orbitFormula`: equivalence to `a` at `Ordinal.lift φ.toLω.qrank` gives an
  automorphism carrying `a` to `b`.
* `exists_finite_orbit_threshold`: the same at some level `β < ω`.
* `orbitRank_le_lift_qrank_of_orbitFormula`: a tuple with an orbit formula `φ` has orbit rank
  at most `Ordinal.lift φ.toLω.qrank`.
* `orbitRank_lt_omega0_of_orbitFormula`: a tuple with an orbit formula has finite orbit rank.
* `internalScottRank_le_omega0_of_orbitFormulas`: if every tuple has an orbit formula,
  `internalScottRank M ≤ ω`.

## Interpretation notes

* **The automorphisms come from the premise.**  The orbit formula itself supplies the
  automorphism, so neither countability nor nonemptiness of `M` is assumed; no pointed Karp
  argument is used.  Neither the language nor the comparison ordinal `α` is assumed countable.
  Empty tuples and tuples with repeated coordinates are included.
* **Relational languages.**  The forward Karp lemma `BFEquiv_implies_agreeQR` is stated for
  relational languages, so the threshold theorems, first-order and infinitary, are too; this is
  a limitation of the present statements.  The finite-rank lemma
  `BoundedFormula.qrank_toLω_lt_omega0` holds for every language.
* **Strict pointwise premise.**  The internal Scott rank is `⨆ a, (orbitRank a + 1)`.  The
  premise of `internalScottRank_le_of_infinitaryOrbitFormulas` is a strict bound `φ.qrank < α`
  for each tuple's own formula, which is what the plus-one convention needs for the conclusion
  `≤ lift α`; no uniform formula is assumed.
* **What is not claimed.**  These results take orbit formulas as hypotheses: they do not
  construct orbit formulas, do not assert that an infinitary formula has finite rank, give no
  bound through `scottHeight`, and make no comparison with ranks shifted by `ω`.
* **`≤ ω`, not `< ω`, in the first-order case.**  Each tuple may have its own orbit formula, of
  its own finite rank; no uniform bound is assumed, so the internal Scott rank is only bounded
  by `ω`.  The exact-`ω` carrier of `ModelTheory/FiberExactOmega.lean` (see
  `scripts/check_rank_comparison_regressions.lean`) has every orbit rank finite and internal
  Scott rank exactly `ω`: pointwise finite thresholds need not give a uniform finite bound.
  That carrier is not claimed to have first-order orbit formulas, so it is not by itself a
  counterexample to a strict bound under the hypothesis here.
* **Stabilization and the Scott process.**  The per-tuple bounds feed the existing bound transport
  (`selfStabilizesCompletely_iff_orbitRank_le`, and `stabilizesAt_of_orbitRank_le` and
  `rank_le_of_orbitRank_le` in `ScottProcess/RankComparison.lean`) directly; no separate
  corollaries are stated here.  The regression guard composes them on the infinite pure set.
* **Orbit formulas, not isolating formulas.**  The premise is about automorphism orbits in the
  given structure.  A formula isolating a complete first-order type need not define an
  automorphism orbit in an arbitrary structure, so first-order atomicity alone is not a premise
  of these results.
* **Universes.**  `M : Type w`; orbit ranks and the internal Scott rank live in `Ordinal.{w}`,
  quantifier ranks of `Lω₁ω` formulas in `Ordinal.{0}`, and the thresholds are the explicit lifts
  `Ordinal.lift.{w, 0} φ.qrank` and `Ordinal.lift.{w, 0} φ.toLω.qrank`.
-/

universe u v w

namespace FirstOrder.Language

open Ordinal

variable {L : Language.{u, v}} [L.IsRelational] {M : Type w} [L.Structure M]

/-! ### Infinitary orbit formulas -/

/-- **An infinitary orbit formula determines the orbit at its own rank.**  If
`φ : L.Formulaω (Fin n)` defines the automorphism orbit of `a` in `M`, then every `b`
back-and-forth equivalent to `a` at level `Ordinal.lift.{w, 0} φ.qrank` is the image of `a` under
an automorphism.

The language is relational; `M` is arbitrary (neither countable nor nonempty), and the empty
tuple and tuples with repeated coordinates are included.  The orbit formula is a hypothesis: no
orbit formula is constructed here. -/
theorem orbit_determined_of_infinitaryOrbitFormula {n : ℕ} {a : Fin n → M}
    {φ : L.Formulaω (Fin n)}
    (hφ : ∀ b : Fin n → M, φ.Realize b ↔ ∃ e : M ≃[L] M, ⇑e ∘ a = b)
    (b : Fin n → M)
    (hb : BFEquiv (L := L) (Ordinal.lift.{w, 0} φ.qrank) n a b) :
    ∃ e : M ≃[L] M, ⇑e ∘ a = b := by
  have ha : φ.Realize a := (hφ a).mpr ⟨Language.Equiv.refl L M, rfl⟩
  have hagree := BFEquiv_implies_agreeQR (ι := ℕ) φ.qrank a b hb.toOrdinalLift φ le_rfl
  exact (hφ b).mp (hagree.mp ha)

/-- **The orbit rank is at most the rank of an infinitary orbit formula.**  If
`φ : L.Formulaω (Fin n)` defines the automorphism orbit of `a` in `M`, then `orbitRank a` is at
most the explicitly lifted rank `Ordinal.lift.{w, 0} φ.qrank`.  This does not assert that the
rank of `φ` is finite. -/
theorem orbitRank_le_lift_qrank_of_infinitaryOrbitFormula {n : ℕ} {a : Fin n → M}
    {φ : L.Formulaω (Fin n)}
    (hφ : ∀ b : Fin n → M, φ.Realize b ↔ ∃ e : M ≃[L] M, ⇑e ∘ a = b) :
    orbitRank (L := L) a ≤ Ordinal.lift.{w, 0} φ.qrank :=
  orbitRank_le_of_mem
    (mem_orbitStable_of_orbit_determined (orbit_determined_of_infinitaryOrbitFormula hφ))

/-- **Infinitary orbit formulas of rank `< α` bound the internal Scott rank by `α`.**  If every
tuple of `M` (of every length, the empty tuple included) has an infinitary orbit formula of
quantifier rank strictly below `α : Ordinal.{0}` (possibly a different formula for each tuple),
then `internalScottRank M ≤ Ordinal.lift.{w, 0} α`.

The premise is strict because the internal Scott rank is the supremum of `orbitRank a + 1`.
Neither `M`, nor the language, nor `α` is assumed countable, and `M` may be empty.  No orbit
formula is constructed and no bound through `scottHeight` is stated. -/
theorem internalScottRank_le_of_infinitaryOrbitFormulas {α : Ordinal.{0}}
    (h : ∀ (n : ℕ) (a : Fin n → M), ∃ φ : L.Formulaω (Fin n),
      φ.qrank < α ∧ ∀ b : Fin n → M,
        φ.Realize b ↔ ∃ e : M ≃[L] M, ⇑e ∘ a = b) :
    internalScottRank (L := L) M ≤ Ordinal.lift.{w, 0} α := by
  apply internalScottRank_le_of_orbits_determined
  intro n a
  obtain ⟨φ, hbound, hφ⟩ := h n a
  exact ⟨Ordinal.lift.{w, 0} φ.qrank, Ordinal.lift_lt.mpr hbound,
    orbit_determined_of_infinitaryOrbitFormula hφ⟩

/-! ### First-order orbit formulas -/

/-- **An orbit formula determines the orbit at its own rank.**  If the first-order formula `φ`
defines the automorphism orbit of `a` in `M`, then every `b` back-and-forth equivalent to `a` at
level `Ordinal.lift.{w} φ.toLω.qrank` is the image of `a` under an automorphism.  This is
`orbit_determined_of_infinitaryOrbitFormula` for `φ.toLω`. -/
theorem orbit_determined_of_orbitFormula {n : ℕ} {a : Fin n → M} {φ : L.Formula (Fin n)}
    (hφ : ∀ b : Fin n → M, φ.Realize b ↔ ∃ e : M ≃[L] M, ⇑e ∘ a = b) (b : Fin n → M)
    (hb : BFEquiv (L := L) (Ordinal.lift.{w, 0} φ.toLω.qrank) n a b) :
    ∃ e : M ≃[L] M, ⇑e ∘ a = b :=
  orbit_determined_of_infinitaryOrbitFormula
    (fun b ↦ (Formula.realize_toLω φ).trans (hφ b)) b hb

/-- **An orbit formula gives a finite threshold.**  If some first-order formula defines the
automorphism orbit of `a` in `M`, then the orbit of `a` is determined at some finite level: some
`β < ω` such that every `b` equivalent to `a` at level `β` is an automorphic image of `a`. -/
theorem exists_finite_orbit_threshold {n : ℕ} {a : Fin n → M} {φ : L.Formula (Fin n)}
    (hφ : ∀ b : Fin n → M, φ.Realize b ↔ ∃ e : M ≃[L] M, ⇑e ∘ a = b) :
    ∃ β : Ordinal.{w}, β < Ordinal.omega0 ∧
      ∀ b : Fin n → M, BFEquiv (L := L) β n a b → ∃ e : M ≃[L] M, ⇑e ∘ a = b := by
  refine ⟨Ordinal.lift.{w, 0} φ.toLω.qrank, ?_, orbit_determined_of_orbitFormula hφ⟩
  simpa only [Ordinal.lift_omega0, Formula.toLω] using
    Ordinal.lift_lt.{w, 0}.2 (BoundedFormula.qrank_toLω_lt_omega0 φ)

/-- **The orbit rank is at most the rank of an orbit formula.**  If the first-order formula `φ`
defines the automorphism orbit of `a` in `M`, then `orbitRank a` is at most the lifted rank
`Ordinal.lift.{w} φ.toLω.qrank`.  This is `orbitRank_le_lift_qrank_of_infinitaryOrbitFormula` for
`φ.toLω`. -/
theorem orbitRank_le_lift_qrank_of_orbitFormula {n : ℕ} {a : Fin n → M} {φ : L.Formula (Fin n)}
    (hφ : ∀ b : Fin n → M, φ.Realize b ↔ ∃ e : M ≃[L] M, ⇑e ∘ a = b) :
    orbitRank (L := L) a ≤ Ordinal.lift.{w, 0} φ.toLω.qrank :=
  orbitRank_le_lift_qrank_of_infinitaryOrbitFormula
    fun b ↦ (Formula.realize_toLω φ).trans (hφ b)

/-- **A tuple with an orbit formula has finite orbit rank.** -/
theorem orbitRank_lt_omega0_of_orbitFormula {n : ℕ} {a : Fin n → M} {φ : L.Formula (Fin n)}
    (hφ : ∀ b : Fin n → M, φ.Realize b ↔ ∃ e : M ≃[L] M, ⇑e ∘ a = b) :
    orbitRank (L := L) a < Ordinal.omega0 := by
  obtain ⟨β, hβ, hdet⟩ := exists_finite_orbit_threshold hφ
  exact (orbitRank_le_of_mem (mem_orbitStable_of_orbit_determined hdet)).trans_lt hβ

/-- **Orbit formulas for all tuples bound the internal Scott rank by `ω`.**  If every tuple of
`M` has a first-order orbit formula (possibly a different formula, of a different finite rank,
for each tuple), then `internalScottRank M ≤ ω`.  No uniform bound is assumed, so the bound is
not strict. -/
theorem internalScottRank_le_omega0_of_orbitFormulas
    (h : ∀ (n : ℕ) (a : Fin n → M), ∃ φ : L.Formula (Fin n),
      ∀ b : Fin n → M, φ.Realize b ↔ ∃ e : M ≃[L] M, ⇑e ∘ a = b) :
    internalScottRank (L := L) M ≤ Ordinal.omega0 :=
  internalScottRank_le_of_orbits_determined fun n a ↦
    let ⟨_, hφ⟩ := h n a
    exists_finite_orbit_threshold hφ

end FirstOrder.Language
