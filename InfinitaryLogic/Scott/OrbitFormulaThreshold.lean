/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Scott.OrbitRank
import InfinitaryLogic.Karp.CarrierTheorem
import InfinitaryLogic.Lomega1omega.QuantifierRank

/-!
# First-order orbit formulas give finite back-and-forth thresholds

An **orbit formula** for a tuple `a : Fin n → M` is an ordinary first-order formula
`φ : L.Formula (Fin n)` of the language `L` itself whose realizations in `M` are exactly the
automorphic images of `a`:
`∀ b, φ.Realize b ↔ ∃ e : M ≃[L] M, ⇑e ∘ a = b`.
Over a relational language, back-and-forth equivalence to `a` at the (lifted) quantifier rank of
`φ.toLω` preserves `φ` (the forward Karp lemma `BFEquiv_implies_agreeQR`), so it already forces
an automorphism carrying `a` to `b`.  That rank is finite
(`BoundedFormula.qrank_toLω_lt_omega0`), so the orbit of `a` is determined at a finite level.
If every tuple has an orbit formula, the semantic upper bound
`internalScottRank_le_of_orbits_determined` gives `internalScottRank M ≤ ω`.

## Main declarations

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
  argument is used.
* **Relational languages.**  The forward Karp lemma `BFEquiv_implies_agreeQR` is stated for
  relational languages, so the threshold theorems are too.  The finite-rank lemma
  `BoundedFormula.qrank_toLω_lt_omega0` holds for every language.
* **`≤ ω`, not `< ω`.**  Each tuple may have its own orbit formula, of its own finite rank; no
  uniform bound is assumed, so the internal Scott rank `⨆ a, (orbitRank a + 1)` is only bounded
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
  quantifier ranks of `Lω₁ω` formulas in `Ordinal.{0}`, and the threshold is
  `Ordinal.lift.{w} φ.toLω.qrank`.
-/

universe u v w

namespace FirstOrder.Language

open Ordinal

variable {L : Language.{u, v}} [L.IsRelational] {M : Type w} [L.Structure M]

/-- **An orbit formula determines the orbit at its own rank.**  If the first-order formula `φ`
defines the automorphism orbit of `a` in `M`, then every `b` back-and-forth equivalent to `a` at
level `Ordinal.lift.{w} φ.toLω.qrank` is the image of `a` under an automorphism. -/
theorem orbit_determined_of_orbitFormula {n : ℕ} {a : Fin n → M} {φ : L.Formula (Fin n)}
    (hφ : ∀ b : Fin n → M, φ.Realize b ↔ ∃ e : M ≃[L] M, ⇑e ∘ a = b) (b : Fin n → M)
    (hb : BFEquiv (L := L) (Ordinal.lift.{w, 0} φ.toLω.qrank) n a b) :
    ∃ e : M ≃[L] M, ⇑e ∘ a = b := by
  have ha : φ.Realize a := (hφ a).2 ⟨Equiv.refl L M, rfl⟩
  have hagree := BFEquiv_implies_agreeQR (ι := ℕ) φ.toLω.qrank a b hb.toOrdinalLift φ.toLω le_rfl
  exact (hφ b).1 ((Formula.realize_toLω φ).1 (hagree.1 ((Formula.realize_toLω φ).2 ha)))

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
`Ordinal.lift.{w} φ.toLω.qrank`. -/
theorem orbitRank_le_lift_qrank_of_orbitFormula {n : ℕ} {a : Fin n → M} {φ : L.Formula (Fin n)}
    (hφ : ∀ b : Fin n → M, φ.Realize b ↔ ∃ e : M ≃[L] M, ⇑e ∘ a = b) :
    orbitRank (L := L) a ≤ Ordinal.lift.{w, 0} φ.toLω.qrank :=
  orbitRank_le_of_mem (mem_orbitStable_of_orbit_determined (orbit_determined_of_orbitFormula hφ))

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
