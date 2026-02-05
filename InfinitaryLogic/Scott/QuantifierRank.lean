/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Scott.Formula
import InfinitaryLogic.Lomega1omega.QuantifierRank

/-!
# Quantifier Rank of Scott Formulas

This file proves bounds on the quantifier rank of Scott formulas and connects
BF-equivalence to agreement on Lω₁ω formulas of bounded quantifier rank.

## Main Results

- `scottFormula_qrank_le`: The Scott formula at level α has quantifier rank ≤ α.
- `BFEquiv_iff_EquivQRω_formulas`: BF-equivalence at level α between tuples is
  equivalent to agreement on all Lω₁ω formulas of quantifier rank ≤ α (for α < ω₁).

## References

- [Marker, "Lectures on Infinitary Model Theory", 2016]
- [Keisler-Knight, "Barwise: Infinitary Logic and Admissible Sets", 2004]
-/

universe u v w w'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable [Countable (Σ l, L.Relations l)]

open FirstOrder Structure Fin Ordinal BoundedFormulaω

/-- The Scott formula at level α has quantifier rank ≤ α.

This is proved by ordinal induction:
- At level 0: the atomic diagram has rank 0.
- At successor α + 1: the formula at α has rank ≤ α, and the forth/back
  conditions add one quantifier, giving rank ≤ α + 1.
- At limit λ: the conjunction over β < λ has rank ≤ λ. -/
theorem scottFormula_qrank_le {M : Type w} [L.Structure M] [Countable M]
    {n : ℕ} (a : Fin n → M) (α : Ordinal) (hα : α < Ordinal.omega 1) :
    (scottFormula (L := L) a α).qrank ≤ α := by
  sorry

/-- BF-equivalence at level α implies agreement on Lω₁ω formulas of quantifier rank ≤ α.

This direction follows from Scott formulas: the Scott formula captures BFEquiv and
has quantifier rank ≤ α, so any Lω₁ω formula of the same rank is a consequence. -/
theorem BFEquiv_implies_agree_formulas_omega {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N]
    {n : ℕ} (a : Fin n → M) (b : Fin n → N)
    (α : Ordinal) (hα : α < Ordinal.omega 1) :
    BFEquiv (L := L) α n a b →
    ∀ (φ : L.Formulaω (Fin n)), φ.qrank ≤ α →
      (Formulaω.Realize φ a ↔ Formulaω.Realize φ b) := by
  sorry

/-- Agreement on all Lω₁ω formulas of quantifier rank ≤ α implies BF-equivalence.

This direction uses the Scott formula: if all rank-≤-α formulas agree, then in particular
the Scott formula at level α agrees, which by `realize_scottFormula_iff_BFEquiv` gives
BFEquiv at level α. -/
theorem agree_formulas_omega_implies_BFEquiv {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N]
    {n : ℕ} (a : Fin n → M) (b : Fin n → N)
    (α : Ordinal) (hα : α < Ordinal.omega 1) :
    (∀ (φ : L.Formulaω (Fin n)), φ.qrank ≤ α →
      (Formulaω.Realize φ a ↔ Formulaω.Realize φ b)) →
    BFEquiv (L := L) α n a b := by
  sorry

/-- BF-equivalence at level α between tuples is equivalent to agreement on all
Lω₁ω formulas of quantifier rank ≤ α (for α < ω₁).

This is the Lω₁ω version of the Karp lemma. -/
theorem BFEquiv_iff_agree_formulas_omega {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N]
    {n : ℕ} (a : Fin n → M) (b : Fin n → N)
    (α : Ordinal) (hα : α < Ordinal.omega 1) :
    BFEquiv (L := L) α n a b ↔
    ∀ (φ : L.Formulaω (Fin n)), φ.qrank ≤ α →
      (Formulaω.Realize φ a ↔ Formulaω.Realize φ b) := by
  exact ⟨BFEquiv_implies_agree_formulas_omega a b α hα,
         agree_formulas_omega_implies_BFEquiv a b α hα⟩

end Language

end FirstOrder
