/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import CountableInfinitaryLogic.Scott.BackAndForth

/-!
# Scott Formulas

This file defines Scott formulas, which are Lω₁ω formulas that capture back-and-forth
equivalence at each ordinal level.

## Main Definitions

- `scottFormula`: The Scott formula for a tuple at a given ordinal level.

## Main Results

- `realize_scottFormula_iff_BFEquiv`: A tuple b satisfies the Scott formula for a at level α
  if and only if a and b are BF-equivalent at level α.

## Implementation Notes

The Scott formula at ordinal α is defined by recursion on α:
- At 0: the atomic diagram of the tuple
- At successor α + 1: the formula at α, plus forth and back conditions
- At limit λ: the conjunction over all β < λ

For the forth and back conditions, we need to quantify over elements of M, which requires
`[Countable M]` to form the countable conjunction/disjunction.

The key technical challenge is handling the variable binding correctly. When we have
a formula φ(x₀,...,xₙ) with n+1 free variables and want to existentially quantify
over the last variable, we use `relabel` to move it into a bound position.
-/

universe u v w w'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable {M : Type w} [L.Structure M]
variable [Countable (Σ l, L.Relations l)]
variable [Countable M]
variable {n : ℕ}

open FirstOrder Structure Fin Ordinal BoundedFormulaω

/-- Maps the last variable of Fin (n+1) to a bound variable position,
keeping the first n as free variables. Used for quantifying over the last position. -/
def insertLastBound : Fin (n + 1) → Fin n ⊕ Fin 1 :=
  fun i => if h : i.val < n then Sum.inl ⟨i.val, h⟩ else Sum.inr 0

/-- Existentially quantify over the last free variable of a formula. -/
def existsLastVar (φ : L.Formulaω (Fin (n + 1))) : L.Formulaω (Fin n) :=
  (φ.relabel insertLastBound).ex

/-- Universally quantify over the last free variable of a formula. -/
def forallLastVar (φ : L.Formulaω (Fin (n + 1))) : L.Formulaω (Fin n) :=
  (φ.relabel insertLastBound).all

/-- The Scott formula for a tuple a at ordinal level α.

At level 0: the atomic diagram of a.
At successor α + 1: formula at α ∧ (forth condition) ∧ (back condition)
At limit λ: conjunction over all β < λ.

The formula has free variables indexed by `Fin n` (representing the positions in the tuple).
Requires `[Countable M]` to quantify over elements of M in the forth/back conditions.

TODO: Complete the definition using well-founded recursion on ordinals.
Currently uses sorry as placeholder for the recursion structure.
-/
noncomputable def scottFormula (a : Fin n → M) (α : Ordinal) : L.Formulaω (Fin n) := by
  haveI : Encodable M := Encodable.ofCountable M
  exact if α = 0 then atomicDiagram a else sorry
  -- TODO: define successor and limit cases properly using ordinal recursion

theorem scottFormula_zero (a : Fin n → M) :
    scottFormula (L := L) a 0 = atomicDiagram a := by
  simp only [scottFormula, ↓reduceIte]

/-- The fundamental correspondence: a tuple b realizes the Scott formula for a at level α
if and only if a and b are BF-equivalent at level α. -/
theorem realize_scottFormula_iff_BFEquiv
    {N : Type w'} [L.Structure N]
    (a : Fin n → M) (b : Fin n → N) (α : Ordinal) :
    (scottFormula (L := L) a α).Realize b ↔ BFEquiv (L := L) α n a b := by
  sorry -- TODO: prove by induction on α

end Language

end FirstOrder
