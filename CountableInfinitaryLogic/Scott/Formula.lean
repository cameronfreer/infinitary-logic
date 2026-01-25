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

-- Derive Encodable from Countable for use in einf/esup
attribute [local instance] Encodable.ofCountable

open FirstOrder Structure Fin Ordinal BoundedFormulaω

/-- Maps the last variable of Fin (n+1) to a bound variable position,
keeping the first n as free variables. Used for quantifying over the last position. -/
def insertLastBound {n : ℕ} : Fin (n + 1) → Fin n ⊕ Fin 1 :=
  fun i => if h : i.val < n then Sum.inl ⟨i.val, h⟩ else Sum.inr 0

/-- Existentially quantify over the last free variable of a formula. -/
def existsLastVar {n : ℕ} (φ : L.Formulaω (Fin (n + 1))) : L.Formulaω (Fin n) :=
  (φ.relabel insertLastBound).ex

/-- Universally quantify over the last free variable of a formula. -/
def forallLastVar {n : ℕ} (φ : L.Formulaω (Fin (n + 1))) : L.Formulaω (Fin n) :=
  (φ.relabel insertLastBound).all

/-- The Scott formula for a tuple a at ordinal level α.

At level 0: the atomic diagram of a.
At successor α + 1: formula at α ∧ (forth condition) ∧ (back condition)
At limit λ: conjunction over all β < λ.

The formula has free variables indexed by `Fin n` (representing the positions in the tuple).
Requires `[Countable M]` to quantify over elements of M in the forth/back conditions.

The definition uses `Ordinal.limitRecOn` with a motive that is constant in the ordinal
(always `(n : ℕ) → (Fin n → M) → L.Formulaω (Fin n)`), allowing uniform treatment of
tuples of different lengths in the recursion.
-/
noncomputable def scottFormula {n : ℕ} (a : Fin n → M) (α : Ordinal) : L.Formulaω (Fin n) :=
  haveI : Encodable M := Encodable.ofCountable M
  Ordinal.limitRecOn (motive := fun _ => (k : ℕ) → (Fin k → M) → L.Formulaω (Fin k)) α
    -- Zero case: atomic diagram
    (fun k a' => atomicDiagram (L := L) a')
    -- Successor case: previous formula ∧ forth ∧ back
    (fun _β ih k a' =>
      ih k a' ⊓
      einf (fun m : M => existsLastVar (ih (k + 1) (snoc a' m))) ⊓
      forallLastVar (esup (fun m : M => ih (k + 1) (snoc a' m))))
    -- Limit case: conjunction over all smaller ordinals
    -- Note: This requires {γ // γ < β} to be encodable, which holds for β < ω₁.
    -- For Scott analysis, we only use ordinals < ω₁, so this is always valid.
    -- For β ≥ ω₁, we return a trivial formula (this case is never used in practice).
    (fun _β _hβ ih k a' =>
      if h_lt : _β < Ordinal.omega 1 then
        haveI : Countable {γ // γ < _β} := by
          -- β.ToType is countable for β < ω₁
          haveI : Countable _β.ToType := by
            rw [← Cardinal.mk_le_aleph0_iff]
            rw [Cardinal.mk_toType]
            have h_card : _β.card < Cardinal.aleph 1 := Cardinal.lt_omega_iff_card_lt.mp h_lt
            have h1 : Cardinal.aleph 1 = Cardinal.aleph (Order.succ 0) := by
              congr 1; exact Ordinal.succ_zero.symm
            rw [h1, Cardinal.aleph_succ, Cardinal.aleph_zero] at h_card
            exact Order.lt_succ_iff.mp h_card
          -- Use equivalence Set.Iio β ≃ β.ToType
          exact Countable.of_equiv _β.ToType (Ordinal.ToType.mk).symm.toEquiv
        haveI : Encodable {γ // γ < _β} := Encodable.ofCountable _
        einf (fun (x : {γ // γ < _β}) => ih x.1 x.2 k a')
      else
        -- For β ≥ ω₁, return ⊤ (true). This case is never invoked for Scott analysis.
        ⊤)
    n a

omit [L.IsRelational] in
theorem scottFormula_zero {n : ℕ} (a : Fin n → M) :
    scottFormula (L := L) a 0 = atomicDiagram a := by
  simp only [scottFormula, Ordinal.limitRecOn_zero]

omit [L.IsRelational] in
theorem scottFormula_succ {n : ℕ} (a : Fin n → M) (α : Ordinal) :
    scottFormula (L := L) a (Order.succ α) =
      scottFormula a α ⊓
      einf (fun m : M => existsLastVar (scottFormula (snoc a m) α)) ⊓
      forallLastVar (esup (fun m : M => scottFormula (snoc a m) α)) := by
  haveI : Encodable M := Encodable.ofCountable M
  simp only [scottFormula, Ordinal.limitRecOn_succ]

/-- The fundamental correspondence: a tuple b realizes the Scott formula for a at level α
if and only if a and b are BF-equivalent at level α.

TODO: This proof requires a `BoundedFormulaω.realize_relabel` lemma (analogous to
`BoundedFormula.realize_relabel` in Mathlib) to handle the existsLastVar/forallLastVar
definitions in the successor case.
-/
theorem realize_scottFormula_iff_BFEquiv
    {N : Type w'} [L.Structure N] {n : ℕ}
    (a : Fin n → M) (b : Fin n → N) (α : Ordinal) :
    (scottFormula (L := L) a α).Realize b ↔ BFEquiv (L := L) α n a b := by
  sorry -- Proof requires realize_relabel lemma for existsLastVar/forallLastVar

end Language

end FirstOrder
