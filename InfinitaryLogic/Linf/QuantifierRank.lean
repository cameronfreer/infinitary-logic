/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Linf.Operations
import Mathlib.SetTheory.Ordinal.Basic

/-!
# L∞ω Quantifier Rank

This file defines the quantifier rank of L∞ω formulas and the "agree up to rank α"
relation between structures.

## Main Definitions

- `BoundedFormulaInf.qrank`: The quantifier rank of an L∞ω formula.
- `EquivQRInf`: Two structures are equivalent up to quantifier rank α if they satisfy
  the same sentences of quantifier rank ≤ α.

## Main Results

- `EquivQRInf.refl`, `EquivQRInf.symm`, `EquivQRInf.trans`: Equivalence relation properties.
- `EquivQRInf.monotone`: Higher rank equivalence implies lower rank equivalence.

## References

- [Keisler-Knight, "Barwise: Infinitary Logic and Admissible Sets", 2004]
-/

universe u v w w'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

open FirstOrder Structure Ordinal

/-! ### Quantifier Rank -/

/-- The quantifier rank of an L∞ω formula.

- Atomic formulas (falsum, equal, rel) have rank 0
- Implication takes the max of its arguments
- Universal quantification adds 1
- Infinitary connectives take the sup of their arguments -/
noncomputable def BoundedFormulaInf.qrank : L.BoundedFormulaInf α n → Ordinal.{0}
  | .falsum       => 0
  | .equal _ _    => 0
  | .rel _ _      => 0
  | .imp φ ψ      => max φ.qrank ψ.qrank
  | .all φ        => φ.qrank + 1
  | .iSup φs      => ⨆ i, (φs i).qrank
  | .iInf φs      => ⨆ i, (φs i).qrank

/-- Quantifier rank of a formula (no bound variables). -/
noncomputable abbrev FormulaInf.qrank (φ : L.FormulaInf α) : Ordinal.{0} :=
  BoundedFormulaInf.qrank φ

/-- Quantifier rank of a sentence. -/
noncomputable abbrev SentenceInf.qrank (φ : L.SentenceInf) : Ordinal.{0} :=
  BoundedFormulaInf.qrank φ

/-! ### Quantifier Rank Lemmas -/

namespace BoundedFormulaInf

variable {α : Type*} {n : ℕ}

@[simp]
theorem qrank_falsum : (falsum : L.BoundedFormulaInf α n).qrank = 0 := rfl

@[simp]
theorem qrank_bot : (⊥ : L.BoundedFormulaInf α n).qrank = 0 := rfl

@[simp]
theorem qrank_equal (t₁ t₂ : L.Term (α ⊕ Fin n)) : (equal t₁ t₂).qrank = 0 := rfl

@[simp]
theorem qrank_rel {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
    (rel R ts).qrank = 0 := rfl

@[simp]
theorem qrank_imp (φ ψ : L.BoundedFormulaInf α n) :
    (imp φ ψ).qrank = max φ.qrank ψ.qrank := rfl

@[simp]
theorem qrank_all (φ : L.BoundedFormulaInf α (n + 1)) :
    (all φ).qrank = φ.qrank + 1 := rfl

@[simp]
theorem qrank_iSup {ι : Type*} (φs : ι → L.BoundedFormulaInf α n) :
    (iSup φs).qrank = ⨆ i, (φs i).qrank := rfl

@[simp]
theorem qrank_iInf {ι : Type*} (φs : ι → L.BoundedFormulaInf α n) :
    (iInf φs).qrank = ⨆ i, (φs i).qrank := rfl

/-- The top formula has rank 0. -/
@[simp]
theorem qrank_top : (⊤ : L.BoundedFormulaInf α n).qrank = 0 := by
  simp only [Top.top, BoundedFormulaInf.top, qrank_imp, qrank_falsum, max_self]

/-- Negation preserves quantifier rank. -/
@[simp]
theorem qrank_not (φ : L.BoundedFormulaInf α n) : φ.not.qrank = φ.qrank := by
  simp only [BoundedFormulaInf.not, qrank_imp, qrank_bot]
  exact max_eq_left (zero_le _)

/-- Conjunction takes max of ranks. -/
theorem qrank_and (φ ψ : L.BoundedFormulaInf α n) :
    (φ.and ψ).qrank = max φ.qrank ψ.qrank := by
  simp only [BoundedFormulaInf.and, qrank_not, qrank_imp, max_comm φ.qrank ψ.qrank]

/-- Disjunction takes max of ranks. -/
theorem qrank_or (φ ψ : L.BoundedFormulaInf α n) :
    (φ.or ψ).qrank = max φ.qrank ψ.qrank := by
  simp only [BoundedFormulaInf.or, qrank_not, qrank_imp]

/-- Existential quantification adds 1 to rank. -/
theorem qrank_ex (φ : L.BoundedFormulaInf α (n + 1)) :
    φ.ex.qrank = φ.qrank + 1 := by
  simp only [BoundedFormulaInf.ex, qrank_not, qrank_all]

/-- `mapFreeVars` preserves quantifier rank. Renaming free variables does not
change the logical complexity of a formula. -/
@[simp]
theorem qrank_mapFreeVars {α α' : Type w'} (f : α → α') {n : ℕ}
    (φ : L.BoundedFormulaInf α n) :
    (φ.mapFreeVars f).qrank = φ.qrank := by
  induction φ with
  | falsum => rfl
  | equal => rfl
  | rel => rfl
  | imp φ ψ ihφ ihψ =>
    simp only [mapFreeVars, qrank_imp, ihφ, ihψ]
  | all φ ih =>
    simp only [mapFreeVars, qrank_all, ih]
  | iSup φs ih =>
    simp only [mapFreeVars, qrank_iSup]
    congr 1; funext i; exact ih i
  | iInf φs ih =>
    simp only [mapFreeVars, qrank_iInf]
    congr 1; funext i; exact ih i

end BoundedFormulaInf

/-! ### Equivalence up to Quantifier Rank -/

/-- Two structures are equivalent up to quantifier rank α if they satisfy the same
sentences of quantifier rank ≤ α.

Both the ordinal `α` and the formula universe are pinned to `Ordinal.{0}` and
`BoundedFormulaInf.{u, v, 0, 0}` respectively. This is inherent: `qrank` returns
`Ordinal.{0}`, so the inequality `φ.qrank ≤ α` requires `α : Ordinal.{0}`.
See `LinfEquiv` for discussion of the `uι = 0` restriction. -/
def EquivQRInf (L : Language.{u, v}) (α : Ordinal.{0}) (M N : Type w)
    [L.Structure M] [L.Structure N] : Prop :=
  ∀ (φ : BoundedFormulaInf.{u, v, 0, 0} L Empty 0),
    φ.qrank ≤ α → (SentenceInf.Realize φ M ↔ SentenceInf.Realize φ N)

namespace EquivQRInf

variable {L : Language.{u, v}}
variable {M : Type w} [L.Structure M]
variable {N : Type w} [L.Structure N]
variable {P : Type w} [L.Structure P]

/-- Equivalence up to quantifier rank is reflexive. -/
theorem refl (α : Ordinal) : EquivQRInf L α M M := fun _ _ => Iff.rfl

/-- Equivalence up to quantifier rank is symmetric. -/
theorem symm (h : EquivQRInf L α M N) : EquivQRInf L α N M :=
  fun φ hφ => (h φ hφ).symm

/-- Equivalence up to quantifier rank is transitive. -/
theorem trans (h₁ : EquivQRInf L α M N) (h₂ : EquivQRInf L α N P) : EquivQRInf L α M P :=
  fun φ hφ => (h₁ φ hφ).trans (h₂ φ hφ)

/-- Equivalence at higher rank implies equivalence at lower rank. -/
theorem monotone {α β : Ordinal} (hαβ : α ≤ β) (h : EquivQRInf L β M N) :
    EquivQRInf L α M N := fun φ hφ => h φ (le_trans hφ hαβ)

/-- Equivalence at rank 0 means agreement on all quantifier-free sentences. -/
theorem zero_iff_agree_atomic : EquivQRInf L 0 M N ↔
    ∀ φ : BoundedFormulaInf.{u, v, 0, 0} L Empty 0, φ.qrank = 0 →
      (SentenceInf.Realize φ M ↔ SentenceInf.Realize φ N) := by
  constructor
  · intro h φ hφ; exact h φ (le_of_eq hφ)
  · intro h φ hφ; exact h φ (nonpos_iff_eq_zero.mp hφ)

end EquivQRInf

end Language

end FirstOrder
