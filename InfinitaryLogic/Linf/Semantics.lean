/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Linf.Syntax
import Mathlib.ModelTheory.Semantics

/-!
# L∞ω Semantics

This file defines the semantics of L∞ω formulas.

## Main Definitions

- `FirstOrder.Language.BoundedFormulaInf.Realize`: Evaluation of a bounded formula in a structure.
- `FirstOrder.Language.FormulaInf.Realize`: Evaluation of a formula with variable assignment.
- `FirstOrder.Language.SentenceInf.Realize`: Truth of a sentence in a structure.

## Main Results

- Simp lemmas for all connectives and quantifiers.
-/

universe u v w u'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}
variable {M : Type w} [L.Structure M]
variable {α : Type u'} {n : ℕ}

open FirstOrder Structure Fin

namespace BoundedFormulaInf

/-- A bounded L∞ω formula can be evaluated as true or false by giving values to each
free and bound variable. -/
def Realize : {n : ℕ} → L.BoundedFormulaInf α n → (α → M) → (Fin n → M) → Prop
  | _, falsum, _, _ => False
  | _, equal t₁ t₂, v, xs => t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs)
  | _, rel R ts, v, xs => RelMap R fun i => (ts i).realize (Sum.elim v xs)
  | _, imp φ ψ, v, xs => Realize φ v xs → Realize ψ v xs
  | _, all φ, v, xs => ∀ x : M, Realize φ v (snoc xs x)
  | _, iSup φs, v, xs => ∃ i, Realize (φs i) v xs
  | _, iInf φs, v, xs => ∀ i, Realize (φs i) v xs

variable {v : α → M} {xs : Fin n → M}

@[simp]
theorem realize_falsum : (falsum : L.BoundedFormulaInf α n).Realize v xs ↔ False := by rfl

@[simp]
theorem realize_bot : (⊥ : L.BoundedFormulaInf α n).Realize v xs ↔ False := by rfl

@[simp]
theorem realize_equal (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    (equal t₁ t₂).Realize v xs ↔ t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs) := by
  rfl

@[simp]
theorem realize_rel {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
    (rel R ts).Realize v xs ↔ RelMap R fun i => (ts i).realize (Sum.elim v xs) := by
  rfl

@[simp]
theorem realize_imp (φ ψ : L.BoundedFormulaInf α n) :
    (imp φ ψ).Realize v xs ↔ (φ.Realize v xs → ψ.Realize v xs) := by rfl

@[simp]
theorem realize_all (φ : L.BoundedFormulaInf α (n + 1)) :
    (all φ).Realize v xs ↔ ∀ x : M, φ.Realize v (snoc xs x) := by rfl

@[simp]
theorem realize_iSup {ι : Type} (φs : ι → L.BoundedFormulaInf α n) :
    (iSup φs).Realize v xs ↔ ∃ i, (φs i).Realize v xs := by rfl

@[simp]
theorem realize_iInf {ι : Type} (φs : ι → L.BoundedFormulaInf α n) :
    (iInf φs).Realize v xs ↔ ∀ i, (φs i).Realize v xs := by rfl

@[simp]
theorem realize_top : (⊤ : L.BoundedFormulaInf α n).Realize v xs ↔ True := by
  simp only [Top.top, BoundedFormulaInf.top, realize_imp, realize_falsum, false_implies]

@[simp]
theorem realize_not (φ : L.BoundedFormulaInf α n) :
    φ.not.Realize v xs ↔ ¬φ.Realize v xs := by
  simp only [BoundedFormulaInf.not, realize_imp, realize_bot]

@[simp]
theorem realize_and (φ ψ : L.BoundedFormulaInf α n) :
    (φ.and ψ).Realize v xs ↔ φ.Realize v xs ∧ ψ.Realize v xs := by
  simp only [BoundedFormulaInf.and, realize_not, realize_imp]
  tauto

@[simp]
theorem realize_inf (φ ψ : L.BoundedFormulaInf α n) :
    (φ ⊓ ψ).Realize v xs ↔ φ.Realize v xs ∧ ψ.Realize v xs :=
  realize_and φ ψ

@[simp]
theorem realize_or (φ ψ : L.BoundedFormulaInf α n) :
    (φ.or ψ).Realize v xs ↔ φ.Realize v xs ∨ ψ.Realize v xs := by
  simp only [BoundedFormulaInf.or, realize_not, realize_imp]
  tauto

@[simp]
theorem realize_sup (φ ψ : L.BoundedFormulaInf α n) :
    (φ ⊔ ψ).Realize v xs ↔ φ.Realize v xs ∨ ψ.Realize v xs :=
  realize_or φ ψ

@[simp]
theorem realize_ex (φ : L.BoundedFormulaInf α (n + 1)) :
    φ.ex.Realize v xs ↔ ∃ x : M, φ.Realize v (snoc xs x) := by
  simp only [BoundedFormulaInf.ex, realize_not, realize_all]
  push_neg
  rfl

@[simp]
theorem realize_iff (φ ψ : L.BoundedFormulaInf α n) :
    (φ.iff ψ).Realize v xs ↔ (φ.Realize v xs ↔ ψ.Realize v xs) := by
  simp only [BoundedFormulaInf.iff, realize_inf, realize_imp, iff_def]

@[simp]
theorem realize_emptyiSup : (emptyiSup : L.BoundedFormulaInf α n).Realize v xs ↔ False := by
  simp only [emptyiSup, realize_iSup, IsEmpty.exists_iff]

@[simp]
theorem realize_emptyiInf : (emptyiInf : L.BoundedFormulaInf α n).Realize v xs ↔ True := by
  simp only [emptyiInf, realize_iInf, IsEmpty.forall_iff]

end BoundedFormulaInf

namespace FormulaInf

/-- A formula can be evaluated by giving values to its free variables. -/
def Realize (φ : L.FormulaInf α) (v : α → M) : Prop :=
  BoundedFormulaInf.Realize φ v Fin.elim0

variable {φ : L.FormulaInf α} {v : α → M}

@[simp]
theorem realize_not : Realize φ.not v ↔ ¬Realize φ v := BoundedFormulaInf.realize_not φ

@[simp]
theorem realize_bot : Realize (⊥ : L.FormulaInf α) v ↔ False := BoundedFormulaInf.realize_bot

@[simp]
theorem realize_top : Realize (⊤ : L.FormulaInf α) v ↔ True := BoundedFormulaInf.realize_top

@[simp]
theorem realize_imp (φ ψ : L.FormulaInf α) :
    Realize (φ.imp ψ) v ↔ (Realize φ v → Realize ψ v) := BoundedFormulaInf.realize_imp φ ψ

@[simp]
theorem realize_inf (φ ψ : L.FormulaInf α) :
    Realize (φ ⊓ ψ) v ↔ Realize φ v ∧ Realize ψ v := BoundedFormulaInf.realize_inf φ ψ

@[simp]
theorem realize_sup (φ ψ : L.FormulaInf α) :
    Realize (φ ⊔ ψ) v ↔ Realize φ v ∨ Realize ψ v := BoundedFormulaInf.realize_sup φ ψ

@[simp]
theorem realize_iSup {ι : Type} (φs : ι → L.FormulaInf α) :
    Realize (BoundedFormulaInf.iSup φs) v ↔ ∃ i, Realize (φs i) v :=
  BoundedFormulaInf.realize_iSup φs

@[simp]
theorem realize_iInf {ι : Type} (φs : ι → L.FormulaInf α) :
    Realize (BoundedFormulaInf.iInf φs) v ↔ ∀ i, Realize (φs i) v :=
  BoundedFormulaInf.realize_iInf φs

end FormulaInf

namespace SentenceInf

/-- A sentence can be evaluated in a structure. -/
def Realize (φ : L.SentenceInf) (M : Type w) [L.Structure M] : Prop :=
  BoundedFormulaInf.Realize φ (Empty.elim : Empty → M) Fin.elim0

/-- Notation for a structure satisfying a sentence. -/
scoped notation:51 M " ⊨∞ " φ:51 => SentenceInf.Realize φ M

end SentenceInf

end Language

end FirstOrder
