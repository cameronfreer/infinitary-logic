/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import CountableInfinitaryLogic.Lomega1omega.Syntax

/-!
# Lω₁ω Semantics

This file defines the semantics of Lω₁ω formulas.

## Main Definitions

- `FirstOrder.Language.BoundedFormulaω.Realize`: Evaluation of a bounded formula in a structure.
- `FirstOrder.Language.Formulaω.Realize`: Evaluation of a formula with variable assignment.
- `FirstOrder.Language.Sentenceω.Realize`: Truth of a sentence in a structure.

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

namespace BoundedFormulaω

/-- A bounded Lω₁ω formula can be evaluated as true or false by giving values to each
free and bound variable. -/
def Realize : L.BoundedFormulaω α n → (α → M) → (Fin n → M) → Prop
  | falsum, _, _ => False
  | equal t₁ t₂, v, xs => t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs)
  | rel R ts, v, xs => RelMap R fun i => (ts i).realize (Sum.elim v xs)
  | imp φ ψ, v, xs => Realize φ v xs → Realize ψ v xs
  | all φ, v, xs => ∀ x : M, Realize φ v (snoc xs x)
  | iSup φs, v, xs => ∃ i, Realize (φs i) v xs
  | iInf φs, v, xs => ∀ i, Realize (φs i) v xs

variable {v : α → M} {xs : Fin n → M}

@[simp]
theorem realize_falsum : (falsum : L.BoundedFormulaω α n).Realize v xs ↔ False := Iff.rfl

@[simp]
theorem realize_bot : (⊥ : L.BoundedFormulaω α n).Realize v xs ↔ False := Iff.rfl

@[simp]
theorem realize_equal (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    (equal t₁ t₂).Realize v xs ↔ t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs) :=
  Iff.rfl

@[simp]
theorem realize_rel {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
    (rel R ts).Realize v xs ↔ RelMap R fun i => (ts i).realize (Sum.elim v xs) :=
  Iff.rfl

@[simp]
theorem realize_imp (φ ψ : L.BoundedFormulaω α n) :
    (imp φ ψ).Realize v xs ↔ (φ.Realize v xs → ψ.Realize v xs) := Iff.rfl

@[simp]
theorem realize_all (φ : L.BoundedFormulaω α (n + 1)) :
    (all φ).Realize v xs ↔ ∀ x : M, φ.Realize v (snoc xs x) := Iff.rfl

@[simp]
theorem realize_iSup (φs : ℕ → L.BoundedFormulaω α n) :
    (iSup φs).Realize v xs ↔ ∃ i, (φs i).Realize v xs := Iff.rfl

@[simp]
theorem realize_iInf (φs : ℕ → L.BoundedFormulaω α n) :
    (iInf φs).Realize v xs ↔ ∀ i, (φs i).Realize v xs := Iff.rfl

@[simp]
theorem realize_top : (⊤ : L.BoundedFormulaω α n).Realize v xs ↔ True := by
  simp [Top.top, BoundedFormulaω.top]

@[simp]
theorem realize_not (φ : L.BoundedFormulaω α n) :
    φ.not.Realize v xs ↔ ¬φ.Realize v xs := by
  simp [BoundedFormulaω.not]

@[simp]
theorem realize_and (φ ψ : L.BoundedFormulaω α n) :
    (φ.and ψ).Realize v xs ↔ φ.Realize v xs ∧ ψ.Realize v xs := by
  simp [BoundedFormulaω.and]
  tauto

@[simp]
theorem realize_inf (φ ψ : L.BoundedFormulaω α n) :
    (φ ⊓ ψ).Realize v xs ↔ φ.Realize v xs ∧ ψ.Realize v xs :=
  realize_and φ ψ

@[simp]
theorem realize_or (φ ψ : L.BoundedFormulaω α n) :
    (φ.or ψ).Realize v xs ↔ φ.Realize v xs ∨ ψ.Realize v xs := by
  simp [BoundedFormulaω.or]
  tauto

@[simp]
theorem realize_sup (φ ψ : L.BoundedFormulaω α n) :
    (φ ⊔ ψ).Realize v xs ↔ φ.Realize v xs ∨ ψ.Realize v xs :=
  realize_or φ ψ

@[simp]
theorem realize_ex (φ : L.BoundedFormulaω α (n + 1)) :
    φ.ex.Realize v xs ↔ ∃ x : M, φ.Realize v (snoc xs x) := by
  simp [BoundedFormulaω.ex]

@[simp]
theorem realize_iff (φ ψ : L.BoundedFormulaω α n) :
    (φ.iff ψ).Realize v xs ↔ (φ.Realize v xs ↔ ψ.Realize v xs) := by
  simp [BoundedFormulaω.iff, iff_def]

@[simp]
theorem realize_einf {ι : Type*} [Encodable ι] (φs : ι → L.BoundedFormulaω α n) :
    (einf φs).Realize v xs ↔ ∀ i, (φs i).Realize v xs := by
  simp only [einf, realize_iInf]
  constructor
  · intro h i
    have := h (Encodable.encode i)
    simp only [Encodable.encodek] at this
    exact this
  · intro h k
    cases hd : Encodable.decode (α := ι) k with
    | none => simp
    | some i => exact h i

@[simp]
theorem realize_esup {ι : Type*} [Encodable ι] (φs : ι → L.BoundedFormulaω α n) :
    (esup φs).Realize v xs ↔ ∃ i, (φs i).Realize v xs := by
  simp only [esup, realize_iSup]
  constructor
  · rintro ⟨k, hk⟩
    cases hd : Encodable.decode (α := ι) k with
    | none => simp [hd] at hk
    | some i =>
      use i
      simp only [hd] at hk
      exact hk
  · rintro ⟨i, hi⟩
    use Encodable.encode i
    simp only [Encodable.encodek, hi]

end BoundedFormulaω

namespace Formulaω

/-- A formula can be evaluated by giving values to its free variables. -/
def Realize (φ : L.Formulaω α) (v : α → M) : Prop :=
  φ.Realize v Fin.elim0

variable {φ : L.Formulaω α} {v : α → M}

@[simp]
theorem realize_not : φ.not.Realize v ↔ ¬φ.Realize v := BoundedFormulaω.realize_not φ

@[simp]
theorem realize_bot : (⊥ : L.Formulaω α).Realize v ↔ False := BoundedFormulaω.realize_bot

@[simp]
theorem realize_top : (⊤ : L.Formulaω α).Realize v ↔ True := BoundedFormulaω.realize_top

@[simp]
theorem realize_imp (φ ψ : L.Formulaω α) :
    (φ.imp ψ).Realize v ↔ (φ.Realize v → ψ.Realize v) := BoundedFormulaω.realize_imp φ ψ

@[simp]
theorem realize_inf (φ ψ : L.Formulaω α) :
    (φ ⊓ ψ).Realize v ↔ φ.Realize v ∧ ψ.Realize v := BoundedFormulaω.realize_inf φ ψ

@[simp]
theorem realize_sup (φ ψ : L.Formulaω α) :
    (φ ⊔ ψ).Realize v ↔ φ.Realize v ∨ ψ.Realize v := BoundedFormulaω.realize_sup φ ψ

end Formulaω

namespace Sentenceω

/-- A sentence can be evaluated in a structure. -/
def Realize (φ : L.Sentenceω) (M : Type w) [L.Structure M] : Prop :=
  φ.Realize (Empty.elim : Empty → M)

/-- Notation for a structure satisfying a sentence. -/
scoped notation:51 M " ⊨ω " φ:51 => Sentenceω.Realize φ M

end Sentenceω

end Language

end FirstOrder
