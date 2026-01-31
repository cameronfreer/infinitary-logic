/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Linf.Countability
import InfinitaryLogic.Lomega1omega.Operations

/-!
# Embeddings between Lω₁ω and L∞ω

This file defines embeddings between Lω₁ω (countable infinitary logic) and L∞ω (arbitrary
infinitary logic).

## Main Definitions

- `BoundedFormulaω.toLinf`: Embeds Lω₁ω into L∞ω (uses ℕ as index type)
- `BoundedFormulaInf.ofCountable`: Converts countable L∞ω back to Lω₁ω via Encodable

## Main Results

- `realize_toLinf`: Semantics preserved by toLinf embedding
- `realize_ofCountable`: Semantics preserved by ofCountable conversion
-/

universe u v u' w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {α : Type u'} {n : ℕ}

namespace BoundedFormulaω

/-- Embeds a Lω₁ω formula into L∞ω (uses ℕ as index type). -/
def toLinf : ∀ {n}, L.BoundedFormulaω α n → L.BoundedFormulaInf α n
  | _, falsum => .falsum
  | _, equal t₁ t₂ => .equal t₁ t₂
  | _, rel R ts => .rel R ts
  | _, imp φ ψ => .imp (toLinf φ) (toLinf ψ)
  | _, all φ => .all (toLinf φ)
  | _, iSup φs => .iSup (fun i : ℕ => toLinf (φs i))
  | _, iInf φs => .iInf (fun i : ℕ => toLinf (φs i))

variable {M : Type w} [L.Structure M] {v : α → M} {xs : Fin n → M}

@[simp]
theorem realize_toLinf (φ : L.BoundedFormulaω α n) :
    (toLinf φ).Realize v xs ↔ φ.Realize v xs := by
  induction φ with
  | falsum => rfl
  | equal => rfl
  | rel => rfl
  | imp φ ψ ih₁ ih₂ =>
    simp only [toLinf, BoundedFormulaInf.realize_imp, BoundedFormulaω.realize_imp, ih₁, ih₂]
  | all φ ih =>
    simp only [toLinf, BoundedFormulaInf.realize_all, BoundedFormulaω.realize_all]
    exact forall_congr' fun x => ih
  | iSup φs ih =>
    simp only [toLinf, BoundedFormulaInf.realize_iSup, BoundedFormulaω.realize_iSup]
    exact exists_congr fun i => ih i
  | iInf φs ih =>
    simp only [toLinf, BoundedFormulaInf.realize_iInf, BoundedFormulaω.realize_iInf]
    exact forall_congr' fun i => ih i

/-- toLinf preserves the countable property. -/
theorem toLinf_isCountable (φ : L.BoundedFormulaω α n) : (toLinf φ).IsCountable := by
  induction φ with
  | falsum => exact .falsum
  | equal t₁ t₂ => exact .equal t₁ t₂
  | rel R ts => exact .rel R ts
  | imp _ _ ih₁ ih₂ => exact .imp ih₁ ih₂
  | all _ ih => exact .all ih
  | iSup φs ih => exact .iSup ih
  | iInf φs ih => exact .iInf ih

end BoundedFormulaω

namespace Formulaω

/-- Embeds a Lω₁ω formula into L∞ω. -/
def toLinf (φ : L.Formulaω α) : L.FormulaInf α := BoundedFormulaω.toLinf φ

@[simp]
theorem realize_toLinf {M : Type w} [L.Structure M] {v : α → M} (φ : L.Formulaω α) :
    FormulaInf.Realize φ.toLinf v ↔ Formulaω.Realize φ v :=
  BoundedFormulaω.realize_toLinf φ

end Formulaω

namespace Sentenceω

/-- Embeds a Lω₁ω sentence into L∞ω. -/
def toLinf (φ : L.Sentenceω) : L.SentenceInf := Formulaω.toLinf φ

@[simp]
theorem realize_toLinf {M : Type w} [L.Structure M] (φ : L.Sentenceω) :
    SentenceInf.Realize φ.toLinf M ↔ Sentenceω.Realize φ M := by
  simp only [SentenceInf.Realize, Sentenceω.Realize, toLinf, Formulaω.toLinf]
  exact BoundedFormulaω.realize_toLinf φ

end Sentenceω

end Language

end FirstOrder
