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


- `BoundedFormulaInfLegacy.ofCountable`: Converts countable L∞ω back to Lω₁ω via Encodable

## Main Results


- `realize_ofCountable`: Semantics preserved by ofCountable conversion
-/

universe u v u' w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {α : Type u'} {n : ℕ}

namespace BoundedFormulaInfLegacy

namespace IsCountable

/-- Extract the IsCountable proofs from an imp proof. -/
theorem imp_left {φ ψ : L.BoundedFormulaInfLegacy α n} (h : (φ.imp ψ).IsCountable) :
    φ.IsCountable := by
  cases h with
  | imp hφ _ => exact hφ

/-- Extract the IsCountable proofs from an imp proof. -/
theorem imp_right {φ ψ : L.BoundedFormulaInfLegacy α n} (h : (φ.imp ψ).IsCountable) :
    ψ.IsCountable := by
  cases h with
  | imp _ hψ => exact hψ

/-- Extract the IsCountable proof from an all proof. -/
theorem all_inner {φ : L.BoundedFormulaInfLegacy α (n + 1)} (h : φ.all.IsCountable) :
    φ.IsCountable := by
  cases h with
  | all hφ => exact hφ

/-- Extract Countable instance from an iSup IsCountable proof. -/
theorem iSup_countable {ι : Type} {φs : ι → L.BoundedFormulaInfLegacy α n}
    (h : (BoundedFormulaInfLegacy.iSup φs).IsCountable) : Countable ι := by
  cases h with
  | iSup _ => assumption

/-- Extract the IsCountable proofs from an iSup proof. -/
theorem iSup_forall {ι : Type} {φs : ι → L.BoundedFormulaInfLegacy α n}
    (h : (BoundedFormulaInfLegacy.iSup φs).IsCountable) : ∀ i, (φs i).IsCountable := by
  cases h with
  | iSup hφs => exact hφs

/-- Extract Countable instance from an iInf IsCountable proof. -/
theorem iInf_countable {ι : Type} {φs : ι → L.BoundedFormulaInfLegacy α n}
    (h : (BoundedFormulaInfLegacy.iInf φs).IsCountable) : Countable ι := by
  cases h with
  | iInf _ => assumption

/-- Extract the IsCountable proofs from an iInf proof. -/
theorem iInf_forall {ι : Type} {φs : ι → L.BoundedFormulaInfLegacy α n}
    (h : (BoundedFormulaInfLegacy.iInf φs).IsCountable) : ∀ i, (φs i).IsCountable := by
  cases h with
  | iInf hφs => exact hφs

end IsCountable

/-- Converts a countable L∞ω formula back to Lω₁ω.
Recurses on the IsCountable proof to extract Countable instances at iSup/iInf nodes. -/
noncomputable def ofCountable : ∀ {n} {φ : L.BoundedFormulaInfLegacy α n}, φ.IsCountable → L.BoundedFormulaω α n
  | _, .falsum, _ => .falsum
  | _, .equal t₁ t₂, _ => .equal t₁ t₂
  | _, .rel R ts, _ => .rel R ts
  | _, .imp _ _, h => .imp (ofCountable h.imp_left) (ofCountable h.imp_right)
  | _, .all _, h => .all (ofCountable h.all_inner)
  | _, @BoundedFormulaInfLegacy.iSup _ _ _ ι _, h =>
    haveI : Countable ι := h.iSup_countable
    haveI : Encodable ι := Encodable.ofCountable ι
    BoundedFormulaω.esup (fun i => ofCountable (h.iSup_forall i))
  | _, @BoundedFormulaInfLegacy.iInf _ _ _ ι _, h =>
    haveI : Countable ι := h.iInf_countable
    haveI : Encodable ι := Encodable.ofCountable ι
    BoundedFormulaω.einf (fun i => ofCountable (h.iInf_forall i))

variable {M : Type w} [L.Structure M] {v : α → M} {xs : Fin n → M}

/-- Semantics is preserved by ofCountable conversion. -/
@[simp]
theorem realize_ofCountable {φ : L.BoundedFormulaInfLegacy α n} (h : φ.IsCountable) :
    (ofCountable h).Realize v xs ↔ φ.Realize v xs := by
  induction h with
  | falsum => rfl
  | equal => rfl
  | rel => rfl
  | imp _ _ ih₁ ih₂ =>
    simp only [ofCountable, BoundedFormulaω.realize_imp, realize_imp, ih₁, ih₂]
  | all _ ih =>
    simp only [ofCountable, BoundedFormulaω.realize_all, realize_all]
    exact forall_congr' fun x => ih
  | iSup hφs ih =>
    simp only [ofCountable, BoundedFormulaω.realize_esup, realize_iSup]
    exact exists_congr fun i => ih i
  | iInf hφs ih =>
    simp only [ofCountable, BoundedFormulaω.realize_einf, realize_iInf]
    exact forall_congr' fun i => ih i

/-- Encoding independence: different `IsCountable` proofs for the same formula
yield semantically equivalent Lω₁ω formulas. The `ofCountable` function uses
`Encodable.ofCountable` (a choice function) at each `iSup`/`iInf` node, so different
proofs may produce syntactically different formulas, but their realizations agree. -/
theorem realize_ofCountable_irrel {φ : L.BoundedFormulaInfLegacy α n}
    (h₁ h₂ : φ.IsCountable) (v : α → M) (xs : Fin n → M) :
    (ofCountable h₁).Realize v xs ↔ (ofCountable h₂).Realize v xs :=
  (realize_ofCountable h₁).trans (realize_ofCountable h₂).symm

end BoundedFormulaInfLegacy

namespace FormulaInfLegacy

/-- Converts a countable L∞ω formula to Lω₁ω. -/
noncomputable def ofCountable {φ : L.FormulaInfLegacy α} (h : φ.IsCountable) : L.Formulaω α :=
  BoundedFormulaInfLegacy.ofCountable h

@[simp]
theorem realize_ofCountable {M : Type w} [L.Structure M] {v : α → M}
    {φ : L.FormulaInfLegacy α} (h : φ.IsCountable) :
    Formulaω.Realize (ofCountable h) v ↔ FormulaInfLegacy.Realize φ v :=
  BoundedFormulaInfLegacy.realize_ofCountable h

end FormulaInfLegacy

namespace SentenceInfLegacy

/-- Converts a countable L∞ω sentence to Lω₁ω. -/
noncomputable def ofCountable {φ : L.SentenceInfLegacy} (h : φ.IsCountable) : L.Sentenceω :=
  FormulaInfLegacy.ofCountable h

@[simp]
theorem realize_ofCountable {M : Type w} [L.Structure M]
    {φ : L.SentenceInfLegacy} (h : φ.IsCountable) :
    Sentenceω.Realize (ofCountable h) M ↔ SentenceInfLegacy.Realize φ M := by
  simp only [Sentenceω.realize_def, SentenceInfLegacy.Realize, ofCountable, FormulaInfLegacy.ofCountable]
  exact BoundedFormulaInfLegacy.realize_ofCountable h

/-- Encoding independence at the sentence level. -/
theorem realize_ofCountable_irrel {φ : L.SentenceInfLegacy}
    (h₁ h₂ : φ.IsCountable) (M : Type w) [L.Structure M] :
    Sentenceω.Realize (ofCountable h₁) M ↔ Sentenceω.Realize (ofCountable h₂) M := by
  simp [realize_ofCountable]

end SentenceInfLegacy

end Language

end FirstOrder
