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

namespace BoundedFormulaInf

namespace IsCountable

/-- Extract the IsCountable proofs from an imp proof. -/
theorem imp_left {φ ψ : L.BoundedFormulaInf α n} (h : (φ.imp ψ).IsCountable) :
    φ.IsCountable := by
  cases h with
  | imp hφ _ => exact hφ

/-- Extract the IsCountable proofs from an imp proof. -/
theorem imp_right {φ ψ : L.BoundedFormulaInf α n} (h : (φ.imp ψ).IsCountable) :
    ψ.IsCountable := by
  cases h with
  | imp _ hψ => exact hψ

/-- Extract the IsCountable proof from an all proof. -/
theorem all_inner {φ : L.BoundedFormulaInf α (n + 1)} (h : φ.all.IsCountable) :
    φ.IsCountable := by
  cases h with
  | all hφ => exact hφ

/-- Extract Countable instance from an iSup IsCountable proof. -/
theorem iSup_countable {ι : Type} {φs : ι → L.BoundedFormulaInf α n}
    (h : (BoundedFormulaInf.iSup φs).IsCountable) : Countable ι := by
  cases h with
  | iSup _ => assumption

/-- Extract the IsCountable proofs from an iSup proof. -/
theorem iSup_forall {ι : Type} {φs : ι → L.BoundedFormulaInf α n}
    (h : (BoundedFormulaInf.iSup φs).IsCountable) : ∀ i, (φs i).IsCountable := by
  cases h with
  | iSup hφs => exact hφs

/-- Extract Countable instance from an iInf IsCountable proof. -/
theorem iInf_countable {ι : Type} {φs : ι → L.BoundedFormulaInf α n}
    (h : (BoundedFormulaInf.iInf φs).IsCountable) : Countable ι := by
  cases h with
  | iInf _ => assumption

/-- Extract the IsCountable proofs from an iInf proof. -/
theorem iInf_forall {ι : Type} {φs : ι → L.BoundedFormulaInf α n}
    (h : (BoundedFormulaInf.iInf φs).IsCountable) : ∀ i, (φs i).IsCountable := by
  cases h with
  | iInf hφs => exact hφs

end IsCountable

/-- Converts a countable L∞ω formula back to Lω₁ω.
Recurses on the IsCountable proof to extract Countable instances at iSup/iInf nodes. -/
noncomputable def ofCountable : ∀ {n} {φ : L.BoundedFormulaInf α n}, φ.IsCountable → L.BoundedFormulaω α n
  | _, .falsum, _ => .falsum
  | _, .equal t₁ t₂, _ => .equal t₁ t₂
  | _, .rel R ts, _ => .rel R ts
  | _, .imp _ _, h => .imp (ofCountable h.imp_left) (ofCountable h.imp_right)
  | _, .all _, h => .all (ofCountable h.all_inner)
  | _, @BoundedFormulaInf.iSup _ _ _ ι _, h =>
    haveI : Countable ι := h.iSup_countable
    haveI : Encodable ι := Encodable.ofCountable ι
    BoundedFormulaω.esup (fun i => ofCountable (h.iSup_forall i))
  | _, @BoundedFormulaInf.iInf _ _ _ ι _, h =>
    haveI : Countable ι := h.iInf_countable
    haveI : Encodable ι := Encodable.ofCountable ι
    BoundedFormulaω.einf (fun i => ofCountable (h.iInf_forall i))

variable {M : Type w} [L.Structure M] {v : α → M} {xs : Fin n → M}

/-- Semantics is preserved by ofCountable conversion. -/
@[simp]
theorem realize_ofCountable {φ : L.BoundedFormulaInf α n} (h : φ.IsCountable) :
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

end BoundedFormulaInf

namespace FormulaInf

/-- Converts a countable L∞ω formula to Lω₁ω. -/
noncomputable def ofCountable {φ : L.FormulaInf α} (h : φ.IsCountable) : L.Formulaω α :=
  BoundedFormulaInf.ofCountable h

@[simp]
theorem realize_ofCountable {M : Type w} [L.Structure M] {v : α → M}
    {φ : L.FormulaInf α} (h : φ.IsCountable) :
    Formulaω.Realize (ofCountable h) v ↔ FormulaInf.Realize φ v :=
  BoundedFormulaInf.realize_ofCountable h

end FormulaInf

namespace SentenceInf

/-- Converts a countable L∞ω sentence to Lω₁ω. -/
noncomputable def ofCountable {φ : L.SentenceInf} (h : φ.IsCountable) : L.Sentenceω :=
  FormulaInf.ofCountable h

@[simp]
theorem realize_ofCountable {M : Type w} [L.Structure M]
    {φ : L.SentenceInf} (h : φ.IsCountable) :
    Sentenceω.Realize (ofCountable h) M ↔ SentenceInf.Realize φ M := by
  simp only [Sentenceω.Realize, SentenceInf.Realize, ofCountable, FormulaInf.ofCountable]
  exact BoundedFormulaInf.realize_ofCountable h

end SentenceInf

end Language

end FirstOrder
