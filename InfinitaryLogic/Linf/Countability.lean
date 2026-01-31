/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Linf.Operations
import Mathlib.SetTheory.Cardinal.Aleph

/-!
# Countability Predicates for L∞ω Formulas

This file defines predicates characterizing when an L∞ω formula belongs to specific
cardinality-bounded fragments.

## Main Definitions

- `BoundedFormulaInf.IsCountable`: A formula is countable if all index types in iSup/iInf
  constructors are countable. This characterizes membership in Lω₁ω.
- `BoundedFormulaInf.IsKappa`: A formula has cardinality < κ if all index types have
  cardinality < κ. This characterizes membership in Lκω.
-/

universe u v u'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {α : Type u'}

namespace BoundedFormulaInf

/-- A formula is countable if all index types in iSup/iInf constructors are countable.
This characterizes membership in Lω₁ω. -/
inductive IsCountable : L.BoundedFormulaInf α n → Prop
  | falsum : IsCountable falsum
  | equal (t₁ t₂ : L.Term (α ⊕ Fin n)) : IsCountable (equal t₁ t₂)
  | rel {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) : IsCountable (rel R ts)
  | imp {φ ψ : L.BoundedFormulaInf α n} : IsCountable φ → IsCountable ψ → IsCountable (imp φ ψ)
  | all {φ : L.BoundedFormulaInf α (n + 1)} : IsCountable φ → IsCountable φ.all
  | iSup {ι : Type} [Countable ι] {φs : ι → L.BoundedFormulaInf α n} :
      (∀ i, IsCountable (φs i)) → IsCountable (iSup φs)
  | iInf {ι : Type} [Countable ι] {φs : ι → L.BoundedFormulaInf α n} :
      (∀ i, IsCountable (φs i)) → IsCountable (iInf φs)

/-- A formula has all index types with cardinality < κ.
This characterizes membership in Lκω. -/
inductive IsKappa (κ : Cardinal) : L.BoundedFormulaInf α n → Prop
  | falsum : IsKappa κ falsum
  | equal (t₁ t₂ : L.Term (α ⊕ Fin n)) : IsKappa κ (equal t₁ t₂)
  | rel {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) : IsKappa κ (rel R ts)
  | imp {φ ψ : L.BoundedFormulaInf α n} : IsKappa κ φ → IsKappa κ ψ → IsKappa κ (imp φ ψ)
  | all {φ : L.BoundedFormulaInf α (n + 1)} : IsKappa κ φ → IsKappa κ φ.all
  | iSup {ι : Type} {φs : ι → L.BoundedFormulaInf α n} :
      Cardinal.mk ι < κ → (∀ i, IsKappa κ (φs i)) → IsKappa κ (iSup φs)
  | iInf {ι : Type} {φs : ι → L.BoundedFormulaInf α n} :
      Cardinal.mk ι < κ → (∀ i, IsKappa κ (φs i)) → IsKappa κ (iInf φs)

variable {n : ℕ}

/-- IsKappa is monotonic in κ. -/
theorem IsKappa.mono {κ κ' : Cardinal} (hle : κ ≤ κ') {φ : L.BoundedFormulaInf α n}
    (h : IsKappa κ φ) : IsKappa κ' φ := by
  induction h with
  | falsum => exact IsKappa.falsum
  | equal t₁ t₂ => exact IsKappa.equal t₁ t₂
  | rel R ts => exact IsKappa.rel R ts
  | imp _ _ ih₁ ih₂ => exact IsKappa.imp ih₁ ih₂
  | all _ ih => exact IsKappa.all ih
  | iSup hcard _ ih => exact IsKappa.iSup (lt_of_lt_of_le hcard hle) ih
  | iInf hcard _ ih => exact IsKappa.iInf (lt_of_lt_of_le hcard hle) ih

/-- Countable types have cardinality < ℵ₁. -/
theorem mk_lt_aleph_one_of_countable' {ι : Type} [Countable ι] : Cardinal.mk ι < Cardinal.aleph 1 := by
  calc Cardinal.mk ι ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
    _ < Cardinal.aleph 1 := Cardinal.aleph0_lt_aleph_one

/-- Types with cardinality < ℵ₁ are countable. -/
theorem countable_of_mk_lt_aleph_one' {ι : Type} (h : Cardinal.mk ι < Cardinal.aleph 1) :
    Countable ι := by
  rw [← Cardinal.succ_aleph0] at h
  exact Cardinal.mk_le_aleph0_iff.mp (Order.lt_succ_iff.mp h)

/-- IsCountable implies IsKappa ℵ₁. -/
theorem IsCountable.toIsKappa_aleph1 {φ : L.BoundedFormulaInf α n}
    (h : IsCountable φ) : IsKappa (Cardinal.aleph 1) φ := by
  induction h with
  | falsum => exact IsKappa.falsum
  | equal t₁ t₂ => exact IsKappa.equal t₁ t₂
  | rel R ts => exact IsKappa.rel R ts
  | imp _ _ ih₁ ih₂ => exact IsKappa.imp ih₁ ih₂
  | all _ ih => exact IsKappa.all ih
  | iSup h ih => exact IsKappa.iSup mk_lt_aleph_one_of_countable' ih
  | iInf h ih => exact IsKappa.iInf mk_lt_aleph_one_of_countable' ih

/-- IsKappa ℵ₁ implies IsCountable. -/
theorem IsKappa.toIsCountable {φ : L.BoundedFormulaInf α n}
    (h : IsKappa (Cardinal.aleph 1) φ) : IsCountable φ := by
  induction h with
  | falsum => exact IsCountable.falsum
  | equal t₁ t₂ => exact IsCountable.equal t₁ t₂
  | rel R ts => exact IsCountable.rel R ts
  | imp _ _ ih₁ ih₂ => exact IsCountable.imp ih₁ ih₂
  | all _ ih => exact IsCountable.all ih
  | iSup hcard h ih =>
    have : Countable _ := countable_of_mk_lt_aleph_one' hcard
    exact IsCountable.iSup ih
  | iInf hcard h ih =>
    have : Countable _ := countable_of_mk_lt_aleph_one' hcard
    exact IsCountable.iInf ih

/-- IsCountable is equivalent to IsKappa ℵ₁. -/
theorem isCountable_iff_isKappa_aleph1 {φ : L.BoundedFormulaInf α n} :
    IsCountable φ ↔ IsKappa (Cardinal.aleph 1) φ :=
  ⟨IsCountable.toIsKappa_aleph1, IsKappa.toIsCountable⟩

end BoundedFormulaInf

end Language

end FirstOrder
