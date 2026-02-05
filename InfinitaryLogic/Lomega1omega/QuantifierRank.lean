/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Lomega1omega.Semantics
import Mathlib.SetTheory.Ordinal.Basic

/-!
# Lω₁ω Quantifier Rank

This file defines the quantifier rank of Lω₁ω formulas and the "agree up to rank α"
relation between structures.

## Main Definitions

- `BoundedFormulaω.qrank`: The quantifier rank of an Lω₁ω formula.
- `EquivQRω`: Two structures are equivalent up to quantifier rank α if they satisfy
  the same sentences of quantifier rank ≤ α.

## Main Results

- `EquivQRω.refl`, `EquivQRω.symm`, `EquivQRω.trans`: Equivalence relation properties.
- `EquivQRω.monotone`: Higher rank equivalence implies lower rank equivalence.
- `qrank_einf`, `qrank_esup`: Quantifier rank of encoded infinitary connectives.

## References

- [Marker, "Lectures on Infinitary Model Theory", 2016]
- [Keisler-Knight, "Barwise: Infinitary Logic and Admissible Sets", 2004]
-/

universe u v w w'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

open FirstOrder Structure Ordinal

/-! ### Quantifier Rank -/

/-- The quantifier rank of an Lω₁ω formula.

- Atomic formulas (falsum, equal, rel) have rank 0
- Implication takes the max of its arguments
- Universal quantification adds 1
- Countable connectives take the sup of their arguments

Note: For Lω₁ω, the quantifier rank is always a countable ordinal (< ω₁). -/
noncomputable def BoundedFormulaω.qrank : L.BoundedFormulaω α n → Ordinal.{0}
  | .falsum       => 0
  | .equal _ _    => 0
  | .rel _ _      => 0
  | .imp φ ψ      => max φ.qrank ψ.qrank
  | .all φ        => φ.qrank + 1
  | .iSup φs      => ⨆ (k : ℕ), (φs k).qrank
  | .iInf φs      => ⨆ (k : ℕ), (φs k).qrank

/-- Quantifier rank of a formula (no bound variables). -/
noncomputable abbrev Formulaω.qrank (φ : L.Formulaω α) : Ordinal.{0} :=
  BoundedFormulaω.qrank φ

/-- Quantifier rank of a sentence. -/
noncomputable abbrev Sentenceω.qrank (φ : L.Sentenceω) : Ordinal.{0} :=
  BoundedFormulaω.qrank φ

/-! ### Quantifier Rank Lemmas -/

namespace BoundedFormulaω

variable {α : Type*} {n : ℕ}

@[simp]
theorem qrank_falsum : (falsum : L.BoundedFormulaω α n).qrank = 0 := rfl

@[simp]
theorem qrank_bot : (⊥ : L.BoundedFormulaω α n).qrank = 0 := rfl

@[simp]
theorem qrank_equal (t₁ t₂ : L.Term (α ⊕ Fin n)) : (equal t₁ t₂).qrank = 0 := rfl

@[simp]
theorem qrank_rel {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
    (rel R ts).qrank = 0 := rfl

@[simp]
theorem qrank_imp (φ ψ : L.BoundedFormulaω α n) :
    (imp φ ψ).qrank = max φ.qrank ψ.qrank := rfl

@[simp]
theorem qrank_all (φ : L.BoundedFormulaω α (n + 1)) :
    (all φ).qrank = φ.qrank + 1 := rfl

@[simp]
theorem qrank_iSup (φs : ℕ → L.BoundedFormulaω α n) :
    (iSup φs).qrank = ⨆ k, (φs k).qrank := rfl

@[simp]
theorem qrank_iInf (φs : ℕ → L.BoundedFormulaω α n) :
    (iInf φs).qrank = ⨆ k, (φs k).qrank := rfl

/-- The top formula has rank 0. -/
@[simp]
theorem qrank_top : (⊤ : L.BoundedFormulaω α n).qrank = 0 := by
  simp only [Top.top, BoundedFormulaω.top, qrank_imp, qrank_falsum, max_self]

/-- Negation preserves quantifier rank. -/
@[simp]
theorem qrank_not (φ : L.BoundedFormulaω α n) : φ.not.qrank = φ.qrank := by
  simp only [BoundedFormulaω.not, qrank_imp, qrank_bot]
  exact max_eq_left (zero_le _)

/-- Conjunction takes max of ranks. -/
theorem qrank_and (φ ψ : L.BoundedFormulaω α n) :
    (φ.and ψ).qrank = max φ.qrank ψ.qrank := by
  simp only [BoundedFormulaω.and, qrank_not, qrank_imp, max_comm φ.qrank ψ.qrank]

/-- Disjunction takes max of ranks. -/
theorem qrank_or (φ ψ : L.BoundedFormulaω α n) :
    (φ.or ψ).qrank = max φ.qrank ψ.qrank := by
  simp only [BoundedFormulaω.or, qrank_not, qrank_imp]

/-- Existential quantification adds 1 to rank. -/
theorem qrank_ex (φ : L.BoundedFormulaω α (n + 1)) :
    φ.ex.qrank = φ.qrank + 1 := by
  simp only [BoundedFormulaω.ex, qrank_not, qrank_all]

/-- The quantifier rank of einf is the sup of the family's ranks.

Note: This requires careful universe handling since `einf` encodes `ι` into `ℕ`,
which changes the universe of the supremum. We need `Small.{0} ι` (from `Encodable`)
for `Ordinal.le_iSup` to work at `Ordinal.{0}`. -/
theorem qrank_einf {ι : Type*} [Encodable ι] (φs : ι → L.BoundedFormulaω α n) :
    (einf φs).qrank = ⨆ i, (φs i).qrank := by
  haveI : Small.{0} ι := Countable.toSmall ι
  simp only [einf, qrank_iInf]
  apply le_antisymm
  · apply Ordinal.iSup_le; intro k
    match h : Encodable.decode (α := ι) k with
    | none => simp
    | some i => exact Ordinal.le_iSup _ i
  · apply Ordinal.iSup_le; intro i
    refine le_trans ?_ (Ordinal.le_iSup
      (fun k : ℕ => (match Encodable.decode (α := ι) k with
        | some i => φs i | none => ⊤).qrank) (Encodable.encode i))
    simp [Encodable.encodek]

/-- The quantifier rank of esup is the sup of the family's ranks. -/
theorem qrank_esup {ι : Type*} [Encodable ι] (φs : ι → L.BoundedFormulaω α n) :
    (esup φs).qrank = ⨆ i, (φs i).qrank := by
  haveI : Small.{0} ι := Countable.toSmall ι
  simp only [esup, qrank_iSup]
  apply le_antisymm
  · apply Ordinal.iSup_le; intro k
    match h : Encodable.decode (α := ι) k with
    | none => simp
    | some i => exact Ordinal.le_iSup _ i
  · apply Ordinal.iSup_le; intro i
    refine le_trans ?_ (Ordinal.le_iSup
      (fun k : ℕ => (match Encodable.decode (α := ι) k with
        | some i => φs i | none => ⊥).qrank) (Encodable.encode i))
    simp [Encodable.encodek]

end BoundedFormulaω

/-! ### Equivalence up to Quantifier Rank -/

/-- Two structures are equivalent up to quantifier rank α if they satisfy the same
Lω₁ω sentences of quantifier rank ≤ α.

This is a semantic relation that captures agreement on formulas of bounded complexity. -/
def EquivQRω (L : Language) (α : Ordinal.{0}) (M N : Type w)
    [L.Structure M] [L.Structure N] : Prop :=
  ∀ (φ : L.Sentenceω), φ.qrank ≤ α → (Sentenceω.Realize φ M ↔ Sentenceω.Realize φ N)

namespace EquivQRω

variable {L : Language.{u, v}}
variable {M : Type w} [L.Structure M]
variable {N : Type w} [L.Structure N]
variable {P : Type w} [L.Structure P]

/-- Equivalence up to quantifier rank is reflexive. -/
theorem refl (α : Ordinal) : EquivQRω L α M M := fun _ _ => Iff.rfl

/-- Equivalence up to quantifier rank is symmetric. -/
theorem symm (h : EquivQRω L α M N) : EquivQRω L α N M :=
  fun φ hφ => (h φ hφ).symm

/-- Equivalence up to quantifier rank is transitive. -/
theorem trans (h₁ : EquivQRω L α M N) (h₂ : EquivQRω L α N P) : EquivQRω L α M P :=
  fun φ hφ => (h₁ φ hφ).trans (h₂ φ hφ)

/-- Equivalence at higher rank implies equivalence at lower rank. -/
theorem monotone {α β : Ordinal} (hαβ : α ≤ β) (h : EquivQRω L β M N) :
    EquivQRω L α M N := fun φ hφ => h φ (le_trans hφ hαβ)

/-- Equivalence at rank 0 means agreement on all quantifier-free sentences. -/
theorem zero_iff_agree_atomic : EquivQRω L 0 M N ↔
    ∀ φ : L.Sentenceω, φ.qrank = 0 →
      (Sentenceω.Realize φ M ↔ Sentenceω.Realize φ N) := by
  constructor
  · intro h φ hφ; exact h φ (le_of_eq hφ)
  · intro h φ hφ; exact h φ (nonpos_iff_eq_zero.mp hφ)

end EquivQRω

end Language

end FirstOrder
