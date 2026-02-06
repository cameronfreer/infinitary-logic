/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Lomega1omega.Theory
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Aleph

/-!
# Hanf Numbers

This file defines Hanf numbers for Lω₁ω sentences and states the fundamental
existence theorem and the Morley-Hanf bound.

## Main Definitions

- `HasArbLargeModels`: A sentence has arbitrarily large models.
- `IsHanfBound`: A cardinal κ is a Hanf bound for a sentence φ if having a model
  of size ≥ κ implies having arbitrarily large models.
- `HanfNumber`: The least Hanf bound for a sentence.

## Main Results

- `hanf_existence`: Every Lω₁ω sentence has a Hanf number.
- `morley_hanf`: The Hanf number for Lω₁ω sentences in a countable language
  is bounded by ℶ_ω₁ (the ω₁-th beth number).

## References

- [Keisler-Knight, "Barwise: Infinitary Logic and Admissible Sets", 2004], §1.6
-/

universe u v

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

open FirstOrder Structure Cardinal Ordinal

/-- A sentence has arbitrarily large models if for every cardinal κ, there
exists a model of size ≥ κ. -/
def HasArbLargeModels (φ : L.Sentenceω) : Prop :=
  ∀ κ : Cardinal, ∃ (M : Type) (_ : L.Structure M),
    Sentenceω.Realize φ M ∧ Cardinal.mk M ≥ κ

/-- A cardinal κ is a Hanf bound for a sentence φ if the existence of a model
of size ≥ κ implies that φ has arbitrarily large models. -/
def IsHanfBound (φ : L.Sentenceω) (κ : Cardinal) : Prop :=
  (∃ (M : Type) (_ : L.Structure M),
    Sentenceω.Realize φ M ∧ Cardinal.mk M ≥ κ) →
  HasArbLargeModels φ

/-- The Hanf number of a sentence is the least cardinal that is a Hanf bound. -/
noncomputable def HanfNumber (φ : L.Sentenceω) : Cardinal :=
  sInf {κ : Cardinal | IsHanfBound φ κ}

/-- Every Lω₁ω sentence has a Hanf number (i.e., a Hanf bound exists).

This is a fundamental structural result about Lω₁ω. -/
theorem hanf_existence (φ : L.Sentenceω) : ∃ κ, IsHanfBound φ κ := by
  by_cases h : HasArbLargeModels φ
  · -- Any κ works: the conclusion `HasArbLargeModels φ` is always true
    exact ⟨0, fun _ => h⟩
  · -- ¬HasArbLargeModels: ∃ κ₀ with no model of size ≥ κ₀, so premise is vacuously false
    simp only [HasArbLargeModels, not_forall] at h
    obtain ⟨κ₀, hκ₀⟩ := h
    push_neg at hκ₀
    exact ⟨κ₀, fun ⟨M, hStr, hM, hge⟩ => absurd hge (not_le.mpr (hκ₀ M hStr hM))⟩

/-- **Morley-Hanf Theorem**: For a countable language, the Hanf number of any Lω₁ω
sentence is bounded by ℶ_ω₁ (the ω₁-th beth number).

This gives an explicit upper bound on the Hanf number in terms of the beth
hierarchy. Uses Mathlib's `Cardinal.beth` function which satisfies
`beth 0 = ℵ₀`, `beth (succ α) = 2 ^ beth α`.

The proof requires Ehrenfeucht-Mostowski indiscernibles or deep type-counting
arguments (Ramsey/Erdős-Rado partition calculus, indiscernible sequences for Lω₁ω,
type-counting over countable parameter sets). None of this infrastructure currently
exists in the project or Mathlib. -/
theorem morley_hanf [Countable (Σ l, L.Relations l)] (φ : L.Sentenceω) :
    IsHanfBound φ (Cardinal.beth (Ordinal.omega 1)) := by
  sorry

end Language

end FirstOrder
