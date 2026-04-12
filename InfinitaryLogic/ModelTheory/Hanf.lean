/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Lomega1omega.Theory
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Aleph
import Architect

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

The conditional Morley-Hanf bound (`morley_hanf_of_transfer` + `MorleyHanfTransfer`
hypothesis) has been moved to `Conditional/MorleyHanfTransfer.lean`.

## References

- [KK04], §1.6
- [Mar16], §5
-/

universe u v

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

open FirstOrder Structure Cardinal Ordinal

/-- A sentence has arbitrarily large models if for every cardinal κ, there
exists a model of size ≥ κ. -/
@[blueprint "def:arb-large-models"
  (title := /-- Arbitrarily large models -/)
  (statement := /-- A sentence $\varphi$ has arbitrarily large models if for every
    cardinal $\kappa$ there is a model of $\varphi$ of cardinality $\geq \kappa$. -/)]
def HasArbLargeModels (φ : L.Sentenceω) : Prop :=
  ∀ κ : Cardinal, ∃ (M : Type) (_ : L.Structure M),
    Sentenceω.Realize φ M ∧ Cardinal.mk M ≥ κ

/-- A cardinal κ is a Hanf bound for a sentence φ if the existence of a model
of size ≥ κ implies that φ has arbitrarily large models. -/
@[blueprint "def:hanf-bound"
  (title := /-- Hanf bound -/)
  (statement := /-- $\kappa$ is a Hanf bound for $\varphi$ if having a model of
    cardinality $\geq \kappa$ implies having arbitrarily large models. -/)]
def IsHanfBound (φ : L.Sentenceω) (κ : Cardinal) : Prop :=
  (∃ (M : Type) (_ : L.Structure M),
    Sentenceω.Realize φ M ∧ Cardinal.mk M ≥ κ) →
  HasArbLargeModels φ

/-- The Hanf number of a sentence is the least cardinal that is a Hanf bound. -/
@[blueprint "def:hanf-number"
  (title := /-- Hanf number -/)
  (statement := /-- The Hanf number of a sentence $\varphi$: the least cardinal that
    is a Hanf bound. -/)]
noncomputable def HanfNumber (φ : L.Sentenceω) : Cardinal :=
  sInf {κ : Cardinal | IsHanfBound φ κ}

/-- Every Lω₁ω sentence has a Hanf number (i.e., a Hanf bound exists).

This is a fundamental structural result about Lω₁ω. -/
@[blueprint "thm:hanf-existence"
  (title := /-- Hanf number existence -/)
  (statement := /-- Every $\Lomegaone$ sentence has a Hanf bound (and therefore a
    Hanf number). -/)
  (proof := /-- Case split: if $\varphi$ has arbitrarily large models then any
    cardinal is a bound; otherwise there is a cutoff cardinal above which
    no models exist, so the premise is vacuously false. -/)
  (uses := ["def:hanf-bound", "def:arb-large-models"])]
theorem hanf_existence (φ : L.Sentenceω) : ∃ κ, IsHanfBound φ κ := by
  by_cases h : HasArbLargeModels φ
  · -- Any κ works: the conclusion `HasArbLargeModels φ` is always true
    exact ⟨0, fun _ => h⟩
  · -- ¬HasArbLargeModels: ∃ κ₀ with no model of size ≥ κ₀, so premise is vacuously false
    simp only [HasArbLargeModels, not_forall] at h
    obtain ⟨κ₀, hκ₀⟩ := h
    push_neg at hκ₀
    exact ⟨κ₀, fun ⟨M, hStr, hM, hge⟩ => absurd hge (not_le.mpr (hκ₀ M hStr hM))⟩

-- MorleyHanfTransfer and morley_hanf_of_transfer have been moved to
-- Conditional/MorleyHanfTransfer.lean to isolate the external hypothesis.

end Language

end FirstOrder
