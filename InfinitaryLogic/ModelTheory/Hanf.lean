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
- `morley_hanf_of_transfer`: The Hanf number for Lω₁ω sentences in a countable
  language is bounded by ℶ_ω₁, conditional on `MorleyHanfTransfer`.

## Definitions

- `MorleyHanfTransfer`: Deep combinatorial transfer hypothesis encapsulating
  Erdős-Rado extraction and Ehrenfeucht-Mostowski stretching for Lω₁ω.

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

/-- **Deep set-theoretic/model-theoretic transfer hypothesis** for the Morley-Hanf theorem.

This encapsulates the combined content of:
1. **Erdős-Rado extraction**: Models of size ≥ ℶ_{ω₁} in a countable language
   contain Lω₁ω-indiscernible sequences of uncountable length.
2. **Ehrenfeucht-Mostowski stretching**: Such indiscernible sequences can be
   stretched to produce models of arbitrary size satisfying the same Lω₁ω sentences.

These deep combinatorial arguments (Ramsey/partition calculus + EM functors)
require infrastructure not currently formalized in Lean or Mathlib.

See [Mar16], §5; [KK04], §1.6. -/
def MorleyHanfTransfer (L : Language.{u, v}) [Countable (Σ l, L.Relations l)] : Prop :=
  ∀ (φ : L.Sentenceω) (M : Type) [L.Structure M],
    Sentenceω.Realize φ M → Cardinal.mk M ≥ Cardinal.beth (Ordinal.omega 1) →
    HasArbLargeModels φ

/-- **Morley-Hanf Theorem** (conditional on transfer hypothesis).

For a countable language, the Hanf number of any Lω₁ω sentence is bounded
by ℶ_ω₁ (the ω₁-th beth number), assuming the deep combinatorial transfer
principle `MorleyHanfTransfer`.

The unconditional version requires formalizing Erdős-Rado partition calculus
and Ehrenfeucht-Mostowski functors for Lω₁ω, which are not currently available
in Lean or Mathlib.

**Boundary**: The hypothesis `htransfer` captures exactly the deep
set-theoretic/model-theoretic transfer step. All other reasoning is formalized. -/
@[blueprint "thm:morley-hanf"
  (title := /-- Morley-Hanf bound -/)
  (statement := /-- Conditional on the Morley-Hanf transfer hypothesis,
    $\beth_{\omegaone}$ is a Hanf bound for every $\Lomegaone$ sentence. -/)
  (proof := /-- Given a model of size $\geq \beth_{\omegaone}$, the transfer
    hypothesis directly yields arbitrarily large models. -/)
  (uses := ["def:hanf-bound", "def:arb-large-models"])]
theorem morley_hanf_of_transfer [Countable (Σ l, L.Relations l)]
    (htransfer : MorleyHanfTransfer L) (φ : L.Sentenceω) :
    IsHanfBound φ (Cardinal.beth (Ordinal.omega 1)) := by
  intro ⟨M, hStr, hφ, hsize⟩
  exact htransfer φ M hφ hsize

end Language

end FirstOrder
