/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Lomega1omega.Semantics
import InfinitaryLogic.Lomega1omega.Operations
import InfinitaryLogic.Lomega1omega.Theory
import Mathlib.SetTheory.Ordinal.Basic
import Architect

/-!
# Admissible Fragments

This file defines an abstract notion of admissible fragment of Lω₁ω, split
into two layers:

- `AdmissibleFragmentCore`: the syntactic closure properties of an admissible
  fragment L_A (formulas, height, closure under connectives, sub-formula
  backward closures). This is the stable part that every consumer needs.
- `AdmissibleFragment`: extends `AdmissibleFragmentCore` with a compactness
  axiom. **Note**: the compactness field uses ordinary finite satisfiability
  (matching the HF / first-order case), which is stronger than the standard
  Barwise compactness theorem (which restricts to Σ₁-on-A theories with
  A-finite subsets). See `BarwiseCompactnessData` (in `BarwiseData.lean`)
  for the literature-faithful version.

## Main Definitions

- `AdmissibleFragmentCore`: closure properties of an admissible fragment,
  without compactness.
- `AdmissibleFragment`: extends `AdmissibleFragmentCore` with a finite-subset
  compactness axiom. Backward compatible with all existing consumers.
- `AdmissibleFragment.AFinite`: a set is A-finite if it is a finite subset
  of the fragment's formulas. (This matches the HF notion; for the standard
  Barwise notion "T₀ ∈ A", see `BarwiseCompactnessData.isAFinite`.)

## Design Note

The split into Core + compactness reflects the standard development in
Barwise's book: Chapter III treats closure properties of admissible fragments
separately from the compactness principle (Σ₁-reflection), which is about
the admissible *set* A, not just the formulas L_A. The project's current
`AdmissibleFragment.compact` field is stronger than the standard Barwise
theorem; it is retained for backward compatibility but should not be read
as a faithful formalization of Barwise compactness.

## References

- [KK04], §3
- [Bar75], Ch. III, VII–VIII
-/

universe u v

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

open FirstOrder Structure Ordinal

/-- The syntactic closure properties of an admissible fragment of Lω₁ω.

This captures the closure of an admissible set's intersection with the
formulas of Lω₁ω (the "admissible fragment" L_A), without including the
compactness principle. Every consumer that needs only closure properties
(proof system, soundness, Nadel bound) can use this layer directly.

The `height` ordinal represents the ordinal height of the admissible set
(o(A)), which bounds the complexity of formulas in the fragment. -/
structure AdmissibleFragmentCore (L : Language.{u, v}) where
  /-- The set of sentences belonging to this fragment. -/
  formulas : Set L.Sentenceω
  /-- The ordinal height of the admissible set. -/
  height : Ordinal
  /-- The height is > ω. -/
  height_gt_omega : Ordinal.omega0 < height
  /-- Closure under negation. -/
  closed_neg : ∀ φ ∈ formulas, φ.not ∈ formulas
  /-- Closure under implication. -/
  closed_imp : ∀ φ ψ, φ ∈ formulas → ψ ∈ formulas → φ.imp ψ ∈ formulas
  /-- Closure under countable conjunction (for families in the fragment). -/
  closed_iInf : ∀ φs : ℕ → L.Sentenceω,
    (∀ k, φs k ∈ formulas) → BoundedFormulaω.iInf φs ∈ formulas
  /-- Closure under countable disjunction (for families in the fragment). -/
  closed_iSup : ∀ φs : ℕ → L.Sentenceω,
    (∀ k, φs k ∈ formulas) → BoundedFormulaω.iSup φs ∈ formulas
  /-- Closure under quantifier instances: if an existential sentence
      `(φ.relabel Sum.inr).ex` is in the fragment, then the substitution
      instance `φ.subst (fun _ => t)` is also in the fragment for any
      closed term t. This ensures Henkin witnesses stay within the fragment
      and is needed for the consistency property in Barwise compactness. -/
  closed_quantifier_instance : ∀ (φ : L.Formulaω (Fin 1)) (t : L.Term Empty),
    (φ.relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)).ex ∈ formulas →
    φ.subst (fun _ => t) ∈ formulas
  /-- Falsum belongs to the fragment. -/
  falsum_mem : (BoundedFormulaω.falsum : L.Sentenceω) ∈ formulas
  /-- Backward closure: implication left component. -/
  closed_imp_left : ∀ φ ψ : L.Sentenceω, BoundedFormulaω.imp φ ψ ∈ formulas → φ ∈ formulas
  /-- Backward closure: implication right component. -/
  closed_imp_right : ∀ φ ψ : L.Sentenceω, BoundedFormulaω.imp φ ψ ∈ formulas → ψ ∈ formulas
  /-- Backward closure: conjunction components. -/
  closed_iInf_component : ∀ (φs : ℕ → L.Sentenceω) (k : ℕ),
    BoundedFormulaω.iInf φs ∈ formulas → φs k ∈ formulas
  /-- Backward closure: disjunction components. -/
  closed_iSup_component : ∀ (φs : ℕ → L.Sentenceω) (k : ℕ),
    BoundedFormulaω.iSup φs ∈ formulas → φs k ∈ formulas

/-- An abstract admissible fragment of Lω₁ω, extending `AdmissibleFragmentCore`
with a finite-subset compactness axiom.

**Important**: the `compact` field uses ordinary finite satisfiability, which
matches the Barwise compactness theorem only for the case A = HF (hereditarily
finite sets, i.e., first-order logic). For Lω₁ω with a general admissible set,
the standard Barwise theorem restricts to Σ₁-on-A theories with A-finite
subsets (where "A-finite" = ∈ A, not ordinary finiteness). See
`BarwiseCompactnessData` for the literature-faithful version.

This structure is retained for backward compatibility with existing consumers
(`barwise_compactness`, `ConsistencyBridge`, `EMRealization`). -/
@[blueprint "def:admissible-fragment"
  (title := /-- Admissible fragment -/)
  (statement := /-- An admissible fragment of $\Lomegaone$: a collection of sentences
    closed under subformulas, negation, quantification, and countable conjunction/disjunction,
    with a compactness axiom for finite subsets. -/)]
structure AdmissibleFragment (L : Language.{u, v}) extends AdmissibleFragmentCore L where
  /-- **Finite-subset compactness** (stronger than the standard Barwise theorem).
  If every finite subset of S ⊆ formulas has a model, then S has a model.
  This is the HF-style compactness principle; the standard Barwise compactness
  restricts to Σ₁-on-A theories and A-finite subsets. -/
  compact : ∀ S ⊆ formulas,
    (∀ F, F ⊆ formulas → F.Finite → F ⊆ S →
      ∃ (M : Type) (_ : L.Structure M), Theoryω.Model F M) →
    ∃ (M : Type) (_ : L.Structure M), Theoryω.Model S M

/-- A set of sentences is A-finite (finite and contained in the fragment).

**Note**: this uses ordinary finiteness, matching the HF case. For the standard
Barwise notion "T₀ ∈ A" (which includes hyperarithmetical sets for
A = L(ω₁^CK)), see `BarwiseCompactnessData.isAFinite`. -/
def AdmissibleFragment.AFinite (A : AdmissibleFragment L) (S : Set L.Sentenceω) : Prop :=
  S ⊆ A.formulas ∧ S.Finite

end Language

end FirstOrder
