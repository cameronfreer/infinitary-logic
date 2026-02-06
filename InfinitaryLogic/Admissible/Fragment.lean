/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Lomega1omega.Semantics
import InfinitaryLogic.Lomega1omega.Operations
import Mathlib.SetTheory.Ordinal.Basic

/-!
# Admissible Fragments

This file defines an abstract notion of admissible fragment of Lω₁ω, providing
the interface needed for Barwise compactness and completeness without formalizing
the full theory of admissible sets or KP set theory.

## Main Definitions

- `AdmissibleFragment`: An abstract admissible fragment, given as a set of Lω₁ω
  sentences closed under subformulas and Boolean/quantifier operations.
- `AdmissibleFragment.AFinite`: A set is A-finite if it is a finite subset of
  the fragment's formulas.

## References

- [Keisler-Knight, "Barwise: Infinitary Logic and Admissible Sets", 2004], §3
- [Barwise, "Admissible Sets and Structures", 1975]
-/

universe u v

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

open FirstOrder Structure Ordinal

/-- An abstract admissible fragment of Lω₁ω.

This captures the essential closure properties of an admissible set's intersection
with the formulas of Lω₁ω, without requiring a full formalization of KP set theory
or admissible sets.

The `height` ordinal represents the ordinal height of the admissible set (o(A)),
which bounds the complexity of formulas in the fragment. -/
structure AdmissibleFragment (L : Language.{u, v}) where
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

/-- A set of sentences is A-finite (finite and contained in the fragment). -/
def AdmissibleFragment.AFinite (A : AdmissibleFragment L) (S : Set L.Sentenceω) : Prop :=
  S ⊆ A.formulas ∧ S.Finite

end Language

end FirstOrder
