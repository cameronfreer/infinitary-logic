/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Admissible.Fragment
import InfinitaryLogic.Methods.Henkin.ModelExistence
import InfinitaryLogic.Lomega1omega.Theory
import Architect

/-!
# Compactness and Completeness for Admissible Fragments

This file provides compactness and completeness theorems for
`AdmissibleFragment`, which uses finite-subset compactness (the HF-style
axiom baked into the `compact` field).

**Important**: `barwise_compactness` here is a direct wrapper around
`AdmissibleFragment.compact`, which assumes compactness for ALL theories with
ordinary finite satisfiability. This is stronger than the standard Barwise
compactness theorem (Theorem 3.1.3 of [KK04]), which restricts to Σ₁-on-A
theories with A-finite subsets. See `BarwiseCompactnessData` (in
`BarwiseData.lean`) for the literature-faithful version.

## Main Results

- `barwise_compactness`: If every finite subset of a theory T (within an
  admissible fragment A) has a model, then T itself has a model. (Wrapper
  around `A.compact`; stronger than the standard Barwise theorem.)
- `barwise_completeness_II`: A theory in an admissible fragment that is
  consistent (in the proof-theoretic sense) has a model.

## References

- [KK04], §3.1
- [Bar75], Ch. III
-/

universe u v

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

open FirstOrder Structure

/-- **Finite-subset compactness** (wrapper around `AdmissibleFragment.compact`).

If every finite subset of a theory T (contained in an admissible fragment A)
has a model, then T itself has a model. This is a direct application of the
`compact` field, which assumes unrestricted finite-subset compactness.

**Naming note**: despite its name, this theorem is strictly stronger than the
standard Barwise Compactness Theorem (KK04 Theorem 3.1.3), which restricts
to Σ₁-on-A theories and A-finite subsets (where "A-finite" = ∈ A, not ordinary
finiteness). The standard theorem is available via `BarwiseCompactnessData`. -/
@[blueprint "thm:barwise-compactness"
  (title := /-- Barwise compactness -/)
  (statement := /-- If every $A$-finite subset of a theory $T \subseteq A$ has a model,
    then $T$ has a model. -/)
  (proof := /-- Direct application of the compactness property of the admissible
    fragment to the finite-satisfiability hypothesis. -/)
  (uses := ["def:admissible-fragment"])]
theorem barwise_compactness (A : AdmissibleFragment L)
    {T : Set L.Sentenceω} (hT : T ⊆ A.formulas)
    (hfin : ∀ S, A.AFinite S → S ⊆ T →
      ∃ (M : Type) (_ : L.Structure M), Theoryω.Model S M) :
    ∃ (M : Type) (_ : L.Structure M), Theoryω.Model T M :=
  A.compact T hT fun F hFA hFfin hFS =>
    hfin F ⟨hFA, hFfin⟩ hFS

/-- **Barwise Completeness II** (KK04 Theorem 3.1.2).

A countable theory in an admissible fragment of a countable language that is consistent
(with equality axioms) has a countable model.

Here "consistent" is stated schematically as membership in some consistency
property restricted to the fragment. The full statement requires a proof system
for the admissible fragment, which we do not formalize. -/
@[blueprint "thm:barwise-completeness-ii"
  (title := /-- Barwise completeness II -/)
  (statement := /-- A countable theory in an admissible fragment that belongs to a
    consistency property has a countable model. -/)
  (proof := /-- Extract the consistency property witness and apply the model existence
    theorem to obtain a countable term model. -/)
  (uses := ["def:admissible-fragment"])
  (proofUses := ["thm:model-existence"])]
theorem barwise_completeness_II [Countable (Σ l, L.Functions l)] [Countable (Σ l, L.Relations l)]
    (A : AdmissibleFragment L)
    {T : Set L.Sentenceω} (_hT : T ⊆ A.formulas) (hT_countable : T.Countable)
    (hcons : ∃ C : ConsistencyPropertyEq L, T ∈ C.toConsistencyProperty.sets) :
    ∃ (M : Type u) (_ : L.Structure M) (_ : Countable M),
      Theoryω.Model T M := by
  rcases hcons with ⟨C, hC⟩
  exact consistent_theory_has_model C T hC hT_countable

end Language

end FirstOrder
