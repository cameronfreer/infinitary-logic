/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Admissible.Fragment
import InfinitaryLogic.ModelExistence.Theorem
import InfinitaryLogic.Lomega1omega.Theory
import Architect

/-!
# Barwise Compactness and Completeness

This file states the Barwise compactness theorem and Barwise completeness II
for admissible fragments of Lω₁ω.

## Main Results

- `barwise_compactness`: If every A-finite subset of a theory T (within an admissible
  fragment A) has a model, then T itself has a model.
- `barwise_completeness_II`: A theory in an admissible fragment that is consistent
  (in the proof-theoretic sense) has a model.

## References

- [KK04], §3.1
- [Bar75]
-/

universe u v

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

open FirstOrder Structure

/-- **Barwise Compactness Theorem** (KK04 Theorem 3.1.3).

If every A-finite subset of a theory T (contained in an admissible fragment A)
has a model, then T itself has a model.

This is a far-reaching generalization of the classical compactness theorem.
While full first-order compactness fails for Lω₁ω, this restricted form holds
for theories within admissible fragments. -/
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
  obtain ⟨C, hC⟩ := hcons
  exact model_existence C T hC hT_countable

end Language

end FirstOrder
