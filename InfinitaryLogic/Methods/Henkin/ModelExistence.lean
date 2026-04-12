/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Methods.Henkin.ConsistencyProperty
import InfinitaryLogic.Methods.Henkin.Construction
import Architect

/-!
# Model Existence Theorem

This file states the model existence theorem for Lω₁ω: any set of sentences
that belongs to a consistency property has a countable model.

## Main Results

- `model_existence`: If S is consistent (belongs to a consistency property),
  then S has a countable model. (Marker Theorem 4.1.2 / Keisler)

## References

- [Mar16], Theorem 4.1.2
- [Kei71]
-/

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

open FirstOrder Structure

/-- **Model Existence Theorem** for Lω₁ω (Marker Theorem 4.1.2).

If a countable set S of Lω₁ω sentences in a countable language belongs to a
consistency property with equality axioms, then S has a countable model.

The proof proceeds by a Henkin-style construction:
1. Extend the language with countably many new constants
2. Extend S to a maximal consistent set S* using a priority argument
3. Build a term model from S*
4. Verify the model satisfies all sentences in S

The countability assumptions on the language and S are essential: without them,
a consistent set like {c_i ≠ c_j | i ≠ j} for uncountably many constants can
force any model to be uncountable.

This is the fundamental model-building tool for infinitary logic. -/
@[blueprint "thm:model-existence"
  (title := /-- Model existence -/)
  (statement := /-- If a countable set $S$ of $\Lomegaone$ sentences in a countable
    language belongs to a consistency property with equality axioms, then $S$ has a
    countable model. -/)
  (proof := /-- Henkin construction: extend the language with constants, extend $S$ to
    a maximal consistent set, build a term model, verify via truth lemma. -/)]
theorem model_existence [Countable (Σ l, L.Functions l)] [Countable (Σ l, L.Relations l)]
    (C : ConsistencyPropertyEq L)
    (S : Set L.Sentenceω) (hS : S ∈ C.toConsistencyProperty.sets)
    (_hS_countable : S.Countable) :
    ∃ (M : Type u) (_ : L.Structure M) (_ : Countable M),
      Theoryω.Model S M := by
  -- Step 1: Extend S to a maximal consistent set S*
  obtain ⟨S', hSS', hmax⟩ := C.toConsistencyProperty.exists_maximal S hS
  -- Step 2: Build the term model from S*
  exact ⟨TermModel C S' hmax, termModelStructure, inferInstance,
    fun φ hφ => (truthLemma φ).mp (hSS' hφ)⟩

/-- A consistent countable theory in a countable language has a countable model.

This is a direct corollary of model existence. -/
theorem consistent_theory_has_model [Countable (Σ l, L.Functions l)] [Countable (Σ l, L.Relations l)]
    (C : ConsistencyPropertyEq L)
    (T : L.Theoryω) (hT : T ∈ C.toConsistencyProperty.sets)
    (hT_countable : T.Countable) :
    ∃ (M : Type u) (_ : L.Structure M) (_ : Countable M),
      T.Model M :=
  model_existence C T hT hT_countable

end Language

end FirstOrder
