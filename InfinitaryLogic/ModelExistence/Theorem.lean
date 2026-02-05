/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelExistence.ConsistencyProperty

/-!
# Model Existence Theorem

This file states the model existence theorem for Lω₁ω: any set of sentences
that belongs to a consistency property has a countable model.

## Main Results

- `model_existence`: If S is consistent (belongs to a consistency property),
  then S has a countable model. (Marker Theorem 4.1.2 / Keisler)

## References

- [Marker, "Lectures on Infinitary Model Theory", 2016], Theorem 4.1.2
- [Keisler, "Model Theory for Infinitary Logic", 1971]
-/

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

open FirstOrder Structure

/-- **Model Existence Theorem** for Lω₁ω (Marker Theorem 4.1.2).

If a set S of Lω₁ω sentences belongs to a consistency property, then S has
a countable model.

The proof proceeds by a Henkin-style construction:
1. Extend the language with countably many new constants
2. Extend S to a maximal consistent set S* using a priority argument
3. Build a term model from S*
4. Verify the model satisfies all sentences in S

This is the fundamental model-building tool for infinitary logic. -/
theorem model_existence (C : ConsistencyProperty L)
    (S : Set L.Sentenceω) (hS : S ∈ C.sets) :
    ∃ (M : Type) (_ : L.Structure M) (_ : Countable M),
      Theoryω.Model S M := by
  sorry

/-- A consistent theory has a countable model.

This is a direct corollary of model existence. -/
theorem consistent_theory_has_model (C : ConsistencyProperty L)
    (T : L.Theoryω) (hT : T ∈ C.sets) :
    ∃ (M : Type) (_ : L.Structure M) (_ : Countable M),
      T.Model M := by
  exact model_existence C T hT

end Language

end FirstOrder
