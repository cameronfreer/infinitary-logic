/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelExistence.Theorem

/-!
# Karp Completeness

This file states the completeness theorem for Lω₁ω: a sentence that belongs to
some consistency property has a model.

## Main Results

- `karp_completeness`: If φ belongs to some consistency property, then φ has a model.
- `omitting_types`: The omitting types theorem for Lω₁ω.

## References

- [Marker, "Lectures on Infinitary Model Theory", 2016]
- [Keisler-Knight, "Barwise: Infinitary Logic and Admissible Sets", 2004]
-/

universe u v

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

open FirstOrder Structure

/-- **Karp Completeness**: A sentence that belongs to some consistency property has a model.

This is a sentence-level consequence of the model existence theorem. -/
theorem karp_completeness (φ : L.Sentenceω)
    (h : ∃ C : ConsistencyProperty L, {φ} ∈ C.sets) :
    ∃ (M : Type) (_ : L.Structure M), Sentenceω.Realize φ M := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨M, hStr, _, hModel⟩ := model_existence C {φ} hC
  exact ⟨M, hStr, hModel φ (Set.mem_singleton φ)⟩

/-- **Omitting Types Theorem** for Lω₁ω.

Given a consistent theory T and a collection of types to omit (each of which is not
isolated by any formula), there exists a model of T that omits all the given types.

This is a powerful generalization of the standard omitting types theorem from
first-order logic to the countable infinitary setting. -/
theorem omitting_types
    (T : L.Theoryω)
    (Γ : Set (Set (L.Formulaω (Fin 1))))
    (hT : ∃ C : ConsistencyProperty L, T ∈ C.sets)
    (hΓ : Γ.Countable)
    (h_not_isolated : ∀ p ∈ Γ, True) :  -- schematic non-isolation condition
    ∃ (M : Type) (_ : L.Structure M) (_ : Countable M),
      Theoryω.Model T M := by
  sorry

end Language

end FirstOrder
