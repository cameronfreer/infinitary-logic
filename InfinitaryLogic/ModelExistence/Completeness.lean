/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelExistence.Theorem
import InfinitaryLogic.Lomega1omega.Operations

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

/-- **Karp Completeness**: A sentence in a countable language that belongs to some
consistency property with equality axioms has a countable model.

This is a sentence-level consequence of the model existence theorem. -/
theorem karp_completeness [Countable (Σ l, L.Functions l)] [Countable (Σ l, L.Relations l)]
    (φ : L.Sentenceω)
    (h : ∃ C : ConsistencyPropertyEq L, {φ} ∈ C.toConsistencyProperty.sets) :
    ∃ (M : Type u) (_ : L.Structure M) (_ : Countable M), Sentenceω.Realize φ M := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨M, hStr, hCount, hModel⟩ := model_existence C {φ} hC (Set.countable_singleton φ)
  exact ⟨M, hStr, hCount, hModel φ (Set.mem_singleton φ)⟩

/-- A type (set of formulas in one free variable) is omitted by a structure M
if no element of M realizes all formulas in the type simultaneously. -/
def OmitsType (M : Type*) [L.Structure M] (p : Set (L.Formulaω (Fin 1))) : Prop :=
  ∀ m : M, ∃ φ ∈ p, ¬ Formulaω.Realize φ (fun _ => m)

/-- **Omitting Types Theorem** for Lω₁ω.

Given a countable consistent theory T in a countable language and a countable collection
of types to omit (each of which is not isolated by any formula consistent with T),
there exists a countable model of T that omits all the given types.

This is a powerful generalization of the standard omitting types theorem from
first-order logic to the countable infinitary setting. -/
theorem omitting_types [Countable (Σ l, L.Functions l)] [Countable (Σ l, L.Relations l)]
    (T : L.Theoryω) (hT_countable : T.Countable)
    (Γ : Set (Set (L.Formulaω (Fin 1))))
    (hT : ∃ C : ConsistencyPropertyEq L, T ∈ C.toConsistencyProperty.sets)
    (hΓ : Γ.Countable)
    (h_not_isolated : ∀ p ∈ Γ, ∀ (C : ConsistencyPropertyEq L)
      (φ : L.Formulaω (Fin 1)),
      T ∪ {(φ.relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)).ex} ∈ C.toConsistencyProperty.sets →
      ∃ ψ ∈ p, T ∪ {((φ.and ψ.not).relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)).ex}
        ∈ C.toConsistencyProperty.sets) :
    ∃ (M : Type u) (_ : L.Structure M) (_ : Countable M),
      Theoryω.Model T M ∧ ∀ p ∈ Γ, OmitsType (L := L) M p := by
  sorry

end Language

end FirstOrder
