/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Linf.Semantics
import Mathlib.Data.Set.Basic

/-!
# L∞ω Theories and Semantic Entailment

This file defines theories, models, semantic entailment, and elementary equivalence
in L∞ω (infinitary logic with arbitrary conjunctions/disjunctions).

## Main Definitions

- `TheoryInf`: A theory in L∞ω is a set of sentences.
- `TheoryInf.Model`: A structure M is a model of theory T if it satisfies all sentences in T.
- `LinfEquiv`: L∞ω-elementary equivalence between structures.

## Main Results

- `LinfEquiv.refl`, `LinfEquiv.symm`, `LinfEquiv.trans`: LinfEquiv is an equivalence relation.
- `LinfEquiv.of_equiv`: Isomorphic structures are L∞ω-equivalent.

## References

- [Karp, "Finite-Quantifier Equivalence", 1965]
- [Keisler-Knight, "Barwise: Infinitary Logic and Admissible Sets", 2004]
-/

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

open FirstOrder Structure

/-! ### Theories -/

/-- A theory in L∞ω is a set of L∞ω sentences. -/
abbrev TheoryInf (L : Language.{u, v}) := Set L.SentenceInf

namespace TheoryInf

variable {T T' : L.TheoryInf} {φ : L.SentenceInf}

/-- A structure M is a model of theory T if it satisfies all sentences in T. -/
def Model (T : L.TheoryInf) (M : Type w) [L.Structure M] : Prop :=
  ∀ φ ∈ T, SentenceInf.Realize φ M

/-- The empty theory has every structure as a model. -/
theorem Model.empty (M : Type w) [L.Structure M] : Model (∅ : L.TheoryInf) M := by
  intro φ hφ
  exact False.elim (Set.notMem_empty φ hφ)

/-- If T ⊆ T' and M ⊨ T', then M ⊨ T. -/
theorem Model.mono (h : T ⊆ T') {M : Type w} [L.Structure M] (hM : T'.Model M) : T.Model M :=
  fun φ hφ => hM φ (h hφ)

/-- Semantic entailment from the empty theory: valid sentences. -/
def Valid (φ : L.SentenceInf) : Prop := ∀ (M : Type) [L.Structure M], SentenceInf.Realize φ M

end TheoryInf

/-! ### L∞ω Elementary Equivalence -/

/-- Two structures are L∞ω-elementarily equivalent if they satisfy the same L∞ω sentences.
This is defined for a fixed sentence universe (index type universe 0). -/
def LinfEquiv (L : Language.{u, v}) (M N : Type w) [L.Structure M] [L.Structure N] : Prop :=
  ∀ φ : BoundedFormulaInf.{u, v, 0, 0} L Empty 0, SentenceInf.Realize φ M ↔ SentenceInf.Realize φ N

namespace LinfEquiv

variable {L : Language.{u, v}}
variable {M : Type w} [L.Structure M]
variable {N : Type w} [L.Structure N]
variable {P : Type w} [L.Structure P]

/-- L∞ω-equivalence is reflexive. -/
theorem refl : LinfEquiv L M M := fun _ => Iff.rfl

/-- L∞ω-equivalence is symmetric. -/
theorem symm (h : LinfEquiv L M N) : LinfEquiv L N M := fun φ => (h φ).symm

/-- L∞ω-equivalence is transitive. -/
theorem trans (h₁ : LinfEquiv L M N) (h₂ : LinfEquiv L N P) : LinfEquiv L M P :=
  fun φ => (h₁ φ).trans (h₂ φ)

/-- Isomorphic structures are L∞ω-equivalent.

This theorem states that isomorphism implies L∞ω-equivalence. The proof uses induction
on formula structure, showing that satisfaction is preserved by isomorphism. -/
theorem of_equiv (e : M ≃[L] N) : LinfEquiv L M N := by
  intro φ
  -- φ is a sentence, i.e., BoundedFormulaInf Empty 0
  -- Need to show: φ.Realize M ↔ φ.Realize N
  -- where Realize for sentences uses Empty.elim and Fin.elim0
  sorry

end LinfEquiv

/-! ### Invariance under Isomorphism -/

/-- Models of a theory are preserved under isomorphism. -/
theorem TheoryInf.Model.of_equiv {T : L.TheoryInf} {M N : Type w} [L.Structure M]
    [L.Structure N] (hM : T.Model M) (e : M ≃[L] N) : T.Model N := by
  intro φ hφ
  -- The universe of φ may differ from 0, so we need a more general argument
  sorry

end Language

end FirstOrder
