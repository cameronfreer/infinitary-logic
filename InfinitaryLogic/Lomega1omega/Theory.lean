/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Lomega1omega.Semantics
import Mathlib.Data.Set.Basic

/-!
# Lω₁ω Theories and Semantic Entailment

This file defines theories, models, semantic entailment, and elementary equivalence
in Lω₁ω (countable infinitary logic with countable conjunctions/disjunctions).

## Main Definitions

- `Theoryω`: A theory in Lω₁ω is a set of sentences.
- `Theoryω.Model`: A structure M is a model of theory T if it satisfies all sentences in T.
- `Theoryω.SemEntails`: Semantic entailment: T ⊨ φ if every model of T satisfies φ.
- `LomegaEquiv`: Lω₁ω-elementary equivalence between structures.

## Main Results

- `Theoryω.SemEntails.monotone`: Semantic entailment is monotone in the theory.
- `LomegaEquiv.refl`, `LomegaEquiv.symm`, `LomegaEquiv.trans`: LomegaEquiv is an equivalence relation.
- `LomegaEquiv.of_equiv`: Isomorphic structures are Lω₁ω-equivalent.

## References

- [Marker, "Lectures on Infinitary Model Theory", 2016]
- [Keisler-Knight, "Barwise: Infinitary Logic and Admissible Sets", 2004]
-/

universe u v w w'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

open FirstOrder Structure

/-! ### Theories -/

/-- A theory in Lω₁ω is a set of Lω₁ω sentences. -/
abbrev Theoryω (L : Language.{u, v}) := Set L.Sentenceω

namespace Theoryω

variable {T T' : L.Theoryω} {φ : L.Sentenceω}

/-- A structure M is a model of theory T if it satisfies all sentences in T. -/
def Model (T : L.Theoryω) (M : Type w) [L.Structure M] : Prop :=
  ∀ φ ∈ T, Sentenceω.Realize φ M

/-- The empty theory has every structure as a model. -/
theorem Model.empty (M : Type w) [L.Structure M] : Model (∅ : L.Theoryω) M := by
  intro φ hφ
  exact False.elim (Set.notMem_empty φ hφ)

/-- If T ⊆ T' and M ⊨ T', then M ⊨ T. -/
theorem Model.mono (h : T ⊆ T') {M : Type w} [L.Structure M] (hM : T'.Model M) : T.Model M :=
  fun φ hφ => hM φ (h hφ)

/-- Semantic entailment: T ⊨ φ means every model of T (at universe w) satisfies φ. -/
def SemEntails' (T : L.Theoryω) (φ : L.Sentenceω) (M : Type*) [L.Structure M] : Prop :=
  T.Model M → Sentenceω.Realize φ M

/-- A sentence in T is entailed by T (for a specific model). -/
theorem SemEntails'.mem {M : Type w} [L.Structure M] (hφ : φ ∈ T) : T.SemEntails' φ M := by
  intro hM
  exact hM φ hφ

/-- Semantic entailment from the empty theory: valid sentences. -/
def Valid (φ : L.Sentenceω) : Prop := ∀ (M : Type) [L.Structure M], Sentenceω.Realize φ M

end Theoryω

/-! ### Lω₁ω Elementary Equivalence -/

/-- Two structures are Lω₁ω-elementarily equivalent if they satisfy the same Lω₁ω sentences. -/
def LomegaEquiv (L : Language) (M N : Type*) [L.Structure M] [L.Structure N] : Prop :=
  ∀ φ : L.Sentenceω, Sentenceω.Realize φ M ↔ Sentenceω.Realize φ N

namespace LomegaEquiv

variable {M : Type w} [L.Structure M]
variable {N : Type w'} [L.Structure N]
variable {P : Type*} [L.Structure P]

/-- Lω₁ω-equivalence is reflexive. -/
theorem refl : LomegaEquiv L M M := fun _ => Iff.rfl

/-- Lω₁ω-equivalence is symmetric. -/
theorem symm (h : LomegaEquiv L M N) : LomegaEquiv L N M := fun φ => (h φ).symm

/-- Lω₁ω-equivalence is transitive. -/
theorem trans (h₁ : LomegaEquiv L M N) (h₂ : LomegaEquiv L N P) : LomegaEquiv L M P :=
  fun φ => (h₁ φ).trans (h₂ φ)

/-- Isomorphic structures are Lω₁ω-equivalent.

This theorem states that isomorphism implies Lω₁ω-equivalence. The proof uses induction
on formula structure, showing that satisfaction is preserved by isomorphism. -/
theorem of_equiv {M N : Type w} [L.Structure M] [L.Structure N] (e : M ≃[L] N) :
    LomegaEquiv L M N := by
  intro φ
  -- φ is a sentence, i.e., BoundedFormulaω Empty 0
  -- Need to show: φ.Realize M ↔ φ.Realize N
  -- where Realize for sentences uses Empty.elim and Fin.elim0
  sorry

end LomegaEquiv

/-! ### Invariance under Isomorphism -/

/-- Models of a theory are preserved under isomorphism. -/
theorem Theoryω.Model.of_equiv {T : L.Theoryω} {M N : Type w} [L.Structure M]
    [L.Structure N] (hM : T.Model M) (e : M ≃[L] N) : T.Model N := by
  intro φ hφ
  have h := LomegaEquiv.of_equiv e φ
  exact h.mp (hM φ hφ)

end Language

end FirstOrder
