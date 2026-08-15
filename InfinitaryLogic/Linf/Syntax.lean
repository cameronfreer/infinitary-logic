/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.ModelTheory.Syntax

/-!
# L∞ω Syntax

This file defines the syntax of the infinitary logic L∞ω, which extends first-order logic
with arbitrary (possibly uncountable) conjunctions and disjunctions.

## Main Definitions

- `FirstOrder.Language.BoundedFormulaInfLegacy`: The type of L∞ω formulas with free variables in `α`
  and bound variables in `Fin n`. Allows arbitrary index types for iSup/iInf.
- `FirstOrder.Language.FormulaInfLegacy`: Formulas with no bound variables.
- `FirstOrder.Language.SentenceInfLegacy`: Sentences (formulas with no free variables).

## Implementation Notes

L∞ω is the union of all Lκω for cardinals κ. Each formula belongs to some Lκω where κ bounds
the cardinality of all index sets used in infinitary connectives. The `IsKappa` predicate
characterizes membership in Lκω; `IsCountable` is the special case for Lω₁ω.

The formulas are parameterized by a universe `uι` for index types. All index types in iSup/iInf
must live in `Type uι`. Choose `uι` large enough for your application; for countable logic,
`uι = 0` suffices.
-/

universe u v u' uι

namespace FirstOrder

namespace Language

variable (L : Language.{u, v})

/-- L∞ω bounded formulas: first-order formulas extended with arbitrary conjunctions and
disjunctions. `BoundedFormulaInfLegacy L α n` has free variables indexed by `α` and `n` bound variables.
The index type `ι` for iSup/iInf lives in universe `uι`. -/
inductive BoundedFormulaInfLegacy (α : Type u') : ℕ → Type max u v u' (uι + 1) where
  /-- The false formula. -/
  | falsum {n} : BoundedFormulaInfLegacy α n
  /-- Equality of two terms. -/
  | equal {n} (t₁ t₂ : L.Term (α ⊕ Fin n)) : BoundedFormulaInfLegacy α n
  /-- A relation applied to terms. -/
  | rel {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) : BoundedFormulaInfLegacy α n
  /-- Implication between formulas. -/
  | imp {n} (φ ψ : BoundedFormulaInfLegacy α n) : BoundedFormulaInfLegacy α n
  /-- Universal quantification. -/
  | all {n} (φ : BoundedFormulaInfLegacy α (n + 1)) : BoundedFormulaInfLegacy α n
  /-- Arbitrary-indexed disjunction (supremum). The index type lives in universe `uι`. -/
  | iSup {n} {ι : Type uι} (φs : ι → BoundedFormulaInfLegacy α n) : BoundedFormulaInfLegacy α n
  /-- Arbitrary-indexed conjunction (infimum). The index type lives in universe `uι`. -/
  | iInf {n} {ι : Type uι} (φs : ι → BoundedFormulaInfLegacy α n) : BoundedFormulaInfLegacy α n

/-- L∞ω formulas with no bound variables in scope. -/
abbrev FormulaInfLegacy (α : Type u') := L.BoundedFormulaInfLegacy α 0

/-- L∞ω sentences: formulas with no free or bound variables in scope. -/
abbrev SentenceInfLegacy := L.FormulaInfLegacy Empty

variable {L} {α : Type u'} {n : ℕ}

namespace BoundedFormulaInfLegacy

instance : Inhabited (L.BoundedFormulaInfLegacy α n) := ⟨falsum⟩

instance : Bot (L.BoundedFormulaInfLegacy α n) := ⟨falsum⟩

/-- The true formula, defined as ¬⊥. -/
protected def top : L.BoundedFormulaInfLegacy α n := imp falsum falsum

instance : Top (L.BoundedFormulaInfLegacy α n) := ⟨BoundedFormulaInfLegacy.top⟩

/-- Negation of a formula. -/
@[match_pattern]
protected def not (φ : L.BoundedFormulaInfLegacy α n) : L.BoundedFormulaInfLegacy α n := φ.imp ⊥

/-- Conjunction of two formulas, defined via De Morgan. -/
@[match_pattern]
protected def and (φ ψ : L.BoundedFormulaInfLegacy α n) : L.BoundedFormulaInfLegacy α n :=
  (φ.imp ψ.not).not

instance : Min (L.BoundedFormulaInfLegacy α n) := ⟨BoundedFormulaInfLegacy.and⟩

/-- Disjunction of two formulas. -/
@[match_pattern]
protected def or (φ ψ : L.BoundedFormulaInfLegacy α n) : L.BoundedFormulaInfLegacy α n :=
  φ.not.imp ψ

instance : Max (L.BoundedFormulaInfLegacy α n) := ⟨BoundedFormulaInfLegacy.or⟩

/-- Existential quantification. -/
@[match_pattern]
protected def ex (φ : L.BoundedFormulaInfLegacy α (n + 1)) : L.BoundedFormulaInfLegacy α n :=
  φ.not.all.not

/-- Biconditional between formulas. -/
protected def iff (φ ψ : L.BoundedFormulaInfLegacy α n) : L.BoundedFormulaInfLegacy α n :=
  (φ.imp ψ) ⊓ (ψ.imp φ)

/-- Empty disjunction (equivalent to ⊥). -/
def emptyiSup : L.BoundedFormulaInfLegacy α n := iSup (ι := Empty) (fun e => e.elim)

/-- Empty conjunction (equivalent to ⊤). -/
def emptyiInf : L.BoundedFormulaInfLegacy α n := iInf (ι := Empty) (fun e => e.elim)

end BoundedFormulaInfLegacy

-- Notation for L∞ω
scoped[Linfomega] infixr:62 " ⟹∞ " => FirstOrder.Language.BoundedFormulaInfLegacy.imp

scoped[Linfomega] prefix:110 "∀'∞ " => FirstOrder.Language.BoundedFormulaInfLegacy.all

scoped[Linfomega] prefix:arg "∼∞" => FirstOrder.Language.BoundedFormulaInfLegacy.not

scoped[Linfomega] prefix:110 "∃'∞ " => FirstOrder.Language.BoundedFormulaInfLegacy.ex

scoped[Linfomega] infixl:61 " ⇔∞ " => FirstOrder.Language.BoundedFormulaInfLegacy.iff

end Language

end FirstOrder
