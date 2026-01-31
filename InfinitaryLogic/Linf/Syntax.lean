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

- `FirstOrder.Language.BoundedFormulaInf`: The type of L∞ω formulas with free variables in `α`
  and bound variables in `Fin n`. Allows arbitrary index types for iSup/iInf.
- `FirstOrder.Language.FormulaInf`: Formulas with no bound variables.
- `FirstOrder.Language.SentenceInf`: Sentences (formulas with no free variables).

## Implementation Notes

L∞ω is the union of all Lκω for cardinals κ. Each formula belongs to some Lκω where κ bounds
the cardinality of all index sets used in infinitary connectives. The `IsKappa` predicate
characterizes membership in Lκω; `IsCountable` is the special case for Lω₁ω.

The formulas are defined with `ι : Type` (universe 0) as the index type for iSup/iInf.
This is sufficient for most applications and avoids universe issues. For higher universes,
one would need a universe-polymorphic definition.
-/

universe u v u'

namespace FirstOrder

namespace Language

variable (L : Language.{u, v})

/-- L∞ω bounded formulas: first-order formulas extended with arbitrary conjunctions and
disjunctions. `BoundedFormulaInf L α n` has free variables indexed by `α` and `n` bound variables.
The index type `ι` for iSup/iInf is `Type` (universe 0). -/
inductive BoundedFormulaInf (α : Type u') : ℕ → Type max u v u' 1 where
  /-- The false formula. -/
  | falsum {n} : BoundedFormulaInf α n
  /-- Equality of two terms. -/
  | equal {n} (t₁ t₂ : L.Term (α ⊕ Fin n)) : BoundedFormulaInf α n
  /-- A relation applied to terms. -/
  | rel {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) : BoundedFormulaInf α n
  /-- Implication between formulas. -/
  | imp {n} (φ ψ : BoundedFormulaInf α n) : BoundedFormulaInf α n
  /-- Universal quantification. -/
  | all {n} (φ : BoundedFormulaInf α (n + 1)) : BoundedFormulaInf α n
  /-- Arbitrary-indexed disjunction (supremum). The index type is `Type` (universe 0). -/
  | iSup {n} {ι : Type} (φs : ι → BoundedFormulaInf α n) : BoundedFormulaInf α n
  /-- Arbitrary-indexed conjunction (infimum). The index type is `Type` (universe 0). -/
  | iInf {n} {ι : Type} (φs : ι → BoundedFormulaInf α n) : BoundedFormulaInf α n

/-- L∞ω formulas with no bound variables in scope. -/
abbrev FormulaInf (α : Type u') := L.BoundedFormulaInf α 0

/-- L∞ω sentences: formulas with no free or bound variables in scope. -/
abbrev SentenceInf := L.FormulaInf Empty

variable {L} {α : Type u'} {n : ℕ}

namespace BoundedFormulaInf

instance : Inhabited (L.BoundedFormulaInf α n) := ⟨falsum⟩

instance : Bot (L.BoundedFormulaInf α n) := ⟨falsum⟩

/-- The true formula, defined as ¬⊥. -/
protected def top : L.BoundedFormulaInf α n := imp falsum falsum

instance : Top (L.BoundedFormulaInf α n) := ⟨BoundedFormulaInf.top⟩

/-- Negation of a formula. -/
@[match_pattern]
protected def not (φ : L.BoundedFormulaInf α n) : L.BoundedFormulaInf α n := φ.imp ⊥

/-- Conjunction of two formulas, defined via De Morgan. -/
@[match_pattern]
protected def and (φ ψ : L.BoundedFormulaInf α n) : L.BoundedFormulaInf α n :=
  (φ.imp ψ.not).not

instance : Min (L.BoundedFormulaInf α n) := ⟨BoundedFormulaInf.and⟩

/-- Disjunction of two formulas. -/
@[match_pattern]
protected def or (φ ψ : L.BoundedFormulaInf α n) : L.BoundedFormulaInf α n :=
  φ.not.imp ψ

instance : Max (L.BoundedFormulaInf α n) := ⟨BoundedFormulaInf.or⟩

/-- Existential quantification. -/
@[match_pattern]
protected def ex (φ : L.BoundedFormulaInf α (n + 1)) : L.BoundedFormulaInf α n :=
  φ.not.all.not

/-- Biconditional between formulas. -/
protected def iff (φ ψ : L.BoundedFormulaInf α n) : L.BoundedFormulaInf α n :=
  (φ.imp ψ) ⊓ (ψ.imp φ)

/-- Empty disjunction (equivalent to ⊥). -/
def emptyiSup : L.BoundedFormulaInf α n := iSup (ι := Empty) (fun e => e.elim)

/-- Empty conjunction (equivalent to ⊤). -/
def emptyiInf : L.BoundedFormulaInf α n := iInf (ι := Empty) (fun e => e.elim)

end BoundedFormulaInf

-- Notation for L∞ω
scoped[Linfomega] infixr:62 " ⟹∞ " => FirstOrder.Language.BoundedFormulaInf.imp

scoped[Linfomega] prefix:110 "∀'∞ " => FirstOrder.Language.BoundedFormulaInf.all

scoped[Linfomega] prefix:arg "∼∞" => FirstOrder.Language.BoundedFormulaInf.not

scoped[Linfomega] prefix:110 "∃'∞ " => FirstOrder.Language.BoundedFormulaInf.ex

scoped[Linfomega] infixl:61 " ⇔∞ " => FirstOrder.Language.BoundedFormulaInf.iff

end Language

end FirstOrder
