/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.ModelTheory.Syntax
import Mathlib.Logic.Encodable.Basic

/-!
# Lω₁ω Syntax

This file defines the syntax of the infinitary logic Lω₁ω, which extends first-order logic
with countable conjunctions and disjunctions.

## Main Definitions

- `FirstOrder.Language.BoundedFormulaω`: The type of Lω₁ω formulas with free variables in `α`
  and bound variables in `Fin n`.
- `FirstOrder.Language.Formulaω`: Formulas with no bound variables.
- `FirstOrder.Language.Sentenceω`: Sentences (formulas with no free variables).

## Implementation Notes

The formulas are defined inductively with constructors for the standard first-order connectives
plus ℕ-indexed conjunction (`iInf`) and disjunction (`iSup`). The `einf` and `esup` variants
handle general countable indices via `Encodable`.

The derived connectives (`and`, `or`, `ex`) are defined classically via De Morgan laws.
This matches Mathlib's `BoundedFormula` conventions and ensures compatibility with
classical semantics.
-/

universe u v u'

namespace FirstOrder

namespace Language

variable (L : Language.{u, v})

/-- Lω₁ω bounded formulas: first-order formulas extended with countable conjunctions and
disjunctions. `BoundedFormulaω L α n` has free variables indexed by `α` and `n` bound variables. -/
inductive BoundedFormulaω (α : Type u') : ℕ → Type max u v u' where
  /-- The false formula. -/
  | falsum {n} : BoundedFormulaω α n
  /-- Equality of two terms. -/
  | equal {n} (t₁ t₂ : L.Term (α ⊕ Fin n)) : BoundedFormulaω α n
  /-- A relation applied to terms. -/
  | rel {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) : BoundedFormulaω α n
  /-- Implication between formulas. -/
  | imp {n} (φ ψ : BoundedFormulaω α n) : BoundedFormulaω α n
  /-- Universal quantification. -/
  | all {n} (φ : BoundedFormulaω α (n + 1)) : BoundedFormulaω α n
  /-- ℕ-indexed disjunction (supremum). Use `esup` for general countable indices. -/
  | iSup {n} (φs : ℕ → BoundedFormulaω α n) : BoundedFormulaω α n
  /-- ℕ-indexed conjunction (infimum). Use `einf` for general countable indices. -/
  | iInf {n} (φs : ℕ → BoundedFormulaω α n) : BoundedFormulaω α n

/-- Lω₁ω formulas with no bound variables in scope. -/
abbrev Formulaω (α : Type u') := L.BoundedFormulaω α 0

/-- Lω₁ω sentences: formulas with no free or bound variables in scope. -/
abbrev Sentenceω := L.Formulaω Empty

variable {L} {α : Type u'} {n : ℕ}

namespace BoundedFormulaω

instance : Inhabited (L.BoundedFormulaω α n) := ⟨falsum⟩

instance : Bot (L.BoundedFormulaω α n) := ⟨falsum⟩

/-- The true formula, defined as ¬⊥. -/
protected def top : L.BoundedFormulaω α n := imp falsum falsum

instance : Top (L.BoundedFormulaω α n) := ⟨BoundedFormulaω.top⟩

/-- Negation of a formula. -/
@[match_pattern]
protected def not (φ : L.BoundedFormulaω α n) : L.BoundedFormulaω α n := φ.imp ⊥

/-- Conjunction of two formulas, defined via De Morgan. -/
@[match_pattern]
protected def and (φ ψ : L.BoundedFormulaω α n) : L.BoundedFormulaω α n :=
  (φ.imp ψ.not).not

instance : Min (L.BoundedFormulaω α n) := ⟨BoundedFormulaω.and⟩

/-- Disjunction of two formulas. -/
@[match_pattern]
protected def or (φ ψ : L.BoundedFormulaω α n) : L.BoundedFormulaω α n :=
  φ.not.imp ψ

instance : Max (L.BoundedFormulaω α n) := ⟨BoundedFormulaω.or⟩

/-- Existential quantification. -/
@[match_pattern]
protected def ex (φ : L.BoundedFormulaω α (n + 1)) : L.BoundedFormulaω α n :=
  φ.not.all.not

/-- Biconditional between formulas. -/
protected def iff (φ ψ : L.BoundedFormulaω α n) : L.BoundedFormulaω α n :=
  (φ.imp ψ) ⊓ (ψ.imp φ)

/-- Indexed conjunction over any `Encodable` type. This extends `iInf` from ℕ-indexed
to general countable indices by encoding. -/
def einf {ι : Type*} [Encodable ι] (φs : ι → L.BoundedFormulaω α n) :
    L.BoundedFormulaω α n :=
  iInf fun k => match Encodable.decode (α := ι) k with
    | some i => φs i
    | none => ⊤

/-- Indexed disjunction over any `Encodable` type. This extends `iSup` from ℕ-indexed
to general countable indices by encoding. -/
def esup {ι : Type*} [Encodable ι] (φs : ι → L.BoundedFormulaω α n) :
    L.BoundedFormulaω α n :=
  iSup fun k => match Encodable.decode (α := ι) k with
    | some i => φs i
    | none => ⊥

end BoundedFormulaω

-- Notation
scoped[Lomega1omega] infixr:62 " ⟹ω " => FirstOrder.Language.BoundedFormulaω.imp

scoped[Lomega1omega] prefix:110 "∀'ω " => FirstOrder.Language.BoundedFormulaω.all

scoped[Lomega1omega] prefix:arg "∼ω" => FirstOrder.Language.BoundedFormulaω.not

scoped[Lomega1omega] prefix:110 "∃'ω " => FirstOrder.Language.BoundedFormulaω.ex

scoped[Lomega1omega] infixl:61 " ⇔ω " => FirstOrder.Language.BoundedFormulaω.iff

end Language

end FirstOrder
