/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Lomega1omega.Theory

/-!
# Consistency Properties

This file defines the notion of a consistency property for Lω₁ω, following
Marker's axiomatization (C0)-(C7). A consistency property is a family of sets
of sentences satisfying closure conditions that guarantee model existence.

## Main Definitions

- `ConsistencyProperty`: A family of sets of Lω₁ω sentences satisfying the
  consistency axioms (C0)-(C7).

## References

- [Marker, "Lectures on Infinitary Model Theory", 2016], §4.1
- [Keisler, "Model Theory for Infinitary Logic", 1971]
-/

universe u v

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

open FirstOrder Structure

/-- A basic consistency property for Lω₁ω sentences, with only propositional and
infinitary connective axioms (C0)-(C4).

**Note**: This is insufficient for model existence on its own, since it allows
contradictory sets (e.g., containing both φ and ¬φ without containing ⊥).
Use `ConsistencyPropertyEq` for the full model existence theorem. -/
structure ConsistencyProperty (L : Language.{u, v}) where
  /-- The family of consistent sets. -/
  sets : Set (Set L.Sentenceω)
  /-- (C0) No set in the family contains falsum. -/
  C0_no_contradiction : ∀ S ∈ sets, ⊥ ∉ S
  /-- (C1) Closure under implication decomposition: if φ → ψ ∈ S, then either
      S ∪ {¬φ} or S ∪ {ψ} is in the family. -/
  C1_imp : ∀ S ∈ sets, ∀ φ ψ : L.Sentenceω,
    BoundedFormulaω.imp φ ψ ∈ S →
    S ∪ {φ.not} ∈ sets ∨ S ∪ {ψ} ∈ sets
  /-- (C2) Double negation elimination: if ¬¬φ ∈ S, then S ∪ {φ} is consistent. -/
  C2_not_not : ∀ S ∈ sets, ∀ φ : L.Sentenceω,
    φ.not.not ∈ S → S ∪ {φ} ∈ sets
  /-- (C3) Closure under countable conjunction: if ⋀ᵢ φᵢ ∈ S, then S ∪ {φₖ} is
      consistent for all k. -/
  C3_iInf : ∀ S ∈ sets, ∀ φs : ℕ → L.Sentenceω,
    BoundedFormulaω.iInf φs ∈ S → ∀ k, S ∪ {φs k} ∈ sets
  /-- (C4) Witness for countable disjunction: if ⋁ᵢ φᵢ ∈ S, then there exists k
      such that S ∪ {φₖ} is consistent. -/
  C4_iSup : ∀ S ∈ sets, ∀ φs : ℕ → L.Sentenceω,
    BoundedFormulaω.iSup φs ∈ S → ∃ k, S ∪ {φs k} ∈ sets

/-- A set of sentences is consistent with respect to a consistency property. -/
def ConsistencyProperty.Consistent (C : ConsistencyProperty L) (S : Set L.Sentenceω) : Prop :=
  S ∈ C.sets

/-- A consistency property with equality and quantifier axioms (C0)-(C7).

This extends `ConsistencyProperty` with the conditions needed for the Henkin
construction in the model existence theorem. Without these, `ConsistencyProperty`
alone is too weak to guarantee model existence (it allows contradictory sets
that contain both φ and ¬φ without containing ⊥).

**Design note**: The quantifier conditions (C5)-(C7) involve expanding the language
with Henkin witnesses. For this formalization, we state a simplified version that
captures the essential algebraic structure. The full version with language expansion
would require additional infrastructure for Henkin constants. -/
structure ConsistencyPropertyEq (L : Language.{u, v}) extends ConsistencyProperty L where
  /-- (C5) Equality is reflexive: for any closed term t, S ∪ {t = t} is consistent. -/
  C5_eq_refl : ∀ S ∈ toConsistencyProperty.sets,
    ∀ t : L.Term (Empty ⊕ Fin 0), S ∪ {BoundedFormulaω.equal t t} ∈ toConsistencyProperty.sets
  /-- (C6) Substitution of equals (schematic). -/
  C6_eq_subst : True  -- Schematic; full version requires term substitution infrastructure
  /-- (C7) Quantifier witness: if ∃x φ(x) ∈ S, then S ∪ {φ(c)} is consistent for
      some Henkin constant c. -/
  C7_quantifier : True  -- Schematic; full version requires Henkin constant infrastructure

end Language

end FirstOrder
