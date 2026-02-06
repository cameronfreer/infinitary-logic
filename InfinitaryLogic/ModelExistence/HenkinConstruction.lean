/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelExistence.ConsistencyProperty
import Mathlib.Order.Zorn

/-!
# Henkin Construction

This file provides the infrastructure for the Henkin-style proof of the model
existence theorem for Lω₁ω. The construction proceeds in several stages:

1. **Maximal consistent extension**: Extend a consistent set of sentences to a
   maximal one within the consistency property (using Zorn's lemma or sequential
   enumeration for countable languages).
2. **Term model**: Build a model from equivalence classes of closed terms.
3. **Truth lemma**: Show that truth in the term model corresponds to membership
   in the maximal consistent set.

## Main Results

- `ConsistencyProperty.exists_maximal`: Every consistent set extends to a
  maximal consistent set (requires chain-closure of C.sets).
- `ConsistencyProperty.MaximalConsistent`: Predicate for maximal consistency.
- Properties of maximal consistent sets (closure under connectives).

## References

- [Marker, "Lectures on Infinitary Model Theory", 2016], §4.1
- [Keisler, "Model Theory for Infinitary Logic", 1971]
-/

universe u v

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

open FirstOrder Structure

/-! ### Maximal Consistent Sets -/

/-- A set is maximal consistent in a consistency property if it is consistent
and no proper superset is consistent. Uses Mathlib's `Maximal` predicate:
`Maximal (· ∈ C.sets) S` means `S ∈ C.sets ∧ ∀ S', S' ∈ C.sets → S ⊆ S' → S = S'`. -/
def ConsistencyProperty.MaximalConsistent (C : ConsistencyProperty L)
    (S : Set L.Sentenceω) : Prop :=
  Maximal (· ∈ C.sets) S

/-- Every consistent set in a consistency property can be extended to a maximal
consistent set, by Zorn's lemma.

The chain-closure axiom of `ConsistencyProperty` ensures that the union of any
nonempty chain of consistent sets remains consistent, providing the upper bound
required by Zorn's lemma. -/
theorem ConsistencyProperty.exists_maximal (C : ConsistencyProperty L)
    (S : Set L.Sentenceω) (hS : S ∈ C.sets) :
    ∃ S', S ⊆ S' ∧ C.MaximalConsistent S' := by
  obtain ⟨m, hSm, hmax⟩ := zorn_subset_nonempty C.sets
    (fun chain hchain hIsChain hne => ⟨⋃₀ chain, C.chain_closure chain hchain hIsChain hne,
      fun s hs => Set.subset_sUnion_of_mem hs⟩) S hS
  exact ⟨m, hSm, hmax⟩

/-! ### Properties of Maximal Consistent Sets

These properties follow from maximality: if adding a sentence preserves
consistency, then it must already be in the maximal set. -/

/-- A maximal consistent set is consistent. -/
theorem ConsistencyProperty.MaximalConsistent.consistent
    {C : ConsistencyProperty L} {S : Set L.Sentenceω}
    (hmax : C.MaximalConsistent S) : S ∈ C.sets :=
  hmax.prop

/-- If S ∪ {φ} is consistent and S is maximal, then φ ∈ S. -/
theorem ConsistencyProperty.MaximalConsistent.mem_of_union_consistent
    {C : ConsistencyProperty L} {S : Set L.Sentenceω}
    (hmax : C.MaximalConsistent S) {φ : L.Sentenceω} (h : S ∪ {φ} ∈ C.sets) :
    φ ∈ S := by
  have heq := hmax.eq_of_ge h Set.subset_union_left
  exact heq ▸ Set.mem_union_right S (Set.mem_singleton φ)

/-- In a maximal consistent set, for every implication φ → ψ in S,
either ¬φ ∈ S or ψ ∈ S. -/
theorem ConsistencyProperty.MaximalConsistent.imp_mem
    {C : ConsistencyProperty L} {S : Set L.Sentenceω}
    (hmax : C.MaximalConsistent S)
    {φ ψ : L.Sentenceω} (h : BoundedFormulaω.imp φ ψ ∈ S) :
    φ.not ∈ S ∨ ψ ∈ S := by
  rcases C.C1_imp S hmax.consistent φ ψ h with h1 | h2
  · exact Or.inl (hmax.mem_of_union_consistent h1)
  · exact Or.inr (hmax.mem_of_union_consistent h2)

/-- In a maximal consistent set, double negation elimination holds. -/
theorem ConsistencyProperty.MaximalConsistent.not_not_mem
    {C : ConsistencyProperty L} {S : Set L.Sentenceω}
    (hmax : C.MaximalConsistent S)
    {φ : L.Sentenceω} (h : φ.not.not ∈ S) :
    φ ∈ S :=
  hmax.mem_of_union_consistent (C.C2_not_not S hmax.consistent φ h)

/-- In a maximal consistent set, if ⋀ᵢ φᵢ ∈ S, then φₖ ∈ S for all k. -/
theorem ConsistencyProperty.MaximalConsistent.iInf_mem
    {C : ConsistencyProperty L} {S : Set L.Sentenceω}
    (hmax : C.MaximalConsistent S)
    {φs : ℕ → L.Sentenceω} (h : BoundedFormulaω.iInf φs ∈ S) (k : ℕ) :
    φs k ∈ S :=
  hmax.mem_of_union_consistent (C.C3_iInf S hmax.consistent φs h k)

/-- In a maximal consistent set, if ⋁ᵢ φᵢ ∈ S, then φₖ ∈ S for some k. -/
theorem ConsistencyProperty.MaximalConsistent.iSup_mem
    {C : ConsistencyProperty L} {S : Set L.Sentenceω}
    (hmax : C.MaximalConsistent S)
    {φs : ℕ → L.Sentenceω} (h : BoundedFormulaω.iSup φs ∈ S) :
    ∃ k, φs k ∈ S := by
  obtain ⟨k, hk⟩ := C.C4_iSup S hmax.consistent φs h
  exact ⟨k, hmax.mem_of_union_consistent hk⟩

/-! ### Term Model Construction

The term model for the Henkin construction is built from closed terms of
the extended language `L' = L[[ℕ]]`. Two terms are equivalent if the
maximal consistent set contains the equation `t₁ = t₂`.

**Note**: The full term model construction requires:
1. Language extension with Henkin constants (`L[[ℕ]]`)
2. An equivalence relation on closed terms (via the maximal set)
3. Interpreting function/relation symbols on equivalence classes
4. A truth lemma by structural induction

Each of these steps requires significant infrastructure. The current file
provides the maximal consistent extension and its properties; the term model
construction is deferred to a future iteration. -/

end Language

end FirstOrder
