/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Scott.Sentence

/-!
# Proof of CountableRefinementHypothesis

This file proves `CountableRefinementHypothesis` (with `sorry` for the counting argument)
and provides unconditional wrappers for all Sentence.lean-level theorems. Together with
the downstream wrappers in Rank.lean, Height.lean, CountableCorollary.lean, and
CountingModels.lean, this recovers the full unconditional API.

## Strategy

The proof proceeds through staged lemmas:
1. Define the refinement-witness set for a fixed tuple
2. Show each refinement ordinal is witnessed by a separating Lω₁ω formula
3. The separating formula determines the ordinal (injective map into countable set)
4. Conclude countability

## Main Result

- `countableRefinementHypothesis` : `CountableRefinementHypothesis L`
-/

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable [Countable (Σ l, L.Relations l)]

open FirstOrder Structure Fin Ordinal BoundedFormulaω

/-! ### The Counting Lemma -/

/-- The countable refinement hypothesis holds for all countable relational languages.

This is the sole remaining `sorry` in the Scott analysis pipeline. The counting
argument (injecting refinement ordinals into a countable set of formula codes)
requires infrastructure connecting BFEquiv types to syntactic objects. -/
theorem countableRefinementHypothesis : CountableRefinementHypothesis.{u, v, w} L := by
  sorry

/-! ### Unconditional Wrappers (Sentence.lean level)

Each theorem below is a one-liner applying `countableRefinementHypothesis` to the
corresponding `_of` variant in Sentence.lean. -/

/-- The set of refinement ordinals for any tuple is countable. -/
theorem countable_refinement_steps
    {M : Type w} [L.Structure M] [Countable M]
    (n : ℕ) (a : Fin n → M) :
    Set.Countable {α : Ordinal.{0} | α < Ordinal.omega 1 ∧
      ∃ (N : Type w) (_ : L.Structure N) (_ : Countable N) (b : Fin n → N),
        BFEquiv (L := L) α n a b ∧ ¬BFEquiv (L := L) (Order.succ α) n a b} :=
  countableRefinementHypothesis M n a

/-- Per-tuple stabilization below ω₁. -/
theorem per_tuple_stabilization_below_omega1
    {M : Type w} [L.Structure M] [Countable M]
    (n : ℕ) (a : Fin n → M) :
    ∃ γ < (Ordinal.omega 1 : Ordinal.{0}),
      ∀ α, γ ≤ α → α < Ordinal.omega 1 → Order.succ α < Ordinal.omega 1 →
        ∀ (N : Type w) [L.Structure N] [Countable N] (b : Fin n → N),
          (BFEquiv (L := L) α n a b ↔ BFEquiv (L := L) (Order.succ α) n a b) :=
  per_tuple_stabilization_below_omega1_of countableRefinementHypothesis n a

/-- Complete stabilization below ω₁. -/
theorem exists_complete_stabilization (M : Type w) [L.Structure M] [Countable M] :
    ∃ α < (Ordinal.omega 1 : Ordinal.{0}), StabilizesCompletely (L := L) M α :=
  exists_complete_stabilization_of countableRefinementHypothesis M

/-- Existence of a stabilization ordinal (BFEquiv0 characterizes isomorphism). -/
theorem exists_stabilization (M : Type w) [L.Structure M] [Countable M] :
    ∃ α < (Ordinal.omega 1 : Ordinal.{0}), StabilizesAt (L := L) M α :=
  exists_stabilization_of countableRefinementHypothesis M

/-- The stabilization ordinal is below ω₁. -/
theorem stabilizationOrdinal_lt_omega1' (M : Type w) [L.Structure M] [Countable M] :
    stabilizationOrdinal (L := L) M < Ordinal.omega 1 :=
  stabilizationOrdinal_lt_omega1_of countableRefinementHypothesis M

/-- The characterization property holds at stabilizationOrdinal. -/
theorem stabilizationOrdinal_stabilizes (M : Type w) [L.Structure M] [Countable M] :
    StabilizesAt (L := L) M (stabilizationOrdinal (L := L) M) :=
  stabilizationOrdinal_stabilizes_of countableRefinementHypothesis M

/-- BFEquiv0 at stabilizationOrdinal characterizes isomorphism. -/
theorem stabilizationOrdinal_spec (M : Type w) [L.Structure M] [Countable M]
    (N : Type w) [L.Structure N] [Countable N] :
    BFEquiv0 (L := L) M N (stabilizationOrdinal (L := L) M) ↔ Nonempty (M ≃[L] N) :=
  stabilizationOrdinal_stabilizes M N

/-- The Scott sentence of M characterizes M up to isomorphism among countable structures. -/
theorem scottSentence_characterizes (M : Type w) [L.Structure M] [Countable M]
    (N : Type w) [L.Structure N] [Countable N] :
    (scottSentence (L := L) M).realize_as_sentence N ↔ Nonempty (M ≃[L] N) :=
  scottSentence_characterizes_of countableRefinementHypothesis M N

/-- If N realizes the Scott sentence of M, then M ≃[L] N. -/
theorem scottSentence_realizes_implies_equiv (M : Type w) [L.Structure M] [Countable M]
    (N : Type w) [L.Structure N] [Countable N]
    (h : (scottSentence (L := L) M).realize_as_sentence N) : Nonempty (M ≃[L] N) :=
  (scottSentence_characterizes M N).mp h

/-- M itself satisfies its own Scott sentence. -/
theorem scottSentence_self (M : Type w) [L.Structure M] [Countable M] :
    (scottSentence (L := L) M).realize_as_sentence M :=
  (scottSentence_characterizes M M).mpr ⟨Equiv.refl L M⟩

/-- Isomorphic structures satisfy each other's Scott sentences. -/
theorem scottSentence_of_equiv (M N : Type w) [L.Structure M] [L.Structure N]
    [Countable M] [Countable N] (e : M ≃[L] N) :
    (scottSentence (L := L) M).realize_as_sentence N :=
  (scottSentence_characterizes M N).mpr ⟨e⟩

end Language

end FirstOrder
