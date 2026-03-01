/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Scott.Sentence
import Mathlib.SetTheory.Cardinal.Regular

/-!
# Scott Rank

This file defines the Scott rank of a structure and proves that it is below ω₁
for countable structures.

## Main Definitions

- `scottRank`: The Scott rank of a structure, defined as the supremum of element ranks + 1.
- `elementRank`: The rank of an individual element (least ordinal where it's distinguished).

## Main Results

- `scottRank_lt_omega1`: For countable structures, Scott rank < ω₁.

## Implementation Notes

We define Scott rank as sup {elementRank a + 1 : a ∈ M}, where elementRank a is the
least ordinal α such that any tuple extending with a is determined by its α-type.
This is equivalent to the stabilization ordinal approach but more compositional.
-/

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable [Countable (Σ l, L.Relations l)]

open FirstOrder Structure Fin Ordinal

/-- The rank of an element m in a structure M: the least ordinal α such that
for any tuple a containing m, the α-type of a determines whether any extension
has a back-and-forth equivalent extension.

We use Ordinal.{0} for consistency with stabilizationOrdinal and BFEquiv in formulas. -/
noncomputable def elementRank {M : Type w} [L.Structure M] (m : M) : Ordinal.{0} :=
  sInf {α : Ordinal.{0} | ∀ (N : Type w) [L.Structure N] [Countable N] (b : Fin 1 → N),
    BFEquiv (L := L) (M := M) (N := N) α 1 ![m] b →
      ∀ (N' : Type w) [L.Structure N'] [Countable N'] (b' : Fin 1 → N'),
        BFEquiv (L := L) (M := M) (N := N') α 1 ![m] b' →
          (BFEquiv (L := L) (M := M) (N := N) (Order.succ α) 1 ![m] b ↔
           BFEquiv (L := L) (M := M) (N := N') (Order.succ α) 1 ![m] b')}

/-- The Scott rank of a structure M is the supremum of element ranks + 1.
We use Ordinal.{0} for consistency with elementRank and stabilizationOrdinal. -/
noncomputable def scottRank (M : Type w) [L.Structure M] [Countable M] : Ordinal.{0} :=
  ⨆ (m : M), elementRank (L := L) m + 1

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- At a complete stabilization ordinal, the elementRank defining set is satisfied trivially:
`StabilizesCompletely M α` gives `BFEquiv α ↔ BFEquiv (succ α)` for all tuples, so both
directions of the iff hold. -/
private theorem completeStab_mem_elementRank_set {M : Type w} [L.Structure M] [Countable M]
    {α : Ordinal.{0}} (hstab : StabilizesCompletely (L := L) M α) (m : M) :
    α ∈ {α : Ordinal.{0} | ∀ (N : Type w) [L.Structure N] [Countable N] (b : Fin 1 → N),
      BFEquiv (L := L) (M := M) (N := N) α 1 ![m] b →
        ∀ (N' : Type w) [L.Structure N'] [Countable N'] (b' : Fin 1 → N'),
          BFEquiv (L := L) (M := M) (N := N') α 1 ![m] b' →
            (BFEquiv (L := L) (M := M) (N := N) (Order.succ α) 1 ![m] b ↔
             BFEquiv (L := L) (M := M) (N := N') (Order.succ α) 1 ![m] b')} := by
  intro N _ _ b hBFN N' _ _ b' hBFN'
  exact ⟨fun _ => (hstab 1 N' ![m] b').mp hBFN', fun _ => (hstab 1 N ![m] b).mp hBFN⟩

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- The elementRank of any element is bounded by any complete stabilization ordinal. -/
private theorem elementRank_le_completeStab {M : Type w} [L.Structure M] [Countable M]
    {α : Ordinal.{0}} (hstab : StabilizesCompletely (L := L) M α) (m : M) :
    elementRank (L := L) m ≤ α :=
  csInf_le' (completeStab_mem_elementRank_set hstab m)

theorem elementRank_lt_omega1 {M : Type w} [L.Structure M] [Countable M] (m : M) :
    elementRank (L := L) m < (Ordinal.omega 1 : Ordinal.{0}) := by
  obtain ⟨α, hα_lt, hstab⟩ := exists_complete_stabilization (L := L) M
  exact lt_of_le_of_lt (elementRank_le_completeStab hstab m) hα_lt

/-- Conditional variant of `elementRank_lt_omega1`. Sorry-free. -/
theorem elementRank_lt_omega1_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    {M : Type w} [L.Structure M] [Countable M] (m : M) :
    elementRank (L := L) m < (Ordinal.omega 1 : Ordinal.{0}) := by
  obtain ⟨α, hα_lt, hstab⟩ := exists_complete_stabilization_of hcount M
  exact lt_of_le_of_lt (elementRank_le_completeStab hstab m) hα_lt

/-- Scott rank of a countable structure is a countable ordinal.

The proof uses that:
1. Each elementRank m ≤ α for a complete stabilization ordinal α < ω₁
2. So scottRank = ⨆ m, elementRank m + 1 ≤ α + 1 < ω₁
-/
theorem scottRank_lt_omega1 (M : Type w) [L.Structure M] [Countable M] :
    scottRank (L := L) M < (Ordinal.omega 1 : Ordinal.{0}) := by
  obtain ⟨α, hα_lt, hstab⟩ := exists_complete_stabilization (L := L) M
  unfold scottRank
  have h_limit : Order.IsSuccLimit (Ordinal.omega (1 : Ordinal.{0})) :=
    Cardinal.isSuccLimit_omega 1
  have h_bound : ∀ m : M, elementRank (L := L) m ≤ α :=
    fun m => elementRank_le_completeStab hstab m
  have h_bound' : ∀ m : M, elementRank (L := L) m + 1 ≤ α + 1 := by
    intro m
    have h := (Ordinal.add_le_add_iff_right 1).mpr (h_bound m)
    convert h using 2 <;> simp [Nat.cast_one]
  by_cases h_nonempty : Nonempty M
  · calc ⨆ m, elementRank (L := L) m + 1 ≤ α + 1 := ciSup_le h_bound'
      _ < Ordinal.omega 1 := h_limit.succ_lt hα_lt
  · haveI : IsEmpty M := not_nonempty_iff.mp h_nonempty
    have h_zero : (⨆ (m : M), elementRank (L := L) m + 1) = 0 := by
      rw [Ordinal.iSup_eq_zero_iff]
      intro m
      exact isEmptyElim m
    rw [h_zero]
    exact Ordinal.omega_pos 1

/-- Conditional variant of `scottRank_lt_omega1`. Sorry-free. -/
theorem scottRank_lt_omega1_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    (M : Type w) [L.Structure M] [Countable M] :
    scottRank (L := L) M < (Ordinal.omega 1 : Ordinal.{0}) := by
  obtain ⟨α, hα_lt, hstab⟩ := exists_complete_stabilization_of hcount M
  unfold scottRank
  have h_limit : Order.IsSuccLimit (Ordinal.omega (1 : Ordinal.{0})) :=
    Cardinal.isSuccLimit_omega 1
  have h_bound : ∀ m : M, elementRank (L := L) m ≤ α :=
    fun m => elementRank_le_completeStab hstab m
  have h_bound' : ∀ m : M, elementRank (L := L) m + 1 ≤ α + 1 := by
    intro m
    have h := (Ordinal.add_le_add_iff_right 1).mpr (h_bound m)
    convert h using 2 <;> simp [Nat.cast_one]
  by_cases h_nonempty : Nonempty M
  · calc ⨆ m, elementRank (L := L) m + 1 ≤ α + 1 := ciSup_le h_bound'
      _ < Ordinal.omega 1 := h_limit.succ_lt hα_lt
  · haveI : IsEmpty M := not_nonempty_iff.mp h_nonempty
    have h_zero : (⨆ (m : M), elementRank (L := L) m + 1) = 0 := by
      rw [Ordinal.iSup_eq_zero_iff]
      intro m
      exact isEmptyElim m
    rw [h_zero]
    exact Ordinal.omega_pos 1

/-- **Legacy (Code-based)**: When scottRank M ≤ α, the structure M stabilizes completely at α.

**Prefer**: `scottRank_le_implies_stabilizesCompletely_of` (conditional on
`CountableRefinementHypothesis`, decoupled from Code.lean sorry).

**Remaining gap** (in both versions): the β > α case requires showing that the complete
stabilization ordinal ≤ scottRank M. This is independent of the Code.lean sorry
(`agree_codes_implies_BFEquiv`). -/
theorem scottRank_le_implies_stabilizesCompletely (M : Type w) [L.Structure M] [Countable M]
    {α : Ordinal.{0}} (hα : scottRank (L := L) M ≤ α) :
    StabilizesCompletely (L := L) M α := by
  obtain ⟨β, _, hstab⟩ := exists_complete_stabilization (L := L) M
  intro n N _ _ a b
  constructor
  · intro hBFα
    by_cases hβα : β ≤ α
    · exact BFEquiv_upgrade_at_stabilization hstab (BFEquiv.monotone hβα hBFα) (Order.succ α)
        (le_trans hβα (Order.le_succ α))
    · -- β > α: mathematically impossible when scottRank M ≤ α (since the complete
      -- stabilization ordinal should be ≤ scottRank), but the formal relationship between
      -- scottRank (sup of elementRanks) and the complete stabilization ordinal from
      -- per_tuple_stabilization_below_omega1 hasn't been established yet.
      -- Inherits sorry from per_tuple_stabilization_below_omega1.
      sorry
  · exact BFEquiv.of_succ

/-- Conditional variant of `scottRank_le_implies_stabilizesCompletely`.

Uses `exists_complete_stabilization_of` (sorry-free conditional on
`CountableRefinementHypothesis`) instead of `exists_complete_stabilization`.
The β ≤ α case is identical to the original. The β > α case remains as a
separate mathematical gap (connecting per-tuple stabilization bounds with
elementRank-based scottRank), independent of the Code.lean sorry.

**Axiom status**: Depends on `CountableRefinementHypothesis` + the β ≤ scottRank M gap.
Neither dependency involves `agree_codes_implies_BFEquiv`. -/
theorem scottRank_le_implies_stabilizesCompletely_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    (M : Type w) [L.Structure M] [Countable M]
    {α : Ordinal.{0}} (hα : scottRank (L := L) M ≤ α) :
    StabilizesCompletely (L := L) M α := by
  obtain ⟨β, _, hstab⟩ := exists_complete_stabilization_of hcount M
  intro n N _ _ a b
  constructor
  · intro hBFα
    by_cases hβα : β ≤ α
    · exact BFEquiv_upgrade_at_stabilization hstab (BFEquiv.monotone hβα hBFα) (Order.succ α)
        (le_trans hβα (Order.le_succ α))
    · -- β > α: mathematically impossible when scottRank M ≤ α (since the complete
      -- stabilization ordinal should be ≤ scottRank), but connecting per-tuple
      -- stabilization bounds with the elementRank-based scottRank definition
      -- requires additional infrastructure (e.g., showing all refinement ordinals
      -- for n-tuples are bounded by element ranks).
      -- This gap is independent of `agree_codes_implies_BFEquiv`.
      sorry
  · exact BFEquiv.of_succ

/-- The stabilization ordinal is below ω₁.

This follows from `stabilizationOrdinal_lt_omega1'` in Sentence.lean, which is the
direct bound from `exists_stabilization`. -/
theorem stabilizationOrdinal_lt_omega1 (M : Type w) [L.Structure M] [Countable M] :
    stabilizationOrdinal (L := L) M < Ordinal.omega 1 :=
  stabilizationOrdinal_lt_omega1' M

end Language

end FirstOrder
