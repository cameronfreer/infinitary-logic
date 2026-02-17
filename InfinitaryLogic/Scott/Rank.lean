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

/-- The stabilization ordinal is below ω₁.

This follows from `stabilizationOrdinal_lt_omega1'` in Sentence.lean, which is the
direct bound from `exists_stabilization`. -/
theorem stabilizationOrdinal_lt_omega1 (M : Type w) [L.Structure M] [Countable M] :
    stabilizationOrdinal (L := L) M < Ordinal.omega 1 :=
  stabilizationOrdinal_lt_omega1' M

/-- The stabilization ordinal is at most the Scott rank.

Note: This theorem involves comparing ordinals potentially in different universes
(stabilizationOrdinal is in Ordinal.{0}, scottRank is in Ordinal.{w}).
The comparison is well-defined when both ordinals are below ω₁.

**BLOCKED**: This theorem requires showing StabilizesAt M (scottRank M). This in turn
requires showing that BFEquiv0 at scottRank implies isomorphism, which has the same
issues as BFEquiv_omega_implies_equiv (coherent ω-level extensions).

The proof strategy would be:
1. Show StabilizesAt M (scottRank M)
2. Apply csInf_le' to get stabilizationOrdinal ≤ scottRank

Step 1 requires proving BFEquiv0 (scottRank) → isomorphism, which needs either:
- A working BFEquiv_omega_implies_equiv, or
- The strategy-based BFEquiv approach

See InfinitaryLogic/Scott/Sentence.lean "Important Limitation" section. -/
theorem stabilizationOrdinal_le_scottRank (M : Type w) [L.Structure M] [Countable M] :
    stabilizationOrdinal (L := L) M ≤ scottRank (L := L) M := by
  sorry

/-- The Scott sentence and Scott formula at Scott rank level are semantically equivalent.

Both scottSentence (at stabilizationOrdinal) and scottFormula at scottRank characterize
the same class of structures (those isomorphic to M), so they have the same realizations.

Note: This is semantic equivalence (same realizations), not syntactic equality. The two
formulas may differ syntactically when stabilizationOrdinal ≠ scottRank.

The proof uses:
1. `stabilizationOrdinal_le_scottRank` to show stab ≤ scottRank
2. `BFEquiv.monotone` to transfer between levels
3. `scottSentence_characterizes` for the characterization at stabilization level

**BLOCKED**: This theorem depends on `stabilizationOrdinal_le_scottRank` which requires
showing StabilizesAt at scottRank level. -/
theorem scottSentence_equiv_scottFormula_rank (M : Type w) [L.Structure M] [Countable M]
    (N : Type w) [L.Structure N] [Countable N] :
    (scottSentence (L := L) M).realize_as_sentence N ↔
    (scottFormula (L := L) (M := M) Fin.elim0 (scottRank (L := L) M)).Realize
      (Fin.elim0 : Fin 0 → N) := by
  -- Both characterize isomorphism with M
  rw [scottSentence_characterizes M N]
  -- Need to show: scottFormula at scottRank characterizes iso
  rw [realize_scottFormula_iff_BFEquiv _ _ _ (scottRank_lt_omega1 M)]
  -- BFEquiv at scottRank ↔ iso
  -- This requires showing StabilizesAt M (scottRank M), which needs stabilizationOrdinal_le_scottRank
  constructor
  · intro ⟨e⟩
    -- Isomorphism implies BFEquiv at all levels
    have h : (e : M → N) ∘ Fin.elim0 = Fin.elim0 := funext (fun i => i.elim0)
    rw [← h]
    exact equiv_implies_BFEquiv e (scottRank (L := L) M) 0 Fin.elim0
  · -- BFEquiv at scottRank implies iso
    -- This is the hard direction that requires stabilizationOrdinal_le_scottRank
    intro hBF
    -- scottRank ≥ stabilizationOrdinal, so BFEquiv at scottRank implies BFEquiv at stab
    have hle := stabilizationOrdinal_le_scottRank (L := L) M
    have hBF_stab := BFEquiv.monotone hle hBF
    exact (stabilizationOrdinal_spec M N).mp hBF_stab

end Language

end FirstOrder
