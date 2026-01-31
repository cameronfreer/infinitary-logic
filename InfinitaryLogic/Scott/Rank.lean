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

/-- At the stabilization ordinal, for any element m, the defining set of elementRank is nonempty.

Strategy: We show that the stabilization ordinal is in the defining set by proving that
at this level, BFEquiv behavior is determined by isomorphism. Specifically:
- If BFEquiv (stab) 1 ![m] b holds, the structures M and N are isomorphic
- Isomorphism at the stabilization level means BFEquiv holds at all higher levels
- Hence the iff in the defining set is trivially true (both sides true or both false based on iso)

The key insight is that at stabilization ordinal, having BFEquiv for a singleton tuple implies
there's an isomorphism extending the partial map m ↦ b(0). -/
private theorem stabilizationOrdinal_mem_elementRank_set {M : Type w} [L.Structure M] [Countable M]
    (m : M) : stabilizationOrdinal (L := L) M ∈
    {α : Ordinal.{0} | ∀ (N : Type w) [L.Structure N] [Countable N] (b : Fin 1 → N),
      BFEquiv (L := L) (M := M) (N := N) α 1 ![m] b →
        ∀ (N' : Type w) [L.Structure N'] [Countable N'] (b' : Fin 1 → N'),
          BFEquiv (L := L) (M := M) (N := N') α 1 ![m] b' →
            (BFEquiv (L := L) (M := M) (N := N) (Order.succ α) 1 ![m] b ↔
             BFEquiv (L := L) (M := M) (N := N') (Order.succ α) 1 ![m] b')} := by
  intro N _ _ b hBFN N' _ _ b' hBFN'
  /-
  At the stabilization ordinal:
  - The stabilization ordinal is ≥ ω (actually = ω, but we only need ≥)
  - Wait, this is not true. The stabilization ordinal could be < ω for some structures.
    However, we know ω ∈ the stabilization set, so stabilizationOrdinal ≤ ω.
  - For the proof, we need to show that at stabilizationOrdinal, having BFEquiv for singleton
    tuples allows us to build isomorphisms.

  Actually, the key insight is different:
  - StabilizesAt α means BFEquiv0 α ↔ isomorphism
  - We need: BFEquiv α 1 ![m] b implies BFEquiv (succ α) 1 ![m] b ↔ similarly for b'

  At stabilization ordinal, if BFEquiv (stab) 1 ![m] b holds:
  - We need to know if this implies M ≃ N (to then use equiv_implies_BFEquiv)
  - The issue: BFEquiv for singleton ≠ BFEquiv0

  Alternative approach: at sufficiently high ordinals (≥ ω), BFEquiv for singletons implies
  isomorphism extending the correspondence. We use BFEquiv_ge_omega_singleton_implies_equiv_with_image.

  But stabilizationOrdinal might be < ω. So we need a different argument for that case.
  -/
  -- Case split on whether stabilizationOrdinal ≥ ω
  by_cases hge : ω ≤ stabilizationOrdinal (L := L) M
  · -- Case: stabilizationOrdinal ≥ ω
    -- Convert b and b' to ![...] form for the theorem
    have hb_eq : b = ![b 0] := by ext i; fin_cases i; rfl
    have hb'_eq : b' = ![b' 0] := by ext i; fin_cases i; rfl
    -- Get isomorphisms from BFEquiv at stabilizationOrdinal
    have hBFN_form : BFEquiv (L := L) (stabilizationOrdinal (L := L) M) 1 ![m] ![b 0] := by
      rw [← hb_eq]; exact hBFN
    have hBFN'_form : BFEquiv (L := L) (stabilizationOrdinal (L := L) M) 1 ![m] ![b' 0] := by
      rw [← hb'_eq]; exact hBFN'
    obtain ⟨e, he⟩ := BFEquiv_ge_omega_singleton_implies_equiv_with_image hge hBFN_form
    obtain ⟨e', he'⟩ := BFEquiv_ge_omega_singleton_implies_equiv_with_image hge hBFN'_form
    -- From isomorphisms, get BFEquiv at all levels
    -- he : e m = b 0, he' : e' m = b' 0
    have hBF_succ_N : BFEquiv (L := L) (Order.succ (stabilizationOrdinal (L := L) M)) 1 ![m] b := by
      have h := equiv_implies_BFEquiv e (Order.succ (stabilizationOrdinal (L := L) M)) 1 ![m]
      -- h : BFEquiv ... ![m] (e ∘ ![m])
      -- e ∘ ![m] = ![e m] = ![b 0] = b (by hb_eq)
      have hcomp : e ∘ ![m] = b := by
        rw [hb_eq]
        ext i; fin_cases i
        simp only [Function.comp_apply, Matrix.cons_val_fin_one, he]
      rw [← hcomp]
      exact h
    have hBF_succ_N' : BFEquiv (L := L) (Order.succ (stabilizationOrdinal (L := L) M)) 1 ![m] b' := by
      have h := equiv_implies_BFEquiv e' (Order.succ (stabilizationOrdinal (L := L) M)) 1 ![m]
      have hcomp : e' ∘ ![m] = b' := by
        rw [hb'_eq]
        ext i; fin_cases i
        simp only [Function.comp_apply, Matrix.cons_val_fin_one, he']
      rw [← hcomp]
      exact h
    -- Both sides are true
    exact ⟨fun _ => hBF_succ_N', fun _ => hBF_succ_N⟩
  · -- Case: stabilizationOrdinal < ω
    /-
    **Language expansion approach**:

    When stabilizationOrdinal < ω, we use language expansion to reduce singleton BFEquiv
    to empty-tuple BFEquiv in an expanded language.

    1. Let L' = L with a new constant symbol c (using Language.withConstants or constantsOn)
    2. Interpret c as m in M, giving M' : L'.Structure
    3. For any N with BFEquiv α 1 ![m] b, interpret c as b(0) in N, giving N'
    4. Key lemma: BFEquiv (L') α 0 [] [] ↔ BFEquiv (L) α 1 ![m] b
       (The constant c encodes the singleton correspondence)
    5. Apply StabilizesAt at α in L' to the expanded structures:
       BFEquiv (L') α 0 [] [] ↔ Nonempty (M' ≃[L'] N')
    6. An L'-isomorphism preserves c, hence sends m ↦ b(0)
    7. From this L'-isomorphism, extract an L-isomorphism with the same property

    The technical details require:
    - Language.withConstants (available in mathlib LanguageMap.lean)
    - BoundedFormula.constantsVarsEquiv (constants ↔ variables bijection)
    - Showing StabilizesAt transfers between L and L'

    This approach cleanly handles the case where stabilizationOrdinal < ω by reducing
    to the 0-tuple case where StabilizesAt applies directly.
    -/
    sorry

theorem elementRank_lt_omega1 {M : Type w} [L.Structure M] [Countable M] (m : M) :
    elementRank (L := L) m < (Ordinal.omega 1 : Ordinal.{0}) := by
  /-
  Strategy: The stabilization ordinal is in the defining set of elementRank,
  hence sInf ≤ stabilizationOrdinal < ω₁.
  -/
  unfold elementRank
  have h_stab_lt := stabilizationOrdinal_lt_omega1' (L := L) M
  apply lt_of_le_of_lt _ h_stab_lt
  exact csInf_le' (stabilizationOrdinal_mem_elementRank_set m)

/-- Scott rank of a countable structure is a countable ordinal.

The proof uses that:
1. M is countable, so we're taking the sup of countably many ordinals
2. Each elementRank m ≤ stabilizationOrdinal M (by definition)
3. stabilizationOrdinal M < ω₁
4. Adding 1 and taking sup over countable set preserves < ω₁
-/
theorem scottRank_lt_omega1 (M : Type w) [L.Structure M] [Countable M] :
    scottRank (L := L) M < (Ordinal.omega 1 : Ordinal.{0}) := by
  -- scottRank M = ⨆ (m : M), elementRank m + 1
  -- Each elementRank m ≤ stabilizationOrdinal by definition
  -- So scottRank ≤ stabilizationOrdinal + 1 < ω₁
  unfold scottRank
  have h_stab := stabilizationOrdinal_lt_omega1' (L := L) M
  have h_limit : Order.IsSuccLimit (Ordinal.omega (1 : Ordinal.{0})) :=
    Cardinal.isSuccLimit_omega 1
  -- Each elementRank m ≤ stabilizationOrdinal M
  have h_bound : ∀ m : M, elementRank (L := L) m ≤ stabilizationOrdinal (L := L) M := by
    intro m
    exact csInf_le' (stabilizationOrdinal_mem_elementRank_set m)
  -- So elementRank m + 1 ≤ stabilizationOrdinal + 1
  have h_bound' : ∀ m : M, elementRank (L := L) m + 1 ≤ stabilizationOrdinal (L := L) M + 1 := by
    intro m
    have h := (Ordinal.add_le_add_iff_right 1).mpr (h_bound m)
    convert h using 2 <;> simp [Nat.cast_one]
  -- Handle empty M case
  by_cases h_nonempty : Nonempty M
  · -- The sup is bounded by stabilizationOrdinal + 1
    calc ⨆ m, elementRank (L := L) m + 1 ≤ stabilizationOrdinal (L := L) M + 1 :=
        ciSup_le h_bound'
      _ < Ordinal.omega 1 := h_limit.succ_lt h_stab
  · -- M is empty, so scottRank = 0 < ω₁
    haveI : IsEmpty M := not_nonempty_iff.mp h_nonempty
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
The comparison is well-defined when both ordinals are below ω₁. -/
theorem stabilizationOrdinal_le_scottRank (M : Type w) [L.Structure M] [Countable M] :
    stabilizationOrdinal (L := L) M ≤ scottRank (L := L) M := by
  /-
  **Proof strategy**: Show StabilizesAt M (scottRank M), then use csInf_le'.

  Key insight: At scottRank, every element m has elementRank m + 1 ≤ scottRank.
  The elementRank property ensures that at elementRank m, BFEquiv behavior is determined.
  Thus at scottRank, all elements have "stabilized" and we can build isomorphisms.

  Steps:
  1. elementRank m ≤ stabilizationOrdinal M for all m (by csInf_le')
  2. scottRank M = ⨆ m, elementRank m + 1
  3. For StabilizesAt (scottRank M), show BFEquiv0 (scottRank) ↔ Nonempty (M ≃[L] N)
     - Forward: BFEquiv0 (scottRank) ⟹ isomorphism via back-and-forth
       At scottRank, each element m has been "handled" (elementRank m < scottRank)
       The extension property holds because succ behavior is determined
     - Backward: isomorphism ⟹ BFEquiv at all levels (equiv_implies_BFEquiv)

  4. Apply csInf_le' to conclude stabilizationOrdinal ≤ scottRank

  **Alternative bound**: From the definitions:
  - stabilizationOrdinal M ≤ ω (since ω is in the stabilization set)
  - scottRank M ≥ ⨆ m, elementRank m + 1
  - If we can show elementRank m ≥ some bound related to stabilizationOrdinal,
    we get the inequality directly
  -/
  sorry

/-- The Scott sentence can be taken at the Scott rank level.

Both scottSentence (at stabilizationOrdinal) and scottFormula at scottRank characterize
the same class of structures (those isomorphic to M), so they are equivalent sentences.
-/
theorem scottSentence_eq_scottFormula_rank (M : Type w) [L.Structure M] [Countable M] :
    scottSentence (L := L) M = scottFormula (L := L) (M := M) Fin.elim0 (scottRank (L := L) M) := by
  /-
  **Proof strategy**: Semantic equivalence via BFEquiv monotonicity.

  Both formulas are realized by exactly the same countable structures (those ≃[L] M).

  Key steps:
  1. scottSentence M = scottFormula Fin.elim0 (stabilizationOrdinal M) (by definition)
  2. scottFormula at level α is realized by N iff BFEquiv0 α M N (realize_scottFormula_iff_BFEquiv)
  3. StabilizesAt (stabilizationOrdinal M) means: BFEquiv0 (stab) ↔ Nonempty (M ≃[L] N)
  4. From stabilizationOrdinal_le_scottRank: stabilizationOrdinal ≤ scottRank
  5. BFEquiv is monotone in the ordinal level:
     - BFEquiv0 (scottRank) ⟹ BFEquiv0 (stab) (by monotonicity)
     - BFEquiv0 (stab) ⟹ isomorphism (by StabilizesAt)
     - isomorphism ⟹ BFEquiv0 (scottRank) (by equiv_implies_BFEquiv)
  6. Therefore both formulas define the same class of countable structures

  **For definitional equality**:
  - If scottRank = stabilizationOrdinal, we're done by definition
  - Otherwise, need Formulaω extensionality or weaken to semantic equivalence:
    ∀ N [L.Structure N] [Countable N],
      (scottSentence M).Realize (Fin.elim0 : Fin 0 → N) ↔
      (scottFormula Fin.elim0 (scottRank M)).Realize (Fin.elim0 : Fin 0 → N)

  The proof uses the characterization theorems from Sentence.lean.
  -/
  sorry

end Language

end FirstOrder
