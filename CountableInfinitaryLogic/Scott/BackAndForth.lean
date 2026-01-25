/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import CountableInfinitaryLogic.Scott.AtomicDiagram

/-!
# Back-and-Forth Equivalence

This file defines the back-and-forth equivalence relation between tuples in structures,
indexed by ordinals. This is the semantic predicate that corresponds to Scott formulas.

## Main Definitions

- `BFEquiv`: The α-back-and-forth equivalence between tuples, indexed by ordinal α.

## Main Results

- `BFEquiv.zero_iff_sameAtomicType`: At level 0, BF-equivalence is atomic type equivalence.
- `BFEquiv.monotone`: BF-equivalence at higher ordinals implies equivalence at lower ordinals.

## Implementation Notes

We use `Ordinal.limitRecOn` for the definition, which requires handling three cases:
- Zero: same atomic type
- Successor `Order.succ α`: equivalence at α plus forth and back conditions
- Limit (with `Order.IsSuccLimit`): equivalence at all smaller ordinals
-/

universe u v w w'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable {M : Type w} [L.Structure M]
variable {N : Type w'} [L.Structure N]

open FirstOrder Structure Fin Ordinal

/-- Back-and-forth equivalence at ordinal α between tuples a in M and b in N.

At level 0: same atomic type.
At successor α + 1: same atomic type, plus:
  - (forth) for every m in M, there exists n in N with BFEquiv α (snoc a m) (snoc b n)
  - (back) for every n in N, there exists m in M with BFEquiv α (snoc a m) (snoc b n)
At limit λ: BFEquiv β for all β < λ.
-/
noncomputable def BFEquiv (α : Ordinal) (n : ℕ) (a : Fin n → M) (b : Fin n → N) : Prop :=
  Ordinal.limitRecOn α
    -- Zero case: same atomic type
    (fun (k : ℕ) (a' : Fin k → M) (b' : Fin k → N) =>
      SameAtomicType (L := L) (M := M) (N := N) a' b')
    -- Successor case
    (fun _β ih (k : ℕ) (a' : Fin k → M) (b' : Fin k → N) =>
      ih k a' b' ∧
      (∀ m : M, ∃ n' : N, ih (k + 1) (snoc a' m) (snoc b' n')) ∧
      (∀ n' : N, ∃ m : M, ih (k + 1) (snoc a' m) (snoc b' n')))
    -- Limit case
    (fun _β _hβ ih (k : ℕ) (a' : Fin k → M) (b' : Fin k → N) =>
      ∀ γ (hγ : γ < _β), ih γ hγ k a' b')
    n a b

variable {n : ℕ}

theorem BFEquiv.zero (a : Fin n → M) (b : Fin n → N) :
    BFEquiv (L := L) 0 n a b ↔ SameAtomicType (L := L) (M := M) (N := N) a b := by
  simp only [BFEquiv, Ordinal.limitRecOn_zero]

theorem BFEquiv.zero_iff_sameAtomicType (a : Fin n → M) (b : Fin n → N) :
    BFEquiv (L := L) 0 n a b ↔ SameAtomicType (L := L) (M := M) (N := N) a b :=
  BFEquiv.zero a b

theorem BFEquiv.succ (α : Ordinal) (a : Fin n → M) (b : Fin n → N) :
    BFEquiv (L := L) (Order.succ α) n a b ↔
      BFEquiv (L := L) α n a b ∧
      (∀ m : M, ∃ n' : N, BFEquiv (L := L) α (n + 1) (snoc a m) (snoc b n')) ∧
      (∀ n' : N, ∃ m : M, BFEquiv (L := L) α (n + 1) (snoc a m) (snoc b n')) := by
  simp only [BFEquiv, Ordinal.limitRecOn_succ]

theorem BFEquiv.limit (α : Ordinal) (hα : Order.IsSuccLimit α) (a : Fin n → M) (b : Fin n → N) :
    BFEquiv (L := L) α n a b ↔ ∀ β (hβ : β < α), BFEquiv (L := L) β n a b := by
  unfold BFEquiv
  rw [Ordinal.limitRecOn_limit _ _ _ _ hα]

/-- BF-equivalence at level α + 1 implies BF-equivalence at level α. -/
theorem BFEquiv.of_succ {α : Ordinal} {a : Fin n → M} {b : Fin n → N}
    (h : BFEquiv (L := L) (Order.succ α) n a b) : BFEquiv (L := L) α n a b :=
  ((BFEquiv.succ α a b).mp h).1

/-- BF-equivalence is monotone: higher ordinals imply lower ordinals. -/
theorem BFEquiv.monotone {α β : Ordinal} (hαβ : α ≤ β)
    {a : Fin n → M} {b : Fin n → N} (h : BFEquiv (L := L) β n a b) :
    BFEquiv (L := L) α n a b := by
  induction β using Ordinal.limitRecOn generalizing n a b with
  | zero =>
    simp only [nonpos_iff_eq_zero] at hαβ
    rwa [hαβ]
  | succ γ ih =>
    rcases hαβ.lt_or_eq with hαβ' | rfl
    · rw [Order.lt_succ_iff] at hαβ'
      exact ih hαβ' (BFEquiv.of_succ h)
    · exact h
  | limit γ hγ _ih =>
    rcases hαβ.lt_or_eq with hαβ' | rfl
    · exact (BFEquiv.limit γ hγ a b).mp h α hαβ'
    · exact h

/-- The "forth" property at a successor level. -/
theorem BFEquiv.forth {α : Ordinal} {a : Fin n → M} {b : Fin n → N}
    (h : BFEquiv (L := L) (Order.succ α) n a b) (m : M) :
    ∃ n' : N, BFEquiv (L := L) α (n + 1) (snoc a m) (snoc b n') :=
  ((BFEquiv.succ α a b).mp h).2.1 m

/-- The "back" property at a successor level. -/
theorem BFEquiv.back {α : Ordinal} {a : Fin n → M} {b : Fin n → N}
    (h : BFEquiv (L := L) (Order.succ α) n a b) (n' : N) :
    ∃ m : M, BFEquiv (L := L) α (n + 1) (snoc a m) (snoc b n') :=
  ((BFEquiv.succ α a b).mp h).2.2 n'

/-- BF-equivalence at level 0 is reflexive. -/
theorem BFEquiv.refl_zero (a : Fin n → M) :
    BFEquiv (L := L) (M := M) (N := M) (0 : Ordinal) n a a :=
  (BFEquiv.zero a a).mpr (SameAtomicType.refl a)

/-- BF-equivalence is symmetric at all levels. -/
theorem BFEquiv.symm {α : Ordinal} {a : Fin n → M} {b : Fin n → N}
    (h : BFEquiv (L := L) α n a b) : BFEquiv (L := L) (M := N) (N := M) α n b a := by
  induction α using Ordinal.limitRecOn generalizing n a b with
  | zero =>
    rw [BFEquiv.zero] at h ⊢
    exact h.symm
  | succ β ih =>
    rw [BFEquiv.succ] at h ⊢
    exact ⟨ih h.1, fun n' => let ⟨m, hm⟩ := h.2.2 n'; ⟨m, ih hm⟩,
           fun m => let ⟨n', hn'⟩ := h.2.1 m; ⟨n', ih hn'⟩⟩
  | limit β hβ ih =>
    rw [BFEquiv.limit β hβ] at h ⊢
    exact fun γ hγ => ih γ hγ (h γ hγ)

end Language

end FirstOrder
