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
noncomputable def BFEquiv : Ordinal → ∀ {n : ℕ}, (Fin n → M) → (Fin n → N) → Prop :=
  Ordinal.limitRecOn
    -- Zero case: same atomic type
    (fun {n} a b => SameAtomicType a b)
    -- Successor case
    (fun α ih {n} a b =>
      ih a b ∧
      (∀ m : M, ∃ n' : N, ih (snoc a m) (snoc b n')) ∧
      (∀ n' : N, ∃ m : M, ih (snoc a m) (snoc b n')))
    -- Limit case
    (fun α ih {n} a b => ∀ β < α, ih β a b)

theorem BFEquiv.zero {n : ℕ} (a : Fin n → M) (b : Fin n → N) :
    BFEquiv 0 a b ↔ SameAtomicType a b := by
  simp only [BFEquiv, Ordinal.limitRecOn_zero]

theorem BFEquiv.zero_iff_sameAtomicType {n : ℕ} (a : Fin n → M) (b : Fin n → N) :
    BFEquiv 0 a b ↔ SameAtomicType a b :=
  BFEquiv.zero a b

theorem BFEquiv.succ {n : ℕ} (α : Ordinal) (a : Fin n → M) (b : Fin n → N) :
    BFEquiv (α + 1) a b ↔
      BFEquiv α a b ∧
      (∀ m : M, ∃ n' : N, BFEquiv α (snoc a m) (snoc b n')) ∧
      (∀ n' : N, ∃ m : M, BFEquiv α (snoc a m) (snoc b n')) := by
  simp only [BFEquiv, Ordinal.limitRecOn_succ]

theorem BFEquiv.limit {n : ℕ} (α : Ordinal) (hα : α.IsLimit) (a : Fin n → M) (b : Fin n → N) :
    BFEquiv α a b ↔ ∀ β < α, BFEquiv β a b := by
  conv_lhs => rw [BFEquiv, Ordinal.limitRecOn_limit _ _ _ hα]

/-- BF-equivalence at level α + 1 implies BF-equivalence at level α. -/
theorem BFEquiv.of_succ {n : ℕ} {α : Ordinal} {a : Fin n → M} {b : Fin n → N}
    (h : BFEquiv (α + 1) a b) : BFEquiv α a b :=
  ((BFEquiv.succ α a b).mp h).1

/-- BF-equivalence is monotone: higher ordinals imply lower ordinals. -/
theorem BFEquiv.monotone {n : ℕ} {α β : Ordinal} (hαβ : α ≤ β)
    {a : Fin n → M} {b : Fin n → N} (h : BFEquiv β a b) : BFEquiv α a b := by
  induction β using Ordinal.limitRecOn with
  | H0 =>
    simp only [Ordinal.le_zero] at hαβ
    rwa [hαβ]
  | Hs γ ih =>
    rcases hαβ.lt_or_eq with hαβ' | rfl
    · rw [Order.lt_succ_iff] at hαβ'
      exact ih hαβ' (BFEquiv.of_succ h)
    · exact h
  | Hl γ hγ ih =>
    rcases hαβ.lt_or_eq with hαβ' | rfl
    · exact ih hαβ' ((BFEquiv.limit γ hγ a b).mp h α hαβ')
    · exact h

/-- The "forth" property at a successor level. -/
theorem BFEquiv.forth {n : ℕ} {α : Ordinal} {a : Fin n → M} {b : Fin n → N}
    (h : BFEquiv (α + 1) a b) (m : M) :
    ∃ n' : N, BFEquiv α (snoc a m) (snoc b n') :=
  ((BFEquiv.succ α a b).mp h).2.1 m

/-- The "back" property at a successor level. -/
theorem BFEquiv.back {n : ℕ} {α : Ordinal} {a : Fin n → M} {b : Fin n → N}
    (h : BFEquiv (α + 1) a b) (n' : N) :
    ∃ m : M, BFEquiv α (snoc a m) (snoc b n') :=
  ((BFEquiv.succ α a b).mp h).2.2 n'

/-- BF-equivalence at level 0 is reflexive. -/
theorem BFEquiv.refl_zero {n : ℕ} (a : Fin n → M) : BFEquiv (0 : Ordinal) a a :=
  (BFEquiv.zero a a).mpr (SameAtomicType.refl a)

/-- BF-equivalence is symmetric at all levels. -/
theorem BFEquiv.symm {n : ℕ} {α : Ordinal} {a : Fin n → M} {b : Fin n → N}
    (h : BFEquiv α a b) : BFEquiv α b a := by
  induction α using Ordinal.limitRecOn with
  | H0 =>
    rw [BFEquiv.zero] at h ⊢
    exact h.symm
  | Hs β ih =>
    rw [BFEquiv.succ] at h ⊢
    exact ⟨ih h.1, fun n' => let ⟨m, hm⟩ := h.2.2 n'; ⟨m, ih hm⟩,
           fun m => let ⟨n', hn'⟩ := h.2.1 m; ⟨n', ih hn'⟩⟩
  | Hl β hβ ih =>
    rw [BFEquiv.limit β hβ] at h ⊢
    exact fun γ hγ => ih hγ (h γ hγ)

end Language

end FirstOrder
