/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Nat.BitIndices
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Finite.Basic

/-!
# Ackermann coding: hereditarily finite sets as naturals (issue #19A, step 4)

The concrete carrier for the HF admissible presentation.  `a ∈ₐ b` means bit `a` of `b` is set, so
**every natural is a finite set of naturals** and the coding is total in both directions.

## Why this file exists

The `WithKP` sketch in the #19A spike stated only that `Pair` and `Union` relations are *total*:

```lean
  pair_total : ∀ a b, ∃ c, Pair a b c
```

That is satisfied by `Pair := fun _ _ _ => True` on any inhabited carrier — **totality is not
pairing**.  A closure obligation is meaningful only against an ambient membership relation together
with specification laws saying *which* element the operation produces.  This file supplies that
membership for HF and proves the specifications hold.

Only pairing and union are built here.  The full KP schema is deliberately **not** attempted: the
#19A source audit must first identify which closure and absoluteness laws later proofs consume.
See `docs/admissible-19a-checkpoint.md` §6(c).

## Main definitions

- `Nat.AckMem` (`∈ₐ`): Ackermann membership.
- `Nat.ackPair`, `Nat.ackUnion`: the witnessing constructions.

## Main results

- `Nat.mem_ackPair`, `Nat.mem_ackUnion`: the specification laws — the content the bare totality
  fields lacked.
- `Nat.ack_ext`: the coding is extensional.
- `Nat.finite_ackMem` / `Nat.exists_ack_of_finite`: codes name exactly the finite sets of naturals.
  This is what will make `A`-finiteness coincide with ordinary finiteness at HF.
-/

namespace Nat

/-- **Ackermann membership**: `a ∈ₐ b` iff bit `a` of `b` is set. -/
def AckMem (a b : ℕ) : Prop := b.testBit a = true

@[inherit_doc] scoped infix:50 " ∈ₐ " => Nat.AckMem

theorem ackMem_def {a b : ℕ} : a ∈ₐ b ↔ b.testBit a = true := Iff.rfl

theorem ackMem_iff_mem_bitIndices {a b : ℕ} : a ∈ₐ b ↔ a ∈ b.bitIndices :=
  mem_bitIndices.symm

instance : Decidable (AckMem a b) := inferInstanceAs (Decidable (_ = true))

/-- Codes with the same members are equal — Ackermann coding is extensional. -/
theorem ack_ext {a b : ℕ} (h : ∀ x, x ∈ₐ a ↔ x ∈ₐ b) : a = b :=
  Nat.eq_of_testBit_eq fun i => Bool.eq_iff_iff.mpr (h i)

/-! ## Pairing -/

/-- The Ackermann code of the pair `{a, b}`. -/
def ackPair (a b : ℕ) : ℕ := 2 ^ a ||| 2 ^ b

/-- **The pairing specification.**  This is the law the bare `pair_total` field lacked. -/
@[simp] theorem mem_ackPair {a b x : ℕ} : x ∈ₐ ackPair a b ↔ x = a ∨ x = b := by
  simp only [AckMem, ackPair, testBit_or, Bool.or_eq_true, testBit_two_pow, decide_eq_true_eq]
  exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩

/-! ## Union -/

/-- The Ackermann code of `⋃ a`: bitwise-or of the members of `a`. -/
def ackUnion (a : ℕ) : ℕ := a.bitIndices.foldr (· ||| ·) 0

/-- **The union specification.** -/
@[simp] theorem mem_ackUnion {a x : ℕ} : x ∈ₐ ackUnion a ↔ ∃ y, y ∈ₐ a ∧ x ∈ₐ y := by
  have key : ∀ L : List ℕ, (x ∈ₐ L.foldr (· ||| ·) 0) ↔ ∃ y ∈ L, x ∈ₐ y := by
    intro L
    induction L with
    | nil => simp [AckMem]
    | cons y ys ih =>
      simp only [AckMem] at ih ⊢
      simp only [List.foldr_cons, testBit_or, Bool.or_eq_true, ih, List.mem_cons]
      constructor
      · rintro (h | ⟨z, hz, hx⟩)
        · exact ⟨y, Or.inl rfl, h⟩
        · exact ⟨z, Or.inr hz, hx⟩
      · rintro ⟨z, rfl | hz, hx⟩
        · exact Or.inl hx
        · exact Or.inr ⟨z, hz, hx⟩
  rw [ackUnion, key]
  simp only [← ackMem_iff_mem_bitIndices]

/-! ## Finiteness — why `A`-finite will collapse to finite at HF -/

/-- Every Ackermann code names a **finite** set. -/
theorem finite_ackMem (a : ℕ) : {x | x ∈ₐ a}.Finite := by
  classical
  have heq : {x | x ∈ₐ a} = ↑a.bitIndices.toFinset := by
    ext x; simp [ackMem_iff_mem_bitIndices]
  rw [heq]
  exact a.bitIndices.toFinset.finite_toSet

/-- …and conversely every finite set of naturals is named by a code. -/
theorem exists_ack_of_finite {s : Set ℕ} (hs : s.Finite) :
    ∃ a : ℕ, ∀ x, x ∈ₐ a ↔ x ∈ s := by
  classical
  obtain ⟨s, rfl⟩ := hs.exists_finset_coe
  refine ⟨((Finset.sort s).map fun i => 2 ^ i).sum, fun x => ?_⟩
  have hsorted : (Finset.sort s).SortedLT := Finset.sortedLT_sort s
  rw [ackMem_iff_mem_bitIndices, bitIndices_sum_map_two_pow hsorted]
  simp

end Nat
