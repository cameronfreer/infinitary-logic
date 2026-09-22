/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.FiberCompanion

/-!
# The Hilbert-hotel row bijection of a companion

For an allowed path `π` and a threshold `N`, `shiftRows hπ N : Row A ⊕ Unit ≃ Row A` sends the
path row to the prefix `π|ₙ`, each **tail prefix** `π|ₖ` with `k ≥ N` to `π|ₖ₊₁`, and every other
row to itself.  Its inverse sends `π|ₙ` back to the path row, `π|ₖ₊₁` (`k ≥ N`) to `π|ₖ`, and fixes
the rest.  The case `N = 0` shifts every prefix and sends the path row to the empty row.

This layer has no component language or structure parameters: it is a bijection of rows, well
defined because prefixes of different lengths are different rows (`prefixRow_injective`).  The
tail-prefix predicate has the finite characterization `isTailPrefix_iff`: a row is a tail prefix
iff its length is at least `N` and it is the prefix of its own length; no search over an unknown
length is needed.  The construction is noncomputable (classical decisions); no effectiveness is
claimed.
-/

namespace FirstOrder.Language

namespace FiberAssembly

universe u

variable {U : Type u} [LinearOrder U] {A : ℕ → Set U} {π : ℕ → U}

/-! ### Tail prefixes -/

/-- A row is a **tail prefix** of `π` at threshold `N`: some `π|ₖ` with `k ≥ N`. -/
def IsTailPrefix (hπ : IsAllowedPath A π) (N : ℕ) (r : Row A) : Prop :=
  ∃ k, N ≤ k ∧ r = prefixRow hπ k

/-- The finite characterization: a tail prefix is the prefix of its own length, which is at
least `N`. -/
theorem isTailPrefix_iff (hπ : IsAllowedPath A π) (N : ℕ) (r : Row A) :
    IsTailPrefix hπ N r ↔ N ≤ r.1.length ∧ r = prefixRow hπ r.1.length := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    simp [hk]
  · rintro ⟨hk, h⟩
    exact ⟨r.1.length, hk, h⟩

theorem isTailPrefix_prefixRow (hπ : IsAllowedPath A π) {N k : ℕ} (hk : N ≤ k) :
    IsTailPrefix hπ N (prefixRow hπ k) :=
  ⟨k, hk, rfl⟩

theorem not_isTailPrefix_of_length_lt (hπ : IsAllowedPath A π) {N : ℕ} {r : Row A}
    (h : r.1.length < N) : ¬ IsTailPrefix hπ N r := by
  rintro ⟨k, hk, rfl⟩
  simp only [prefixRow_val, pathPrefix_length] at h
  omega

/-- The length of a tail prefix is at least `N`. -/
theorem IsTailPrefix.length_ge {hπ : IsAllowedPath A π} {N : ℕ} {r : Row A}
    (h : IsTailPrefix hπ N r) : N ≤ r.1.length :=
  ((isTailPrefix_iff hπ N r).mp h).1

/-- A tail prefix is the prefix of its own length. -/
theorem IsTailPrefix.eq_prefixRow {hπ : IsAllowedPath A π} {N : ℕ} {r : Row A}
    (h : IsTailPrefix hπ N r) : r = prefixRow hπ r.1.length :=
  ((isTailPrefix_iff hπ N r).mp h).2

/-! ### The bijection -/

open Classical in
/-- **The Hilbert-hotel row bijection** at threshold `N`: the path row goes to `π|ₙ`, each tail
prefix `π|ₖ` (`k ≥ N`) to `π|ₖ₊₁`, every other row to itself. -/
noncomputable def shiftRows (hπ : IsAllowedPath A π) (N : ℕ) : (Row A ⊕ Unit) ≃ Row A where
  toFun
    | Sum.inr _ => prefixRow hπ N
    | Sum.inl r => if IsTailPrefix hπ N r then prefixRow hπ (r.1.length + 1) else r
  invFun r :=
    if r = prefixRow hπ N then Sum.inr ()
    else if IsTailPrefix hπ N r then Sum.inl (prefixRow hπ (r.1.length - 1)) else Sum.inl r
  left_inv := by
    rintro (r | _)
    · by_cases ht : IsTailPrefix hπ N r
      · obtain ⟨k, hk, rfl⟩ := ht
        have hne : prefixRow hπ (k + 1) ≠ prefixRow hπ N := fun h => by
          have := prefixRow_injective hπ h
          omega
        have htail : IsTailPrefix hπ N (prefixRow hπ (k + 1)) :=
          isTailPrefix_prefixRow hπ (by omega)
        simp only [isTailPrefix_prefixRow hπ hk, ite_true, prefixRow_val, pathPrefix_length,
          hne, ite_false, htail, Nat.add_sub_cancel]
      · have hne : r ≠ prefixRow hπ N := fun h => ht (h ▸ isTailPrefix_prefixRow hπ le_rfl)
        simp only [ht, ite_false, hne]
    · simp
  right_inv := by
    intro r
    by_cases hN : r = prefixRow hπ N
    · simp only [hN, ite_true]
    · by_cases ht : IsTailPrefix hπ N r
      · obtain ⟨k, hk, rfl⟩ := ht
        have hkN : N < k := lt_of_le_of_ne hk fun h => hN (by rw [h])
        have htail : IsTailPrefix hπ N (prefixRow hπ (k - 1)) :=
          isTailPrefix_prefixRow hπ (by omega)
        simp only [hN, ite_false, isTailPrefix_prefixRow hπ hk, ite_true, prefixRow_val,
          pathPrefix_length, htail, Nat.sub_add_cancel (Nat.one_le_of_lt hkN)]
      · simp only [hN, ite_false, ht]

/-! ### Forward equations -/

@[simp] theorem shiftRows_inr (hπ : IsAllowedPath A π) (N : ℕ) :
    shiftRows hπ N (Sum.inr ()) = prefixRow hπ N := rfl

theorem shiftRows_inl_prefixRow (hπ : IsAllowedPath A π) {N k : ℕ} (hk : N ≤ k) :
    shiftRows hπ N (Sum.inl (prefixRow hπ k)) = prefixRow hπ (k + 1) := by
  classical
  show (if IsTailPrefix hπ N (prefixRow hπ k) then _ else _) = _
  simp [isTailPrefix_prefixRow hπ hk]

theorem shiftRows_inl_of_not (hπ : IsAllowedPath A π) {N : ℕ} {r : Row A}
    (h : ¬ IsTailPrefix hπ N r) : shiftRows hπ N (Sum.inl r) = r := by
  classical
  show (if IsTailPrefix hπ N r then _ else _) = _
  simp [h]

/-! ### Inverse equations -/

@[simp] theorem shiftRows_symm_prefixRow (hπ : IsAllowedPath A π) (N : ℕ) :
    (shiftRows hπ N).symm (prefixRow hπ N) = Sum.inr () := by
  classical
  show (if prefixRow hπ N = prefixRow hπ N then _ else _) = _
  simp

theorem shiftRows_symm_prefixRow_succ (hπ : IsAllowedPath A π) {N k : ℕ} (hk : N ≤ k) :
    (shiftRows hπ N).symm (prefixRow hπ (k + 1)) = Sum.inl (prefixRow hπ k) := by
  classical
  have hne : prefixRow hπ (k + 1) ≠ prefixRow hπ N := fun h => by
    have := prefixRow_injective hπ h
    omega
  show (if prefixRow hπ (k + 1) = prefixRow hπ N then _
    else if IsTailPrefix hπ N (prefixRow hπ (k + 1)) then _ else _) = _
  simp [hne, isTailPrefix_prefixRow hπ (Nat.le_succ_of_le hk)]

theorem shiftRows_symm_of_not (hπ : IsAllowedPath A π) {N : ℕ} {r : Row A}
    (h : ¬ IsTailPrefix hπ N r) : (shiftRows hπ N).symm r = Sum.inl r := by
  classical
  have hne : r ≠ prefixRow hπ N := fun h' => h (h' ▸ isTailPrefix_prefixRow hπ le_rfl)
  show (if r = prefixRow hπ N then _ else if IsTailPrefix hπ N r then _ else _) = _
  simp [hne, h]

end FiberAssembly

end FirstOrder.Language
