/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.FiberAssembly
import InfinitaryLogic.Scott.BlockBackAndForth

/-!
# Adding owner rows to a tuple

Every element of an assembled carrier has an **owner row**: a point `pt r τ x` is owned by
`row r`, and a row is its own owner (`owner`, `ownerRow`).

**Theorem** (`bfEquiv_append_ownerRows`): if `a ≡_{β + n} b` for `n`-tuples, then appending the
owner rows gives `a ++ ownerRow a ≡_β b ++ ownerRow b`.  One block move (`BFEquiv.forth_block`)
answers the whole owner tuple at once; the answer is then identified atomically at level `0`:
for a point coordinate the `own` atom forces the answer to be the owner of the matched point, and
for a row coordinate the equality atom (a row is its own owner) together with the `row` atom
forces it.

The cost `β + n` is sufficient, not claimed optimal.  The statement covers empty tuples, repeated
owners, and owners already present among the coordinates; the appended tuple is `n` rows long
regardless.
-/

namespace FirstOrder.Language

namespace FiberAssembly

universe u v w

variable {U : Type u} {Lc : Language.{v, w}} {R : Type u} {C : R → Label U → Type u}
  {S : Type u} {D : S → Label U → Type u} [∀ r τ, Lc.Structure (C r τ)]
  [∀ s τ, Lc.Structure (D s τ)]

/-- The owner row of an element: a point is owned by its row, a row by itself. -/
def owner : Carrier R C → R
  | .row r => r
  | .pt r _ _ => r

@[simp] theorem owner_row (r : R) : owner (Carrier.row r : Carrier R C) = r := rfl

@[simp] theorem owner_pt (r : R) (τ : Label U) (x : C r τ) :
    owner (Carrier.pt r τ x : Carrier R C) = r := rfl

/-- The owner rows of a tuple, coordinatewise. -/
def ownerRow {n : ℕ} (a : Fin n → Carrier R C) : Fin n → Carrier R C :=
  fun i => Carrier.row (owner (a i))

@[simp] theorem ownerRow_apply {n : ℕ} (a : Fin n → Carrier R C) (i : Fin n) :
    ownerRow a i = Carrier.row (owner (a i)) := rfl

/-- The owner tuple of a matched answer is determined atomically: the answer to the block move
for `ownerRow a` is `ownerRow b`. -/
private theorem eq_ownerRow_of_sameAtomicType {n : ℕ} {a : Fin n → Carrier R C}
    {b : Fin n → Carrier S D} {d : Fin n → Carrier S D}
    (h : SameAtomicType (L := lang U Lc) (Fin.append a (ownerRow a)) (Fin.append b d)) :
    d = ownerRow b := by
  funext i
  rcases ha : a i with ⟨r⟩ | ⟨r, τ, x⟩
  · -- a row coordinate: it equals its owner row, so the answer equals `b i`, which is a row
    have heq := h (AtomicIdx.eq (Fin.castAdd n i) (Fin.natAdd n i))
    simp only [AtomicIdx.holds, Fin.append_left, Fin.append_right, ownerRow_apply, ha,
      owner_row, true_iff] at heq
    have hrow := h (AtomicIdx.rel Sym.row ![Fin.castAdd n i])
    simp only [AtomicIdx.holds, relMap_row, Function.comp_apply, Matrix.cons_val_zero,
      Fin.append_left, ha] at hrow
    obtain ⟨r', hr'⟩ := hrow.mp ⟨r, rfl⟩
    rw [ownerRow_apply, ← heq, hr', owner_row]
  · -- a point coordinate: the `own` atom forces the answer to be the owner of `b i`
    have hown := h (AtomicIdx.rel Sym.own ![Fin.castAdd n i, Fin.natAdd n i])
    simp only [AtomicIdx.holds, relMap_own, Function.comp_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.append_left, Fin.append_right, ownerRow_apply, ha, owner_pt]
      at hown
    obtain ⟨r', τ', x', hb, hd⟩ := hown.mp ⟨r, τ, x, rfl, rfl⟩
    rw [ownerRow_apply, hb, owner_pt, hd]

/-- **Owner rows at finite cost.**  From `a ≡_{β + n} b`, appending the owner rows gives
`a ++ ownerRow a ≡_β b ++ ownerRow b`. -/
theorem bfEquiv_append_ownerRows {β : Ordinal} {n : ℕ} {a : Fin n → Carrier R C}
    {b : Fin n → Carrier S D} (h : BFEquiv (L := lang U Lc) (β + n) n a b) :
    BFEquiv (L := lang U Lc) β (n + n) (Fin.append a (ownerRow a))
      (Fin.append b (ownerRow b)) := by
  obtain ⟨d, hd⟩ := BFEquiv.forth_block (L := lang U Lc) n h (ownerRow a)
  have h0 := (BFEquiv.zero _ _).mp (BFEquiv.monotone _root_.zero_le hd)
  rw [← eq_ownerRow_of_sameAtomicType h0]
  exact hd

end FiberAssembly

end FirstOrder.Language
