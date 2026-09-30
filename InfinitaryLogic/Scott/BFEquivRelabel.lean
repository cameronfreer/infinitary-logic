/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Scott.BackAndForth

/-!
# Relabeling back-and-forth equivalent tuples

`BFEquiv.relabel`: back-and-forth equivalence at any level is preserved under relabeling the
index set by an arbitrary map `σ : Fin m → Fin n` (sub-tuples, repetitions, permutations), the
back-and-forth analogue of `SameAtomicType.relabel`.  The successor step extends `σ` to the new
last coordinate (a private helper).

`BFEquiv.comp_iff_of_surjective`: along a surjective `σ` the relabeling also reflects
back-and-forth equivalence, by relabeling back along a right inverse of `σ`.  Along a map that
forgets a coordinate it does not: `(0, 1)` and `(1, 2)` in `ℕ` with the equivalence relation
whose classes are `{2k, 2k + 1}` are not equivalent even at level `0`, while their first
coordinates `(0)` and `(1)` are equivalent at every level.
-/

/-- Extending a relabeling to a new last coordinate. -/
private theorem Fin.snoc_comp_lastCases {α : Type*} {m n : ℕ} (a : Fin n → α) (x : α)
    (σ : Fin m → Fin n) :
    (Fin.snoc a x : Fin (n + 1) → α) ∘
      (Fin.lastCases (Fin.last n) (fun j => Fin.castSucc (σ j)) : Fin (m + 1) → Fin (n + 1)) =
      Fin.snoc (a ∘ σ) x := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp

namespace FirstOrder.Language

variable {L : Language.{u, v}} {M : Type w} [L.Structure M] {N : Type w'} [L.Structure N]

/-- **Relabeling**: `BFEquiv` at every level is preserved by an arbitrary relabeling of the
index set. -/
theorem BFEquiv.relabel (α : Ordinal) :
    ∀ {n m : ℕ} {a : Fin n → M} {b : Fin n → N}, BFEquiv (L := L) α n a b →
      ∀ σ : Fin m → Fin n, BFEquiv (L := L) α m (a ∘ σ) (b ∘ σ) := by
  induction α using Ordinal.limitRecOn with
  | zero =>
    intro n m a b h σ
    exact (BFEquiv.zero _ _).mpr (((BFEquiv.zero _ _).mp h).relabel σ)
  | add_one β ih =>
    intro n m a b h σ
    rw [← Order.succ_eq_add_one, BFEquiv.succ] at h ⊢
    obtain ⟨h0, hf, hb⟩ := h
    refine ⟨ih h0 σ, fun x => ?_, fun y => ?_⟩
    · obtain ⟨y, hy⟩ := hf x
      refine ⟨y, ?_⟩
      have := ih hy (Fin.lastCases (Fin.last n) (fun j => Fin.castSucc (σ j)))
      rwa [Fin.snoc_comp_lastCases, Fin.snoc_comp_lastCases] at this
    · obtain ⟨x, hx⟩ := hb y
      refine ⟨x, ?_⟩
      have := ih hx (Fin.lastCases (Fin.last n) (fun j => Fin.castSucc (σ j)))
      rwa [Fin.snoc_comp_lastCases, Fin.snoc_comp_lastCases] at this
  | limit β hβ ih =>
    intro n m a b h σ
    rw [BFEquiv.limit β hβ] at h ⊢
    exact fun γ hγ => ih γ hγ (h γ hγ) σ

/-- **Reflection along a surjection**: for a surjective `σ : Fin m → Fin n`, the relabeled tuples
`a ∘ σ` and `b ∘ σ` are back-and-forth equivalent at level `α` iff `a` and `b` are.  The
reverse direction is `BFEquiv.relabel`; the forward direction relabels along a right inverse of
`σ`.  Surjectivity cannot be dropped (see the module docstring). -/
theorem BFEquiv.comp_iff_of_surjective {α : Ordinal} {n m : ℕ} {σ : Fin m → Fin n}
    (hσ : Function.Surjective σ) {a : Fin n → M} {b : Fin n → N} :
    BFEquiv (L := L) α m (a ∘ σ) (b ∘ σ) ↔ BFEquiv (L := L) α n a b := by
  refine ⟨fun h ↦ ?_, fun h ↦ BFEquiv.relabel α h σ⟩
  have := BFEquiv.relabel α h (Function.surjInv hσ)
  rwa [Function.comp_assoc, Function.comp_assoc, (Function.rightInverse_surjInv hσ).comp_eq_id,
    Function.comp_id, Function.comp_id] at this

end FirstOrder.Language
