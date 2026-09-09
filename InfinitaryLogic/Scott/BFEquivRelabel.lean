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

end FirstOrder.Language
