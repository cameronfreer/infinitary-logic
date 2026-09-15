/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fin.SuccPred

/-!
# Extending a finite matching to a permutation respecting an equivalence relation

**Generic lemma** (`exists_equiv_of_matching`): for an equivalence relation `E` on a type `X`
and finite families `r s : Fin m → X` with `E (r j) (s j)` that are **compatible**
(`r j = r j' ↔ s j = s j'`, so repeated entries match consistently and the induced partial map is
well defined and injective), there is a permutation `e : X ≃ X` with `e (r j) = s j`, with
`E x (e x)` everywhere, and fixing every point outside the finite union of the sources and
targets.  Proof by induction on `m`: an entry already handled by an earlier repeat is skipped;
otherwise the current permutation is followed by the transposition of `s j` and `e (r j)`, which
respects `E` because both are `E`-related to `r j`, and moves only points of the finite union.
`exists_equiv_of_matching_injective` is the injective special case.

Pure combinatorics; no model theory.  The names keep their original location in the
`FiberAssembly` namespace, where the lemma was first used.
-/

namespace FirstOrder.Language

namespace FiberAssembly

/-! ### The generic lemma -/

section Generic

variable {X : Type*} {E : X → X → Prop}

/-- A permutation fixing every point outside a set maps the set into itself. -/
private theorem mem_of_fixes_compl (e : X ≃ X) {S : Set X} (hfix : ∀ x, x ∉ S → e x = x)
    {w : X} (hw : w ∈ S) : e w ∈ S := by
  by_contra h
  have h2 : e w = w := e.injective (hfix _ h)
  exact h (by rw [h2]; exact hw)

/-- **Extending a finite compatible matching.**  For an equivalence relation `E`, families
`r s : Fin m → X` with `E (r j) (s j)` and `r j = r j' ↔ s j = s j'` extend to a permutation
`e` with `e (r j) = s j`, `E x (e x)` for all `x`, and `e x = x` for `x` outside the sources and
targets. -/
theorem exists_equiv_of_matching (hE : Equivalence E) :
    ∀ (m : ℕ) (r s : Fin m → X), (∀ j j', r j = r j' ↔ s j = s j') → (∀ j, E (r j) (s j)) →
      ∃ e : X ≃ X, (∀ j, e (r j) = s j) ∧ (∀ x, E x (e x)) ∧
        ∀ x, (∀ j, x ≠ r j ∧ x ≠ s j) → e x = x := by
  classical
  intro m
  induction m with
  | zero =>
    intro r s _ _
    exact ⟨_root_.Equiv.refl X, fun j => j.elim0, fun x => hE.refl x, fun _ _ => rfl⟩
  | succ m ih =>
    intro r s hcomp hrs
    obtain ⟨e, he, hEe, hfix⟩ := ih (r ∘ Fin.castSucc) (s ∘ Fin.castSucc)
      (fun j j' => hcomp _ _) (fun j => hrs _)
    -- the finite union handled so far
    set S : Set X := {x | ∃ j : Fin m, x = r (Fin.castSucc j) ∨ x = s (Fin.castSucc j)} with hS
    have hfixS : ∀ x, x ∉ S → e x = x := fun x hx =>
      hfix x fun j => ⟨fun h => hx ⟨j, Or.inl h⟩, fun h => hx ⟨j, Or.inr h⟩⟩
    set x := r (Fin.last m)
    set y := s (Fin.last m)
    by_cases hx : ∃ i : Fin m, r (Fin.castSucc i) = x
    · -- already matched through a repeat
      obtain ⟨i, hi⟩ := hx
      refine ⟨e, fun j => ?_, hEe, fun z hz => hfix z fun j => hz _⟩
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · exact he j'
      · show e x = y
        rw [← hi]
        exact (he i).trans ((hcomp _ _).mp hi)
    · push Not at hx
      -- fresh source: transpose `y` with `e x`
      have hy : ∀ i : Fin m, s (Fin.castSucc i) ≠ y := fun i h =>
        hx i ((hcomp _ _).mpr h)
      refine ⟨e.trans (_root_.Equiv.swap y (e x)), fun j => ?_, fun z => ?_, fun z hz => ?_⟩
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
        · simp only [_root_.Equiv.trans_apply, Function.comp_apply] at he ⊢
          rw [he j']
          exact _root_.Equiv.swap_apply_of_ne_of_ne (hy j') fun h =>
            hx j' (e.injective ((he j').trans h))
        · exact _root_.Equiv.swap_apply_right _ _
      · simp only [_root_.Equiv.trans_apply]
        by_cases h1 : e z = y
        · rw [h1, _root_.Equiv.swap_apply_left]
          have hzy : E z y := h1 ▸ hEe z
          exact hE.trans hzy (hE.trans (hE.symm (hrs _)) (hEe x))
        · by_cases h2 : e z = e x
          · rw [h2, _root_.Equiv.swap_apply_right]
            have hzx : E z (e x) := h2 ▸ hEe z
            exact hE.trans hzx (hE.trans (hE.symm (hEe x)) (hrs _))
          · rw [_root_.Equiv.swap_apply_of_ne_of_ne h1 h2]
            exact hEe z
      · simp only [_root_.Equiv.trans_apply]
        have hzS : z ∉ S := fun ⟨j, hj⟩ => by
          rcases hj with rfl | rfl
          · exact (hz _).1 rfl
          · exact (hz _).2 rfl
        rw [hfixS z hzS]
        refine _root_.Equiv.swap_apply_of_ne_of_ne (hz (Fin.last m)).2 fun h => ?_
        -- `e x` lies in `S ∪ {x}`, but `z` does not
        by_cases hxS : x ∈ S
        · exact hzS (h ▸ mem_of_fixes_compl e hfixS hxS)
        · rw [hfixS x hxS] at h
          exact (hz (Fin.last m)).1 h

/-- The injective special case: distinct sources and distinct targets. -/
theorem exists_equiv_of_matching_injective (hE : Equivalence E) {m : ℕ} {r s : Fin m → X}
    (hr : Function.Injective r) (hs : Function.Injective s) (hrs : ∀ j, E (r j) (s j)) :
    ∃ e : X ≃ X, (∀ j, e (r j) = s j) ∧ (∀ x, E x (e x)) ∧
      ∀ x, (∀ j, x ≠ r j ∧ x ≠ s j) → e x = x :=
  exists_equiv_of_matching hE m r s (fun _ _ => ⟨fun h => hr h ▸ rfl, fun h => hs h ▸ rfl⟩) hrs

end Generic

end FiberAssembly

end FirstOrder.Language
