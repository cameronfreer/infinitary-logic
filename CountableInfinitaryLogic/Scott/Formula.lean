/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import CountableInfinitaryLogic.Scott.BackAndForth

/-!
# Scott Formulas

This file defines Scott formulas, which are Lω₁ω formulas that capture back-and-forth
equivalence at each ordinal level.

## Main Definitions

- `scottFormula`: The Scott formula for a tuple at a given ordinal level.

## Main Results

- `realize_scottFormula_iff_BFEquiv`: A tuple b satisfies the Scott formula for a at level α
  if and only if a and b are BF-equivalent at level α.
-/

universe u v w w'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable {M : Type w} [L.Structure M]
variable [Countable (Σ l, L.Relations l)]

open FirstOrder Structure Fin Ordinal BoundedFormulaω

/-- The Scott formula for a tuple a at ordinal level α.

At level 0: the atomic diagram of a.
At successor α + 1: atomic diagram ∧ (∀m. ∃ witness for snoc) ∧ (∀. ∃ witness back)
At limit λ: conjunction over all β < λ.

The formula has free variables indexed by `Fin n` (representing the positions in the tuple).
-/
noncomputable def scottFormula (a : Fin n → M) : Ordinal → L.Formulaω (Fin n) :=
  Ordinal.limitRecOn
    -- Zero case: atomic diagram
    (atomicDiagram a)
    -- Successor case
    (fun α φα =>
      φα ⊓
      -- Forth: for all m in M, there exists a witness n' in N
      einf (fun m : M => (scottFormula (snoc a m) α).ex) ⊓
      -- Back: for all, there exists a witness
      ((scottFormula (snoc a ·) α).ex).all)
    -- Limit case
    (fun α ih => einf fun ⟨β, _⟩ => ih β)

-- We need to phrase things carefully to handle the recursion.
-- The formula definition uses well-founded recursion, so we state lemmas about its values.

theorem scottFormula_zero (a : Fin n → M) :
    scottFormula a 0 = atomicDiagram a := by
  simp only [scottFormula, Ordinal.limitRecOn_zero]

theorem scottFormula_succ (a : Fin n → M) (α : Ordinal) :
    scottFormula a (α + 1) =
      scottFormula a α ⊓
      einf (fun m : M => (scottFormula (snoc a m) α).ex) ⊓
      ((scottFormula (snoc a ·) α).ex).all := by
  conv_lhs => rw [scottFormula, Ordinal.limitRecOn_succ]

theorem scottFormula_limit (a : Fin n → M) (α : Ordinal) (hα : α.IsLimit) :
    scottFormula a α = einf (fun ⟨β, _⟩ => scottFormula a β) := by
  conv_lhs => rw [scottFormula, Ordinal.limitRecOn_limit _ _ _ hα]

/-- The fundamental correspondence: a tuple b realizes the Scott formula for a at level α
if and only if a and b are BF-equivalent at level α. -/
theorem realize_scottFormula_iff_BFEquiv
    {N : Type w'} [L.Structure N] [Countable (Σ l, L.Relations l)]
    (a : Fin n → M) (b : Fin n → N) (α : Ordinal) :
    (scottFormula a α).Realize b Fin.elim0 ↔ BFEquiv α a b := by
  induction α using Ordinal.limitRecOn with
  | H0 =>
    rw [scottFormula_zero, BFEquiv.zero]
    exact sameAtomicType_iff_realize_atomicDiagram a b
  | Hs β ih =>
    rw [scottFormula_succ, BFEquiv.succ]
    simp only [Formulaω.Realize, realize_inf, realize_einf, realize_all, realize_ex]
    constructor
    · rintro ⟨⟨hbase, hforth⟩, hback⟩
      refine ⟨ih a b |>.mp hbase, ?_, ?_⟩
      · intro m
        obtain ⟨n', hn'⟩ := hforth m
        exact ⟨n', ih (snoc a m) (snoc b n') |>.mp hn'⟩
      · intro n'
        specialize hback n'
        obtain ⟨m, hm⟩ := hback
        exact ⟨m, ih (snoc a m) (snoc b n') |>.mp hm⟩
    · rintro ⟨hbase, hforth, hback⟩
      refine ⟨⟨ih a b |>.mpr hbase, ?_⟩, ?_⟩
      · intro m
        obtain ⟨n', hn'⟩ := hforth m
        exact ⟨n', ih (snoc a m) (snoc b n') |>.mpr hn'⟩
      · intro n'
        obtain ⟨m, hm⟩ := hback n'
        exact ⟨m, ih (snoc a m) (snoc b n') |>.mpr hm⟩
  | Hl β hβ ih =>
    rw [scottFormula_limit a β hβ, BFEquiv.limit β hβ]
    simp only [Formulaω.Realize, realize_einf]
    constructor
    · intro h γ hγ
      exact ih hγ |>.mp (h ⟨γ, hγ⟩)
    · intro h ⟨γ, hγ⟩
      exact ih hγ |>.mpr (h γ hγ)

end Language

end FirstOrder
