/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Linf.Semantics
import InfinitaryLogic.Util
import Mathlib.Data.Set.Basic
import Architect

/-!
# L∞ω Elementary Equivalence

This file defines L∞ω-elementary equivalence between structures, in both the
universe-restricted and universe-correct forms, and its invariance under isomorphism.

## Main Definitions

- `LinfEquiv`: L∞ω-elementary equivalence between structures.

## Main Results

- `LinfEquiv.refl`, `LinfEquiv.symm`, `LinfEquiv.trans`: LinfEquiv is an equivalence relation.
- `LinfEquiv.of_equiv`: Isomorphic structures are L∞ω-equivalent.

## References

- [Karp65]
- [KK04]
-/

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

open FirstOrder Structure

/-! ### Isomorphism Invariance of Realization -/

/-- Realization of L∞ω formulas is preserved by language isomorphisms.

Given an isomorphism `e : M ≃[L] N`, a formula realized in M with variable assignments
`v` and `xs` is also realized in N with the transported assignments `e ∘ v` and `e ∘ xs`. -/
theorem BoundedFormulaInfLegacy.realize_equiv {M N : Type w} [L.Structure M] [L.Structure N]
    (e : M ≃[L] N) {α : Type*} {n : ℕ} (φ : L.BoundedFormulaInfLegacy α n)
    (v : α → M) (xs : Fin n → M) :
    φ.Realize v xs ↔ φ.Realize (e ∘ v) (e ∘ xs) := by
  have h_elim : ∀ {m : ℕ} (v' : α → M) (xs' : Fin m → M),
      Sum.elim (⇑e ∘ v') (⇑e ∘ xs') = ⇑e ∘ Sum.elim v' xs' := by
    intro m v' xs'; funext x; cases x <;> rfl
  induction φ with
  | falsum => simp [BoundedFormulaInfLegacy.Realize]
  | equal t₁ t₂ =>
    simp only [BoundedFormulaInfLegacy.Realize, h_elim, HomClass.realize_term e]
    exact e.injective.eq_iff.symm
  | rel R ts =>
    simp only [BoundedFormulaInfLegacy.Realize]
    simp_rw [h_elim, HomClass.realize_term e]
    exact (StrongHomClass.map_rel e R _).symm
  | imp φ ψ ihφ ihψ =>
    simp only [BoundedFormulaInfLegacy.Realize]
    exact Iff.imp (ihφ xs) (ihψ xs)
  | all φ ih =>
    simp only [BoundedFormulaInfLegacy.Realize]
    constructor
    · intro h y
      have h1 := (ih (Fin.snoc xs (e.symm y))).mp (h (e.symm y))
      rwa [Fin.comp_snoc, e.apply_symm_apply] at h1
    · intro h x
      have h1 := h (e x)
      rw [← Fin.comp_snoc] at h1
      exact (ih (Fin.snoc xs x)).mpr h1
  | iSup φs ih =>
    simp only [BoundedFormulaInfLegacy.Realize]
    exact exists_congr fun i => ih i xs
  | iInf φs ih =>
    simp only [BoundedFormulaInfLegacy.Realize]
    exact forall_congr' fun i => ih i xs

/-! ### L∞ω Elementary Equivalence -/

/-- Two structures are L∞ω-elementarily equivalent if they satisfy the same L∞ω sentences.

The current definition quantifies over `BoundedFormulaInfLegacy.{u, v, 0, 0}`, pinning the
free-variable universe (`u'`) and index-type universe (`uι`) to 0 for practicality.
The `uι = 0` choice ensures compatibility with `qrank : Ordinal.{0}` (whose suprema
at `iSup`/`iInf` nodes must live in a fixed universe) and suffices for all standard
applications (any countable or `Type 0` index type falls within this definition). -/
def LinfEquiv (L : Language.{u, v}) (M N : Type w) [L.Structure M] [L.Structure N] : Prop :=
  ∀ φ : BoundedFormulaInfLegacy.{u, v, 0, 0} L Empty 0, SentenceInfLegacy.Realize φ M ↔ SentenceInfLegacy.Realize φ N

namespace LinfEquiv

variable {L : Language.{u, v}}
variable {M : Type w} [L.Structure M]
variable {N : Type w} [L.Structure N]
variable {P : Type w} [L.Structure P]

/-- L∞ω-equivalence is reflexive. -/
theorem refl : LinfEquiv L M M := fun _ => Iff.rfl

/-- L∞ω-equivalence is symmetric. -/
theorem symm (h : LinfEquiv L M N) : LinfEquiv L N M := fun φ => (h φ).symm

/-- L∞ω-equivalence is transitive. -/
theorem trans (h₁ : LinfEquiv L M N) (h₂ : LinfEquiv L N P) : LinfEquiv L M P :=
  fun φ => (h₁ φ).trans (h₂ φ)

/-- Isomorphic structures are L∞ω-equivalent.

The proof transports variable assignments along the isomorphism using
`BoundedFormulaInfLegacy.realize_equiv`, then observes that `e ∘ Empty.elim = Empty.elim`
and `e ∘ Fin.elim0 = Fin.elim0` since both domains are empty. -/
theorem of_equiv (e : M ≃[L] N) : LinfEquiv L M N := by
  intro φ
  have h := BoundedFormulaInfLegacy.realize_equiv e φ (Empty.elim : Empty → M) (Fin.elim0 : Fin 0 → M)
  rwa [comp_empty_elim e, comp_fin_elim0 e] at h

end LinfEquiv

/-! ### Universe-correct L∞ω Elementary Equivalence -/

/-- L∞ω-elementary equivalence with index types matching the structure universe.

Unlike `LinfEquiv` which pins `uι = 0`, this version uses `BoundedFormulaInfLegacy.{u, v, 0, w}`
so that index types for `iSup`/`iInf` may be any `Type w`. The backward direction of
Karp's theorem constructs formulas with `iInf` indexed by `N : Type w`, which needs
`uι = w`. -/
@[blueprint "def:linf-equiv"
  (title := /-- $L_{\infty\omega}$-equivalence -/)
  (statement := /-- $L_{\infty\omega}$-equivalence: $M$ and $N$ satisfy the same
    $L_{\infty\omega}^w$ sentences, where $w$ is the universe of the index types. -/)]
def LinfEquivW (L : Language.{u, v}) (M N : Type w) [L.Structure M] [L.Structure N] : Prop :=
  ∀ φ : BoundedFormulaInfLegacy.{u, v, 0, w} L Empty 0,
    SentenceInfLegacy.Realize φ M ↔ SentenceInfLegacy.Realize φ N

namespace LinfEquivW

variable {L : Language.{u, v}}
variable {M : Type w} [L.Structure M]
variable {N : Type w} [L.Structure N]
variable {P : Type w} [L.Structure P]

theorem refl : LinfEquivW L M M := fun _ => Iff.rfl

theorem symm (h : LinfEquivW L M N) : LinfEquivW L N M := fun φ => (h φ).symm

theorem trans (h₁ : LinfEquivW L M N) (h₂ : LinfEquivW L N P) : LinfEquivW L M P :=
  fun φ => (h₁ φ).trans (h₂ φ)

theorem of_equiv (e : M ≃[L] N) : LinfEquivW L M N := by
  intro φ
  have h := BoundedFormulaInfLegacy.realize_equiv e φ (Empty.elim : Empty → M) (Fin.elim0 : Fin 0 → M)
  rwa [comp_empty_elim e, comp_fin_elim0 e] at h

end LinfEquivW

end Language

end FirstOrder
