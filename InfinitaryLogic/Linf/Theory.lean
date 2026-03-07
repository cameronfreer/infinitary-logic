/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Linf.Semantics
import Mathlib.Data.Set.Basic
import Architect

/-!
# L∞ω Theories and Semantic Entailment

This file defines theories, models, semantic entailment, and elementary equivalence
in L∞ω (infinitary logic with arbitrary conjunctions/disjunctions).

## Main Definitions

- `TheoryInf`: A theory in L∞ω is a set of sentences.
- `TheoryInf.Model`: A structure M is a model of theory T if it satisfies all sentences in T.
- `LinfEquiv`: L∞ω-elementary equivalence between structures.

## Main Results

- `LinfEquiv.refl`, `LinfEquiv.symm`, `LinfEquiv.trans`: LinfEquiv is an equivalence relation.
- `LinfEquiv.of_equiv`: Isomorphic structures are L∞ω-equivalent.

## References

- [Karp, "Finite-Quantifier Equivalence", 1965]
- [Keisler-Knight, "Barwise: Infinitary Logic and Admissible Sets", 2004]
-/

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

open FirstOrder Structure

/-! ### Theories -/

/-- A theory in L∞ω is a set of L∞ω sentences. -/
abbrev TheoryInf (L : Language.{u, v}) := Set L.SentenceInf

namespace TheoryInf

variable {T T' : L.TheoryInf} {φ : L.SentenceInf}

/-- A structure M is a model of theory T if it satisfies all sentences in T. -/
def Model (T : L.TheoryInf) (M : Type w) [L.Structure M] : Prop :=
  ∀ φ ∈ T, SentenceInf.Realize φ M

/-- The empty theory has every structure as a model. -/
theorem Model.empty (M : Type w) [L.Structure M] : Model (∅ : L.TheoryInf) M := by
  intro φ hφ
  exact False.elim (Set.notMem_empty φ hφ)

/-- If T ⊆ T' and M ⊨ T', then M ⊨ T. -/
theorem Model.mono (h : T ⊆ T') {M : Type w} [L.Structure M] (hM : T'.Model M) : T.Model M :=
  fun φ hφ => hM φ (h hφ)

/-- Semantic entailment from the empty theory: valid sentences. -/
def Valid (φ : L.SentenceInf) : Prop := ∀ (M : Type) [L.Structure M], SentenceInf.Realize φ M

end TheoryInf

/-! ### Isomorphism Invariance of Realization -/

/-- Realization of L∞ω formulas is preserved by language isomorphisms.

Given an isomorphism `e : M ≃[L] N`, a formula realized in M with variable assignments
`v` and `xs` is also realized in N with the transported assignments `e ∘ v` and `e ∘ xs`. -/
theorem BoundedFormulaInf.realize_equiv {M N : Type w} [L.Structure M] [L.Structure N]
    (e : M ≃[L] N) {α : Type*} {n : ℕ} (φ : L.BoundedFormulaInf α n)
    (v : α → M) (xs : Fin n → M) :
    φ.Realize v xs ↔ φ.Realize (e ∘ v) (e ∘ xs) := by
  have h_elim : ∀ {m : ℕ} (v' : α → M) (xs' : Fin m → M),
      Sum.elim (⇑e ∘ v') (⇑e ∘ xs') = ⇑e ∘ Sum.elim v' xs' := by
    intro m v' xs'; funext x; cases x <;> rfl
  induction φ with
  | falsum => simp [BoundedFormulaInf.Realize]
  | equal t₁ t₂ =>
    simp only [BoundedFormulaInf.Realize, h_elim, HomClass.realize_term e]
    exact e.injective.eq_iff.symm
  | rel R ts =>
    simp only [BoundedFormulaInf.Realize]
    simp_rw [h_elim, HomClass.realize_term e]
    exact (StrongHomClass.map_rel e R _).symm
  | imp φ ψ ihφ ihψ =>
    simp only [BoundedFormulaInf.Realize]
    exact Iff.imp (ihφ xs) (ihψ xs)
  | all φ ih =>
    simp only [BoundedFormulaInf.Realize]
    have snoc_comp : ∀ {m : ℕ} (xs' : Fin m → M) (x : M),
        ⇑e ∘ Fin.snoc xs' x = Fin.snoc (⇑e ∘ xs') (e x) := by
      intro m xs' x; funext i; refine Fin.lastCases ?_ ?_ i
      · simp [Fin.snoc]
      · intro j; simp [Fin.snoc]
    constructor
    · intro h y
      have h1 := (ih (Fin.snoc xs (e.symm y))).mp (h (e.symm y))
      rwa [snoc_comp, e.apply_symm_apply] at h1
    · intro h x
      have h1 := h (e x)
      rw [← snoc_comp] at h1
      exact (ih (Fin.snoc xs x)).mpr h1
  | iSup φs ih =>
    simp only [BoundedFormulaInf.Realize]
    exact ⟨fun ⟨i, hi⟩ => ⟨i, (ih i xs).mp hi⟩,
           fun ⟨i, hi⟩ => ⟨i, (ih i xs).mpr hi⟩⟩
  | iInf φs ih =>
    simp only [BoundedFormulaInf.Realize]
    exact ⟨fun h i => (ih i xs).mp (h i),
           fun h i => (ih i xs).mpr (h i)⟩

/-! ### L∞ω Elementary Equivalence -/

/-- Two structures are L∞ω-elementarily equivalent if they satisfy the same L∞ω sentences.

The current definition quantifies over `BoundedFormulaInf.{u, v, 0, 0}`, pinning the
free-variable universe (`u'`) and index-type universe (`uι`) to 0 for practicality.
The `uι = 0` choice ensures compatibility with `qrank : Ordinal.{0}` (whose suprema
at `iSup`/`iInf` nodes must live in a fixed universe) and suffices for all standard
applications (any countable or `Type 0` index type falls within this definition). -/
def LinfEquiv (L : Language.{u, v}) (M N : Type w) [L.Structure M] [L.Structure N] : Prop :=
  ∀ φ : BoundedFormulaInf.{u, v, 0, 0} L Empty 0, SentenceInf.Realize φ M ↔ SentenceInf.Realize φ N

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
`BoundedFormulaInf.realize_equiv`, then observes that `e ∘ Empty.elim = Empty.elim`
and `e ∘ Fin.elim0 = Fin.elim0` since both domains are empty. -/
theorem of_equiv (e : M ≃[L] N) : LinfEquiv L M N := by
  intro φ
  have h := BoundedFormulaInf.realize_equiv e φ (Empty.elim : Empty → M) (Fin.elim0 : Fin 0 → M)
  have hv : ⇑e ∘ (Empty.elim : Empty → M) = (Empty.elim : Empty → N) :=
    funext (fun x => x.elim)
  have hxs : ⇑e ∘ (Fin.elim0 : Fin 0 → M) = (Fin.elim0 : Fin 0 → N) :=
    funext (fun x => x.elim0)
  rw [hv, hxs] at h; exact h

end LinfEquiv

/-! ### Universe-correct L∞ω Elementary Equivalence -/

/-- L∞ω-elementary equivalence with index types matching the structure universe.

Unlike `LinfEquiv` which pins `uι = 0`, this version uses `BoundedFormulaInf.{u, v, 0, w}`
so that index types for `iSup`/`iInf` may be any `Type w`. This is the "universe-correct"
version needed for the sorry-free Karp theorem at higher universes: the backward direction
requires constructing formulas with `iInf` indexed by `N : Type w`, which needs `uι = w`. -/
@[blueprint "def:linf-equiv"
  (title := /-- $L_{\infty\omega}$-equivalence --/)]
def LinfEquivW (L : Language.{u, v}) (M N : Type w) [L.Structure M] [L.Structure N] : Prop :=
  ∀ φ : BoundedFormulaInf.{u, v, 0, w} L Empty 0,
    SentenceInf.Realize φ M ↔ SentenceInf.Realize φ N

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
  have h := BoundedFormulaInf.realize_equiv e φ (Empty.elim : Empty → M) (Fin.elim0 : Fin 0 → M)
  have hv : ⇑e ∘ (Empty.elim : Empty → M) = (Empty.elim : Empty → N) :=
    funext (fun x => x.elim)
  have hxs : ⇑e ∘ (Fin.elim0 : Fin 0 → M) = (Fin.elim0 : Fin 0 → N) :=
    funext (fun x => x.elim0)
  rw [hv, hxs] at h; exact h

end LinfEquivW

/-! ### Invariance under Isomorphism -/

/-- Models of a theory are preserved under isomorphism. -/
theorem TheoryInf.Model.of_equiv {T : L.TheoryInf} {M N : Type w} [L.Structure M]
    [L.Structure N] (hM : T.Model M) (e : M ≃[L] N) : T.Model N := by
  intro φ hφ
  have h := BoundedFormulaInf.realize_equiv e φ (Empty.elim : Empty → M) (Fin.elim0 : Fin 0 → M)
  have hv : ⇑e ∘ (Empty.elim : Empty → M) = (Empty.elim : Empty → N) :=
    funext (fun x => x.elim)
  have hxs : ⇑e ∘ (Fin.elim0 : Fin 0 → M) = (Fin.elim0 : Fin 0 → N) :=
    funext (fun x => x.elim0)
  rw [hv, hxs] at h
  exact h.mp (hM φ hφ)

end Language

end FirstOrder
