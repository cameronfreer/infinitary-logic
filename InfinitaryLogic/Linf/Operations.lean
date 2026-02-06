/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Linf.Semantics

/-!
# Operations on L∞ω Formulas

This file defines operations on L∞ω formulas including relabeling, casting, and substitution.

## Main Definitions

- `BoundedFormulaInf.relabel`: Relabels free variables.
- `BoundedFormulaInf.castLE`: Increases the number of bound variables.
- `BoundedFormulaInf.subst`: Substitutes terms for free variables.
- `BoundedFormula.toLinf`: Embeds first-order formulas into L∞ω.
- `BoundedFormulaω.toLinf`: Embeds Lω₁ω formulas into L∞ω.

## Implementation Notes

The operations here (castLE, relabel, mapFreeVars, subst) closely mirror those in
`Lomega1omega/Operations.lean`. The duplication exists because `BoundedFormulaInf` and
`BoundedFormulaω` are separate inductive types: the former uses arbitrary `{ι : Type uι}`
for `iSup`/`iInf` while the latter uses `ℕ`. Factoring into a shared abstraction would
require a typeclass over the formula type, deferred for future work.
-/

universe u v u'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}
variable {α β : Type u'} {n m : ℕ}

open FirstOrder Structure Fin

namespace BoundedFormulaInf

/-- Casts a bounded formula to one with more bound variables. -/
@[simp]
def castLE : ∀ {m n : ℕ} (_h : m ≤ n), L.BoundedFormulaInf α m → L.BoundedFormulaInf α n
  | _, _, _, falsum => falsum
  | _, _, h, equal t₁ t₂ =>
    equal (t₁.relabel (Sum.map id (Fin.castLE h))) (t₂.relabel (Sum.map id (Fin.castLE h)))
  | _, _, h, rel R ts => rel R (fun i => (ts i).relabel (Sum.map id (Fin.castLE h)))
  | _, _, h, imp φ ψ => (φ.castLE h).imp (ψ.castLE h)
  | _, _, h, all φ => (φ.castLE (Nat.succ_le_succ h)).all
  | _, _, h, iSup φs => iSup fun i => (φs i).castLE h
  | _, _, h, iInf φs => iInf fun i => (φs i).castLE h

/-- Relabeling a term by the identity function returns the same term. -/
private theorem Term.relabel_id' {α : Type*} (t : L.Term α) : t.relabel id = t := by
  induction t with
  | var => rfl
  | func f ts ih =>
    simp only [Term.relabel]
    congr 1
    funext i
    exact ih i

/-- `castLE (le_refl n)` is the identity on formulas. -/
theorem castLE_refl : (φ : L.BoundedFormulaInf α n) → φ.castLE (le_refl n) = φ := by
  intro φ
  induction φ with
  | falsum => rfl
  | @equal m t₁ t₂ =>
    simp only [castLE]
    congr 1 <;> {
      have h : Sum.map id (Fin.castLE (le_refl m)) = (id : α ⊕ Fin m → α ⊕ Fin m) := by
        funext x; cases x <;> rfl
      rw [h, Term.relabel_id']
    }
  | @rel m l R ts =>
    simp only [castLE]
    congr 1
    funext i
    have h : Sum.map id (Fin.castLE (le_refl m)) = (id : α ⊕ Fin m → α ⊕ Fin m) := by
      funext x; cases x <;> rfl
    rw [h, Term.relabel_id']
  | imp φ ψ ih_φ ih_ψ =>
    simp only [castLE, ih_φ, ih_ψ]
  | all φ ih =>
    simp only [castLE, ih]
  | iSup φs ih =>
    simp only [castLE]
    congr 1
    funext i
    exact ih i
  | iInf φs ih =>
    simp only [castLE]
    congr 1
    funext i
    exact ih i

variable {M : Type*} [L.Structure M]

/-- `castLE` over a proof of `m ≤ m` preserves semantics.
This is more general than matching on `le_refl` directly, as it works for any
proof `h : m ≤ m` regardless of how it was constructed. -/
theorem realize_castLE_of_eq {m n : ℕ} (φ : L.BoundedFormulaInf α m) (h : m ≤ n) (heq : m = n)
    (v : α → M) (xs : Fin n → M) :
    (φ.castLE h).Realize v xs ↔ φ.Realize v (xs ∘ Fin.cast heq) := by
  subst heq
  have hcast : Fin.cast (Eq.refl m) = id := funext (fun i => rfl)
  simp only [hcast, Function.comp_id]
  have : h = le_refl m := rfl
  rw [this, castLE_refl]

/-- `castLE (le_refl n)` preserves semantics. -/
theorem realize_castLE_refl {n : ℕ} (φ : L.BoundedFormulaInf α n)
    (v : α → M) (xs : Fin n → M) :
    (φ.castLE (le_refl n)).Realize v xs ↔ φ.Realize v xs := by
  rw [castLE_refl]

/-- `castLE` over any proof `h : n ≤ n` preserves semantics. -/
theorem realize_castLE_self {n : ℕ} (φ : L.BoundedFormulaInf α n) (h : n ≤ n)
    (v : α → M) (xs : Fin n → M) :
    (φ.castLE h).Realize v xs ↔ φ.Realize v xs :=
  realize_castLE_of_eq φ h rfl v xs

/-- A function to help relabel the variables in bounded formulas. -/
def relabelAux (g : α → β ⊕ Fin n) (k : ℕ) : α ⊕ Fin k → β ⊕ Fin (n + k) :=
  Sum.map id finSumFinEquiv ∘ Equiv.sumAssoc _ _ _ ∘ Sum.map g id

/-- Relabels a bounded formula's free variables. -/
def relabel (g : α → β ⊕ Fin n) : ∀ {k}, L.BoundedFormulaInf α k → L.BoundedFormulaInf β (n + k)
  | _, falsum => falsum
  | _, equal t₁ t₂ => equal (t₁.relabel (relabelAux g _)) (t₂.relabel (relabelAux g _))
  | _, rel R ts => rel R fun i => (ts i).relabel (relabelAux g _)
  | _, imp φ ψ => (φ.relabel g).imp (ψ.relabel g)
  | k, all φ => (φ.relabel g).castLE (Nat.add_right_comm n k 1 ▸ le_refl _) |>.all
  | _, iSup φs => iSup fun i => (φs i).relabel g
  | _, iInf φs => iInf fun i => (φs i).relabel g

/-- Renames free variables in a bounded formula using a function f : α → β.

Unlike `relabel`, which can move free variables into bound positions, `mapFreeVars`
simply renames free variables while preserving the bound variable structure. -/
def mapFreeVars (f : α → β) : ∀ {n}, L.BoundedFormulaInf α n → L.BoundedFormulaInf β n
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal (t₁.relabel (Sum.map f id)) (t₂.relabel (Sum.map f id))
  | _, .rel R ts => .rel R (fun i => (ts i).relabel (Sum.map f id))
  | _, .imp φ ψ => .imp (φ.mapFreeVars f) (ψ.mapFreeVars f)
  | _, .all φ => .all (φ.mapFreeVars f)
  | _, .iSup φs => .iSup (fun i => (φs i).mapFreeVars f)
  | _, .iInf φs => .iInf (fun i => (φs i).mapFreeVars f)

private theorem sum_elim_comp_sum_map (f : α → β) (v : β → M) (xs : Fin n → M) :
    Sum.elim v xs ∘ Sum.map f id = Sum.elim (v ∘ f) xs := by
  funext x; cases x <;> rfl

/-- Realization commutes with free variable renaming. -/
theorem realize_mapFreeVars {M : Type*} [L.Structure M]
    (f : α → β) (φ : L.BoundedFormulaInf α n) (v : β → M) (xs : Fin n → M) :
    (φ.mapFreeVars f).Realize v xs ↔ φ.Realize (v ∘ f) xs := by
  induction φ with
  | falsum => simp [mapFreeVars, Realize]
  | equal t₁ t₂ =>
    simp only [mapFreeVars, realize_equal, Term.realize_relabel, sum_elim_comp_sum_map]
  | rel R ts =>
    simp only [mapFreeVars, realize_rel]
    constructor <;> intro h
    · convert h using 1; ext i; simp [Term.realize_relabel, sum_elim_comp_sum_map]
    · convert h using 1; ext i; simp [Term.realize_relabel, sum_elim_comp_sum_map]
  | imp φ ψ ihφ ihψ =>
    simp only [mapFreeVars, realize_imp, ihφ xs, ihψ xs]
  | all φ ih =>
    simp only [mapFreeVars, realize_all]
    exact forall_congr' fun x => ih (Fin.snoc xs x)
  | iSup φs ih =>
    simp only [mapFreeVars]
    exact exists_congr fun i => ih i xs
  | iInf φs ih =>
    simp only [mapFreeVars]
    exact forall_congr' fun i => ih i xs

/-- Substitutes the free variables in a bounded formula with terms. -/
def subst : ∀ {n : ℕ}, L.BoundedFormulaInf α n → (α → L.Term β) → L.BoundedFormulaInf β n
  | _, falsum, _ => falsum
  | _, equal t₁ t₂, tf =>
    equal (t₁.subst (Sum.elim (Term.relabel Sum.inl ∘ tf) (Term.var ∘ Sum.inr)))
          (t₂.subst (Sum.elim (Term.relabel Sum.inl ∘ tf) (Term.var ∘ Sum.inr)))
  | _, rel R ts, tf =>
    rel R fun i => (ts i).subst (Sum.elim (Term.relabel Sum.inl ∘ tf) (Term.var ∘ Sum.inr))
  | _, imp φ ψ, tf => (φ.subst tf).imp (ψ.subst tf)
  | _, all φ, tf => (φ.subst tf).all
  | _, iSup φs, tf => iSup fun i => (φs i).subst tf
  | _, iInf φs, tf => iInf fun i => (φs i).subst tf

end BoundedFormulaInf

namespace BoundedFormula

/-- Embeds a first-order bounded formula into L∞ω. -/
def toLinf : ∀ {n : ℕ}, L.BoundedFormula α n → L.BoundedFormulaInf α n
  | _, falsum => BoundedFormulaInf.falsum
  | _, equal t₁ t₂ => BoundedFormulaInf.equal t₁ t₂
  | _, rel R ts => BoundedFormulaInf.rel R ts
  | _, imp φ ψ => (φ.toLinf).imp (ψ.toLinf)
  | _, all φ => φ.toLinf.all

variable {M : Type*} [L.Structure M] {v : α → M} {xs : Fin n → M}

@[simp]
theorem realize_toLinf (φ : L.BoundedFormula α n) :
    φ.toLinf.Realize v xs ↔ φ.Realize v xs := by
  induction φ with
  | falsum => rfl
  | equal => rfl
  | rel => rfl
  | imp _ _ ih₁ ih₂ =>
    simp only [toLinf, BoundedFormulaInf.realize_imp, BoundedFormula.realize_imp, ih₁, ih₂]
  | all _ ih =>
    simp only [toLinf, BoundedFormulaInf.realize_all, BoundedFormula.realize_all, ih]

end BoundedFormula

namespace Formula

/-- Embeds a first-order formula into L∞ω. -/
def toLinf (φ : L.Formula α) : L.FormulaInf α := BoundedFormula.toLinf φ

@[simp]
theorem realize_toLinf {M : Type*} [L.Structure M] {v : α → M} (φ : L.Formula α) :
    FormulaInf.Realize φ.toLinf v ↔ φ.Realize v :=
  BoundedFormula.realize_toLinf φ

end Formula

namespace Sentence

/-- Embeds a first-order sentence into L∞ω. -/
def toLinf (φ : L.Sentence) : L.SentenceInf := Formula.toLinf φ

@[simp]
theorem realize_toLinf {M : Type*} [L.Structure M] [Nonempty M] (φ : L.Sentence) :
    SentenceInf.Realize φ.toLinf M ↔ M ⊨ φ := by
  have h : (default : Empty → M) = (fun e : Empty => e.elim) := by
    funext e; exact e.elim
  simp only [SentenceInf.Realize, Sentence.Realize, Formula.Realize, toLinf, Formula.toLinf, h]
  exact BoundedFormula.realize_toLinf φ

end Sentence

end Language

end FirstOrder
