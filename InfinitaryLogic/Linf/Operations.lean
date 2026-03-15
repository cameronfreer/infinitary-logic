/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Linf.Semantics
import InfinitaryLogic.Util

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
    constructor <;> intro h <;> convert h using 1 <;>
      ext i <;> simp [Term.realize_relabel, sum_elim_comp_sum_map]
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

/-! ### Universe lifting for index types -/

section LiftUI

universe w

/-- Lift a formula from index universe 0 to index universe `w` by ULifting each index type.
This maps `BoundedFormulaInf.{u,v,u',0}` to `BoundedFormulaInf.{u,v,u',w}`, preserving
semantics and quantifier rank. -/
def liftUI : ∀ {n}, BoundedFormulaInf.{u, v, u', 0} L α n →
    BoundedFormulaInf.{u, v, u', w} L α n
  | _, falsum => falsum
  | _, equal t₁ t₂ => equal t₁ t₂
  | _, rel R ts => rel R ts
  | _, imp φ ψ => imp (liftUI φ) (liftUI ψ)
  | _, all φ => all (liftUI φ)
  | _, iSup φs => iSup (ι := ULift.{w} _) (fun i => liftUI (φs i.down))
  | _, iInf φs => iInf (ι := ULift.{w} _) (fun i => liftUI (φs i.down))

variable {M : Type*} [L.Structure M]

/-- Universe lifting preserves semantics. -/
theorem realize_liftUI :
    ∀ {n} (φ : BoundedFormulaInf.{u, v, u', 0} L α n) (v : α → M) (xs : Fin n → M),
    (liftUI.{u, v, u', w} φ).Realize v xs ↔ φ.Realize v xs := by
  intro n φ
  induction φ with
  | falsum => intro v xs; rfl
  | equal => intro v xs; rfl
  | rel => intro v xs; rfl
  | imp φ ψ ihφ ihψ =>
    intro v xs; simp only [liftUI, realize_imp]; exact Iff.imp (ihφ v xs) (ihψ v xs)
  | all φ ih =>
    intro v xs; simp only [liftUI, realize_all]
    exact forall_congr' fun x => ih v (Fin.snoc xs x)
  | iSup φs ih =>
    intro v xs
    show (∃ i : ULift _, _) ↔ ∃ i, _
    constructor
    · rintro ⟨⟨i⟩, hi⟩; exact ⟨i, (ih i v xs).mp hi⟩
    · rintro ⟨i, hi⟩; exact ⟨⟨i⟩, (ih i v xs).mpr hi⟩
  | iInf φs ih =>
    intro v xs
    show (∀ i : ULift _, _) ↔ ∀ i, _
    constructor
    · intro h i; exact (ih i v xs).mp (h ⟨i⟩)
    · intro h ⟨i⟩; exact (ih i v xs).mpr (h i)

end LiftUI

/-! ### Quantifying over the last free variable -/

section LastVar

variable {γ : Type*}

/-- Maps the last variable of `Fin (n+1)` to a bound variable position,
keeping the first n as free variables. This is identical to the version
in `Scott/Formula.lean` for `BoundedFormulaω`, redefined here to avoid
importing the Scott module. -/
private def insertLastBoundInf {n : ℕ} : Fin (n + 1) → Fin n ⊕ Fin 1 :=
  fun i => if h : i.val < n then Sum.inl ⟨i.val, h⟩ else Sum.inr 0

/-- Existentially quantify over the last free variable of an L∞ω formula. -/
def existsLastVarInf {n : ℕ} (φ : L.FormulaInf (Fin (n + 1))) : L.FormulaInf (Fin n) :=
  (φ.relabel insertLastBoundInf).ex

/-- Universally quantify over the last free variable of an L∞ω formula. -/
def forallLastVarInf {n : ℕ} (φ : L.FormulaInf (Fin (n + 1))) : L.FormulaInf (Fin n) :=
  (φ.relabel insertLastBoundInf).all

/-- Maps `j : Fin k` to `⟨j.val + 1, ...⟩ : Fin (1 + k)`. -/
private def Fin.succShiftInf {k : ℕ} : Fin k → Fin (1 + k) :=
  fun j => ⟨j.val + 1, by omega⟩

/-- The composition of `Sum.elim v xs` with `relabelAux insertLastBoundInf k`
equals `Sum.elim (Fin.snoc v (xs 0)) (xs ∘ Fin.succShiftInf)`. -/
private lemma sum_elim_relabelAux_insertLastBoundInf {n : ℕ} {k : ℕ}
    (v : Fin n → γ) (xs : Fin (1 + k) → γ) :
    Sum.elim v xs ∘ relabelAux insertLastBoundInf k =
    Sum.elim (Fin.snoc v (xs 0)) (xs ∘ Fin.succShiftInf) := by
  funext x
  cases x with
  | inl i =>
    simp only [Function.comp_apply, relabelAux, Sum.map_inl, Sum.elim_inl, insertLastBoundInf]
    split_ifs with h
    · simp only [Equiv.sumAssoc_apply_inl_inl, Sum.map_inl, Sum.elim_inl, Fin.snoc, h, dite_true]
      congr 1
    · simp only [Equiv.sumAssoc_apply_inl_inr, Sum.map_inr, Sum.elim_inr, finSumFinEquiv_apply_left]
      have hi : i = Fin.last n := by ext; simp only [Fin.last]; omega
      rw [hi, Fin.snoc_last]; rfl
  | inr j =>
    simp only [Function.comp_apply, relabelAux, Sum.map_inr, Sum.elim_inr]
    simp only [Equiv.sumAssoc_apply_inr, Sum.map_inr, Sum.elim_inr, finSumFinEquiv_apply_right,
      Fin.succShiftInf]
    congr 1; ext; simp only [Fin.natAdd, id_eq]; omega

/-- snoc xs y at position 0 equals xs at position 0. -/
private lemma snoc_zero_eq_inf {k : ℕ} (xs : Fin (1 + k) → γ) (y : γ) :
    (Fin.snoc (α := fun _ => γ) xs y) (0 : Fin (1 + k + 1)) = xs (0 : Fin (1 + k)) := by
  simp [Fin.snoc, show (0 : ℕ) < 1 + k from by omega]

/-- snoc composed with succShiftInf: on LHS, `Fin.succShiftInf` is at `k+1`
(mapping `Fin (k+1) → Fin (1+k+1)`); on RHS, it is at `k` (mapping `Fin k → Fin (1+k)`).
Lean infers the different implicit args from the types of `Fin.snoc xs y` and `xs`. -/
private lemma snoc_comp_succShiftInf_eq {k : ℕ} (xs : Fin (1 + k) → γ) (y : γ) :
    Fin.snoc xs y ∘ Fin.succShiftInf = Fin.snoc (xs ∘ Fin.succShiftInf) y := by
  funext i
  simp only [Function.comp_apply]
  -- i : Fin (k+1); LHS succShiftInf: Fin (k+1) → Fin (1+k+1); RHS snoc: Fin (k+1) → γ
  cases i using Fin.lastCases with
  | last =>
    -- LHS: snoc xs y (succShiftInf (last k))
    -- succShiftInf (last k) : Fin (1+k+1), val = k + 1 = last (1+k)
    have h1 : Fin.succShiftInf (Fin.last k) = Fin.last (1 + k) :=
      Fin.ext (by simp [Fin.succShiftInf, Fin.last]; omega)
    rw [h1, Fin.snoc_last, Fin.snoc_last]
  | cast j =>
    rw [Fin.snoc_castSucc]
    -- Goal: snoc xs y (succShiftInf (castSucc j)) = (xs ∘ succShiftInf) j
    simp only [Function.comp_apply]
    -- Goal: snoc xs y (succShiftInf (castSucc j)) = xs (succShiftInf j)
    unfold Fin.snoc
    have hlt : (Fin.succShiftInf (j.castSucc)).val < 1 + k := by
      simp [Fin.succShiftInf, Fin.castSucc]; omega
    simp only [hlt, dite_true]
    apply congrArg xs
    exact Fin.ext (by simp [Fin.succShiftInf, Fin.castSucc, Fin.castLT])

variable {M : Type*} [L.Structure M]

/-- The general semantics lemma for relabeling with `insertLastBoundInf`:
    For a formula with k bound variables, relabeling shifts the last free variable
    to bound position 0, while bound variables shift up by 1. -/
private theorem realize_relabel_insertLastBoundInf {n : ℕ} :
    ∀ {k : ℕ} (φ : L.BoundedFormulaInf (Fin (n + 1)) k) (v : Fin n → M)
      (xs : Fin (1 + k) → M),
    (φ.relabel insertLastBoundInf).Realize v xs ↔
    φ.Realize (Fin.snoc v (xs 0)) (xs ∘ Fin.succShiftInf) := by
  intro k φ
  induction φ with
  | falsum => intro v xs; simp only [relabel, realize_falsum]
  | equal t₁ t₂ =>
    intro v xs
    simp only [relabel, realize_equal, Term.realize_relabel,
      sum_elim_relabelAux_insertLastBoundInf]
  | rel R ts =>
    intro v xs; simp only [relabel, realize_rel]
    constructor <;> intro h <;> convert h using 1 <;> ext i <;>
      simp [Term.realize_relabel, sum_elim_relabelAux_insertLastBoundInf]
  | imp φ ψ ih_φ ih_ψ =>
    intro v xs; simp only [relabel, realize_imp]
    exact Iff.imp (ih_φ v xs) (ih_ψ v xs)
  | all φ ih =>
    intro v xs; simp only [relabel, realize_all]
    constructor <;> intro hall y
    · specialize hall y; rw [realize_castLE_self] at hall
      rw [ih v (Fin.snoc xs y)] at hall
      rw [snoc_zero_eq_inf, snoc_comp_succShiftInf_eq] at hall; exact hall
    · rw [realize_castLE_self, ih v (Fin.snoc xs y), snoc_zero_eq_inf,
        snoc_comp_succShiftInf_eq]; exact hall y
  | iSup φs ih =>
    intro v xs; simp only [relabel]
    exact exists_congr (fun i => ih i v xs)
  | iInf φs ih =>
    intro v xs; simp only [relabel]
    exact forall_congr' (fun i => ih i v xs)

/-- The key semantics lemma for formulas with 0 bound variables. -/
private theorem realize_relabel_insertLastBoundInf_zero {n : ℕ}
    (φ : L.FormulaInf (Fin (n + 1)))
    (v : Fin n → M) (xs : Fin 1 → M) :
    (φ.relabel insertLastBoundInf).Realize v xs ↔
    φ.Realize (Fin.snoc v (xs 0)) := by
  have h := realize_relabel_insertLastBoundInf (k := 0) φ v xs
  rw [h]
  simp only [FormulaInf.Realize]
  rw [show (xs ∘ Fin.succShiftInf : Fin 0 → M) = Fin.elim0 from Fin.eq_elim0 _]

/-- Helper: `Fin.snoc Fin.elim0 x` evaluated at 0 gives x. -/
private theorem snoc_elim0_zero_inf (x : M) :
    (Fin.snoc (α := fun _ => M) Fin.elim0 x) 0 = x :=
  congrFun (Fin.snoc_elim0_eq x) 0

/-- Semantics of `existsLastVarInf`: existentially quantifies over the last variable. -/
theorem realize_existsLastVarInf {n : ℕ} (φ : L.FormulaInf (Fin (n + 1))) (v : Fin n → M) :
    FormulaInf.Realize (existsLastVarInf φ) v ↔ ∃ x : M, FormulaInf.Realize φ (Fin.snoc v x) := by
  simp only [existsLastVarInf, FormulaInf.Realize, realize_ex,
    realize_relabel_insertLastBoundInf_zero, snoc_elim0_zero_inf]

/-- Semantics of `forallLastVarInf`: universally quantifies over the last variable. -/
theorem realize_forallLastVarInf {n : ℕ} (φ : L.FormulaInf (Fin (n + 1))) (v : Fin n → M) :
    FormulaInf.Realize (forallLastVarInf φ) v ↔ ∀ x : M, FormulaInf.Realize φ (Fin.snoc v x) := by
  simp only [forallLastVarInf, FormulaInf.Realize, realize_all,
    realize_relabel_insertLastBoundInf_zero, snoc_elim0_zero_inf]

end LastVar

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
  have h : (default : Empty → M) = (fun e : Empty => e.elim) := Empty.eq_elim default
  simp only [SentenceInf.Realize, Sentence.Realize, Formula.Realize, toLinf, Formula.toLinf, h]
  exact BoundedFormula.realize_toLinf φ

end Sentence

end Language

end FirstOrder
