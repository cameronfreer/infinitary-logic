/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Lomega1omega.Semantics

/-!
# Operations on Lω₁ω Formulas

This file defines operations on Lω₁ω formulas including relabeling, casting, and substitution.

## Main Definitions

- `BoundedFormulaω.relabel`: Relabels free variables.
- `BoundedFormulaω.castLE`: Increases the number of bound variables.
- `BoundedFormulaω.subst`: Substitutes terms for free variables.
- `BoundedFormula.toLω`: Embeds first-order formulas into Lω₁ω.
-/

universe u v u'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}
variable {α β : Type u'} {n m : ℕ}

open FirstOrder Structure Fin

namespace BoundedFormulaω

/-- Casts a bounded formula to one with more bound variables. -/
@[simp]
def castLE : ∀ {m n : ℕ} (_h : m ≤ n), L.BoundedFormulaω α m → L.BoundedFormulaω α n
  | _, _, _, falsum => falsum
  | _, _, h, equal t₁ t₂ =>
    equal (t₁.relabel (Sum.map id (Fin.castLE h))) (t₂.relabel (Sum.map id (Fin.castLE h)))
  | _, _, h, rel R ts => rel R (fun i => (ts i).relabel (Sum.map id (Fin.castLE h)))
  | _, _, h, imp φ ψ => (φ.castLE h).imp (ψ.castLE h)
  | _, _, h, all φ => (φ.castLE (Nat.succ_le_succ h)).all
  | _, _, h, iSup φs => iSup fun i => (φs i).castLE h
  | _, _, h, iInf φs => iInf fun i => (φs i).castLE h

/-- Relabeling a term by the identity function returns the same term. -/
theorem Term.relabel_id' {α : Type*} (t : L.Term α) : t.relabel id = t := by
  induction t with
  | var => rfl
  | func f ts ih =>
    simp only [Term.relabel]
    congr 1
    funext i
    exact ih i

/-- `castLE (le_refl n)` is the identity on formulas. -/
theorem castLE_refl : (φ : L.BoundedFormulaω α n) → φ.castLE (le_refl n) = φ := by
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
theorem realize_castLE_of_eq {m n : ℕ} (φ : L.BoundedFormulaω α m) (h : m ≤ n) (heq : m = n)
    (v : α → M) (xs : Fin n → M) :
    (φ.castLE h).Realize v xs ↔ φ.Realize v (xs ∘ Fin.cast heq) := by
  subst heq
  have hcast : Fin.cast (Eq.refl m) = id := funext (fun i => rfl)
  simp only [hcast, Function.comp_id]
  have : h = le_refl m := rfl
  rw [this, castLE_refl]

/-- `castLE (le_refl n)` preserves semantics. -/
theorem realize_castLE_refl {n : ℕ} (φ : L.BoundedFormulaω α n)
    (v : α → M) (xs : Fin n → M) :
    (φ.castLE (le_refl n)).Realize v xs ↔ φ.Realize v xs := by
  rw [castLE_refl]

/-- `castLE` over any proof `h : n ≤ n` preserves semantics.
This handles the case where the proof term is not definitionally `le_refl`
(e.g., constructed via rewriting or other means). -/
theorem realize_castLE_self {n : ℕ} (φ : L.BoundedFormulaω α n) (h : n ≤ n)
    (v : α → M) (xs : Fin n → M) :
    (φ.castLE h).Realize v xs ↔ φ.Realize v xs :=
  realize_castLE_of_eq φ h rfl v xs

variable {M : Type*} in
/-- A function to help relabel the variables in bounded formulas. -/
def relabelAux (g : α → β ⊕ Fin n) (k : ℕ) : α ⊕ Fin k → β ⊕ Fin (n + k) :=
  Sum.map id finSumFinEquiv ∘ Equiv.sumAssoc _ _ _ ∘ Sum.map g id

/-- Relabels a bounded formula's free variables. -/
def relabel (g : α → β ⊕ Fin n) : ∀ {k}, L.BoundedFormulaω α k → L.BoundedFormulaω β (n + k)
  | _, falsum => falsum
  | _, equal t₁ t₂ => equal (t₁.relabel (relabelAux g _)) (t₂.relabel (relabelAux g _))
  | _, rel R ts => rel R fun i => (ts i).relabel (relabelAux g _)
  | _, imp φ ψ => (φ.relabel g).imp (ψ.relabel g)
  | k, all φ => (φ.relabel g).castLE (Nat.add_right_comm n k 1 ▸ le_refl _) |>.all
  | _, iSup φs => iSup fun i => (φs i).relabel g
  | _, iInf φs => iInf fun i => (φs i).relabel g

-- Note: The general realize_relabel lemma is complex due to castLE in the all case.
-- For Scott formulas, we only need specific lemmas for existsLastVar and forallLastVar,
-- which are proved directly in Scott/Formula.lean using a more targeted approach.

/-- Substitutes the free variables in a bounded formula with terms. -/
def subst : ∀ {n : ℕ}, L.BoundedFormulaω α n → (α → L.Term β) → L.BoundedFormulaω β n
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

/-- Renames free variables in a bounded formula using a function f : α → β.

Unlike `relabel`, which can move free variables into bound positions, `mapFreeVars`
simply renames free variables while preserving the bound variable structure. -/
def mapFreeVars (f : α → β) : ∀ {n}, L.BoundedFormulaω α n → L.BoundedFormulaω β n
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal (t₁.relabel (Sum.map f id)) (t₂.relabel (Sum.map f id))
  | _, .rel R ts => .rel R (fun i => (ts i).relabel (Sum.map f id))
  | _, .imp φ ψ => .imp (φ.mapFreeVars f) (ψ.mapFreeVars f)
  | _, .all φ => .all (φ.mapFreeVars f)
  | _, .iSup φs => .iSup (fun k => (φs k).mapFreeVars f)
  | _, .iInf φs => .iInf (fun k => (φs k).mapFreeVars f)

private theorem sum_elim_comp_sum_map (f : α → β) (v : β → M) (xs : Fin n → M) :
    Sum.elim v xs ∘ Sum.map f id = Sum.elim (v ∘ f) xs := by
  funext x; cases x <;> rfl

/-- Realization commutes with free variable renaming. -/
theorem realize_mapFreeVars {M : Type*} [L.Structure M]
    (f : α → β) (φ : L.BoundedFormulaω α n) (v : β → M) (xs : Fin n → M) :
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
    simp only [mapFreeVars, realize_iSup]
    exact exists_congr fun k => ih k xs
  | iInf φs ih =>
    simp only [mapFreeVars, realize_iInf]
    exact forall_congr' fun k => ih k xs

end BoundedFormulaω

namespace Formulaω

/-- Converts a formula with `Fin 0` free variables to a sentence (with `Empty` free variables).

Since both `Fin 0` and `Empty` are empty types, this is a purely type-theoretic conversion
that does not change the semantics of the formula. -/
def toSentenceω (φ : L.Formulaω (Fin 0)) : L.Sentenceω :=
  φ.mapFreeVars Fin.elim0

/-- `toSentenceω` preserves semantics: the sentence realizes in M iff the original
formula realizes with the `Fin.elim0` assignment. -/
theorem realize_toSentenceω {M : Type*} [L.Structure M]
    (φ : L.Formulaω (Fin 0)) :
    Sentenceω.Realize φ.toSentenceω M ↔ Formulaω.Realize φ (Fin.elim0 : Fin 0 → M) := by
  unfold toSentenceω Sentenceω.Realize Formulaω.Realize
  rw [BoundedFormulaω.realize_mapFreeVars]
  have h : (Empty.elim : Empty → M) ∘ (Fin.elim0 : Fin 0 → Empty) = (Fin.elim0 : Fin 0 → M) :=
    funext (fun x => Fin.elim0 x)
  simp only [h]

end Formulaω

namespace BoundedFormula

/-- Embeds a first-order bounded formula into Lω₁ω. -/
def toLω : ∀ {n : ℕ}, L.BoundedFormula α n → L.BoundedFormulaω α n
  | _, falsum => BoundedFormulaω.falsum
  | _, equal t₁ t₂ => BoundedFormulaω.equal t₁ t₂
  | _, rel R ts => BoundedFormulaω.rel R ts
  | _, imp φ ψ => (φ.toLω).imp (ψ.toLω)
  | _, all φ => φ.toLω.all

variable {M : Type*} [L.Structure M] {v : α → M} {xs : Fin n → M}

@[simp]
theorem realize_toLω (φ : L.BoundedFormula α n) :
    φ.toLω.Realize v xs ↔ φ.Realize v xs := by
  induction φ with
  | falsum => rfl
  | equal => rfl
  | rel => rfl
  | imp _ _ ih₁ ih₂ =>
    simp only [toLω, BoundedFormulaω.realize_imp, BoundedFormula.realize_imp, ih₁, ih₂]
  | all _ ih =>
    simp only [toLω, BoundedFormulaω.realize_all, BoundedFormula.realize_all, ih]

end BoundedFormula

namespace Formula

/-- Embeds a first-order formula into Lω₁ω. -/
def toLω (φ : L.Formula α) : L.Formulaω α := BoundedFormula.toLω φ

@[simp]
theorem realize_toLω {M : Type*} [L.Structure M] {v : α → M} (φ : L.Formula α) :
    Formulaω.Realize φ.toLω v ↔ φ.Realize v :=
  BoundedFormula.realize_toLω φ

end Formula

namespace Sentence

/-- Embeds a first-order sentence into Lω₁ω. -/
def toLω (φ : L.Sentence) : L.Sentenceω := Formula.toLω φ

@[simp]
theorem realize_toLω {M : Type*} [L.Structure M] [Nonempty M] (φ : L.Sentence) :
    Sentenceω.Realize φ.toLω M ↔ M ⊨ φ := by
  -- M ⊨ φ uses `default : Empty → M`, while Sentenceω.Realize uses `Empty.elim`
  -- These are propositionally equal
  have h : (default : Empty → M) = (fun e : Empty => e.elim) := by
    funext e; exact e.elim
  simp only [Sentenceω.Realize, Sentence.Realize, Formula.Realize, toLω, Formula.toLω, h]
  exact BoundedFormula.realize_toLω φ

end Sentence

end Language

end FirstOrder
