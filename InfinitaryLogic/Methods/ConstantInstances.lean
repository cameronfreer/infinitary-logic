/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Methods.ConstantSupport

/-!
# Constant instances: `instConst`, `closeBy`, and their substitution algebra

The two closing operations by the auxiliary constants of `L[[ℕ]]`, in a neutral module below
both the interpolation layer and the countable-completion kernel:

* `instConst c ψ` — open the single bound variable of `ψ : BoundedFormulaω Empty 1` and substitute
  the constant `c_c`;
* `closeBy φ τ` — open all `n` bound variables of `φ : BoundedFormulaω Empty n` and substitute the
  constants `c_{τ i}`.

Their semantic consumer lemmas (`realize_instConst`, `realize_closeBy`, …) stay in the modules
that own the structures they realize in.  This module holds only syntax: the definitional
commutations of `closeBy` with the connectives and quantifier, and the composition law for
`BoundedFormulaω.subst`, which is what lets one closing substitution be split into two.
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}}

/-! ## Term-level substitution algebra -/

namespace Term

variable {α β γ : Type}

/-- Substituting after substituting is substituting the composite. -/
theorem subst_subst (t : L.Term α) (f : α → L.Term β) (g : β → L.Term γ) :
    (t.subst f).subst g = t.subst fun a => (f a).subst g := by
  induction t with
  | var a => rfl
  | func F ts ih =>
    simp only [subst]
    congr 1; funext i; exact ih i

/-- Substituting after relabeling is substituting along the relabeling. -/
theorem subst_relabel (t : L.Term α) (f : α → β) (g : β → L.Term γ) :
    (t.relabel f).subst g = t.subst (g ∘ f) := by
  induction t with
  | var a => rfl
  | func F ts ih =>
    simp only [relabel, subst]
    congr 1; funext i; exact ih i

/-- Relabeling after substituting is substituting the relabeled terms. -/
theorem relabel_subst (t : L.Term α) (f : α → L.Term β) (g : β → γ) :
    (t.subst f).relabel g = t.subst fun a => (f a).relabel g := by
  induction t with
  | var a => rfl
  | func F ts ih =>
    simp only [relabel, subst]
    congr 1; funext i; exact ih i

end Term

/-! ## Formula-level substitution composition -/

namespace BoundedFormulaω

variable {α β γ : Type}

/-- The bound-variable-aware term substitution used by `BoundedFormulaω.subst`, composed. -/
private theorem substAux_comp (f : α → L.Term β) (g : β → L.Term γ)
    (t : L.Term (α ⊕ Fin n)) :
    (t.subst (Sum.elim (Term.relabel Sum.inl ∘ f) (Term.var ∘ Sum.inr))).subst
        (Sum.elim (Term.relabel Sum.inl ∘ g) (Term.var ∘ Sum.inr)) =
      t.subst (Sum.elim (Term.relabel Sum.inl ∘ fun a => (f a).subst g) (Term.var ∘ Sum.inr)) := by
  rw [Term.subst_subst]
  congr 1
  funext x
  rcases x with a | i
  · simp only [Sum.elim_inl, Function.comp_apply, Term.subst_relabel, Term.relabel_subst]
    rfl
  · rfl

/-- **Composition of substitutions**: substituting `f` and then `g` is substituting
`a ↦ (f a).subst g`.  No side condition: `subst` never touches bound variables. -/
theorem subst_subst : ∀ {n : ℕ} (φ : L.BoundedFormulaω α n) (f : α → L.Term β)
    (g : β → L.Term γ), (φ.subst f).subst g = φ.subst fun a => (f a).subst g
  | _, falsum, _, _ => rfl
  | _, equal t₁ t₂, f, g => by
    simp only [subst, substAux_comp]
  | _, rel R ts, f, g => by
    simp only [subst]
    congr 1; funext i; exact substAux_comp f g (ts i)
  | _, imp φ ψ, f, g => by
    simp only [subst, subst_subst φ, subst_subst ψ]
  | _, all φ, f, g => by
    simp only [subst, subst_subst φ]
  | _, iSup φs, f, g => by
    simp only [subst]
    congr 1; funext i; exact subst_subst (φs i) f g
  | _, iInf φs, f, g => by
    simp only [subst]
    congr 1; funext i; exact subst_subst (φs i) f g

end BoundedFormulaω

/-! ## The closing operations -/

/-- The constant instance `ψ(c)`: open the bound variable of `ψ` and substitute the constant
`c_c`. -/
def instConst (c : ℕ) (ψ : L[[ℕ]].BoundedFormulaω Empty 1) : L[[ℕ]].Sentenceω :=
  (ψ.openBounds).subst (fun _ => constTerm c)

/-- The closing substitution of a bounded formula by constants. -/
noncomputable def closeBy {n : ℕ} (φ : L[[ℕ]].BoundedFormulaω Empty n) (τ : Fin n → ℕ) :
    L[[ℕ]].Sentenceω :=
  (φ.openBounds).subst (fun i => constTerm (τ i))

/-! ## Definitional commutations of `closeBy`

Each holds by unfolding `openBounds` and `subst` on the constructor.  The `all` case exhibits the
arity-one remainder explicitly; relating its `instConst` to `closeBy` at the extended parameter
tuple is a separate lemma about `openBounds`, proved where it is consumed. -/

section CloseBy

variable {n : ℕ}

@[simp]
theorem closeBy_falsum (τ : Fin n → ℕ) :
    closeBy (BoundedFormulaω.falsum : L[[ℕ]].BoundedFormulaω Empty n) τ = BoundedFormulaω.falsum :=
  rfl

@[simp]
theorem closeBy_imp (φ ψ : L[[ℕ]].BoundedFormulaω Empty n) (τ : Fin n → ℕ) :
    closeBy (φ.imp ψ) τ = (closeBy φ τ).imp (closeBy ψ τ) :=
  rfl

@[simp]
theorem closeBy_not (φ : L[[ℕ]].BoundedFormulaω Empty n) (τ : Fin n → ℕ) :
    closeBy φ.not τ = (closeBy φ τ).not :=
  rfl

@[simp]
theorem closeBy_iInf (φs : ℕ → L[[ℕ]].BoundedFormulaω Empty n) (τ : Fin n → ℕ) :
    closeBy (BoundedFormulaω.iInf φs) τ = BoundedFormulaω.iInf fun k => closeBy (φs k) τ :=
  rfl

@[simp]
theorem closeBy_iSup (φs : ℕ → L[[ℕ]].BoundedFormulaω Empty n) (τ : Fin n → ℕ) :
    closeBy (BoundedFormulaω.iSup φs) τ = BoundedFormulaω.iSup fun k => closeBy (φs k) τ :=
  rfl

/-- The arity-one remainder of closing a universal: `closeBy φ.all τ` is the universal closure of
`φ` opened, relabeled so that the last bound variable stays bound, and closed by `τ`. -/
theorem closeBy_all (φ : L[[ℕ]].BoundedFormulaω Empty (n + 1)) (τ : Fin n → ℕ) :
    closeBy φ.all τ =
      (((φ.openBounds).relabel insertLastBound).subst fun i => constTerm (τ i)).all :=
  rfl

/-- `instConst` is `closeBy` at arity one. -/
theorem instConst_eq_closeBy (c : ℕ) (ψ : L[[ℕ]].BoundedFormulaω Empty 1) :
    instConst c ψ = closeBy ψ (fun _ => c) :=
  rfl

end CloseBy

end FirstOrder.Language
