/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.SmallVocabulary
import InfinitaryLogic.Descriptive.SatisfactionBorel
import InfinitaryLogic.Lomega1omega.QuantifierRank

/-!
# Lifting formulas of the small presentation back to the original language

`liftFormula` sends a formula of `lang L` to the formula of `L` obtained by decoding each relation
symbol through `toLang L`.  It is a self-contained definition: `BoundedFormulaω.mapLanguage`
takes both languages in the same universe pair, which excludes this case, and that definition is
left unchanged.

* `realize_liftFormula`: the lift holds in `c.toStructure` iff the original holds in
  `(code L c).toStructure`, for every valuation.
* `qrank_liftFormula`: the quantifier rank is unchanged.
* `modelsOf_liftFormula`: `ModelsOf (liftFormula L ψ) = code L ⁻¹' ModelsOf ψ`, with the
  pointwise form `code_mem_modelsOf_iff`.

No lowering of `L`-formulas into the small presentation is provided.  The vocabulary is relational,
so terms are variables.
-/

universe u v uι u'

namespace FirstOrder.Language.SmallVocabulary

variable (L : Language.{u, v}) [L.IsRelational] [Countable (Σ n, L.Relations n)]

/-- Terms of the small presentation are variables (the vocabulary is relational). -/
def liftTerm {γ : Type u'} : (lang L).Term γ → L.Term γ
  | .var x => .var x
  | .func f _ => isEmptyElim f

omit [L.IsRelational] in
@[simp] theorem liftTerm_var {γ : Type u'} (x : γ) : liftTerm L (.var x : (lang L).Term γ) = .var x :=
  rfl

/-- **Lifting a formula** of the small presentation to `L`: decode each relation symbol. -/
noncomputable def liftFormula {ι : Type uι} {γ : Type u'} :
    ∀ {n : ℕ}, (lang L).BoundedFormulaInf ι γ n → L.BoundedFormulaInf ι γ n
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal (liftTerm L t₁) (liftTerm L t₂)
  | _, .rel R ts => .rel ((toLang L).onRelation R) fun i => liftTerm L (ts i)
  | _, .imp φ ψ => .imp (liftFormula φ) (liftFormula ψ)
  | _, .all φ => .all (liftFormula φ)
  | _, .iSup φs => .iSup fun i => liftFormula (φs i)
  | _, .iInf φs => .iInf fun i => liftFormula (φs i)

theorem realize_liftTerm {γ : Type u'} (c : StructureSpace L) (t : (lang L).Term γ)
    (w : γ → ℕ) :
    @Term.realize L ℕ c.toStructure γ w (liftTerm L t) =
      @Term.realize (lang L) ℕ (code L c).toStructure γ w t := by
  cases t with
  | var x => rfl
  | func f _ => exact isEmptyElim f

/-- **Realization is preserved by lifting**: the lifted formula holds in the decoded structure of
`c` iff the original holds in the decoded structure of its code. -/
theorem realize_liftFormula {ι : Type uι} {γ : Type u'} (c : StructureSpace L) {n : ℕ}
    (φ : (lang L).BoundedFormulaInf ι γ n) (v : γ → ℕ) (xs : Fin n → ℕ) :
    @BoundedFormulaInf.Realize L ι γ ℕ c.toStructure n (liftFormula L φ) v xs ↔
      @BoundedFormulaInf.Realize (lang L) ι γ ℕ (code L c).toStructure n φ v xs := by
  induction φ with
  | falsum => exact Iff.rfl
  | equal t₁ t₂ =>
    change @Term.realize L ℕ c.toStructure _ _ (liftTerm L t₁) =
        @Term.realize L ℕ c.toStructure _ _ (liftTerm L t₂) ↔ _
    rw [realize_liftTerm, realize_liftTerm]
    exact Iff.rfl
  | rel R ts =>
    change c ⟨⟨_, (shrinkRel L _).symm R⟩,
        fun i => @Term.realize L ℕ c.toStructure _ _ (liftTerm L (ts i))⟩ = true ↔
      code L c ⟨⟨_, R⟩, fun i => @Term.realize (lang L) ℕ (code L c).toStructure _ _ (ts i)⟩ = true
    simp only [realize_liftTerm]
    exact Iff.rfl
  | imp φ ψ ihφ ihψ => exact imp_congr (ihφ xs) (ihψ xs)
  | all φ ih => exact forall_congr' fun y => ih (Fin.snoc xs y)
  | iSup φs ih => exact exists_congr fun i => ih i xs
  | iInf φs ih => exact forall_congr' fun i => ih i xs

omit [L.IsRelational] in
/-- **The quantifier rank is preserved by lifting.** -/
theorem qrank_liftFormula {ι : Type uι} {γ : Type u'} {n : ℕ}
    (φ : (lang L).BoundedFormulaInf ι γ n) : (liftFormula L φ).qrank = φ.qrank := by
  induction φ with
  | falsum => rfl
  | equal _ _ => rfl
  | rel _ _ => rfl
  | imp φ ψ ihφ ihψ =>
    change max (liftFormula L φ).qrank (liftFormula L ψ).qrank = max φ.qrank ψ.qrank
    rw [ihφ, ihψ]
  | all φ ih =>
    change Order.succ (liftFormula L φ).qrank = Order.succ φ.qrank
    rw [ih]
  | iSup φs ih =>
    change (⨆ i, (liftFormula L (φs i)).qrank) = ⨆ i, (φs i).qrank
    simp only [ih]
  | iInf φs ih =>
    change (⨆ i, (liftFormula L (φs i)).qrank) = ⨆ i, (φs i).qrank
    simp only [ih]

/-- **Models through the presentation**: the code of `c` models a sentence of the small
presentation iff `c` models its lift. -/
theorem code_mem_modelsOf_iff (c : StructureSpace L) (ψ : (lang L).Sentenceω) :
    code L c ∈ ModelsOf ψ ↔ c ∈ ModelsOf (liftFormula L ψ) :=
  (realize_liftFormula L c ψ Empty.elim Fin.elim0).symm

/-- The models of a lifted sentence are the preimage of the models of the original. -/
theorem modelsOf_liftFormula (ψ : (lang L).Sentenceω) :
    ModelsOf (liftFormula L ψ) = code L ⁻¹' ModelsOf ψ :=
  Set.ext fun c => (code_mem_modelsOf_iff L c ψ).symm

end FirstOrder.Language.SmallVocabulary
