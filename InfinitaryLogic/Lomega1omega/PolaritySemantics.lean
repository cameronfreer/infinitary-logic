/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Lomega1omega.Polarity
import InfinitaryLogic.Lomega1omega.Semantics

/-!
# Semantic monotonicity under signed reinterpretation (issue #14, Unit 1)

The semantic content of the signed traversal of `Lomega1omega/Polarity.lean`: over a relational
language, **growing the relations that occur positively and shrinking those that occur negatively
preserves truth**.

```
realize_mono_of_signed φ S₁ S₂ hpos hneg : Realize[S₁] φ v xs → Realize[S₂] φ v xs
```

The two structures are **explicit arguments quantified after `φ`**, which is what makes the
induction go through: the implication case calls the antecedent's inductive hypothesis at the
**swapped** pair `(S₂, S₁)`, where the two hypotheses exchange roles exactly as
`positiveRelationsIn (φ.imp ψ) = negativeRelationsIn φ ∪ positiveRelationsIn ψ` predicts.  This is
the semantic stop/go gate for the polarity definition: if the traversal had the wrong sign
convention anywhere, this induction would not close.

Only the **forward** monotonicity theorem is exported.  The dual (shrink positives, grow
negatives, reflect truth) is the same statement with the structures swapped — it is already
encoded in the hypotheses and in the implication recursion, so a separate theorem would only
duplicate the API.

Relationality is used exactly once, to make term realization structure-independent
(`realize_term_of_isRelational`); the public statement therefore needs **no** function-agreement
hypothesis.
-/

namespace FirstOrder.Language

open FirstOrder Structure

namespace BoundedFormulaω

variable {L : Language.{0, 0}} {α : Type} {M : Type}

/-- Over a relational language a term's value does not depend on the structure: terms are
variables. -/
private theorem realize_term_of_isRelational [L.IsRelational] (S₁ S₂ : L.Structure M)
    {γ : Type} (v : γ → M) :
    ∀ t : L.Term γ, @Term.realize L M S₁ γ v t = @Term.realize L M S₂ γ v t
  | .var _ => rfl
  | .func f _ => isEmptyElim f

/-- **Semantic monotonicity under signed reinterpretation** (the Unit-1 acceptance gate): if `S₂`
interprets every relation occurring **positively** in `φ` at least as widely as `S₁`, and every
relation occurring **negatively** in `φ` at most as widely, then truth of `φ` transports from `S₁`
to `S₂`.

The structures are quantified after `φ` on purpose: the `imp` case applies the inductive
hypothesis for the antecedent at the swapped pair `(S₂, S₁)`. -/
theorem realize_mono_of_signed [L.IsRelational] :
    ∀ {n : ℕ} (φ : L.BoundedFormulaω α n) (S₁ S₂ : L.Structure M),
      (∀ p ∈ φ.positiveRelationsIn, ∀ a : Fin p.1 → M,
        @Structure.RelMap L M S₁ p.1 p.2 a → @Structure.RelMap L M S₂ p.1 p.2 a) →
      (∀ p ∈ φ.negativeRelationsIn, ∀ a : Fin p.1 → M,
        @Structure.RelMap L M S₂ p.1 p.2 a → @Structure.RelMap L M S₁ p.1 p.2 a) →
      ∀ {v : α → M} {xs : Fin n → M},
        @Realize L M S₁ α n φ v xs → @Realize L M S₂ α n φ v xs := by
  intro n φ
  induction φ with
  | falsum => intro S₁ S₂ _ _ v xs h; exact h
  | equal t₁ t₂ =>
    intro S₁ S₂ _ _ v xs h
    show @Term.realize L M S₂ _ _ t₁ = @Term.realize L M S₂ _ _ t₂
    rw [← realize_term_of_isRelational S₁ S₂ _ t₁, ← realize_term_of_isRelational S₁ S₂ _ t₂]
    exact h
  | rel R ts =>
    intro S₁ S₂ hpos _ v xs h
    show @Structure.RelMap L M S₂ _ R fun i => @Term.realize L M S₂ _ _ (ts i)
    have hterm : (fun i => @Term.realize L M S₂ _ (Sum.elim v xs) (ts i)) =
        fun i => @Term.realize L M S₁ _ (Sum.elim v xs) (ts i) :=
      funext fun i => (realize_term_of_isRelational S₁ S₂ _ (ts i)).symm
    rw [hterm]
    exact hpos ⟨_, R⟩ (by simp) _ h
  | imp φ ψ ihφ ihψ =>
    intro S₁ S₂ hpos hneg v xs h hφ₂
    -- the antecedent is transported *backwards*, i.e. by the inductive hypothesis at `(S₂, S₁)`
    have hφ₁ : @Realize L M S₁ α _ φ v xs :=
      ihφ S₂ S₁
        (fun p hp a => hneg p (Set.mem_union_left _ hp) a)
        (fun p hp a => hpos p (Set.mem_union_left _ hp) a) hφ₂
    exact ihψ S₁ S₂
      (fun p hp a => hpos p (Set.mem_union_right _ hp) a)
      (fun p hp a => hneg p (Set.mem_union_right _ hp) a) (h hφ₁)
  | all φ ih =>
    intro S₁ S₂ hpos hneg v xs h x
    exact ih S₁ S₂ hpos hneg (h x)
  | iSup φs ih =>
    intro S₁ S₂ hpos hneg v xs h
    obtain ⟨i, hi⟩ := h
    exact ⟨i, ih i S₁ S₂
      (fun p hp a => hpos p (Set.mem_iUnion.mpr ⟨i, hp⟩) a)
      (fun p hp a => hneg p (Set.mem_iUnion.mpr ⟨i, hp⟩) a) hi⟩
  | iInf φs ih =>
    intro S₁ S₂ hpos hneg v xs h i
    exact ih i S₁ S₂
      (fun p hp a => hpos p (Set.mem_iUnion.mpr ⟨i, hp⟩) a)
      (fun p hp a => hneg p (Set.mem_iUnion.mpr ⟨i, hp⟩) a) (h i)

end BoundedFormulaω

end FirstOrder.Language
