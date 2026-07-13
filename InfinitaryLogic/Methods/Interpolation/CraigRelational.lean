/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Methods.Interpolation.PairedInsepFamily
import InfinitaryLogic.Methods.Interpolation.RootGate
import InfinitaryLogic.Methods.SchemaCompletion

/-!
# Craig interpolation for `L_ω₁ω`, countable relational core (issue #8, Layer 1)

The internal countable joint-language Craig theorem.  Its conclusion is already a **base-`L`
interpolant** — `L[[ℕ]]` occurs only inside the proof, at the abstraction boundary given by the
three constant-expansion transport equalities below.

```
craig_interpolation_relational_countable :
  Sentenceω.Entails r₁ r₂ →
    ∃ θ, θ.functionsIn ⊆ r₁.functionsIn ∩ r₂.functionsIn ∧
         θ.relationsIn ⊆ r₁.relationsIn ∩ r₂.relationsIn ∧
         Sentenceω.Entails r₁ θ ∧ Sentenceω.Entails θ r₂
```

No coverage or side-bound hypotheses are needed: the side vocabularies are specialized to the roots'
exact occurrence sets, and the paired family (`PairedInsepFamily.lean`) maintains coordinatewise
side membership field-by-field, so the audit's global `GenU ⊆ Sent₁ ∪ Sent₂` coverage invariant —
and with it the coverage hypothesis — is unnecessary (an audit correction).

## The root argument

Assume no interpolant.  Then the mapped root pair `({r₁'}, {r₂'.not})` is inseparable at empty
support: an empty-support separator would strip (`base_interpolant_of_empty_support_separator`) to a
base interpolant `θ₀` with `r₁ ⊨ θ₀` and `{r₂.not} ⊨ θ₀.not`, and the latter is `θ₀ ⊨ r₂` by
semantic contraposition — contradiction.  Feeding the inseparable root pair to `exists_paired_model_neg`
gives one model with `M ⊨ r₁` and `¬ M ⊨ r₂`; its base reduct contradicts `r₁ ⊨ r₂`.
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}}

/-! ## `relationsIn` of a language-mapped formula (companion to `functionsIn_mapLanguage`) -/

theorem BoundedFormulaω.relationsIn_mapLanguage {L L' : Language} (g : L →ᴸ L') {α : Type} {n : ℕ}
    (φ : L.BoundedFormulaω α n) :
    (φ.mapLanguage g).relationsIn =
      (fun p : Σ n, L.Relations n => ⟨p.1, g.onRelation p.2⟩) '' φ.relationsIn := by
  induction φ with
  | falsum => simp [BoundedFormulaω.mapLanguage, BoundedFormulaω.relationsIn]
  | equal t u => simp [BoundedFormulaω.mapLanguage, BoundedFormulaω.relationsIn]
  | rel R ts => simp [BoundedFormulaω.mapLanguage, BoundedFormulaω.relationsIn]
  | imp φ ψ ihφ ihψ =>
    simp [BoundedFormulaω.mapLanguage, BoundedFormulaω.relationsIn, ihφ, ihψ, Set.image_union]
  | all φ ih => simp [BoundedFormulaω.mapLanguage, BoundedFormulaω.relationsIn, ih]
  | iSup φs ih =>
    simp [BoundedFormulaω.mapLanguage, BoundedFormulaω.relationsIn, ih, Set.image_iUnion]
  | iInf φs ih =>
    simp [BoundedFormulaω.mapLanguage, BoundedFormulaω.relationsIn, ih, Set.image_iUnion]

/-! ## The three constant-expansion transport equalities (the base-`L` ↔ `L[[ℕ]]` boundary) -/

private theorem tag_inl_fun_injective :
    Function.Injective
      (fun p : Σ n, L.Functions n => (⟨p.1, Sum.inl p.2⟩ : Σ n, L[[ℕ]].Functions n)) := by
  rintro ⟨a1, a2⟩ ⟨b1, b2⟩ h
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp h
  rw [heq_eq_eq] at h2
  exact Sigma.ext rfl (heq_of_eq (Sum.inl_injective h2))

private theorem tag_inl_rel_injective :
    Function.Injective
      (fun p : Σ n, L.Relations n => (⟨p.1, Sum.inl p.2⟩ : Σ n, L[[ℕ]].Relations n)) := by
  rintro ⟨a1, a2⟩ ⟨b1, b2⟩ h
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp h
  rw [heq_eq_eq] at h2
  exact Sigma.ext rfl (heq_of_eq (Sum.inl_injective h2))

/-- **Base functions of a constant-expansion image** are the sentence's own functions. -/
theorem baseFunctionsIn_mapLanguage_withConstants (r : L.Sentenceω) :
    (BoundedFormulaω.mapLanguage (L.lhomWithConstants ℕ) r).baseFunctionsIn = r.functionsIn := by
  ext s
  simp only [BoundedFormulaω.baseFunctionsIn, Set.mem_setOf_eq,
    BoundedFormulaω.functionsIn_mapLanguage]
  exact tag_inl_fun_injective.mem_set_image

/-- **Base relations of a constant-expansion image** are the sentence's own relations. -/
theorem baseRelationsIn_mapLanguage_withConstants (r : L.Sentenceω) :
    (BoundedFormulaω.mapLanguage (L.lhomWithConstants ℕ) r).baseRelationsIn = r.relationsIn := by
  ext s
  simp only [BoundedFormulaω.baseRelationsIn, Set.mem_setOf_eq,
    BoundedFormulaω.relationsIn_mapLanguage]
  exact tag_inl_rel_injective.mem_set_image

/-- **A constant-expansion image carries no constants**: its constant support is empty. -/
theorem sentenceJConsts_mapLanguage_withConstants (r : L.Sentenceω) :
    sentenceJConsts (L' := L) (J := ℕ)
      (BoundedFormulaω.mapLanguage (L.lhomWithConstants ℕ) r) = ∅ := by
  ext j
  simp only [sentenceJConsts, Set.mem_setOf_eq, BoundedFormulaω.functionsIn_mapLanguage,
    Set.mem_image, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
  rintro ⟨p1, p2⟩ - hpe
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp hpe
  rw [heq_eq_eq] at h2
  exact absurd (show (Sum.inl p2 : L[[ℕ]].Functions 0) = Sum.inr j from h2) (by simp)

/-! ## The semantic contraposition / singleton bridge -/

/-- **Semantic contraposition (singleton form)**: `{r₂.not} ⊨ θ.not` is `{θ} ⊨ r₂`. -/
theorem entails_singleton_of_neg_entails_neg {r₂ θ : L.Sentenceω}
    (hE : Theoryω.Entails {r₂.not} θ.not) : Theoryω.Entails {θ} r₂ := by
  intro M _ _ hmodel
  by_contra hr₂
  have hnr₂ : Theoryω.Model {r₂.not} M := by
    intro ψ hψ; rw [Set.mem_singleton_iff] at hψ; subst hψ
    simp only [Sentenceω.Realize, BoundedFormulaω.realize_not]; exact hr₂
  have := hE M hnr₂
  simp only [Sentenceω.Realize, BoundedFormulaω.realize_not] at this
  exact this (hmodel θ (Set.mem_singleton _))

/-! ## The countable relational Craig theorem -/

/-- **Craig interpolation for `L_ω₁ω` — countable relational core.** Over a relational language with
countably many relation symbols, an `L_ω₁ω`-entailment `r₁ ⊨ r₂` has a base-`L` interpolant whose
function/relation symbols lie in the intersection of the roots' occurrence sets. -/
theorem craig_interpolation_relational_countable [L.IsRelational]
    [Countable (Σ n, L.Relations n)] (r₁ r₂ : L.Sentenceω) (h : Sentenceω.Entails r₁ r₂) :
    ∃ θ : L.Sentenceω,
      θ.functionsIn ⊆ r₁.functionsIn ∩ r₂.functionsIn ∧
      θ.relationsIn ⊆ r₁.relationsIn ∩ r₂.relationsIn ∧
      Sentenceω.Entails r₁ θ ∧ Sentenceω.Entails θ r₂ := by
  by_contra hcon
  push Not at hcon
  set g := L.lhomWithConstants ℕ with hg
  -- The mapped root pair is inseparable at empty support.
  have hroot : InsepAt (r₁.functionsIn ∩ r₂.functionsIn) (r₁.relationsIn ∩ r₂.relationsIn) ∅
      {BoundedFormulaω.mapLanguage g r₁} {(BoundedFormulaω.mapLanguage g r₂).not} := by
    rintro ⟨σ, hbf, hbr, hsupp, hΓσ, hΔσ⟩
    have hsupp0 : sentenceJConsts (L' := L) (J := ℕ) σ ⊆ ∅ := by simpa using hsupp
    have hΓmap : Theoryω.Entails (BoundedFormulaω.mapLanguage g '' {r₁}) σ := by
      rwa [Set.image_singleton]
    have hΔmap : Theoryω.Entails (BoundedFormulaω.mapLanguage g '' {r₂.not}) σ.not := by
      rw [Set.image_singleton, BoundedFormulaω.mapLanguage_not]; exact hΔσ
    obtain ⟨θ₀, hθf, hθr, hθΓ, hθΔ⟩ :=
      base_interpolant_of_empty_support_separator σ hsupp0 hΓmap hΔmap
    exact hcon θ₀ (hθf.trans hbf) (hθr.trans hbr) hθΓ (entails_singleton_of_neg_entails_neg hθΔ)
  -- A single model of both sides.
  obtain ⟨M, instM, neM, hM1, hM2⟩ := exists_paired_model_neg
    r₁.functionsIn r₁.relationsIn r₂.functionsIn r₂.relationsIn
    (BoundedFormulaω.mapLanguage g r₁) (BoundedFormulaω.mapLanguage g r₂)
    (by rw [sentenceJConsts_mapLanguage_withConstants]; exact Set.finite_empty)
    (by rw [sentenceJConsts_mapLanguage_withConstants]; exact Set.finite_empty)
    ⟨(baseFunctionsIn_mapLanguage_withConstants r₁).le,
      (baseRelationsIn_mapLanguage_withConstants r₁).le⟩
    ⟨((baseFunctionsIn_not _).trans (baseFunctionsIn_mapLanguage_withConstants r₂)).le,
      ((baseRelationsIn_not _).trans (baseRelationsIn_mapLanguage_withConstants r₂)).le⟩
    ∅
    (by simp only [hg, sentenceJConsts_not, sentenceJConsts_mapLanguage_withConstants,
        Set.union_self, Finset.coe_empty, Set.subset_empty_iff])
    hroot
  -- The base reduct contradicts `r₁ ⊨ r₂`.
  letI : L.Structure M := (L.lhomWithConstants ℕ).reduct M
  have hb1 : @Sentenceω.Realize L r₁ M _ :=
    (BoundedFormulaω.realize_mapLanguage (L.lhomWithConstants ℕ) r₁ Empty.elim Fin.elim0).mp hM1
  have hb2 : ¬ @Sentenceω.Realize L r₂ M _ := fun hc =>
    hM2 ((BoundedFormulaω.realize_mapLanguage (L.lhomWithConstants ℕ) r₂ Empty.elim Fin.elim0).mpr hc)
  exact hb2 (h M (fun ψ hψ => by rw [Set.mem_singleton_iff] at hψ; subst hψ; exact hb1))

end FirstOrder.Language
