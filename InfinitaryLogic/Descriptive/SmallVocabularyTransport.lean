/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.SmallVocabularyLift
import InfinitaryLogic.Descriptive.LopezEscobar
import InfinitaryLogic.Descriptive.SentenceSplits
import InfinitaryLogic.Descriptive.SentenceObservables

/-!
# Descriptive transport through the small-vocabulary presentation

The coded descriptive theorems are stated for `L : Language.{0, 0}`.  Through the chosen
presentation `lang L` and its code homeomorphism (`Descriptive/SmallVocabulary.lean`) and formula
lift (`Descriptive/SmallVocabularyLift.lean`), each of them yields a statement for every countable
relational `L : Language.{u, v}`.  The underlying small-universe proofs are unchanged; every
theorem here is a transport.

* **Truth sequences**: `sentenceTheory_code` (the truth sequence of a code along a list of the
  small presentation is the truth sequence of the original along the lifted list) and its image
  form `sentenceTheory_image_code`.
* **Sets of codes**: measurability and isomorphism invariance transfer along `code` in both
  directions (`measurableSet_image_code_iff`, `isomorphismInvariant_image_code_iff`).
* **López–Escobar** (`SmallVocabulary.lopezEscobar_iff`), the **relative pullbacks**
  (`SmallVocabulary.sentence_pullback_of_iso_compatible`, `…_on_antichain`), **Cantor recovery**
  (`SmallVocabulary.sentences_recover_cantor`), and **observable recovery and encoding**
  (`SmallVocabulary.sentences_recover_observable`, `…_encode_observable`), for `L`.
* **Thinness**: Cantor antichains and thinness transfer along `code`
  (`hasCantorAntichainOn_image_code_iff`, `isThinOn_image_code_iff`), giving the spectrum and
  splits endpoints for `L` (`SmallVocabulary.isThinOn_of_countable_sentence_spectra`,
  `SmallVocabulary.isThinOn_of_countable_sentence_splits`, and the sentence-specific corollary).

Names coincide with the small-universe originals inside the `SmallVocabulary` namespace; the
originals are referred to fully qualified.
-/

universe u v w x y

namespace FirstOrder.Language.SmallVocabulary

open MeasureTheory Set

variable (L : Language.{u, v}) [L.IsRelational] [Countable (Σ n, L.Relations n)]

/-! ### Truth sequences -/

/-- The lifted sentence list. -/
noncomputable def liftList (θ : ℕ → (lang L).Sentenceω) : ℕ → L.Sentenceω :=
  fun n => liftFormula L (θ n)

/-- **Truth sequences through the presentation.** -/
theorem sentenceTheory_code (θ : ℕ → (lang L).Sentenceω) (c : StructureSpace L) :
    sentenceTheory θ (code L c) = sentenceTheory (liftList L θ) c := by
  funext n
  exact decide_eq_decide.mpr (code_mem_modelsOf_iff L c (θ n))

theorem sentenceTheory_image_code (θ : ℕ → (lang L).Sentenceω) (C : Set (StructureSpace L)) :
    sentenceTheory θ '' (code L '' C) = sentenceTheory (liftList L θ) '' C := by
  rw [Set.image_image]
  exact Set.image_congr fun c _ => sentenceTheory_code L θ c

omit [Countable (Σ n, L.Relations n)] in
/-- Membership in `ModelsOf` is realization of the sentence in the decoded structure (the empty
valuation is unique). -/
theorem mem_modelsOf_iff_realize (c : StructureSpace L) (φ : L.Sentenceω) :
    c ∈ ModelsOf φ ↔ @Sentenceω.Realize L φ ℕ c.toStructure := by
  change @BoundedFormulaω.Realize L ℕ c.toStructure Empty 0 φ Empty.elim Fin.elim0 ↔
    @BoundedFormulaω.Realize L ℕ c.toStructure Empty 0 φ Empty.elim _
  exact iff_of_eq (congrArg (@BoundedFormulaω.Realize L ℕ c.toStructure Empty 0 φ Empty.elim)
    (Subsingleton.elim _ _))

/-- **Equal truth sequences from agreement on the lifted sentences**: two codes whose decoded
structures satisfy the same lifted sentences have the same truth sequence along the list. -/
theorem sentenceTheory_code_eq_of_agree (θ : ℕ → (lang L).Sentenceω) (c d : StructureSpace L)
    (h : ∀ n, (@Sentenceω.Realize L (liftFormula L (θ n)) ℕ c.toStructure ↔
      @Sentenceω.Realize L (liftFormula L (θ n)) ℕ d.toStructure)) :
    sentenceTheory θ (code L c) = sentenceTheory θ (code L d) := by
  rw [sentenceTheory_code, sentenceTheory_code]
  funext n
  apply decide_eq_decide.mpr
  rw [mem_modelsOf_iff_realize, mem_modelsOf_iff_realize]
  exact h n

/-! ### Sets of codes -/

omit [L.IsRelational] in
theorem image_code_eq_preimage_decode (B : Set (StructureSpace L)) :
    code L '' B = decode L ⁻¹' B := by
  ext c
  constructor
  · rintro ⟨b, hb, rfl⟩
    show decode L (code L b) ∈ B
    rwa [decode_code]
  · intro h
    exact ⟨decode L c, h, code_decode L c⟩

omit [L.IsRelational] in
theorem measurableSet_image_code_iff (B : Set (StructureSpace L)) :
    MeasurableSet (code L '' B) ↔ MeasurableSet B := by
  rw [image_code_eq_preimage_decode]
  refine ⟨fun h => ?_, fun h => h.preimage (measurable_decode L)⟩
  have := h.preimage (measurable_code L)
  rwa [Set.preimage_preimage, show (fun c => decode L (code L c)) = id from funext (decode_code L),
    Set.preimage_id] at this

theorem isomorphismInvariant_image_code_iff (B : Set (StructureSpace L)) :
    IsomorphismInvariant (code L '' B) ↔ IsomorphismInvariant B := by
  constructor
  · intro h a b hab
    have := h (code L a) (code L b) ((iso_code_iff L a b).mpr hab)
    rwa [(code_injective L).mem_set_image, (code_injective L).mem_set_image] at this
  · intro h c d hcd
    rw [← code_decode L c, ← code_decode L d] at hcd ⊢
    rw [(code_injective L).mem_set_image, (code_injective L).mem_set_image]
    exact h _ _ ((iso_code_iff L _ _).mp hcd)

/-! ### López–Escobar and the relative pullbacks -/

/-- **López–Escobar for `L`.** -/
theorem lopezEscobar_iff {B : Set (StructureSpace L)} :
    (MeasurableSet B ∧ IsomorphismInvariant B) ↔ ∃ φ : L.Sentenceω, B = ModelsOf φ := by
  constructor
  · rintro ⟨hB, hinv⟩
    obtain ⟨ψ, hψ⟩ := FirstOrder.Language.lopezEscobar_iff.mp
      ⟨(measurableSet_image_code_iff L B).mpr hB, (isomorphismInvariant_image_code_iff L B).mpr hinv⟩
    refine ⟨liftFormula L ψ, ?_⟩
    rw [modelsOf_liftFormula, ← hψ, (code_injective L).preimage_image]
  · rintro ⟨φ, rfl⟩
    exact ⟨modelsOf_measurableSet φ, isomorphismInvariant_modelsOf φ⟩

/-- **Relative López–Escobar for `L`.** -/
theorem sentence_pullback_of_iso_compatible {X : Type x} [MeasurableSpace X]
    [StandardBorelSpace X] (f : X → StructureSpace L) (hf : Measurable f)
    (U : Set X) (hU : MeasurableSet U)
    (hiso : ∀ x y, (structureIsoSetoid L).r (f x) (f y) → (x ∈ U ↔ y ∈ U)) :
    ∃ θ : L.Sentenceω, ∀ x, f x ∈ ModelsOf θ ↔ x ∈ U := by
  obtain ⟨ψ, hψ⟩ := FirstOrder.Language.sentence_pullback_of_iso_compatible (code L ∘ f)
    ((measurable_code L).comp hf) U hU
    (fun x y h => hiso x y ((iso_code_iff L _ _).mp h))
  exact ⟨liftFormula L ψ, fun x => by rw [← code_mem_modelsOf_iff]; exact hψ x⟩

/-- **Pullback on an antichain for `L`.** -/
theorem sentence_pullback_on_antichain {X : Type x} [MeasurableSpace X]
    [StandardBorelSpace X] (f : X → StructureSpace L) (hf : Measurable f)
    (hanti : ∀ x y, x ≠ y → ¬ (structureIsoSetoid L).r (f x) (f y))
    (U : Set X) (hU : MeasurableSet U) :
    ∃ θ : L.Sentenceω, ∀ x, f x ∈ ModelsOf θ ↔ x ∈ U :=
  sentence_pullback_of_iso_compatible L f hf U hU fun x y h => by
    by_contra hne
    exact hanti x y (fun hxy => hne (hxy ▸ Iff.rfl)) h

/-! ### Cantor and observable recovery -/

/-- **Sentences recover the Cantor parameter, for `L`.** -/
theorem sentences_recover_cantor (f : (ℕ → Bool) → StructureSpace L) (hf : Measurable f)
    (hanti : ∀ x y, x ≠ y → ¬ (structureIsoSetoid L).r (f x) (f y)) :
    ∃ θ : ℕ → L.Sentenceω, ∀ x n, f x ∈ ModelsOf (θ n) ↔ x n = true := by
  obtain ⟨ψ, hψ⟩ := FirstOrder.Language.sentences_recover_cantor (code L ∘ f)
    ((measurable_code L).comp hf) (fun x y hxy h => hanti x y hxy ((iso_code_iff L _ _).mp h))
  exact ⟨liftList L ψ, fun x n => by
    show f x ∈ ModelsOf (liftFormula L (ψ n)) ↔ _
    rw [← code_mem_modelsOf_iff]; exact hψ x n⟩

/-- **Observable recovery for `L`.** -/
theorem sentences_recover_observable {X : Type x} [MeasurableSpace X] [StandardBorelSpace X]
    (f : X → StructureSpace L) (hf : Measurable f) (p : X → (ℕ → Bool)) (hp : Measurable p)
    (hiso : ∀ x y, (structureIsoSetoid L).r (f x) (f y) → p x = p y) :
    ∃ θ : ℕ → L.Sentenceω, ∀ x, sentenceTheory θ (f x) = p x := by
  obtain ⟨ψ, hψ⟩ := FirstOrder.Language.sentences_recover_observable (code L ∘ f)
    ((measurable_code L).comp hf) p hp (fun x y h => hiso x y ((iso_code_iff L _ _).mp h))
  exact ⟨liftList L ψ, fun x => by rw [← sentenceTheory_code]; exact hψ x⟩

/-- **Observable encoding for `L`.** -/
theorem sentences_encode_observable {X : Type x} {Y : Type y} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [MeasurableSpace.CountablySeparated Y]
    (f : X → StructureSpace L) (hf : Measurable f) (p : X → Y) (hp : Measurable p)
    (hiso : ∀ x y, (structureIsoSetoid L).r (f x) (f y) → p x = p y) :
    ∃ (e : Y → (ℕ → Bool)) (θ : ℕ → L.Sentenceω),
      Measurable e ∧ Function.Injective e ∧ ∀ x, sentenceTheory θ (f x) = e (p x) := by
  obtain ⟨e, ψ, he, hi, hψ⟩ := FirstOrder.Language.sentences_encode_observable (code L ∘ f)
    ((measurable_code L).comp hf) p hp (fun x y h => hiso x y ((iso_code_iff L _ _).mp h))
  exact ⟨e, liftList L ψ, he, hi, fun x => by rw [← sentenceTheory_code]; exact hψ x⟩

/-! ### Thinness -/

/-- Cantor antichains transfer along `code` in both directions. -/
theorem hasCantorAntichainOn_image_code_iff (C : Set (StructureSpace L)) :
    HasCantorAntichainOn (structureIsoSetoid (lang L)) (code L '' C) ↔
      HasCantorAntichainOn (structureIsoSetoid L) C := by
  constructor
  · rintro ⟨f, hf, hC, hanti⟩
    refine ⟨decode L ∘ f, (continuous_decode L).comp hf, fun x => ?_, fun x y hxy h => ?_⟩
    · obtain ⟨c, hc, hcx⟩ := hC x
      show decode L (f x) ∈ C
      rw [← hcx, decode_code]; exact hc
    · apply hanti x y hxy
      have := (iso_code_iff L _ _).mpr h
      rwa [Function.comp_apply, Function.comp_apply, code_decode, code_decode] at this
  · rintro ⟨f, hf, hC, hanti⟩
    exact ⟨code L ∘ f, (continuous_code L).comp hf, fun x => ⟨f x, hC x, rfl⟩,
      fun x y hxy h => hanti x y hxy ((iso_code_iff L _ _).mp h)⟩

/-- **Thinness transfers along `code`** in both directions. -/
theorem isThinOn_image_code_iff (C : Set (StructureSpace L)) :
    IsThinOn (structureIsoSetoid (lang L)) (code L '' C) ↔ IsThinOn (structureIsoSetoid L) C := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable (StructureSpace L)
  let := TopologicalSpace.upgradeIsCompletelyMetrizable (StructureSpace (lang L))
  constructor
  · intro h
    exact IsThinOn.of_no_cantorAntichain fun hc =>
      h.no_cantorAntichain ((hasCantorAntichainOn_image_code_iff L C).mpr hc)
  · intro h
    exact IsThinOn.of_no_cantorAntichain fun hc =>
      h.no_cantorAntichain ((hasCantorAntichainOn_image_code_iff L C).mp hc)

/-- **Countable sentence spectra give thinness, for `L`.** -/
theorem isThinOn_of_countable_sentence_spectra (C : Set (StructureSpace L))
    (hsmall : ∀ θ : ℕ → L.Sentenceω, (sentenceTheory θ '' C).Countable) :
    IsThinOn (structureIsoSetoid L) C := by
  rw [← isThinOn_image_code_iff]
  refine FirstOrder.Language.isThinOn_of_countable_sentence_spectra _ fun θ => ?_
  rw [sentenceTheory_image_code]
  exact hsmall _

/-- **Thinness from single-sentence splits, for `L`.** -/
theorem isThinOn_of_countable_sentence_splits (C : Set (StructureSpace L)) {Q : Type w}
    (classOf : C → Q) (truth : L.Sentenceω → Q → Prop)
    (htruth : ∀ θ c, truth θ (classOf c) ↔ c.1 ∈ ModelsOf θ)
    (hsplit : ∀ θ, ({q | truth θ q} : Set Q).Countable ∨
      ({q | ¬ truth θ q} : Set Q).Countable) :
    IsThinOn (structureIsoSetoid L) C :=
  isThinOn_of_countable_sentence_spectra L C
    (FirstOrder.Language.countable_sentenceTheory_image_of_splits C classOf truth htruth hsplit)

/-- The sentence-specific corollary for `L`. -/
theorem isThinOnNatModels_of_countable_sentence_splits (φ : L.Sentenceω) {Q : Type w}
    (classOf : ModelsOf φ → Q) (truth : L.Sentenceω → Q → Prop)
    (htruth : ∀ θ c, truth θ (classOf c) ↔ c.1 ∈ ModelsOf θ)
    (hsplit : ∀ θ, ({q | truth θ q} : Set Q).Countable ∨
      ({q | ¬ truth θ q} : Set Q).Countable) :
    φ.IsThinOnNatModels :=
  isThinOn_of_countable_sentence_splits L (ModelsOf φ) classOf truth htruth hsplit

end FirstOrder.Language.SmallVocabulary
