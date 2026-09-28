/-
Regression guard for descriptive transport through the small-vocabulary presentation
(`Descriptive/SmallVocabularyTransport.lean`), on a `Language.{0, 1}` signature with nullary symbols.

Checked: the **truth-sequence equation** on a **repeated list**; **thinness transfer** along `code`
in **both directions**; **López–Escobar** for the higher-universe language, both directions applied;
**Cantor recovery**, **observable recovery**, and **observable encoding** applied to a concrete
measurable family; **actual thinness composition**: the splits endpoint on a singleton class with a
**nonsurjective presentation** in `Bool`, the spectrum endpoint on the empty class, and the
sentence-specific corollary as a conditional API composition.  Headline declarations use only the
standard axioms.

Run with: lake env lean scripts/check_small_vocabulary_transport_regressions.lean
-/
import InfinitaryLogic.Descriptive.SmallVocabularyTransport

open Lean FirstOrder Language SmallVocabulary

/-- A `Type 1` relational signature with a symbol at every arity, including arity `0`. -/
def bigLang : Language.{0, 1} where
  Functions _ := Empty
  Relations n := ULift.{1} (Fin (n + 1))

instance : bigLang.IsRelational := fun _ => inferInstanceAs (IsEmpty Empty)

instance : Countable (Σ n, bigLang.Relations n) :=
  inferInstanceAs (Countable (Σ n, ULift.{1} (Fin (n + 1))))

/-- **Repeated list** through the truth-sequence equation. -/
theorem repeated_list_regression (ψ : (lang bigLang).Sentenceω) (c : StructureSpace bigLang) :
    sentenceTheory (fun _ : ℕ => ψ) (code bigLang c) =
      sentenceTheory (fun _ : ℕ => liftFormula bigLang ψ) c :=
  sentenceTheory_code bigLang _ c

/-- **Thinness transfer**, both directions applied. -/
theorem thin_transfer_regression (C : Set (StructureSpace bigLang)) :
    (IsThinOn (structureIsoSetoid bigLang) C →
      IsThinOn (structureIsoSetoid (lang bigLang)) (code bigLang '' C)) ∧
    (IsThinOn (structureIsoSetoid (lang bigLang)) (code bigLang '' C) →
      IsThinOn (structureIsoSetoid bigLang) C) :=
  ⟨(isThinOn_image_code_iff bigLang C).mpr, (isThinOn_image_code_iff bigLang C).mp⟩

/-- **López–Escobar** for the higher-universe language, both directions. -/
theorem lopez_escobar_regression (B : Set (StructureSpace bigLang)) :
    ((MeasurableSet B ∧ IsomorphismInvariant B) → ∃ φ : bigLang.Sentenceω, B = ModelsOf φ) ∧
    ((∃ φ : bigLang.Sentenceω, B = ModelsOf φ) → MeasurableSet B ∧ IsomorphismInvariant B) :=
  ⟨(SmallVocabulary.lopezEscobar_iff bigLang).mp, (SmallVocabulary.lopezEscobar_iff bigLang).mpr⟩

/-- **Cantor recovery** on a concrete family. -/
theorem cantor_recovery_regression (f : (ℕ → Bool) → StructureSpace bigLang) (hf : Measurable f)
    (hanti : ∀ x y, x ≠ y → ¬ (structureIsoSetoid bigLang).r (f x) (f y)) :
    ∃ θ : ℕ → bigLang.Sentenceω, ∀ x n, f x ∈ ModelsOf (θ n) ↔ x n = true :=
  SmallVocabulary.sentences_recover_cantor bigLang f hf hanti

/-- **Observable recovery and encoding** on a constant family (repetitions, no antichain). -/
theorem observable_regression (c : StructureSpace bigLang) (p : ℕ → Bool) (b : Bool) :
    (∃ θ : ℕ → bigLang.Sentenceω, ∀ _x : ℕ, sentenceTheory θ c = p) ∧
    (∃ (e : Bool → (ℕ → Bool)) (θ : ℕ → bigLang.Sentenceω), Measurable e ∧ Function.Injective e ∧
      ∀ _x : ℕ, sentenceTheory θ c = e b) :=
  ⟨SmallVocabulary.sentences_recover_observable bigLang (fun _ : ℕ => c) measurable_const
      (fun _ : ℕ => p) measurable_const (fun _ _ _ => rfl),
    SmallVocabulary.sentences_encode_observable bigLang (fun _ : ℕ => c) measurable_const
      (fun _ : ℕ => b) measurable_const (fun _ _ _ => rfl)⟩

/-- The nonsurjective presentation of a singleton class in `Bool`. -/
def constPres (c : StructureSpace bigLang) : ({c} : Set (StructureSpace bigLang)) → Bool :=
  fun _ => true

theorem constPres_not_surjective (c : StructureSpace bigLang) :
    ¬ Function.Surjective (constPres c) :=
  fun h => by obtain ⟨_, hx⟩ := h false; simp [constPres] at hx

/-- **Actual thinness composition** through the higher-universe splits endpoint on the
nonsurjective presentation, and the spectrum endpoint on the empty class. -/
theorem thinness_composition_regression (c : StructureSpace bigLang) :
    IsThinOn (structureIsoSetoid bigLang) {c} ∧ IsThinOn (structureIsoSetoid bigLang) ∅ :=
  ⟨SmallVocabulary.isThinOn_of_countable_sentence_splits bigLang {c} (constPres c)
      (fun θ _ => c ∈ ModelsOf θ)
      (fun θ d => by have : d.1 = c := d.2; simp [this])
      (fun _ => Or.inl (Set.to_countable _)),
    SmallVocabulary.isThinOn_of_countable_sentence_spectra bigLang ∅
      (fun θ => Set.countable_empty.image (sentenceTheory θ))⟩

/-- **Conditional API composition** for the sentence-specific corollary. -/
theorem sentence_endpoint_regression (φ : bigLang.Sentenceω)
    (hdec : ∀ θ : bigLang.Sentenceω, ∀ c ∈ ModelsOf φ,
      (c ∈ ModelsOf θ ↔ ∀ d ∈ ModelsOf φ, d ∈ ModelsOf θ)) :
    φ.IsThinOnNatModels :=
  SmallVocabulary.isThinOnNatModels_of_countable_sentence_splits bigLang φ (fun _ => ())
    (fun θ _ => ∀ c ∈ ModelsOf φ, c ∈ ModelsOf θ) (fun θ c => (hdec θ c.1 c.2).symm)
    (fun _ => Or.inl (Set.to_countable _))

/-! ### Axiom hygiene -/

def headline : List Name :=
  [`FirstOrder.Language.SmallVocabulary.sentenceTheory_code,
   `FirstOrder.Language.SmallVocabulary.sentenceTheory_code_eq_of_agree,
   `FirstOrder.Language.SmallVocabulary.mem_modelsOf_iff_realize,
   `FirstOrder.Language.SmallVocabulary.measurableSet_image_code_iff,
   `FirstOrder.Language.SmallVocabulary.isomorphismInvariant_image_code_iff,
   `FirstOrder.Language.SmallVocabulary.lopezEscobar_iff,
   `FirstOrder.Language.SmallVocabulary.sentence_pullback_of_iso_compatible,
   `FirstOrder.Language.SmallVocabulary.sentence_pullback_on_antichain,
   `FirstOrder.Language.SmallVocabulary.sentences_recover_cantor,
   `FirstOrder.Language.SmallVocabulary.sentences_recover_observable,
   `FirstOrder.Language.SmallVocabulary.sentences_encode_observable,
   `FirstOrder.Language.SmallVocabulary.isThinOn_image_code_iff,
   `FirstOrder.Language.SmallVocabulary.isThinOn_of_countable_sentence_spectra,
   `FirstOrder.Language.SmallVocabulary.isThinOn_of_countable_sentence_splits,
   `FirstOrder.Language.SmallVocabulary.isThinOnNatModels_of_countable_sentence_splits,
   `FirstOrder.Language.sentenceTheory, `FirstOrder.Language.measurable_sentenceTheory,
   `FirstOrder.Language.sentenceTheory_eq_of_iso,
   `FirstOrder.Language.countable_sentenceTheory_image_of_splits,
   `repeated_list_regression, `thin_transfer_regression, `lopez_escobar_regression,
   `cantor_recovery_regression, `observable_regression, `constPres_not_surjective,
   `thinness_composition_regression, `sentence_endpoint_regression]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "small-vocabulary transport regression guard: OK (Language.{0, 1} with nullary symbols: \
    repeated list, thinness transfer both ways, López–Escobar both ways, Cantor recovery, \
    observable recovery and encoding, thinness composition on a nonsurjective presentation and \
    the empty class, conditional sentence-specific composition; headline declarations on \
    standard axioms)"
