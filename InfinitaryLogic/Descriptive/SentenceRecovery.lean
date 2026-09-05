/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.InvariantSeparation
import InfinitaryLogic.Descriptive.StructureIsoSetoid

/-!
# Recovering Borel data by sentences

## Truth sequences

`sentenceTheory θ c` is the truth sequence of a countable list of sentences `θ` at the coded
structure `c`.  It is measurable (`measurable_sentenceTheory`) and isomorphism-invariant
(`sentenceTheory_eq_of_iso`).  These basics stay here, below any use of Silver: the spectrum
characterization (`Conditional/SentenceSpectrum.lean`) consumes them, and observable recovery
need not import it.

## Relative López–Escobar

`sentence_pullback_of_iso_compatible`: a Borel predicate on a standard Borel family of
structures that is constant on isomorphic outputs is the pullback of one sentence.  The proof
saturates the two images, separates them by `sentence_separates_analytic_classes`, and reads the
sentence back along the family.  The antichain form `sentence_pullback_on_antichain`, where
isomorphism compatibility is automatic, is a corollary.

## Cantor parameters

On a Borel Cantor isomorphism antichain, countably many sentences recover every parameter bit
(`sentences_recover_cantor`, `sentenceTheory_eq_parameter`).  Hence a class on which every
countable sentence list has countably many realized truth sequences carries no such antichain
(`no_antichain_of_countable_sentence_spectra`), and a sentence with that property is thin
(`thin_of_countable_sentence_spectra`).  The converse needs Silver and lives in
`Conditional/SentenceSpectrum.lean`.

## Classical background

López–Escobar is Marker, *Lectures on Infinitary Model Theory* (Cambridge, 2016),
Theorem 4.3.7; Gao, *Invariant Descriptive Set Theory* (CRC Press, 2009), Theorem 11.3.6, is
an alternative exposition.  The relative form on a Borel family and the recovery of Cantor
parameters are derived here from invariant separation; these formulations are not claimed to
occur in the sources.
-/

namespace FirstOrder.Language

open MeasureTheory Set

variable {L : Language.{0, 0}} [L.IsRelational] [Countable (Σ n, L.Relations n)]

/-! ## Truth sequences -/

/-- The truth sequence of a countable list of sentences at a coded structure. -/
noncomputable def sentenceTheory (θ : ℕ → L.Sentenceω) (c : StructureSpace L) : ℕ → Bool :=
  fun n => @decide (c ∈ ModelsOf (θ n)) (Classical.propDecidable _)

omit [Countable (Σ n, L.Relations n)] in
theorem measurable_sentenceTheory (θ : ℕ → L.Sentenceω) : Measurable (sentenceTheory θ) := by
  apply measurable_pi_lambda
  intro n
  apply measurable_to_bool
  convert modelsOf_measurableSet (θ n) using 1
  ext c
  simp [sentenceTheory]

omit [Countable (Σ n, L.Relations n)] in
theorem sentenceTheory_eq_of_iso (θ : ℕ → L.Sentenceω) {c d : StructureSpace L}
    (h : (structureIsoSetoid L).r c d) : sentenceTheory θ c = sentenceTheory θ d := by
  funext n
  simp only [sentenceTheory]
  congr 1
  exact propext ((isomorphismInvariant_modelsOf (θ n)) c d h)

/-! ## Relative López–Escobar -/

/-- **Relative López–Escobar.**  A Borel predicate on a standard Borel family of structures that
respects isomorphism of the outputs is the pullback of one sentence.  No antichain is required,
and the family may have repetitions. -/
theorem sentence_pullback_of_iso_compatible {X : Type} [MeasurableSpace X]
    [StandardBorelSpace X] (f : X → StructureSpace L) (hf : Measurable f)
    (U : Set X) (hU : MeasurableSet U)
    (hiso : ∀ x y, (structureIsoSetoid L).r (f x) (f y) → (x ∈ U ↔ y ∈ U)) :
    ∃ θ : L.Sentenceω, ∀ x, f x ∈ ModelsOf θ ↔ x ∈ U := by
  let A := saturation (f '' U)
  let B := saturation (f '' Uᶜ)
  have hA : AnalyticSet A := analyticSet_saturation (hU.analyticSet_image hf)
  have hB : AnalyticSet B := analyticSet_saturation (hU.compl.analyticSet_image hf)
  have hd : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro z hzA hzB
    obtain ⟨σ, a, ⟨x, hx, rfl⟩, hσ⟩ := mem_saturation.mp hzA
    obtain ⟨τ, b, ⟨y, hy, rfl⟩, hτ⟩ := mem_saturation.mp hzB
    apply hy
    apply (hiso x y ?_).mp hx
    apply (orbit_iff_iso (f x) (f y)).mp
    refine ⟨τ⁻¹ * σ, ?_⟩
    rw [mul_smul, hσ, ← hτ, inv_smul_smul]
  obtain ⟨θ, hpos, hneg⟩ :=
    sentence_separates_analytic_classes hA hB (saturation_invariant _) hd
  refine ⟨θ, fun x => ⟨?_, ?_⟩⟩
  · intro hθ
    by_contra hx
    exact Set.disjoint_left.mp hneg (subset_saturation _ ⟨x, hx, rfl⟩) hθ
  · intro hx
    exact hpos (subset_saturation _ ⟨x, hx, rfl⟩)

/-- On an isomorphism antichain every Borel predicate is the pullback of one sentence:
compatibility with isomorphism is automatic. -/
theorem sentence_pullback_on_antichain {X : Type} [MeasurableSpace X]
    [StandardBorelSpace X] (f : X → StructureSpace L) (hf : Measurable f)
    (hanti : ∀ x y, x ≠ y → ¬ (structureIsoSetoid L).r (f x) (f y))
    (U : Set X) (hU : MeasurableSet U) :
    ∃ θ : L.Sentenceω, ∀ x, f x ∈ ModelsOf θ ↔ x ∈ U :=
  sentence_pullback_of_iso_compatible f hf U hU fun x y h => by
    by_contra hne
    exact hanti x y (fun hxy => hne (hxy ▸ Iff.rfl)) h

/-! ## Cantor parameters -/

/-- Cantor space is Polish: second countable and completely metrizable, from the countable
product instances.  Local to this file. -/
private theorem polishSpace_cantor : PolishSpace (ℕ → Bool) :=
  PolishSpace.mk

attribute [local instance] polishSpace_cantor

/-- **Sentences recover the Cantor parameter** on a Borel isomorphism antichain: each bit is the
truth of one sentence. -/
theorem sentences_recover_cantor (f : (ℕ → Bool) → StructureSpace L) (hf : Measurable f)
    (hanti : ∀ x y, x ≠ y → ¬ (structureIsoSetoid L).r (f x) (f y)) :
    ∃ θ : ℕ → L.Sentenceω, ∀ x n, f x ∈ ModelsOf (θ n) ↔ x n = true := by
  have h (n : ℕ) : ∃ θ : L.Sentenceω, ∀ x, f x ∈ ModelsOf θ ↔ x n = true :=
    sentence_pullback_on_antichain f hf hanti {x | x n = true}
      ((isClosed_eq (continuous_apply n) continuous_const).measurableSet)
  choose θ hθ using h
  exact ⟨θ, fun x n => hθ n x⟩

omit [Countable (Σ n, L.Relations n)] in
theorem sentenceTheory_eq_parameter (f : (ℕ → Bool) → StructureSpace L) (θ : ℕ → L.Sentenceω)
    (hθ : ∀ x n, f x ∈ ModelsOf (θ n) ↔ x n = true) (x : ℕ → Bool) :
    sentenceTheory θ (f x) = x := by
  funext n
  simp only [sentenceTheory, hθ]
  cases x n <;> rfl

/-- A class on which every countable sentence list has countably many realized truth sequences
carries no Borel Cantor isomorphism antichain. -/
theorem no_antichain_of_countable_sentence_spectra (C : Set (StructureSpace L))
    (hsmall : ∀ θ : ℕ → L.Sentenceω, (sentenceTheory θ '' C).Countable)
    (f : (ℕ → Bool) → StructureSpace L) (hf : Measurable f) (hC : ∀ x, f x ∈ C) :
    ¬ (∀ x y, x ≠ y → ¬ (structureIsoSetoid L).r (f x) (f y)) := by
  intro hanti
  obtain ⟨θ, hθ⟩ := sentences_recover_cantor f hf hanti
  have hsub : Set.univ ⊆ sentenceTheory θ '' C := fun x _ =>
    ⟨f x, hC x, sentenceTheory_eq_parameter f θ hθ x⟩
  have : Countable (ℕ → Bool) := Set.countable_univ_iff.mp ((hsmall θ).mono hsub)
  obtain ⟨g, hg⟩ := exists_surjective_nat (ℕ → Bool)
  obtain ⟨n, hn⟩ := hg fun k => !(g k k)
  have he := congrFun hn n
  simp at he

/-- **Countable sentence spectra give thinness**: the sufficient direction, without Silver. -/
theorem thin_of_countable_sentence_spectra (φ : L.Sentenceω)
    (hsmall : ∀ θ : ℕ → L.Sentenceω, (sentenceTheory θ '' ModelsOf φ).Countable) :
    φ.IsThinOnNatModels := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable (StructureSpace L)
  intro hperfect
  obtain ⟨f, hf, hm, ha⟩ := hperfect.hasCantorAntichainOn
  exact no_antichain_of_countable_sentence_spectra (ModelsOf φ) hsmall f hf.measurable hm ha

end FirstOrder.Language
