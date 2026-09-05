/-
Regression guard for the sentence-spectrum characterization of thinness.

`thin_iff_countable_sentence_spectra` must admit the empty class and an arbitrary singleton
class, without assuming isomorphism-invariance or nonemptiness, a repeated constant family must be
admitted by observable recovery, and the headline declarations must use
only the standard axioms.

Run with: lake env lean scripts/check_sentence_spectrum_regressions.lean
-/
import InfinitaryLogic.Conditional.SentenceSpectrum
import InfinitaryLogic.Descriptive.FragmentTail

open Lean FirstOrder Language MeasureTheory

variable {L : Language.{0, 0}} [L.IsRelational] [Countable (Σ n, L.Relations n)]

theorem empty_class_regression : IsThinOn (structureIsoSetoid L) ∅ := by
  apply (thin_iff_countable_sentence_spectra ∅ MeasurableSet.empty).mpr
  intro θ
  exact Set.countable_empty.image (sentenceTheory θ)

/-- An arbitrary singleton, with no invariance assumed: the characterization applies as is. -/
theorem singleton_class_regression (c : StructureSpace L) :
    IsThinOn (structureIsoSetoid L) {c} := by
  apply (thin_iff_countable_sentence_spectra {c} (measurableSet_singleton c)).mpr
  intro θ
  exact (Set.countable_singleton c).image (sentenceTheory θ)

/-- A constant family with repetitions is admitted: no antichain premise. -/
theorem repeated_family_regression (c : StructureSpace L) (p : ℕ → Bool) :
    ∃ θ : ℕ → L.Sentenceω, ∀ _x : ℕ, sentenceTheory θ c = p :=
  sentences_recover_observable (fun _ : ℕ => c) measurable_const
    (fun _ : ℕ => p) measurable_const (fun _ _ _ => rfl)

def headline : List Name :=
  [`FirstOrder.Language.sentences_recover_observable,
   `FirstOrder.Language.sentences_encode_observable,
   `FirstOrder.Language.sentence_classification_iff_borel_classification,
   `FirstOrder.Language.countable_iso_classes_of_thin_borel_classifiable,
   `FirstOrder.Language.antichain_rank_bounded_of_fragment_tails,
   `FirstOrder.Language.fragment_tails_of_eventual_sentence_decision,
   `FirstOrder.Language.ThinRankAnalysis.bounded_refined_of_fragment_tails,
   `repeated_family_regression,
   `FirstOrder.Language.invariant_analytic_separation,
   `FirstOrder.Language.sentence_separates_analytic_classes,
   `FirstOrder.Language.sentence_pullback_of_iso_compatible,
   `FirstOrder.Language.sentences_recover_cantor,
   `FirstOrder.Language.thin_of_countable_sentence_spectra,
   `FirstOrder.Language.sentence_spectrum_countable_or_cantor,
   `FirstOrder.Language.thin_iff_countable_sentence_spectra,
   `FirstOrder.Language.Sentenceω.isThinOnNatModels_iff_countable_sentence_spectra,
   `empty_class_regression, `singleton_class_regression]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "sentence-spectrum regression guard: OK (empty and arbitrary singleton classes \
    admitted without an invariance premise; repeated families admitted; headline declarations \
    on standard axioms)"
