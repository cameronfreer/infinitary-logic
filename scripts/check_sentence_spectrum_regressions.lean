/-
Regression guard for the sentence-spectrum characterization of thinness.

`thin_iff_countable_sentence_spectra` must admit the empty class and a non-invariant singleton
class with no hidden nonemptiness or invariance premise, and the headline declarations must use
only the standard axioms.

Run with: lake env lean scripts/check_sentence_spectrum_regressions.lean
-/
import InfinitaryLogic.Conditional.SentenceSpectrum

open Lean FirstOrder Language MeasureTheory

variable {L : Language.{0, 0}} [L.IsRelational] [Countable (Σ n, L.Relations n)]

theorem empty_class_regression : IsThinOn (structureIsoSetoid L) ∅ := by
  apply (thin_iff_countable_sentence_spectra ∅ MeasurableSet.empty).mpr
  intro θ
  exact Set.countable_empty.image (sentenceTheory θ)

/-- A singleton is not isomorphism-invariant; the characterization still applies. -/
theorem singleton_class_regression (c : StructureSpace L) :
    IsThinOn (structureIsoSetoid L) {c} := by
  apply (thin_iff_countable_sentence_spectra {c} (measurableSet_singleton c)).mpr
  intro θ
  exact (Set.countable_singleton c).image (sentenceTheory θ)

def headline : List Name :=
  [`FirstOrder.Language.invariant_analytic_separation,
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
  logInfo "sentence-spectrum regression guard: OK (empty and non-invariant singleton classes \
    admitted; headline declarations on standard axioms)"
