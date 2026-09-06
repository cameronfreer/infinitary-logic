/-
Regression guard for the fragment-spectrum characterization of thinness.

`thin_iff_countable_fragment_spectra` must admit the empty class with no hidden premise; the
empty fragment (empty slices) must have countable spectra on every class; at arity zero the
characterization must recover countable sentence spectra from thinness; and the headline
declarations must use only the standard axioms.

Run with: lake env lean scripts/check_fragment_spectrum_thin_regressions.lean
-/
import InfinitaryLogic.Conditional.FragmentSpectrumThin

open Lean FirstOrder Language MeasureTheory

variable {L : Language.{0, 0}} [L.IsRelational] [Countable (Σ n, L.Relations n)]

theorem empty_class_regression : IsThinOn (structureIsoSetoid L) ∅ :=
  (Fragment.thin_iff_countable_fragment_spectra ∅ MeasurableSet.empty).mpr fun F _ n => by
    rw [F.typeSpectrum_empty n]
    exact Set.countable_empty

omit [Countable (Σ n, L.Relations n)] in
/-- The empty fragment has countable spectra on every class at every arity: its slices are
empty, so there is at most one type. -/
theorem empty_slice_regression (C : Set (StructureSpace L)) (n : ℕ) :
    ((Fragment.generated (∅ : Set (Σ n, L.BoundedFormulaω Empty n))).typeSpectrum n
      C).Countable := by
  have hgen : ∀ p : Σ n, L.BoundedFormulaω Empty n,
      ¬ Fragment.GeneratedFrom (∅ : Set (Σ n, L.BoundedFormulaω Empty n)) p := by
    intro p h
    induction h with
    | base h => exact h
    | imp_left _ ih => exact ih
    | imp_right _ ih => exact ih
    | all_body _ ih => exact ih
    | iInf_comp _ _ ih => exact ih
    | iSup_comp _ _ ih => exact ih
  have hempty : ∀ φ : (Fragment.generated (∅ : Set (Σ n, L.BoundedFormulaω Empty n))).slice n,
      False := fun φ => hgen _ φ.2
  have : Subsingleton ((Fragment.generated (∅ : Set (Σ n, L.BoundedFormulaω Empty n))).slice n →
      Bool) := ⟨fun f g => funext fun φ => (hempty φ).elim⟩
  exact Set.to_countable _

/-- Arity zero: thinness gives countable sentence spectra through the fragment characterization,
recovering the sentence interface. -/
theorem arity_zero_regression (C : Set (StructureSpace L)) (hC : MeasurableSet C)
    (hthin : IsThinOn (structureIsoSetoid L) C) (θ : ℕ → L.Sentenceω) :
    (sentenceTheory θ '' C).Countable :=
  (thin_iff_countable_sentence_spectra C hC).mp hthin θ

def headline : List Name :=
  [`FirstOrder.Language.Fragment.measurableSet_sameRealizedSpectrum,
   `FirstOrder.Language.Fragment.sameRealizedSpectrum_of_iso,
   `FirstOrder.Language.Fragment.fragmentSpectrum_countable_or_cantor,
   `FirstOrder.Language.Fragment.thin_iff_countable_fragment_spectra,
   `FirstOrder.Language.Sentenceω.isThinOnNatModels_iff_countable_fragment_spectra,
   `empty_class_regression, `empty_slice_regression, `arity_zero_regression]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "fragment-spectrum thinness guard: OK (empty class, empty slices, arity zero; headline \
    declarations on standard axioms)"
