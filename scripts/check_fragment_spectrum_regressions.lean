/-
Regression guard for pointed fragment types and spectra.

The counting theorem must count realized types across the selected class from coverage and
determination alone, and the API must admit: arity zero (the sentence interface), the empty
fragment (empty slices), the empty class, one isomorphism class, and repeated tuple
coordinates.  No isomorphism-invariance of the class is assumed anywhere.  Headline
declarations use only the standard axioms.

Run with: lake env lean scripts/check_fragment_spectrum_regressions.lean
-/
import InfinitaryLogic.Descriptive.FragmentSpectrum

open Lean FirstOrder Language MeasureTheory

variable {L : Language.{0, 0}} [L.IsRelational]

/-- The empty class has empty spectrum at every arity. -/
theorem empty_class_regression (F : Fragment L) (n : ℕ) : F.typeSpectrum n ∅ = ∅ :=
  F.typeSpectrum_empty n

/-- An arbitrary singleton class, no invariance assumed, has countable spectrum at every arity. -/
theorem singleton_regression (F : Fragment L) (n : ℕ) (c : StructureSpace L) :
    (F.typeSpectrum n {c}).Countable :=
  F.typeSpectrum_singleton_countable n c

/-- One isomorphism class has countable spectrum at every arity. -/
theorem isoClass_regression (F : Fragment L) (n : ℕ) (c : StructureSpace L) :
    (F.typeSpectrum n {d | (structureIsoSetoid L).r c d}).Countable :=
  F.typeSpectrum_isoClass_countable n c

/-- Repeated coordinates: the tuple `(a, a)` is admitted and its type is in the spectrum. -/
theorem repeated_coordinates_regression (F : Fragment L) (c : StructureSpace L) (a : ℕ) :
    F.pointedType c ![a, a] ∈ F.typeSpectrum 2 {c} :=
  Fragment.mem_typeSpectrum.mpr ⟨c, rfl, ![a, a], rfl⟩

/-- Arity zero is the sentence interface. -/
theorem arity_zero_regression (F : Fragment L) (θ : ℕ → L.Sentenceω)
    (hθ : ∀ k, (⟨0, θ k⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ F) (c : StructureSpace L) :
    sentenceTheory θ c = fun k => F.pointedType c Fin.elim0 ⟨θ k, hθ k⟩ :=
  F.pointedType_zero_eq_sentenceTheory θ hθ c

omit [L.IsRelational] in
/-- Nothing is generated from nothing. -/
theorem generatedFrom_empty (p : Σ n, L.BoundedFormulaω Empty n) :
    ¬ Fragment.GeneratedFrom (∅ : Set (Σ n, L.BoundedFormulaω Empty n)) p := by
  intro h
  induction h with
  | base h => exact h
  | imp_left _ ih => exact ih
  | imp_right _ ih => exact ih
  | all_body _ ih => exact ih
  | iInf_comp _ _ ih => exact ih
  | iSup_comp _ _ ih => exact ih

/-- Empty slices are admitted: the empty fragment has countable spectrum on ANY class, from the
one-description cover `⊤`, with determination vacuous on the empty slice. -/
theorem empty_fragment_regression (C : Set (StructureSpace L)) (n : ℕ) :
    ((Fragment.generated (∅ : Set (Σ n, L.BoundedFormulaω Empty n))).typeSpectrum n
      C).Countable := by
  refine Fragment.typeSpectrum_countable_of_determining_cover _ C
    (fun _ : Unit => (BoundedFormulaω.falsum : L.BoundedFormulaω Empty n).not) ?_ ?_
  · intro c _ a
    refine ⟨(), ?_⟩
    show @BoundedFormulaω.Realize L ℕ c.toStructure Empty n (BoundedFormulaω.falsum.not)
      Empty.elim a
    simp
  · intro _ _ _ _ _ _ _ _ _ φ
    exact absurd φ.2 (generatedFrom_empty _)


def headline : List Name :=
  [`Set.countable_image_of_determining_cover,
   `FirstOrder.Language.Fragment.realizedType_equiv,
   `FirstOrder.Language.Fragment.realizedType_reindex,
   `FirstOrder.Language.Fragment.pointedType_iso,
   `FirstOrder.Language.Fragment.typeSpectrum_countable_of_determining_cover,
   `FirstOrder.Language.Fragment.typeSpectrum_isoClass,
   `FirstOrder.Language.Fragment.measurable_pointedType,
   `FirstOrder.Language.Fragment.typeSpectrum_countable_iff_encoded,
   `empty_class_regression, `singleton_regression, `isoClass_regression,
   `repeated_coordinates_regression, `arity_zero_regression, `empty_fragment_regression]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "fragment-spectrum regression guard: OK (empty class, singleton, isomorphism class, \
    repeated coordinates, arity zero, and empty slices admitted; headline declarations on \
    standard axioms)"
