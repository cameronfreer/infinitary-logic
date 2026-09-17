/-
Regression guard for the sentence-spectrum-to-isomorphism-classes corollaries.

The corollaries must compose with the determining-cover counting theorem and must admit the
empty class and overlapping descriptions.  The classification hypothesis stays an explicit
input in every regression: nothing here constructs a cover or a classification.  Headline
declarations use only the standard axioms.

Run with: lake env lean scripts/check_fragment_spectrum_classification.lean
-/
import InfinitaryLogic.Descriptive.FragmentSpectrumClassification

open Lean FirstOrder Language

variable {L : Language.{0, 0}} [L.IsRelational]

/-- **Empty class**: every hypothesis is vacuous and the quotient is countable. -/
theorem empty_class_regression (F : Fragment L) :
    Countable (Quotient (structureIsoSetoidRestrict L (∅ : Set (StructureSpace L)))) :=
  F.countable_isoQuotient_of_countable_sentenceSpectrum ∅
    (by rw [F.typeSpectrum_empty]; exact Set.countable_empty)
    (fun _ h => h.elim)

/-- **Composition through the counting theorem** with an arbitrary countable description family
and an explicitly assumed classification hypothesis. -/
theorem composition_regression (F : Fragment L) (C : Set (StructureSpace L))
    {E : Type} [Countable E] (χ : E → L.BoundedFormulaω Empty 0)
    (cover : ∀ c ∈ C, ∀ a : Fin 0 → ℕ, ∃ e, c ∈ ModelsOfBounded (χ e) Empty.elim a)
    (det : ∀ e, ∀ c ∈ C, ∀ d ∈ C, ∀ (a b : Fin 0 → ℕ),
      c ∈ ModelsOfBounded (χ e) Empty.elim a → d ∈ ModelsOfBounded (χ e) Empty.elim b →
      ∀ φ : F.slice 0,
        c ∈ ModelsOfBounded φ.1 Empty.elim a ↔ d ∈ ModelsOfBounded φ.1 Empty.elim b)
    (hclass : ∀ c ∈ C, ∀ d ∈ C,
      F.pointedType c Fin.elim0 = F.pointedType d Fin.elim0 → (structureIsoSetoid L).r c d) :
    Countable (Quotient (structureIsoSetoidRestrict L C)) :=
  F.countable_isoQuotient_of_determining_cover C χ cover det hclass

/-- **Overlapping descriptions**: two indices carrying the same description.  Coverage and
determination are inherited from a one-index family; the quotient stays countable. -/
theorem overlapping_descriptions_regression (F : Fragment L) (C : Set (StructureSpace L))
    (ψ : L.BoundedFormulaω Empty 0)
    (cover : ∀ c ∈ C, ∀ a : Fin 0 → ℕ, c ∈ ModelsOfBounded ψ Empty.elim a)
    (det : ∀ c ∈ C, ∀ d ∈ C, ∀ (a b : Fin 0 → ℕ),
      c ∈ ModelsOfBounded ψ Empty.elim a → d ∈ ModelsOfBounded ψ Empty.elim b →
      ∀ φ : F.slice 0,
        c ∈ ModelsOfBounded φ.1 Empty.elim a ↔ d ∈ ModelsOfBounded φ.1 Empty.elim b)
    (hclass : ∀ c ∈ C, ∀ d ∈ C,
      F.pointedType c Fin.elim0 = F.pointedType d Fin.elim0 → (structureIsoSetoid L).r c d) :
    Countable (Quotient (structureIsoSetoidRestrict L C)) :=
  F.countable_isoQuotient_of_determining_cover C (fun _ : Bool => ψ)
    (fun c hc a => ⟨true, cover c hc a⟩)
    (fun _ c hc d hd a b hca hdb => det c hc d hd a b hca hdb) hclass

/-- **One isomorphism class** satisfies the classification hypothesis outright, so any countable
sentence spectrum on it gives a countable quotient (it is a single class). -/
theorem isoClass_regression (F : Fragment L) (c : StructureSpace L) :
    Countable (Quotient (structureIsoSetoidRestrict L {d | (structureIsoSetoid L).r c d})) :=
  F.countable_isoQuotient_of_countable_sentenceSpectrum _
    (F.typeSpectrum_isoClass_countable 0 c)
    (fun _ hd _ hd' _ => (structureIsoSetoid L).trans ((structureIsoSetoid L).symm hd) hd')

/-! ### Axiom hygiene -/

def headline : List Name :=
  [`FirstOrder.Language.Fragment.countable_isoQuotient_of_countable_sentenceSpectrum,
   `FirstOrder.Language.Fragment.countable_isoQuotient_of_determining_cover,
   `FirstOrder.Language.countable_quotient_of_countable_range,
   `empty_class_regression, `composition_regression, `overlapping_descriptions_regression,
   `isoClass_regression]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "fragment-spectrum classification guard: OK (empty class, composition, overlapping \
    descriptions, and one isomorphism class admitted; classification hypothesis explicit; \
    headline declarations on standard axioms)"
