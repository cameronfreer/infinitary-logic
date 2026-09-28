/-
Regression guard for thinness from single-sentence splits (`Descriptive/CountableSplits.lean`,
`Descriptive/SentenceSplits.lean`).

Checked: the **counting helper** on an uncountable domain with **both choices of countable truth
side** (a predicate whose true side is a singleton and one whose false side is a singleton) and a
constant predicate; the **empty class**; a **nonempty class with a nonsurjective presentation**
(a singleton class presented in `Bool` through the constant map to `true`, so `false` is not a
value); **repeated sentences** (the constant list) through the bridge; **composition through the
arbitrary-class thinness endpoint** (`isThinOn_of_countable_sentence_splits`) on that nonsurjective
presentation; and a **conditional API-composition regression** for the sentence-specific corollary,
presenting `ModelsOf φ` in `Unit` under an explicit decision hypothesis, with the split premise
discharged directly since `Unit` is finite.  Headline declarations use only the standard axioms.

Run with: lake env lean scripts/check_sentence_splits_regressions.lean
-/
import InfinitaryLogic.Descriptive.SentenceSplits

open Lean FirstOrder Language

/-! ### The counting helper: both choices of countable side -/

/-- Three predicates on Cantor space: true side a singleton, false side a singleton, constant. -/
def P₃ (x₀ : ℕ → Bool) : Fin 3 → (ℕ → Bool) → Prop
  | 0 => fun x => x = x₀
  | 1 => fun x => x ≠ x₀
  | 2 => fun _ => True

theorem P₃_splits (x₀ : ℕ → Bool) : ∀ i, ({x | P₃ x₀ i x} : Set (ℕ → Bool)).Countable ∨
    ({x | ¬ P₃ x₀ i x} : Set (ℕ → Bool)).Countable
  | 0 => Or.inl (by simp [P₃])
  | 1 => Or.inr (by simp [P₃])
  | 2 => Or.inr (by simp [P₃])

open Classical in
/-- **Both sides**: simultaneous constancy and countable range on an uncountable domain. -/
theorem helper_regression (x₀ : ℕ → Bool) :
    (∃ E : Set (ℕ → Bool), E.Countable ∧ ∀ x ∉ E, ∀ y ∉ E, ∀ i, P₃ x₀ i x ↔ P₃ x₀ i y) ∧
    (Set.range fun x : ℕ → Bool => fun i : Fin 3 => decide (P₃ x₀ i x)).Countable :=
  ⟨exists_countable_exceptions_of_splits (P₃ x₀) (P₃_splits x₀),
    countable_range_of_splits (P₃ x₀) _ (fun _ _ h => funext fun i => decide_eq_decide.mpr (h i))
      (P₃_splits x₀)⟩

/-! ### The descriptive endpoints -/

variable {L : Language.{0, 0}} [L.IsRelational] [Countable (Σ n, L.Relations n)]

/-- **Empty class**, presented in `Empty`. -/
theorem empty_class_regression : IsThinOn (structureIsoSetoid L) ∅ :=
  isThinOn_of_countable_sentence_splits ∅ (fun c => (c.2.elim : Empty)) (fun _ _ => False)
    (fun _ c => c.2.elim) (fun _ => Or.inl (Set.countable_empty.mono fun _ h => h.elim))

/-- The nonsurjective presentation of a singleton class: everything maps to `true`, and truth is
read off the code. -/
def constPres (c : StructureSpace L) : ({c} : Set (StructureSpace L)) → Bool := fun _ => true

omit [L.IsRelational] [Countable (Σ n, L.Relations n)] in
theorem constPres_not_surjective (c : StructureSpace L) : ¬ Function.Surjective (constPres c) :=
  fun h => by obtain ⟨_, hx⟩ := h false; simp [constPres] at hx

def constTruth (c : StructureSpace L) : L.Sentenceω → Bool → Prop := fun θ _ => c ∈ ModelsOf θ

omit [Countable (Σ n, L.Relations n)] in
theorem constTruth_htruth (c : StructureSpace L) :
    ∀ θ (d : ({c} : Set (StructureSpace L))), constTruth c θ (constPres c d) ↔ d.1 ∈ ModelsOf θ :=
  fun θ d => by
    have : d.1 = c := d.2
    simp [constTruth, this]

omit [Countable (Σ n, L.Relations n)] in
theorem constTruth_splits (c : StructureSpace L) : ∀ θ,
    ({q | constTruth c θ q} : Set Bool).Countable ∨ ({q | ¬ constTruth c θ q} : Set Bool).Countable :=
  fun _ => Or.inl (Set.to_countable _)

omit [Countable (Σ n, L.Relations n)] in
/-- **Repeated sentences** through the bridge on the nonsurjective presentation. -/
theorem repeated_sentences_regression (c : StructureSpace L) (φ : L.Sentenceω) :
    (sentenceTheory (fun _ : ℕ => φ) '' ({c} : Set (StructureSpace L))).Countable :=
  countable_sentenceTheory_image_of_splits {c} (constPres c) (constTruth c) (constTruth_htruth c)
    (constTruth_splits c) _

/-- **Composition through the thinness endpoint** on the nonsurjective presentation. -/
theorem endpoint_regression (c : StructureSpace L) : IsThinOn (structureIsoSetoid L) {c} :=
  isThinOn_of_countable_sentence_splits {c} (constPres c) (constTruth c) (constTruth_htruth c)
    (constTruth_splits c)

/-- **Conditional API composition** for the sentence-specific corollary: `ModelsOf φ` presented in
`Unit`, under the explicit hypothesis that every sentence is decided uniformly on the models of `φ`.
The split premise is discharged directly: every subset of `Unit` is countable. -/
theorem sentence_endpoint_regression (φ : L.Sentenceω)
    (hdec : ∀ θ : L.Sentenceω, ∀ c ∈ ModelsOf φ, (c ∈ ModelsOf θ ↔ ∀ d ∈ ModelsOf φ, d ∈ ModelsOf θ)) :
    φ.IsThinOnNatModels :=
  φ.isThinOnNatModels_of_countable_sentence_splits (fun _ => ())
    (fun θ _ => ∀ c ∈ ModelsOf φ, c ∈ ModelsOf θ) (fun θ c => (hdec θ c.1 c.2).symm)
    (fun _ => Or.inl (Set.to_countable _))

/-! ### Axiom hygiene -/

def headline : List Name :=
  [`exists_countable_exceptions_of_splits, `countable_range_of_splits,
   `FirstOrder.Language.countable_sentenceTheory_image_of_splits,
   `FirstOrder.Language.isThinOn_of_countable_sentence_spectra,
   `FirstOrder.Language.isThinOn_of_countable_sentence_splits,
   `FirstOrder.Language.Sentenceω.isThinOnNatModels_of_countable_sentence_splits,
   `FirstOrder.Language.thin_of_countable_sentence_spectra,
   `helper_regression, `empty_class_regression, `constPres_not_surjective,
   `repeated_sentences_regression, `endpoint_regression, `sentence_endpoint_regression]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "sentence-splits regression guard: OK (both countable sides on an uncountable domain, \
    empty class, nonsurjective presentation, repeated sentences, composition through the \
    arbitrary-class thinness endpoint, conditional API composition for the sentence-specific \
    corollary; headline declarations on standard axioms)"
