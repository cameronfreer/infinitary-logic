/-
Regression guard for the fragment-tail route.

The sentence-list specialization of the generic counting kernel must compose with the
tail-boundedness theorem using arbitrary predicate covers, and must admit the empty class and
overlapping covers.  Coverage and determination stay explicit inputs throughout: nothing here
constructs a cover for any class.  Headline declarations use only the standard axioms.

Run with: lake env lean scripts/check_fragment_tail_regressions.lean
-/
import InfinitaryLogic.Descriptive.FragmentTail

open Lean FirstOrder Language

variable {L : Language.{0, 0}} [L.IsRelational]

/-- **Empty class**: the spectrum of the empty class is countable with any (vacuous) cover. -/
theorem empty_class_regression (θ : ℕ → L.Sentenceω) :
    (sentenceTheory θ '' (∅ : Set (StructureSpace L))).Countable :=
  sentenceTheory_image_countable_of_determining_cover θ ∅ (fun (_ : Unit) _ => False)
    (fun _ h => h.elim) (fun _ _ h => h.elim)

/-- **Overlapping cover**: two indices carrying the same predicate; coverage and determination
are inherited from the one-predicate case. -/
theorem overlapping_cover_regression (θ : ℕ → L.Sentenceω) (C : Set (StructureSpace L))
    (Q : StructureSpace L → Prop) (cover : ∀ c ∈ C, Q c)
    (det : ∀ c ∈ C, ∀ d ∈ C, Q c → Q d → sentenceTheory θ c = sentenceTheory θ d) :
    (sentenceTheory θ '' C).Countable :=
  sentenceTheory_image_countable_of_determining_cover θ C (fun _ : Bool => Q)
    (fun c hc => ⟨true, cover c hc⟩) (fun _ c hc d hd hc' hd' => det c hc d hd hc' hd')

/-- **Composition with tail boundedness** from arbitrary predicate covers: for each list `θ` the
producer supplies a threshold and a countable determining predicate cover of that tail; the rank
is then bounded on every measurable Cantor isomorphism antichain in `C`. -/
theorem composition_regression [Countable (Σ n, L.Relations n)] (C : Set (StructureSpace L))
    (r : StructureSpace L → Ordinal.{0}) (hr : ∀ c ∈ C, r c < Ordinal.omega 1)
    (E : (ℕ → L.Sentenceω) → Type) [∀ θ, Countable (E θ)]
    (P : ∀ θ, E θ → StructureSpace L → Prop)
    (b : (ℕ → L.Sentenceω) → Ordinal.{0}) (hb : ∀ θ, b θ < Ordinal.omega 1)
    (cover : ∀ θ, ∀ c ∈ {c | c ∈ C ∧ b θ ≤ r c}, ∃ e, P θ e c)
    (det : ∀ θ, ∀ e, ∀ c ∈ {c | c ∈ C ∧ b θ ≤ r c}, ∀ d ∈ {c | c ∈ C ∧ b θ ≤ r c},
      P θ e c → P θ e d → sentenceTheory θ c = sentenceTheory θ d)
    (f : (ℕ → Bool) → StructureSpace L) (hf : Measurable f) (hm : ∀ x, f x ∈ C)
    (hanti : ∀ x y, x ≠ y → ¬ (structureIsoSetoid L).r (f x) (f y)) :
    ∃ β < Ordinal.omega 1, ∀ x, r (f x) < β :=
  antichain_rank_bounded_of_fragment_tails C r hr
    (fun θ => ⟨b θ, hb θ,
      sentenceTheory_image_countable_of_determining_cover θ _ (P θ) (cover θ) (det θ)⟩)
    f hf hm hanti

/-- **The refined field** from the same inputs, with the subcopy `e := id`. -/
theorem refined_field_regression [Countable (Σ n, L.Relations n)] (C : Set (StructureSpace L))
    (r : StructureSpace L → Ordinal.{0}) (hr : ∀ c ∈ C, r c < Ordinal.omega 1)
    (E : (ℕ → L.Sentenceω) → Type) [∀ θ, Countable (E θ)]
    (P : ∀ θ, E θ → StructureSpace L → Prop)
    (b : (ℕ → L.Sentenceω) → Ordinal.{0}) (hb : ∀ θ, b θ < Ordinal.omega 1)
    (cover : ∀ θ, ∀ c ∈ {c | c ∈ C ∧ b θ ≤ r c}, ∃ e, P θ e c)
    (det : ∀ θ, ∀ e, ∀ c ∈ {c | c ∈ C ∧ b θ ≤ r c}, ∀ d ∈ {c | c ∈ C ∧ b θ ≤ r c},
      P θ e c → P θ e d → sentenceTheory θ c = sentenceTheory θ d) :
    ∀ f : (ℕ → Bool) → StructureSpace L, Continuous f → (∀ x, f x ∈ C) →
      (∀ x y, x ≠ y → ¬ (structureIsoSetoid L).r (f x) (f y)) →
      ∃ e : (ℕ → Bool) → (ℕ → Bool), Continuous e ∧ Function.Injective e ∧
        ∃ β < Ordinal.omega 1, ∀ x, r (f (e x)) < β :=
  ThinRankAnalysis.bounded_refined_of_fragment_tails C r hr
    (fun θ => ⟨b θ, hb θ,
      sentenceTheory_image_countable_of_determining_cover θ _ (P θ) (cover θ) (det θ)⟩)

/-! ### Axiom hygiene -/

def headline : List Name :=
  [`FirstOrder.Language.sentenceTheory_image_countable_of_determining_cover,
   `Set.countable_image_of_determining_cover,
   `FirstOrder.Language.antichain_rank_bounded_of_fragment_tails,
   `FirstOrder.Language.ThinRankAnalysis.bounded_refined_of_fragment_tails,
   `empty_class_regression, `overlapping_cover_regression, `composition_regression,
   `refined_field_regression]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "fragment-tail regression guard: OK (empty class, overlapping cover, composition with \
    tail boundedness and the refined field from arbitrary predicate covers; headline \
    declarations on standard axioms)"
