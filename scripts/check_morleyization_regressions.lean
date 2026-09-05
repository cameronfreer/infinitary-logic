/-
Regression guard for the canonical definitional expansion (Morleyization).

Required shapes: the empty family recovers the base structure by reduct; a relation defined by
an atomic formula, by an existential formula with several possible witnesses, and by a countable
conjunction each read off the truth lemma definitionally; the reduct after expansion is the
identity; translated sentence families stay countable; the coded expansion is injective and its
image is the class of models of the defining theory.  The lifted isomorphism has the given
underlying bijection (`morleyEquiv_toEquiv`): no witness is selected in its data.  Headline
declarations on standard axioms.

Run with: lake env lean scripts/check_morleyization_regressions.lean
-/
import InfinitaryLogic.ModelTheory.MorleyizationElementary
import InfinitaryLogic.Descriptive.MorleyizationCode

open Lean FirstOrder Language

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

/-- Empty family: the reduct of the canonical expansion is the base structure. -/
theorem empty_family_regression :
    @LHom.reduct L (L.morleyize ∅) (lhomMorleyize ∅) M (morleyExpansion ∅ M) = ‹L.Structure M› :=
  reduct_morleyExpansion

/-- A relation defined by an atomic formula: the truth lemma is the base relation. -/
theorem atomic_regression {n : ℕ} (R : L.Relations n) {Φ : Set (Σ n, L.BoundedFormulaω Empty n)}
    (h : (⟨n, BoundedFormulaω.rel R fun i => Term.var (Sum.inr i)⟩ :
      Σ n, L.BoundedFormulaω Empty n) ∈ Φ) (x : Fin n → M) :
    @Structure.RelMap (L.morleyize Φ) M (morleyExpansion Φ M) n (Sum.inr ⟨_, h⟩) x ↔
      Structure.RelMap R x :=
  Iff.rfl

/-- A relation defined by an existential formula, with several possible witnesses: the truth
lemma is the existential, no witness selected. -/
theorem existential_regression {n : ℕ} (φ : L.BoundedFormulaω Empty (n + 1))
    {Φ : Set (Σ n, L.BoundedFormulaω Empty n)}
    (h : (⟨n, φ.not.all.not⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ Φ) (x : Fin n → M) :
    @Structure.RelMap (L.morleyize Φ) M (morleyExpansion Φ M) n (Sum.inr ⟨_, h⟩) x ↔
      ∃ y, φ.Realize Empty.elim (Fin.snoc x y) := by
  show φ.not.all.not.Realize Empty.elim x ↔ _
  simp

/-- A relation defined by a countable conjunction: the truth lemma is the conjunction. -/
theorem conjunction_regression {n : ℕ} (φs : ℕ → L.BoundedFormulaω Empty n)
    {Φ : Set (Σ n, L.BoundedFormulaω Empty n)}
    (h : (⟨n, BoundedFormulaω.iInf φs⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ Φ) (x : Fin n → M) :
    @Structure.RelMap (L.morleyize Φ) M (morleyExpansion Φ M) n (Sum.inr ⟨_, h⟩) x ↔
      ∀ k, (φs k).Realize Empty.elim x := by
  show (BoundedFormulaω.iInf φs).Realize Empty.elim x ↔ _
  exact BoundedFormulaω.realize_iInf φs

/-- Translated sentence families stay countable. -/
theorem countable_translation_regression {Φ : Set (Σ n, L.BoundedFormulaω Empty n)}
    (T : Set (L.morleyize Φ).Sentenceω) (hT : T.Countable) :
    ((fun σ => (unMorleyize σ : L.Sentenceω)) '' T).Countable :=
  hT.image _

/-- The coded expansion is left-inverted by the reduct code. -/
theorem coded_reduct_regression {L : Language.{0, 0}} [L.IsRelational]
    {Φ : Set (Σ n, L.BoundedFormulaω Empty n)} (c : StructureSpace L) :
    reductCode (morleyCode Φ c) = c :=
  reductCode_morleyCode c

def headline : List Name :=
  [`FirstOrder.Language.reduct_morleyExpansion,
   `FirstOrder.Language.morleyExpansion_model_definingTheory,
   `FirstOrder.Language.eq_morleyExpansion_of_model_definingTheory,
   `FirstOrder.Language.realize_unMorleyize,
   `FirstOrder.Language.morleyEquiv, `FirstOrder.Language.morleyEquiv_toEquiv,
   `FirstOrder.Language.exists_morleyEmbedding_iff_aElementary,
   `FirstOrder.Language.morleyEmbedding_unique,
   `FirstOrder.Language.measurable_morleyCode,
   `FirstOrder.Language.measurableEmbedding_morleyCode,
   `FirstOrder.Language.measurableSet_image_morleyCode,
   `FirstOrder.Language.range_morleyCode,
   `empty_family_regression, `atomic_regression, `existential_regression,
   `conjunction_regression, `countable_translation_regression, `coded_reduct_regression]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "morleyization regression guard: OK (empty family, atomic, existential, conjunction, \
    countable translation, coded reduct; lifted isomorphism carries the given bijection; headline \
    declarations on standard axioms)"
