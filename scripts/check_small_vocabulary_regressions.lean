/-
Regression guard for the chosen small-vocabulary presentation
(`Descriptive/SmallVocabulary.lean`, `Descriptive/SmallVocabularyLift.lean`).

On a genuinely **higher-universe signature** `bigLang : Language.{0, 1}` with
`Relations n := ULift.{1} (Fin (n + 1))` (so **nullary symbols** exist, and every arity has a symbol):
the inverse laws of `code`/`decode` and the homeomorphism; **isomorphism preserved and reflected**
(both directions of `iso_code_iff` applied); the code of a **nullary** query and the lift of a
**nullary atomic sentence** with `modelsOf_liftFormula` there; **quantifier rank** through a
universal quantifier and a countable disjunction; **realization** of a countable conjunction through
the lift; measurability of both code maps.  Headline declarations use only the standard axioms.

Run with: lake env lean scripts/check_small_vocabulary_regressions.lean
-/
import InfinitaryLogic.Descriptive.SmallVocabularyLift

open Lean FirstOrder Language SmallVocabulary

/-- A `Type 1` relational signature with one more symbol at each arity, including arity `0`. -/
def bigLang : Language.{0, 1} where
  Functions _ := Empty
  Relations n := ULift.{1} (Fin (n + 1))

instance : bigLang.IsRelational := fun _ => inferInstanceAs (IsEmpty Empty)

instance : Countable (Σ n, bigLang.Relations n) :=
  inferInstanceAs (Countable (Σ n, ULift.{1} (Fin (n + 1))))

/-- The small presentation of `bigLang` lives in `Type 0`. -/
noncomputable example : Language.{0, 0} := lang bigLang

/-- **Inverse laws and the homeomorphism** on the higher-universe signature. -/
theorem inverse_regression (c : StructureSpace bigLang) (d : StructureSpace (lang bigLang)) :
    decode bigLang (code bigLang c) = c ∧ code bigLang (decode bigLang d) = d ∧
    (codeHomeomorph bigLang).symm (codeHomeomorph bigLang c) = c :=
  ⟨decode_code bigLang c, code_decode bigLang d, (codeHomeomorph bigLang).symm_apply_apply c⟩

/-- **Isomorphism preserved and reflected**, both directions applied. -/
theorem iso_regression (a b : StructureSpace bigLang) :
    ((structureIsoSetoid bigLang).r a b →
      (structureIsoSetoid (lang bigLang)).r (code bigLang a) (code bigLang b)) ∧
    ((structureIsoSetoid (lang bigLang)).r (code bigLang a) (code bigLang b) →
      (structureIsoSetoid bigLang).r a b) :=
  ⟨(iso_code_iff bigLang a b).mpr, (iso_code_iff bigLang a b).mp⟩

/-- The nullary symbol of `bigLang`. -/
def R₀ : bigLang.Relations 0 := ⟨0⟩

/-- **Nullary query**: the code at arity `0` reads the original at the decoded symbol. -/
theorem nullary_code_regression (c : StructureSpace bigLang) :
    code bigLang c ⟨⟨0, shrinkRel bigLang 0 R₀⟩, Fin.elim0⟩ = c ⟨⟨0, R₀⟩, Fin.elim0⟩ := by
  rw [code_apply, (shrinkRel bigLang 0).symm_apply_apply]

/-- The nullary atomic sentence of the small presentation. -/
noncomputable def atom₀ : (lang bigLang).Sentenceω :=
  .rel (shrinkRel bigLang 0 R₀) Fin.elim0

/-- **Nullary atomic sentence** through the lift: its models are the preimage of the small
presentation's models. -/
theorem nullary_sentence_regression :
    ModelsOf (liftFormula bigLang atom₀) = code bigLang ⁻¹' ModelsOf atom₀ :=
  modelsOf_liftFormula bigLang atom₀

/-- **Quantifier rank** through a universal quantifier and a countable disjunction. -/
theorem qrank_regression (φ : (lang bigLang).BoundedFormulaInf ℕ Empty 1)
    (φs : ℕ → (lang bigLang).BoundedFormulaInf ℕ Empty 0) :
    (liftFormula bigLang (.all φ)).qrank = (BoundedFormulaInf.all φ).qrank ∧
    (liftFormula bigLang (.iSup φs)).qrank = (BoundedFormulaInf.iSup φs).qrank :=
  ⟨qrank_liftFormula bigLang _, qrank_liftFormula bigLang _⟩

/-- **Realization** of a countable conjunction through the lift. -/
theorem realize_regression (c : StructureSpace bigLang)
    (φs : ℕ → (lang bigLang).BoundedFormulaInf ℕ Empty 0) :
    @BoundedFormulaInf.Realize bigLang ℕ Empty ℕ c.toStructure 0 (liftFormula bigLang (.iInf φs))
        Empty.elim Fin.elim0 ↔
      @BoundedFormulaInf.Realize (lang bigLang) ℕ Empty ℕ (code bigLang c).toStructure 0 (.iInf φs)
        Empty.elim Fin.elim0 :=
  realize_liftFormula bigLang c _ _ _

theorem measurable_regression : Measurable (code bigLang) ∧ Measurable (decode bigLang) :=
  ⟨measurable_code bigLang, measurable_decode bigLang⟩

/-! ### Axiom hygiene -/

def headline : List Name :=
  [`FirstOrder.Language.SmallVocabulary.decode_code, `FirstOrder.Language.SmallVocabulary.code_decode,
   `FirstOrder.Language.SmallVocabulary.codeHomeomorph,
   `FirstOrder.Language.SmallVocabulary.measurable_code,
   `FirstOrder.Language.SmallVocabulary.iso_code_iff,
   `FirstOrder.Language.SmallVocabulary.realize_liftFormula,
   `FirstOrder.Language.SmallVocabulary.qrank_liftFormula,
   `FirstOrder.Language.SmallVocabulary.modelsOf_liftFormula,
   `inverse_regression, `iso_regression, `nullary_code_regression, `nullary_sentence_regression,
   `qrank_regression, `realize_regression, `measurable_regression]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "small-vocabulary regression guard: OK (Type 1 signature with nullary symbols: inverse \
    laws and homeomorphism, isomorphism preserved and reflected, nullary query and atomic sentence \
    through the lift, quantifier rank through all and iSup, realization through iInf, \
    measurable code maps; headline declarations on standard axioms)"
