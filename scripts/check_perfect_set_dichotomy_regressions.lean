/-
Regression guard for the perfect-set dichotomy across carrier tiers
(`Descriptive/PerfectSetDichotomy.lean`).

Checked: the `ℕ`-tier refutation and the all-countable refutation as conditional API compositions,
the latter with **explicit emptiness at every finite tier including `Fin 0`** and, separately,
with the weaker no-finite-antichain premise; **why `ℕ`-tier thinness alone is insufficient**: a concrete
sentence over countably many nullary predicates ("exactly one element") with no `ℕ`-models but a
Cantor family of pairwise non-isomorphic `Fin 1`-models, hence a finite-tier perfect set and the
all-countable dichotomy (this tests that `ℕ`-tier thinness does not exclude finite-tier perfect
sets, not the `hbig` premise);
the **`Fin 0` tier** specifically (emptiness there refutes a `Fin 0` perfect set); and the
**sum injection** of the `ℕ`-tier classes.  Headline declarations use only the standard axioms.

Run with: lake env lean scripts/check_perfect_set_dichotomy_regressions.lean
-/
import InfinitaryLogic.Descriptive.PerfectSetDichotomy

open Lean FirstOrder Language Cardinal

variable {L : Language.{0, 0}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

omit [Countable (Σ l, L.Relations l)] in
/-- **`ℕ`-tier refutation**, conditional composition. -/
theorem nat_regression (φ : L.Sentenceω) (hthin : φ.IsThinOnNatModels)
    (hbig : ℵ₀ < #(Quotient (isoSetoid φ))) : ¬ φ.PerfectSetDichotomyNat :=
  φ.not_perfectSetDichotomyNat_of_thin hthin hbig

omit [Countable (Σ l, L.Relations l)] in
/-- **All-countable refutation** with explicit emptiness at every tier, and with the weaker
no-finite-antichain premise. -/
theorem all_countable_regression (φ : L.Sentenceω) (hthin : φ.IsThinOnNatModels)
    (hbig : ℵ₀ < #(Quotient (isoSetoid φ))) (hfin : ∀ n, ModelsOfOn (α := Fin n) φ = ∅) :
    ¬ φ.PerfectSetDichotomyAllCountable ∧
    ((∀ n, ¬ φ.HasPerfectSetOfPairwiseNonisomorphicFinModels n) →
      ¬ φ.PerfectSetDichotomyAllCountable) :=
  ⟨φ.not_perfectSetDichotomyAllCountable_of_thin hthin hbig hfin,
    fun h => φ.not_perfectSetDichotomyAllCountable_of_thin_of_finThin hthin hbig h⟩

/-! ### Why `ℕ`-tier thinness alone is insufficient: a concrete sentence

The language with countably many nullary predicates and the sentence "there is exactly one element":
it has **no `ℕ`-models** (so it is thin on the `ℕ` tier for the trivial reason), yet its `Fin 1`-models
form a copy of Cantor space on which isomorphism is equality, so it has a **perfect set of pairwise
non-isomorphic `Fin 1`-models** and satisfies the all-countable dichotomy.  This tests that `ℕ`-tier
thinness does not exclude finite-tier perfect sets; it says nothing about the `hbig` premise. -/

/-- Countably many nullary predicates, nothing else. -/
def nullaryLang : Language.{0, 0} where
  Functions _ := Empty
  Relations l := { _n : ℕ // l = 0 }

instance : nullaryLang.IsRelational := fun _ => inferInstanceAs (IsEmpty Empty)

instance : Countable (Σ l, nullaryLang.Relations l) :=
  inferInstanceAs (Countable (Σ l, { _n : ℕ // l = 0 }))

/-- "There is exactly one element": `∃ x, ∀ y, x = y`. -/
def exactlyOne : nullaryLang.Sentenceω :=
  BoundedFormulaω.ex (BoundedFormulaω.all
    (BoundedFormulaInf.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1))))

theorem realize_exactlyOne (M : Type) [inst : nullaryLang.Structure M] (v : Empty → M)
    (xs : Fin 0 → M) :
    @BoundedFormulaω.Realize nullaryLang M inst Empty 0 exactlyOne v xs ↔ ∃ x : M, ∀ y : M, x = y := by
  simp [exactlyOne, BoundedFormulaInf.realize_equal, Term.realize, Fin.snoc]

/-- **No `ℕ`-models**. -/
theorem modelsOf_exactlyOne_eq_empty : ModelsOf exactlyOne = ∅ := by
  ext c
  refine ⟨fun h => ?_, fun h => h.elim⟩
  have := (@realize_exactlyOne ℕ c.toStructure Empty.elim Fin.elim0).mp h
  obtain ⟨x, hx⟩ := this
  have h0 := hx 0
  have h1 := hx 1
  omega

/-- Hence thin on the `ℕ` tier, for the trivial reason. -/
theorem exactlyOne_thin : exactlyOne.IsThinOnNatModels := by
  rintro ⟨P, _, ⟨x, hx⟩, hsub, _⟩
  have := hsub hx
  rw [modelsOf_exactlyOne_eq_empty] at this
  exact this

/-- The Cantor family of `Fin 1`-codes: the `n`-th nullary predicate holds iff `z n = true`. -/
def finOneCode (z : ℕ → Bool) : StructureSpaceOn nullaryLang (Fin 1) := fun q => z q.1.2.1

theorem continuous_finOneCode : Continuous finOneCode :=
  continuous_pi fun _ => continuous_apply _

theorem finOneCode_models (z : ℕ → Bool) :
    finOneCode z ∈ ModelsOfOn (α := Fin 1) exactlyOne := by
  show @BoundedFormulaω.Realize nullaryLang (Fin 1) (finOneCode z).toStructure Empty 0 exactlyOne
    Empty.elim Fin.elim0
  rw [@realize_exactlyOne (Fin 1) (finOneCode z).toStructure]
  exact ⟨0, fun y => Subsingleton.elim _ _⟩

/-- Distinct parameters give non-isomorphic `Fin 1`-codes: an isomorphism preserves every nullary
predicate. -/
theorem finOneCode_antichain (z w : ℕ → Bool) (hzw : z ≠ w) :
    ¬ (structureIsoSetoidOn nullaryLang 1).r (finOneCode z) (finOneCode w) := by
  rintro ⟨e⟩
  apply hzw
  funext n
  have := @Language.Equiv.map_rel' nullaryLang (Fin 1) (Fin 1) (finOneCode z).toStructure
    (finOneCode w).toStructure e 0 ⟨n, rfl⟩ Fin.elim0
  change finOneCode w _ = true ↔ finOneCode z _ = true at this
  simp only [finOneCode] at this
  exact (Bool.coe_iff_coe.mp this).symm

/-- **The concrete finite-tier perfect set**, and the resulting all-countable dichotomy, alongside
`ℕ`-tier thinness. -/
theorem finite_tier_perfect_set_regression :
    exactlyOne.IsThinOnNatModels ∧
    exactlyOne.HasPerfectSetOfPairwiseNonisomorphicFinModels 1 ∧
    exactlyOne.PerfectSetDichotomyAllCountable := by
  have hperf : exactlyOne.HasPerfectSetOfPairwiseNonisomorphicFinModels 1 :=
    Sentenceω.hasPerfectSetFin_of_ambient_cantorAntichain
      ⟨finOneCode, continuous_finOneCode, finOneCode_models, finOneCode_antichain⟩
  exact ⟨exactlyOne_thin, hperf, Or.inr (Or.inr ⟨1, hperf⟩)⟩

omit [Countable (Σ l, L.Relations l)] in
/-- **The `Fin 0` tier**: emptiness there refutes a `Fin 0` perfect set. -/
theorem fin_zero_regression (φ : L.Sentenceω) (h : ModelsOfOn (α := Fin 0) φ = ∅) :
    ¬ φ.HasPerfectSetOfPairwiseNonisomorphicFinModels 0 :=
  Sentenceω.not_hasPerfectSetFin_of_modelsOfOn_eq_empty h

omit [Countable (Σ l, L.Relations l)] in
/-- **The sum injection.** -/
theorem injection_regression (φ : L.Sentenceω) :
    #(Quotient (isoSetoid φ)) ≤ #(AllCodedIsoClasses φ) :=
  mk_quotient_isoSetoid_le_allCodedIsoClasses φ

/-! ### Axiom hygiene -/

def headline : List Name :=
  [`FirstOrder.Language.Sentenceω.not_perfectSetDichotomyNat_of_thin,
   `FirstOrder.Language.Sentenceω.not_perfectSetDichotomyAllCountable_of_thin,
   `FirstOrder.Language.Sentenceω.not_perfectSetDichotomyAllCountable_of_thin_of_finThin,
   `FirstOrder.Language.Sentenceω.not_hasPerfectSetFin_of_modelsOfOn_eq_empty,
   `FirstOrder.Language.mk_quotient_isoSetoid_le_allCodedIsoClasses,
   `nat_regression, `all_countable_regression, `modelsOf_exactlyOne_eq_empty,
   `finite_tier_perfect_set_regression,
   `fin_zero_regression, `injection_regression]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "perfect-set dichotomy regression guard: OK (ℕ-tier and all-countable refutations with \
    explicit finite-tier emptiness including Fin 0 and with the no-finite-antichain premise; a concrete \
    sentence with no ℕ-models but a Cantor family of Fin 1-models, so ℕ-tier thinness does not \
    exclude finite-tier perfect sets; \
    Fin 0 tier; sum injection; headline declarations on standard axioms)"
