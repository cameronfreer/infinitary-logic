/-
Regression guard for the perfect-set dichotomy across carrier tiers
(`Descriptive/PerfectSetDichotomy.lean`).

Checked: the `ℕ`-tier refutation and the all-countable refutation as conditional API compositions,
the latter with **explicit emptiness at every finite tier including `Fin 0`** and, separately,
with the weaker no-finite-antichain premise; **why `ℕ`-tier thinness alone is insufficient**: a
perfect set in any finite tier satisfies the all-countable dichotomy whatever the `ℕ` tier does;
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

omit [Countable (Σ l, L.Relations l)] in
/-- **Why `ℕ`-tier thinness alone is insufficient**: a perfect set in any finite tier satisfies
the all-countable dichotomy, whatever the `ℕ` tier does. -/
theorem finite_tier_suffices_regression (φ : L.Sentenceω) (n : ℕ)
    (h : φ.HasPerfectSetOfPairwiseNonisomorphicFinModels n) :
    φ.PerfectSetDichotomyAllCountable :=
  Or.inr (Or.inr ⟨n, h⟩)

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
   `nat_regression, `all_countable_regression, `finite_tier_suffices_regression,
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
    explicit finite-tier emptiness including Fin 0 and with the no-finite-antichain premise; a \
    finite-tier perfect set satisfies the all-countable dichotomy regardless of ℕ-tier thinness; \
    Fin 0 tier; sum injection; headline declarations on standard axioms)"
