/-
Regression guard for the finite-character closure and the two-generator cardinal bounds
(`InfinitaryLogic/FiniteSupportClosure.lean`, `InfinitaryLogic/TwoGeneratorCardinality.lean`).

Checked: the **API** (closure of an infinite set keeps its cardinality; proper closed subsets are
countable; the carrier is at most `ℵ₁`; an uncountable embedding with closed range is surjective)
as conditional compositions; the **empty carrier** and the **singleton carrier** with the identity
closure, where whole-hull two-generation holds and the bound applies; the **three-point
identity-closure counterexample**: the identity closure on `Fin 3` has a two-point witness for every
individual membership, yet whole-hull two-generation fails (the hull of the whole carrier is not the
hull of any two points), so pair witnesses must not replace whole-hull generation; and, on a carrier
of cardinality above `ℵ₁`, the identity closure still has pair witnesses while the `ℵ₁` bound fails.
Headline declarations use only the standard axioms.

Run with: lake env lean scripts/check_finite_support_closure_regressions.lean
-/
import InfinitaryLogic.TwoGeneratorCardinality
import Mathlib.SetTheory.Cardinal.Continuum

open Lean Cardinal InfinitaryLogic.FiniteSupportClosure

/-! ### The API, as conditional compositions -/

theorem api_regression {M : Type} (c : ClosureOperator (Finset M))
    (hgen : ∀ S, ∃ T ⊆ S, T.card ≤ 2 ∧ c T = c S) {A : Set M} (hA : A.Infinite)
    (hclosed : (setClosure c).IsClosed A) (hproper : A ≠ Set.univ)
    {N : Type} [Uncountable N] (e : N ↪ M) (he : (setClosure c).IsClosed (Set.range e)) :
    #(setClosure c A) = #A ∧ A.Countable ∧ #M ≤ ℵ₁ ∧ Function.Surjective e :=
  ⟨mk_setClosure_eq c hA, countable_of_isClosed_ne_univ c hgen hclosed hproper,
    mk_le_aleph_one c hgen, surjective_of_isClosed_range c hgen e he⟩

/-! ### The identity closure -/

/-- The identity closure on the finite subsets of `M`. -/
def idClosure (M : Type) : ClosureOperator (Finset M) := ClosureOperator.id (Finset M)

/-- **Pair witnesses for every individual membership** hold for the identity closure on any
carrier. -/
theorem idClosure_pair_witnesses (M : Type) [DecidableEq M] :
    ∀ (S : Finset M) (x : M), x ∈ idClosure M S → ∃ T ⊆ S, T.card ≤ 2 ∧ x ∈ idClosure M T :=
  fun S x hx => ⟨{x}, Finset.singleton_subset_iff.mpr hx, by simp, by simp [idClosure]⟩

/-- **Empty carrier**: whole-hull two-generation holds, and the bound applies. -/
theorem empty_carrier_regression :
    (∀ S : Finset Empty, ∃ T ⊆ S, T.card ≤ 2 ∧ idClosure Empty T = idClosure Empty S) ∧
    #Empty ≤ ℵ₁ ∧ setClosure (idClosure Empty) ∅ = ∅ := by
  have hgen : ∀ S : Finset Empty, ∃ T ⊆ S, T.card ≤ 2 ∧ idClosure Empty T = idClosure Empty S :=
    fun S => ⟨S, le_rfl, (Finset.card_le_univ S).trans (by simp), rfl⟩
  exact ⟨hgen, mk_le_aleph_one _ hgen, setClosure_empty _ rfl⟩

/-- **Singleton carrier**: whole-hull two-generation holds, the bound applies, and the empty set
is a countable proper closed subset. -/
theorem singleton_carrier_regression :
    (∀ S : Finset Unit, ∃ T ⊆ S, T.card ≤ 2 ∧ idClosure Unit T = idClosure Unit S) ∧
    #Unit ≤ ℵ₁ ∧ (∅ : Set Unit).Countable := by
  have hgen : ∀ S : Finset Unit, ∃ T ⊆ S, T.card ≤ 2 ∧ idClosure Unit T = idClosure Unit S :=
    fun S => ⟨S, le_rfl, (Finset.card_le_univ S).trans (by simp), rfl⟩
  refine ⟨hgen, mk_le_aleph_one _ hgen, ?_⟩
  exact countable_of_isClosed_ne_univ (idClosure Unit) hgen
    (by rw [setClosure_closed_iff]; intro S hS; simpa [idClosure] using hS)
    Set.empty_ne_univ

/-- **The three-point counterexample**: on `Fin 3` the identity closure has pair witnesses for
every membership, but whole-hull two-generation fails at the whole carrier. -/
theorem three_point_regression :
    (∀ (S : Finset (Fin 3)) (x : Fin 3), x ∈ idClosure (Fin 3) S →
      ∃ T ⊆ S, T.card ≤ 2 ∧ x ∈ idClosure (Fin 3) T) ∧
    ¬ (∀ S : Finset (Fin 3), ∃ T ⊆ S, T.card ≤ 2 ∧ idClosure (Fin 3) T = idClosure (Fin 3) S) := by
  refine ⟨idClosure_pair_witnesses (Fin 3), fun h => ?_⟩
  obtain ⟨T, _, hcard, hT⟩ := h Finset.univ
  have : T = Finset.univ := by simpa [idClosure] using hT
  rw [this, Finset.card_univ, Fintype.card_fin] at hcard
  omega

/-- **Pair witnesses give no bound**: on a carrier of cardinality above `ℵ₁`, the identity closure
has pair witnesses for every membership while `#M ≤ ℵ₁` fails. -/
theorem large_carrier_regression :
    (∀ (S : Finset (Set (ℕ → Bool))) (x : Set (ℕ → Bool)),
      x ∈ idClosure (Set (ℕ → Bool)) S →
        ∃ T ⊆ S, T.card ≤ 2 ∧ x ∈ idClosure (Set (ℕ → Bool)) T) ∧
    ¬ (#(Set (ℕ → Bool)) ≤ ℵ₁) := by
  classical
  refine ⟨idClosure_pair_witnesses _, fun h => ?_⟩
  have h1 : #(Set (ℕ → Bool)) = 2 ^ #(ℕ → Bool) := Cardinal.mk_set
  have h2 : #(ℕ → Bool) = 𝔠 := by simp
  rw [h1, h2] at h
  exact absurd (h.trans Cardinal.aleph_one_le_continuum) (not_le.mpr (Cardinal.cantor 𝔠))

/-! ### Axiom hygiene -/

def headline : List Name :=
  [`InfinitaryLogic.FiniteSupportClosure.setClosure,
   `InfinitaryLogic.FiniteSupportClosure.setClosure_finset,
   `InfinitaryLogic.FiniteSupportClosure.setClosure_closed_iff,
   `InfinitaryLogic.FiniteSupportClosure.setClosure_unique,
   `InfinitaryLogic.FiniteSupportClosure.setClosure_antiExchange,
   `InfinitaryLogic.FiniteSupportClosure.mk_setClosure_eq,
   `InfinitaryLogic.FiniteSupportClosure.countable_of_isClosed_ne_univ,
   `InfinitaryLogic.FiniteSupportClosure.eq_univ_of_isClosed_uncountable,
   `InfinitaryLogic.FiniteSupportClosure.mk_le_aleph_one,
   `InfinitaryLogic.FiniteSupportClosure.surjective_of_isClosed_range,
   `api_regression, `empty_carrier_regression, `singleton_carrier_regression,
   `three_point_regression, `large_carrier_regression]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "finite-support closure regression guard: OK (API compositions; empty and singleton \
    carriers; three-point identity-closure counterexample separating pair witnesses from \
    whole-hull generation; pair witnesses give no bound on a large carrier; headline declarations \
    on standard axioms)"
