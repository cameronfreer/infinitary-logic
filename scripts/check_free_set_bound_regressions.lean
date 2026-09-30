/-
Regression guard for the free-set lemma and its two-generation corollaries
(`InfinitaryLogic/FreeSetBound.lean`).

Checked: the **base case** on `ℕ` (a finite-valued map, `ℵ_(0 + 0) ≤ #ℕ`, yields an independent
singleton); a **genuine pair** on the uncountable carrier `ℕ → Bool` (`ℵ_(0 + 1) ≤ 𝔠`, a
finite-valued map, an independent pair); the **identity closure**, whose hull map makes every
finite set independent (so on `Fin 3` there is an independent triple, consistent with the failure
of whole-hull two-generation there) and which has pair witnesses for every membership on a carrier
above `ℵ₁` while the `ℵ₁` bound fails, so pair witnesses must not replace whole-hull generation;
and **compatibility with `mk_le_aleph_one`**: the free-set derivation `mk_le_aleph_one_of_freeSet`
and the triple exclusion `not_fIndependent_of_two_generation` are applied to hypothesis-carrying
examples (an arbitrary two-generated closure, and the constant closure on `Fin 3`), next to the
original bound.  Headline declarations use only the standard axioms.

Run with: lake env lean scripts/check_free_set_bound_regressions.lean
-/
import InfinitaryLogic.FreeSetBound
import Mathlib.SetTheory.Cardinal.Continuum

open Lean Cardinal InfinitaryLogic.FreeSet InfinitaryLogic.FiniteSupportClosure

/-! ### The base case on a countable carrier -/

/-- **Base case**: the finite-valued map `A ↦ [0, max A]` on `ℕ` has an independent
singleton. -/
theorem base_case_regression :
    ∃ A : Finset ℕ, A.card = 1 ∧
      FIndependent (fun A : Finset ℕ ↦ (↑(Finset.range (A.sup id + 1)) : Set ℕ)) A := by
  refine exists_fIndependent (fun A : Finset ℕ ↦ (↑(Finset.range (A.sup id + 1)) : Set ℕ)) 0 0
    (fun A ↦ ?_) ?_
  · rw [aleph_zero]
    exact (Finset.finite_toSet _).lt_aleph0
  · simp

/-! ### A genuine pair on an uncountable carrier -/

/-- The pointwise complement of a binary sequence. -/
def negSeq (x : ℕ → Bool) : ℕ → Bool := fun n ↦ !x n

/-- **Uncountable pair**: on `ℕ → Bool` (cardinality `𝔠 ≥ ℵ₁`), the finite-valued map sending a
finite set to itself together with the complements of its members has an independent pair. -/
theorem uncountable_pair_regression :
    ∃ A : Finset (ℕ → Bool), A.card = 2 ∧
      FIndependent (fun A ↦ (↑A ∪ negSeq '' ↑A : Set (ℕ → Bool))) A := by
  refine exists_fIndependent (fun A ↦ (↑A ∪ negSeq '' ↑A : Set (ℕ → Bool))) 0 1
    (fun A ↦ ?_) ?_
  · rw [aleph_zero]
    exact (A.finite_toSet.union (A.finite_toSet.image _)).lt_aleph0
  · have h : #(ℕ → Bool) = 𝔠 := by simp
    rw [h, Nat.cast_one, zero_add]
    exact aleph_one_le_continuum

/-! ### The identity closure -/

/-- The identity closure on the finite subsets of `M`. -/
def idClosure (M : Type) : ClosureOperator (Finset M) := ClosureOperator.id (Finset M)

/-- For the identity closure every finite set is independent for the hull map. -/
theorem idClosure_fIndependent (M : Type) (A : Finset M) :
    FIndependent (fun S ↦ (↑(idClosure M S) : Set M)) A :=
  fun _ _ _ _ haB haf ↦ haB haf

/-- **Three points**: the identity closure on `Fin 3` has an independent triple, and whole-hull
two-generation fails there, as the triple exclusion predicts. -/
theorem three_point_regression :
    FIndependent (fun S ↦ (↑(idClosure (Fin 3) S) : Set (Fin 3))) Finset.univ ∧
    ¬ (∀ S : Finset (Fin 3), ∃ T ⊆ S, T.card ≤ 2 ∧ idClosure (Fin 3) T = idClosure (Fin 3) S) :=
  ⟨idClosure_fIndependent _ _, fun hgen ↦
    not_fIndependent_of_two_generation _ hgen Finset.univ (by simp)
      (idClosure_fIndependent _ _)⟩

/-- **Pair witnesses give no bound**: on a carrier of cardinality above `ℵ₁`, the identity closure
has pair witnesses for every membership while `#M ≤ ℵ₁` fails. -/
theorem large_carrier_regression :
    (∀ (S : Finset (Set (ℕ → Bool))) (x : Set (ℕ → Bool)),
      x ∈ idClosure (Set (ℕ → Bool)) S →
        ∃ T ⊆ S, T.card ≤ 2 ∧ x ∈ idClosure (Set (ℕ → Bool)) T) ∧
    ¬ (#(Set (ℕ → Bool)) ≤ ℵ₁) := by
  classical
  refine ⟨fun S x hx ↦ ⟨{x}, Finset.singleton_subset_iff.mpr hx, by simp,
    by simp [idClosure]⟩, fun h ↦ ?_⟩
  have h1 : #(Set (ℕ → Bool)) = 2 ^ #(ℕ → Bool) := Cardinal.mk_set
  have h2 : #(ℕ → Bool) = 𝔠 := by simp
  rw [h1, h2] at h
  exact absurd (h.trans Cardinal.aleph_one_le_continuum) (not_le.mpr (Cardinal.cantor 𝔠))

/-! ### Compatibility with `mk_le_aleph_one` -/

/-- **Both derivations**: under whole-hull two-generation, the free-set derivation and the
original bound both give `#M ≤ ℵ₁`, and no triple is independent for the hull map. -/
theorem compatibility_regression {M : Type} (c : ClosureOperator (Finset M))
    (hgen : ∀ S, ∃ T ⊆ S, T.card ≤ 2 ∧ c T = c S) :
    #M ≤ ℵ₁ ∧ #M ≤ ℵ₁ ∧
      ∀ A : Finset M, A.card = 3 → ¬ FIndependent (fun S ↦ (↑(c S) : Set M)) A :=
  ⟨mk_le_aleph_one_of_freeSet c hgen, mk_le_aleph_one c hgen,
    fun A hA ↦ not_fIndependent_of_two_generation c hgen A hA⟩

/-- The constant closure on `Fin 3`: every finite set has the whole carrier as its hull. -/
def topClosure : ClosureOperator (Finset (Fin 3)) :=
  ClosureOperator.mk' (fun _ ↦ Finset.univ) (fun _ _ _ ↦ le_rfl)
    (fun _ ↦ Finset.subset_univ _) (fun _ ↦ le_rfl)

/-- **A concrete two-generated closure**: the constant closure on `Fin 3` is generated by the
empty set, the free-set derivation bounds the carrier, and the whole carrier is not an
independent triple. -/
theorem top_closure_regression :
    (∀ S, ∃ T ⊆ S, T.card ≤ 2 ∧ topClosure T = topClosure S) ∧ #(Fin 3) ≤ ℵ₁ ∧
      ¬ FIndependent (fun S ↦ (↑(topClosure S) : Set (Fin 3))) Finset.univ := by
  have hgen : ∀ S, ∃ T ⊆ S, T.card ≤ 2 ∧ topClosure T = topClosure S :=
    fun S ↦ ⟨∅, Finset.empty_subset S, by simp, rfl⟩
  exact ⟨hgen, mk_le_aleph_one_of_freeSet topClosure hgen,
    not_fIndependent_of_two_generation topClosure hgen Finset.univ (by simp)⟩

/-! ### Axiom hygiene -/

def headline : List Name :=
  [`InfinitaryLogic.FreeSet.FIndependent,
   `InfinitaryLogic.FreeSet.fClosure,
   `InfinitaryLogic.FreeSet.fClosure_closed,
   `InfinitaryLogic.FreeSet.mk_fClosure_le,
   `InfinitaryLogic.FreeSet.exists_fIndependent,
   `InfinitaryLogic.FreeSet.not_fIndependent_of_two_generation,
   `InfinitaryLogic.FreeSet.mk_le_aleph_one_of_freeSet,
   `base_case_regression, `uncountable_pair_regression, `three_point_regression,
   `large_carrier_regression, `compatibility_regression, `top_closure_regression]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "free-set bound regression guard: OK (base case on ℕ; independent pair on the \
    uncountable carrier ℕ → Bool; identity closure: independent triple on Fin 3 and pair \
    witnesses with no bound on a large carrier; free-set derivation of the ℵ₁ bound applied \
    alongside the original, on an arbitrary two-generated closure and on the constant closure; \
    headline declarations on standard axioms)"
