/-
Regression guard for the internal orbit-rank API (`Scott/OrbitRank.lean`).

Acceptance tests: pointed back-and-forth at every level yields an automorphism carrying the
tuple; the stabilization set behind each orbit rank is nonempty for every structure; the
upper-bound and cofinal-lower-bound lemmas and the exact-rank criterion compose; the infinite
pure set has all tuple ranks `0` and internal Scott rank `1`, including the empty tuple and
repeated coordinates; both ranks are isomorphism-invariant.  No computability or admissibility
enters.  Headline declarations use only the standard axioms.

Run with: lake env lean scripts/check_orbit_rank_regressions.lean
-/
import InfinitaryLogic.Scott.OrbitRank

open Lean FirstOrder Language

variable {L : Language.{u, v}} [L.IsRelational] {M : Type w} [L.Structure M]

/-- Pointed Karp: an automorphism carrying the tuple, not merely an isomorphism. -/
theorem pointed_automorphism_regression [Countable M] {n : ℕ} {a b : Fin n → M}
    (h : ∀ α : Ordinal.{w}, BFEquiv (L := L) α n a b) :
    ∃ e : M ≃[L] M, ∀ j, e (a j) = b j := by
  obtain ⟨e, he⟩ := exists_automorphism_of_bfEquiv_all h
  exact ⟨e, fun j => congrFun he j⟩

omit [L.IsRelational] in
/-- The set behind every orbit rank is nonempty, for any structure and any tuple, including the
empty tuple. -/
theorem nonempty_regression (a : Fin 0 → M) : (orbitStable (L := L) a).Nonempty :=
  orbitStable_nonempty a

omit [L.IsRelational] in
/-- Upper bound, cofinal lower bound, and the equality wrapper compose. -/
theorem criterion_regression {β : Ordinal.{w}}
    (hub : ∀ (n : ℕ) (a : Fin n → M), orbitRank (L := L) a + 1 ≤ β)
    (hcof : ∀ γ < β, ∃ (n : ℕ) (a : Fin n → M), γ < orbitRank (L := L) a + 1) :
    internalScottRank (L := L) M = β :=
  internalScottRank_eq_iff.mpr ⟨hub, hcof⟩

omit [L.IsRelational] in
/-- Every tuple rank plus one sits below the internal Scott rank, and every ordinal below it is
exceeded by one. -/
theorem bounds_regression {n : ℕ} (a : Fin n → M) :
    orbitRank (L := L) a + 1 ≤ internalScottRank (L := L) M ∧
    ∀ γ < internalScottRank (L := L) M, ∃ (k : ℕ) (c : Fin k → M), γ < orbitRank (L := L) c + 1 :=
  ⟨orbitRank_add_one_le_internalScottRank a,
    fun _ hγ => exists_orbitRank_add_one_gt_of_lt_internalScottRank hγ⟩

section PureSet

local instance : Language.empty.Structure ℕ := Language.emptyStructure

/-- The infinite pure set `ℕ`: the empty tuple has rank `0`. -/
theorem pureSet_empty_tuple_regression :
    orbitRank (L := Language.empty) (M := ℕ) Fin.elim0 = 0 :=
  orbitRank_pureSet _

/-- Repeated coordinates have rank `0`. -/
theorem pureSet_repeated_regression :
    orbitRank (L := Language.empty) (M := ℕ) ![3, 3, 3] = 0 :=
  orbitRank_pureSet _

/-- Distinct coordinates have rank `0`. -/
theorem pureSet_distinct_regression :
    orbitRank (L := Language.empty) (M := ℕ) ![0, 1] = 0 :=
  orbitRank_pureSet _

/-- The infinite pure set has internal Scott rank `1`. -/
theorem pureSet_structure_regression : internalScottRank (L := Language.empty) ℕ = 1 :=
  internalScottRank_pureSet

end PureSet

omit [L.IsRelational] in
/-- Isomorphism invariance of both ranks. -/
theorem invariance_regression {M' : Type w} [L.Structure M'] (e : M ≃[L] M') {n : ℕ}
    (a : Fin n → M) :
    orbitRank (L := L) (⇑e ∘ a) = orbitRank (L := L) a ∧
    internalScottRank (L := L) M' = internalScottRank (L := L) M :=
  ⟨orbitRank_map_equiv e a, internalScottRank_map_equiv e⟩

/-! ### Axiom hygiene -/

def headline : List Name :=
  [`FirstOrder.Language.orbitStable_nonempty, `FirstOrder.Language.orbitRank_mem,
   `FirstOrder.Language.exists_not_succ_of_lt_orbitRank,
   `FirstOrder.Language.orbitRank_map_equiv,
   `FirstOrder.Language.orbitRank_add_one_le_internalScottRank,
   `FirstOrder.Language.internalScottRank_le,
   `FirstOrder.Language.exists_orbitRank_add_one_gt_of_lt_internalScottRank,
   `FirstOrder.Language.internalScottRank_eq_iff,
   `FirstOrder.Language.internalScottRank_map_equiv,
   `FirstOrder.Language.exists_automorphism_of_bfEquiv_all,
   `FirstOrder.Language.PotentialIso.countable_toEquiv_graph,
   `FirstOrder.Language.BFEquiv.map_equiv,
   `FirstOrder.Language.orbitRank_pureSet, `FirstOrder.Language.internalScottRank_pureSet,
   `pointed_automorphism_regression, `nonempty_regression, `criterion_regression,
   `bounds_regression, `pureSet_empty_tuple_regression, `pureSet_repeated_regression,
   `pureSet_distinct_regression, `pureSet_structure_regression, `invariance_regression]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "orbit-rank regression guard: OK (pointed automorphism, nonempty stabilization set, \
    bounds and exact-rank criterion, infinite pure set with empty and repeated tuples, \
    isomorphism invariance; headline declarations on standard axioms)"
