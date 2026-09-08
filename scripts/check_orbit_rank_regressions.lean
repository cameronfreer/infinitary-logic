/-
Regression guard for the internal orbit-rank API (`Scott/OrbitRank.lean`).

Acceptance tests: pointed back-and-forth at every level yields an automorphism carrying the
tuple; equivalence at the orbit rank is automorphism; the stabilization set behind each orbit
rank is nonempty for every structure; the supremum lemmas and the semantic exact-rank criterion
(orbits determined below `α`, non-automorphic `β`-equivalent tuples for every `β < α`) compose;
the graph `K₂ ⊔ K₃` separates the all-levels definition from one-step agreement (a `K₂`-vertex
and a `K₃`-vertex are equivalent at level `1` but not automorphic, so the orbit rank of a vertex
is at least `2`; one-step agreement would have given `0`); the infinite pure set has all tuple
ranks `0` and internal Scott rank `1`, including the empty tuple and repeated coordinates; both
ranks are isomorphism-invariant.  No computability or admissibility enters.  Headline
declarations use only the standard axioms.

Run with: lake env lean scripts/check_orbit_rank_regressions.lean
-/
import InfinitaryLogic.Scott.OrbitRank
import Mathlib.Tactic.FinCases

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
/-- Supremum API: upper bound, cofinal lower bound, and the equality wrapper compose. -/
theorem criterion_regression {β : Ordinal.{w}}
    (hub : ∀ (n : ℕ) (a : Fin n → M), orbitRank (L := L) a + 1 ≤ β)
    (hcof : ∀ γ < β, ∃ (n : ℕ) (a : Fin n → M), γ < orbitRank (L := L) a + 1) :
    internalScottRank (L := L) M = β :=
  internalScottRank_eq_iff.mpr ⟨hub, hcof⟩

/-- Equivalence at the orbit rank is exactly automorphism, for countable structures. -/
theorem orbit_characterization_regression [Countable M] {n : ℕ} {a b : Fin n → M} :
    BFEquiv (L := L) (orbitRank (L := L) a) n a b ↔ ∃ e : M ≃[L] M, ⇑e ∘ a = b :=
  bfEquiv_orbitRank_iff_exists_automorphism

/-- Semantic exact-rank criterion: orbits determined below `α`, and non-automorphic
`β`-equivalent tuples for every `β < α`, give internal Scott rank `α`. -/
theorem semantic_criterion_regression [Countable M] {α : Ordinal.{w}}
    (hup : ∀ (n : ℕ) (a : Fin n → M), ∃ β < α,
      ∀ b : Fin n → M, BFEquiv (L := L) β n a b → ∃ e : M ≃[L] M, ⇑e ∘ a = b)
    (hlow : ∀ β < α, ∃ (n : ℕ) (a b : Fin n → M),
      BFEquiv (L := L) β n a b ∧ ¬ ∃ e : M ≃[L] M, ⇑e ∘ a = b) :
    internalScottRank (L := L) M = α :=
  internalScottRank_eq_of_orbits hup hlow

omit [L.IsRelational] in
/-- Every tuple rank plus one sits below the internal Scott rank, and every ordinal below it is
exceeded by one. -/
theorem bounds_regression {n : ℕ} (a : Fin n → M) :
    orbitRank (L := L) a + 1 ≤ internalScottRank (L := L) M ∧
    ∀ γ < internalScottRank (L := L) M, ∃ (k : ℕ) (c : Fin k → M), γ < orbitRank (L := L) c + 1 :=
  ⟨orbitRank_add_one_le_internalScottRank a,
    fun _ hγ => exists_orbitRank_add_one_gt_of_lt_internalScottRank hγ⟩

/-! ### The graph `K₂ ⊔ K₃`

One binary relation on `Fin 5`: vertices `0, 1` form `K₂`, vertices `2, 3, 4` form `K₃`.  Every
vertex has a neighbour and a distinct non-neighbour, so all singletons are equivalent at level
`1`; a `K₂`-vertex has one neighbour and a `K₃`-vertex has two, so no automorphism carries one to
the other.  Under the all-levels definition the orbit rank of `![0]` is therefore at least `2`;
under one-step agreement it would have been `0`. -/

section Graph

/-- The one-symbol graph language. -/
inductive GSym : ℕ → Type
  | adj : GSym 2

/-- The graph language: one binary relation, no functions. -/
def graphLang : Language := ⟨fun _ => Empty, GSym⟩

instance : graphLang.IsRelational := fun _ => inferInstanceAs (IsEmpty Empty)

/-- Adjacency of `K₂ ⊔ K₃` on `Fin 5`. -/
def adjK : Fin 5 → Fin 5 → Bool
  | 0, 1 | 1, 0 => true
  | 2, 3 | 3, 2 | 2, 4 | 4, 2 | 3, 4 | 4, 3 => true
  | _, _ => false

/-- The structure `K₂ ⊔ K₃`. -/
instance instGraphK : graphLang.Structure (Fin 5) where
  funMap f _ := (f : Empty).elim
  RelMap {n} R v := match n, R with
    | _, GSym.adj => adjK (v 0) (v 1) = true

instance decRelMapK {n : ℕ} (R : graphLang.Relations n) (v : Fin n → Fin 5) :
    Decidable (Structure.RelMap R v) := by
  cases R
  exact inferInstanceAs (Decidable (adjK (v 0) (v 1) = true))

/-- Atomic types of concrete tuples in `K₂ ⊔ K₃` are decided by exhaustion over the finitely
many atoms of each arity. -/
theorem sameAtomicType_K {n : ℕ} (a b : Fin n → Fin 5)
    (heq : ∀ i j : Fin n, a i = a j ↔ b i = b j)
    (hrel : ∀ f : Fin 2 → Fin n, adjK (a (f 0)) (a (f 1)) = true ↔ adjK (b (f 0)) (b (f 1)) = true) :
    SameAtomicType (L := graphLang) (M := Fin 5) (N := Fin 5) a b := by
  intro idx
  cases idx with
  | eq i j => exact heq i j
  | rel R f =>
    cases R
    exact hrel f

/-- Vertices `0 ∈ K₂` and `2 ∈ K₃` are equivalent at level `1`. -/
theorem bfEquiv_one_K : BFEquiv (L := graphLang) (M := Fin 5) (N := Fin 5) 1 1 ![0] ![2] := by
  rw [show (1 : Ordinal) = Order.succ 0 by simp, BFEquiv.succ]
  refine ⟨(BFEquiv.zero _ _).mpr (sameAtomicType_K _ _ (by decide) (by decide)), ?_, ?_⟩
  · intro m
    -- match `m` by its relation to `0`: itself, its neighbour, or a non-neighbour
    have : ∃ n' : Fin 5, SameAtomicType (L := graphLang) (M := Fin 5) (N := Fin 5)
        (Fin.snoc ![0] m) (Fin.snoc ![2] n') := by
      fin_cases m
      · exact ⟨2, sameAtomicType_K _ _ (by decide) (by decide)⟩
      · exact ⟨3, sameAtomicType_K _ _ (by decide) (by decide)⟩
      · exact ⟨0, sameAtomicType_K _ _ (by decide) (by decide)⟩
      · exact ⟨0, sameAtomicType_K _ _ (by decide) (by decide)⟩
      · exact ⟨0, sameAtomicType_K _ _ (by decide) (by decide)⟩
    obtain ⟨n', hn'⟩ := this
    exact ⟨n', (BFEquiv.zero _ _).mpr hn'⟩
  · intro n'
    have : ∃ m : Fin 5, SameAtomicType (L := graphLang) (M := Fin 5) (N := Fin 5)
        (Fin.snoc ![0] m) (Fin.snoc ![2] n') := by
      fin_cases n'
      · exact ⟨2, sameAtomicType_K _ _ (by decide) (by decide)⟩
      · exact ⟨2, sameAtomicType_K _ _ (by decide) (by decide)⟩
      · exact ⟨0, sameAtomicType_K _ _ (by decide) (by decide)⟩
      · exact ⟨1, sameAtomicType_K _ _ (by decide) (by decide)⟩
      · exact ⟨1, sameAtomicType_K _ _ (by decide) (by decide)⟩
    obtain ⟨m, hm⟩ := this
    exact ⟨m, (BFEquiv.zero _ _).mpr hm⟩

/-- No automorphism carries `0 ∈ K₂` to `2 ∈ K₃`: the two neighbours of `2` would pull back to
two distinct neighbours of `0`, which has one. -/
theorem no_automorphism_K : ¬ ∃ e : Fin 5 ≃[graphLang] Fin 5, ⇑e ∘ ![0] = ![2] := by
  rintro ⟨e, he⟩
  have h0 : e 0 = 2 := congrFun he 0
  have hadj : ∀ x y : Fin 5, adjK (e x) (e y) = true ↔ adjK x y = true := fun x y => by
    have := e.map_rel GSym.adj ![x, y]
    simpa [instGraphK, Structure.RelMap, Function.comp] using this
  -- `e.symm 3` and `e.symm 4` are distinct neighbours of `0`
  have h3 : adjK 0 (e.symm 3) = true := by
    rw [← hadj, h0, e.apply_symm_apply]; decide
  have h4 : adjK 0 (e.symm 4) = true := by
    rw [← hadj, h0, e.apply_symm_apply]; decide
  have hne : e.symm 3 ≠ e.symm 4 := fun h => by
    have := congrArg e h
    simp only [Language.Equiv.apply_symm_apply] at this
    exact absurd this (by decide)
  -- but `0` has exactly one neighbour
  have hone : ∀ y : Fin 5, adjK 0 y = true → y = 1 := by decide
  exact hne ((hone _ h3).trans (hone _ h4).symm)

/-- **The orbit rank of a `K₂`-vertex is at least `2`**: levels `0` and `1` are not stabilization
levels because `![2]` is equivalent there without being automorphic. -/
theorem orbitRank_K_ge_two : 2 ≤ orbitRank (L := graphLang) (M := Fin 5) ![0] := by
  by_contra hlt
  push Not at hlt
  have hle : orbitRank (L := graphLang) (M := Fin 5) ![0] ≤ 1 := Order.lt_succ_iff.mp
    (by simpa [Order.succ_eq_add_one, one_add_one_eq_two] using hlt)
  exact no_automorphism_K (bfEquiv_orbitRank_iff_exists_automorphism.mp
    (BFEquiv.monotone hle bfEquiv_one_K))

end Graph

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
   `FirstOrder.Language.exists_not_all_of_lt_orbitRank,
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
   `FirstOrder.Language.bfEquiv_orbitRank_iff_exists_automorphism,
   `FirstOrder.Language.internalScottRank_le_of_orbits_determined,
   `FirstOrder.Language.le_internalScottRank_of_not_automorphic,
   `FirstOrder.Language.internalScottRank_eq_of_orbits,
   `pointed_automorphism_regression, `nonempty_regression, `criterion_regression,
   `orbit_characterization_regression, `semantic_criterion_regression,
   `bounds_regression, `bfEquiv_one_K, `no_automorphism_K, `orbitRank_K_ge_two,
   `pureSet_empty_tuple_regression, `pureSet_repeated_regression,
   `pureSet_distinct_regression, `pureSet_structure_regression, `invariance_regression]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "orbit-rank regression guard: OK (pointed automorphism, orbit characterization, \
    nonempty stabilization set, supremum and semantic exact-rank criteria, K2+K3 separates \
    all-levels from one-step, infinite pure set with empty and repeated tuples, isomorphism \
    invariance; headline declarations on standard axioms)"
