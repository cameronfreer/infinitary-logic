/-
Regression guard for the rank of the Scott process of a structure against the orbit ranks and the
internal Scott rank (`InfinitaryLogic/ScottProcess/RankComparison.lean`).

Every theorem below is *applied* to a concrete structure, not only listed for its axioms.  The
two conventions are `R = ⨆ a, orbitRank a` (the lifted process rank) and
`S = ⨆ a, (orbitRank a + 1) = internalScottRank`.

* **The infinite pure set** `ℕ` over the empty language: the process of length `δ > 1` has
  rank `0` (`isRank_iff_lift_eq_iSup_orbitRank`, from `orbitRank_pure_eq_zero`, and
  `isRank_iff_of_not_isSuccLimit`, from `internalScottRank_pureSet`); the empty tuple attains
  the supremum, so `internalScottRank ℕ = 1` is read off the rank through
  `lift_rank_add_one_eq_internalScottRank_iff`, and the non-attained equation fails
  (`lift_rank_eq_internalScottRank_iff`).  The same on `ULift.{w} ℕ`, with
  `Ordinal.lift.{w}` in `Ordinal.{w}`.
* **The exact-`ω` carrier** `FiberExactOmega.Carrier'` over the relational `lang ℕ
  Language.empty`: from `internalScottRank_exactOmega` (a limit), the process of length `ω + 2`
  has rank `ω` (`isRank_iff_of_isSuccLimit`); non-attainment (every orbit rank is finite) is
  derived from `orbitRank_add_one_le_internalScottRank`, and the non-attained comparison
  `lift_rank_eq_internalScottRank_iff` gives `internalScottRank = ω` back from the rank.  The
  process stabilizes at `ω` and at no finite level.
* **Larson's Remark 5.11 graph** on `Bool × ℕ` (the `true` side an infinite clique, the `false`
  side infinitely many isolated nodes): every tuple has orbit rank at most `1` (same equality
  pattern and same sides is a back-and-forth system, and equivalence at level `1` detects the
  sides), `(true, 0)` has orbit rank `1` (it is equivalent to `(false, 0)` at level `0` and not at
  level `1`), so the process of length `3` stabilizes at `1` and not at `0` and has rank `1`
  (`stabilizesAt_iff_bfEquiv`, `stabilizesAt_iff_selfStabilizesCompletely`,
  `isRank_iff_isLeast_selfStabilizesCompletely`, `isRank_iff_lift_eq_iSup_orbitRank`,
  `sInf_selfStabilizesCompletely_eq_iSup_orbitRank`); the supremum is attained, so
  `internalScottRank = 2` (`lift_rank_add_one_eq_internalScottRank_iff`), consistent with
  `lift_rank_le_internalScottRank` and `internalScottRank_le_lift_rank_add_one`.
* **Bound transport** (`stabilizesAt_of_orbitRank_le`, `orbitRank_le_of_stabilizesAt`,
  `rank_le_of_orbitRank_le`): on the graph, orbit ranks at most `1` give stabilization at `1`,
  and stabilization at `0` would bound the orbit rank of `(true, 0)` by `0`; on the exact-`ω`
  carrier, the strict pointwise bounds `orbitRank a < ω` give `rank ≤ ω`, and the rank is `ω`,
  not below it.

The headline declarations use only the standard axioms.

Run with: lake env lean scripts/check_rank_comparison_regressions.lean
-/
import InfinitaryLogic.ScottProcess.RankComparison
import InfinitaryLogic.ModelTheory.FiberExactOmega
import Mathlib.Tactic.NormNum

open Lean Order FirstOrder FirstOrder.Language InfinitaryLogic InfinitaryLogic.ScottProcess.Semantic

universe w

noncomputable section

/-! ### The infinite pure set -/

section PureSet

/-- Every tuple of the pure set `ℕ` has orbit rank `0`, so the supremum is `0`. -/
theorem nat_iSup_orbitRank :
    (⨆ x : (Σ n : ℕ, Fin n → ℕ), orbitRank (L := Language.empty) x.2) = 0 :=
  Ordinal.iSup_eq_zero_iff.2 fun x ↦ PureSet.orbitRank_pure_eq_zero x.2

/-- `1` is not a limit ordinal. -/
theorem not_isSuccLimit_one : ¬ IsSuccLimit (1 : Ordinal.{w}) := by
  simpa using not_isSuccLimit_succ (0 : Ordinal.{w})

/-- **The pure set has process rank `0`** (`isRank_iff_lift_eq_iSup_orbitRank`). -/
theorem nat_isRank_zero {δ : Ordinal.{0}} (hδ : 1 < δ) :
    (scottProcessOf Language.empty ℕ δ (zero_lt_one.trans hδ)).IsRank 0 :=
  isRank_iff_lift_eq_iSup_orbitRank.2 ⟨by rwa [zero_add], by rw [nat_iSup_orbitRank]; simp⟩

/-- **The same rank from the internal Scott rank** (`isRank_iff_of_not_isSuccLimit`, with
`internalScottRank_pureSet`). -/
theorem nat_isRank_zero' {δ : Ordinal.{0}} (hδ : 1 < δ) :
    (scottProcessOf Language.empty ℕ δ (zero_lt_one.trans hδ)).IsRank 0 := by
  have hS : internalScottRank (L := Language.empty) ℕ = 1 := internalScottRank_pureSet
  refine (isRank_iff_of_not_isSuccLimit (hS ▸ not_isSuccLimit_one)).2 ⟨by rwa [zero_add], ?_⟩
  rw [hS]
  simp

/-- **Attained case on the pure set**: the empty tuple has orbit rank `0 = rank`, so the internal
Scott rank is `rank + 1 = 1` (`lift_rank_add_one_eq_internalScottRank_iff`), and it is not the
rank (`lift_rank_eq_internalScottRank_iff`). -/
theorem nat_internalScottRank {δ : Ordinal.{0}} (hδ : 1 < δ) :
    internalScottRank (L := Language.empty) ℕ = 1 ∧
      internalScottRank (L := Language.empty) ℕ ≠
        Ordinal.lift.{0} ((scottProcessOf Language.empty ℕ δ (zero_lt_one.trans hδ)).rank
          (nat_isRank_zero hδ).terminating) := by
  have hr := (nat_isRank_zero hδ).rank_eq (nat_isRank_zero hδ).terminating
  have hatt := (lift_rank_add_one_eq_internalScottRank_iff
    (nat_isRank_zero hδ).terminating).2 ⟨0, Fin.elim0, by
      rw [PureSet.orbitRank_pure_eq_zero, hr, Ordinal.lift_zero]⟩
  refine ⟨by rw [← hatt, hr]; simp, fun h ↦ ?_⟩
  have := (lift_rank_eq_internalScottRank_iff (nat_isRank_zero hδ).terminating).1 h.symm 0
    Fin.elim0
  rw [PureSet.orbitRank_pure_eq_zero, hr, Ordinal.lift_zero] at this
  exact lt_irrefl _ this

/-- The empty-language structure on `ULift.{w} ℕ`. -/
local instance instEmptyULift : Language.empty.Structure (ULift.{w} ℕ) := Language.emptyStructure

/-- **Universes**: the pure set `ULift.{w} ℕ` has process rank `0` in `Ordinal.{0}`. -/
theorem ulift_isRank_zero {δ : Ordinal.{0}} (hδ : 1 < δ) :
    (scottProcessOf Language.empty (ULift.{w} ℕ) δ (zero_lt_one.trans hδ)).IsRank 0 :=
  isRank_iff_lift_eq_iSup_orbitRank.2 ⟨by rwa [zero_add], by
    rw [Ordinal.lift_zero, eq_comm, Ordinal.iSup_eq_zero_iff]
    exact fun x ↦ PureSet.orbitRank_pure_eq_zero x.2⟩

/-- **Universes, attained case**: the lift to `Ordinal.{w}` of the rank of the process of
`ULift.{w} ℕ`, plus one, is its internal Scott rank `1`. -/
theorem ulift_internalScottRank {δ : Ordinal.{0}} (hδ : 1 < δ) :
    Ordinal.lift.{w} ((scottProcessOf Language.empty (ULift.{w} ℕ) δ (zero_lt_one.trans hδ)).rank
        (ulift_isRank_zero hδ).terminating) + 1 =
      internalScottRank (L := Language.empty) (ULift.{w} ℕ) ∧
    internalScottRank (L := Language.empty) (ULift.{w} ℕ) = 1 := by
  have hr := (ulift_isRank_zero hδ).rank_eq (ulift_isRank_zero hδ).terminating
  have hatt := (lift_rank_add_one_eq_internalScottRank_iff
    (ulift_isRank_zero hδ).terminating).2 ⟨0, Fin.elim0, by
      rw [PureSet.orbitRank_pure_eq_zero, hr, Ordinal.lift_zero]⟩
  exact ⟨hatt, by rw [← hatt, hr]; simp⟩

end PureSet

/-! ### The exact-`ω` carrier -/

section ExactOmega

open FirstOrder.Language.FiberAssembly FirstOrder.Language.FiberAssembly.ExactOmega

/-- The constant words `[0, …, 0]` are allowed rows. -/
theorem isAllowed_replicate (k : ℕ) : IsAllowed Aiic (List.replicate k 0) :=
  ⟨List.pairwise_replicate.2 (Or.inr le_rfl), fun i _ ↦ by simp [Aiic]⟩

/-- The exact-`ω` carrier is infinite: its rows `[0, …, 0]` are distinct. -/
instance : Infinite Carrier' :=
  Infinite.of_injective (fun k : ℕ ↦ (Carrier.row ⟨List.replicate k 0, isAllowed_replicate k⟩ :
    Carrier')) fun k l h ↦ by
      have := congrArg List.length (congrArg Subtype.val (Carrier.row.inj h))
      simpa using this

/-- `ω + 1 < ω + 2`. -/
theorem omega_add_one_lt : Ordinal.omega0.{0} + 1 < Ordinal.omega0 + 2 :=
  (add_lt_add_iff_left _).2 one_lt_two

/-- `0 < ω + 2`. -/
theorem omega_add_two_pos : 0 < Ordinal.omega0.{0} + 2 :=
  Ordinal.omega0_pos.trans_le le_self_add

/-- The process of the exact-`ω` carrier of length `ω + 2`. -/
abbrev omegaProcess := scottProcessOf (lang ℕ Language.empty) Carrier' _ omega_add_two_pos

/-- **The exact-`ω` carrier has process rank `ω`**, read off its internal Scott rank `ω`, a limit
(`isRank_iff_of_isSuccLimit`). -/
theorem omega_isRank : omegaProcess.IsRank Ordinal.omega0 := by
  have hS := internalScottRank_exactOmega
  refine (isRank_iff_of_isSuccLimit (hS ▸ Ordinal.isSuccLimit_omega0)).2
    ⟨omega_add_one_lt, ?_⟩
  rw [hS, Ordinal.lift_id]

/-- **Non-attainment** from the library bounds: every tuple of the exact-`ω` carrier has finite
orbit rank, since `orbitRank a + 1 ≤ internalScottRank = ω`. -/
theorem omega_orbitRank_lt {n : ℕ} (a : Fin n → Carrier') :
    orbitRank (L := lang ℕ Language.empty) a < Ordinal.omega0 :=
  add_one_le_iff.1 (internalScottRank_exactOmega ▸ orbitRank_add_one_le_internalScottRank a)

/-- **Non-attained case on the exact-`ω` carrier**: every orbit rank is below the lifted rank
`ω`, so the lifted rank is the internal Scott rank (`lift_rank_eq_internalScottRank_iff`), and
their common value `ω` is also the supremum of the orbit ranks (`lift_rank_eq_iSup_orbitRank`);
`lift_rank_le_internalScottRank` and `internalScottRank_le_lift_rank_add_one` agree. -/
theorem omega_rank_eq :
    omegaProcess.rank omega_isRank.terminating = Ordinal.omega0 ∧
      Ordinal.lift.{0} (omegaProcess.rank omega_isRank.terminating) =
        internalScottRank (L := lang ℕ Language.empty) Carrier' ∧
      (⨆ x : (Σ n : ℕ, Fin n → Carrier'), orbitRank (L := lang ℕ Language.empty) x.2) =
        Ordinal.omega0 := by
  have h := omega_isRank.terminating
  have hr := omega_isRank.rank_eq h
  have hS := (lift_rank_eq_internalScottRank_iff h).2 fun n a ↦ by
    rw [hr, Ordinal.lift_id]
    exact omega_orbitRank_lt a
  refine ⟨hr, hS, ?_⟩
  rw [← lift_rank_eq_iSup_orbitRank h, hr, Ordinal.lift_id]

/-- The two unconditional bounds on the exact-`ω` carrier. -/
theorem omega_bounds :
    Ordinal.lift.{0} (omegaProcess.rank omega_isRank.terminating) ≤
        internalScottRank (L := lang ℕ Language.empty) Carrier' ∧
      internalScottRank (L := lang ℕ Language.empty) Carrier' ≤
        Ordinal.lift.{0} (omegaProcess.rank omega_isRank.terminating) + 1 :=
  ⟨lift_rank_le_internalScottRank _, internalScottRank_le_lift_rank_add_one _⟩

/-- **Bound transport with strict pointwise bounds**: every orbit rank is `< ω`, which gives
stabilization at `ω` and `rank ≤ ω` (`stabilizesAt_of_orbitRank_le`,
`rank_le_of_orbitRank_le`), and not more: the process stabilizes at no finite level, since that
would bound every orbit rank by a natural number (`orbitRank_le_of_stabilizesAt`). -/
theorem omega_bound_transport :
    omegaProcess.StabilizesAt Ordinal.omega0 ∧
      omegaProcess.rank omega_isRank.terminating ≤ Ordinal.omega0 ∧
      ∀ k : ℕ, ¬ omegaProcess.StabilizesAt k := by
  have hb : ∀ n (a : Fin n → Carrier'),
      orbitRank (L := lang ℕ Language.empty) a ≤ Ordinal.lift.{0} Ordinal.omega0 :=
    fun n a ↦ (Ordinal.lift_id Ordinal.omega0).symm ▸ (omega_orbitRank_lt a).le
  refine ⟨stabilizesAt_of_orbitRank_le omega_add_one_lt hb,
    rank_le_of_orbitRank_le _ hb, fun k hk ↦ ?_⟩
  have := omegaProcess.rank_le omega_isRank.terminating hk
  rw [omega_isRank.rank_eq] at this
  exact (Ordinal.natCast_lt_omega0 k).not_ge this

end ExactOmega

/-! ### Larson's Remark 5.11 graph -/

section Graph

/-- The one-symbol graph language. -/
inductive GSym : ℕ → Type
  /-- Adjacency. -/
  | adj : GSym 2

/-- The graph language: one binary relation, no functions. -/
def graphLang : Language := ⟨fun _ ↦ Empty, GSym⟩

/-- The graph language is relational. -/
instance : graphLang.IsRelational := fun _ ↦ inferInstanceAs (IsEmpty Empty)

/-- Adjacency in the graph of Remark 5.11: the `true` side is an infinite clique without loops,
the `false` side is an infinite set of isolated nodes. -/
def Adj (x y : Bool × ℕ) : Prop := x.1 = true ∧ y.1 = true ∧ x ≠ y

/-- The graph of Remark 5.11. -/
instance instGraph : graphLang.Structure (Bool × ℕ) where
  funMap f _ := (f : Empty).elim
  RelMap {n} R v := match n, R with
    | _, GSym.adj => Adj (v 0) (v 1)

/-- Same equality pattern and same sides: the back-and-forth system of the graph. -/
def SideInv {n : ℕ} (a b : Fin n → Bool × ℕ) : Prop :=
  (∀ i j, a i = a j ↔ b i = b j) ∧ ∀ i, (a i).1 = (b i).1

/-- `SideInv` is symmetric. -/
theorem SideInv.symm {n : ℕ} {a b : Fin n → Bool × ℕ} (h : SideInv a b) : SideInv b a :=
  ⟨fun i j ↦ (h.1 i j).symm, fun i ↦ (h.2 i).symm⟩

/-- `SideInv` gives the same atomic type. -/
theorem SideInv.sameAtomicType {n : ℕ} {a b : Fin n → Bool × ℕ} (h : SideInv a b) :
    SameAtomicType (L := graphLang) a b := by
  intro idx
  cases idx with
  | eq i j => exact h.1 i j
  | rel R f =>
    cases R
    show Adj (a (f 0)) (a (f 1)) ↔ Adj (b (f 0)) (b (f 1))
    simp only [Adj, h.2, (h.1 _ _).not]

/-- `SideInv` is preserved by appending matched points on the same side. -/
theorem SideInv.snoc {n : ℕ} {a b : Fin n → Bool × ℕ} (h : SideInv a b) {x y : Bool × ℕ}
    (hxy : ∀ i, a i = x ↔ b i = y) (hside : x.1 = y.1) :
    SideInv (Fin.snoc a x : Fin (n + 1) → Bool × ℕ) (Fin.snoc b y) := by
  refine ⟨PureSet.pattern_snoc h.1 hxy, fun p ↦ ?_⟩
  refine Fin.lastCases ?_ (fun p ↦ ?_) p <;> simp only [Fin.snoc_last, Fin.snoc_castSucc]
  · exact hside
  · exact h.2 p

/-- The forth step of `SideInv`: an old point is answered by its match, a fresh point by a fresh
point on the same side. -/
theorem SideInv.forth {n : ℕ} {a b : Fin n → Bool × ℕ} (h : SideInv a b) (m : Bool × ℕ) :
    ∃ m', SideInv (Fin.snoc a m : Fin (n + 1) → Bool × ℕ) (Fin.snoc b m') := by
  by_cases hm : ∃ i, a i = m
  · obtain ⟨i, rfl⟩ := hm
    exact ⟨b i, h.snoc (fun j ↦ h.1 j i) (h.2 i)⟩
  · push Not at hm
    have hinf : {y : Bool × ℕ | y.1 = m.1}.Infinite :=
      Set.infinite_of_injective_forall_mem (f := fun k : ℕ ↦ (m.1, k))
        (fun _ _ e ↦ (Prod.mk.inj e).2) fun _ ↦ rfl
    obtain ⟨y, hy1, hy2⟩ := hinf.exists_notMem_finite (Set.finite_range b)
    exact ⟨y, h.snoc (fun i ↦ ⟨fun e ↦ (hm i e).elim, fun e ↦ (hy2 ⟨i, e⟩).elim⟩) hy1.symm⟩

/-- The back-and-forth system as a potential isomorphism of the graph with itself. -/
def invIso : PotentialIso graphLang (Bool × ℕ) (Bool × ℕ) :=
  PotentialIso.ofExtensionFamily (fun _ a b ↦ SideInv a b)
    ⟨fun i ↦ i.elim0, fun i ↦ i.elim0⟩ (fun h ↦ h.sameAtomicType) (fun h m ↦ h.forth m)
    fun h m ↦ let ⟨m', h'⟩ := h.symm.forth m; ⟨m', h'.symm⟩

/-- `SideInv` gives equivalence at every level. -/
theorem SideInv.bfEquiv {n : ℕ} {a b : Fin n → Bool × ℕ} (h : SideInv a b) (γ : Ordinal.{0}) :
    BFEquiv (L := graphLang) γ n a b :=
  invIso.family_bfEquiv γ h

/-- `1 = succ 0` in `Ordinal.{0}`. -/
theorem one_eq_succ_zero : (1 : Ordinal.{0}) = succ 0 := by
  rw [succ_eq_add_one, zero_add]

/-- Equivalence at level `1` carries the `true` side: a clique point has a neighbour. -/
theorem side_of_bfEquiv_one {n : ℕ} {a b : Fin n → Bool × ℕ}
    (h : BFEquiv (L := graphLang) (1 : Ordinal.{0}) n a b) (i : Fin n) (ha : (a i).1 = true) :
    (b i).1 = true := by
  rw [one_eq_succ_zero] at h
  obtain ⟨m', hm'⟩ := h.forth (true, (a i).2 + 1)
  have hadj := ((BFEquiv.zero _ _).1 hm' (.rel GSym.adj ![i.castSucc, Fin.last n])).1 (by
    show Adj _ _
    simp only [Function.comp, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.snoc_castSucc,
      Fin.snoc_last]
    exact ⟨ha, rfl, fun e ↦ by simpa using congrArg Prod.snd e⟩)
  change Adj _ _ at hadj
  simpa [Fin.snoc_castSucc] using hadj.1

/-- Equivalence at level `1` gives `SideInv`. -/
theorem inv_of_bfEquiv_one {n : ℕ} {a b : Fin n → Bool × ℕ}
    (h : BFEquiv (L := graphLang) (1 : Ordinal.{0}) n a b) : SideInv a b :=
  ⟨h.eq_iff_eq, fun i ↦ Bool.eq_iff_iff.2
    ⟨side_of_bfEquiv_one h i, side_of_bfEquiv_one h.symm i⟩⟩

/-- Every tuple of the graph has orbit rank at most `1`. -/
theorem graph_orbitRank_le_one {n : ℕ} (a : Fin n → Bool × ℕ) :
    orbitRank (L := graphLang) a ≤ 1 :=
  orbitRank_le_of_mem fun _ hb γ ↦ (inv_of_bfEquiv_one hb).bfEquiv γ

/-- The clique point `(true, 0)` and the isolated point `(false, 0)`. -/
abbrev vT : Fin 1 → Bool × ℕ := ![(true, 0)]

/-- The isolated point `(false, 0)`. -/
abbrev vF : Fin 1 → Bool × ℕ := ![(false, 0)]

/-- `(true, 0)` and `(false, 0)` are equivalent at level `0`: a single point without a loop. -/
theorem vT_vF_zero : BFEquiv (L := graphLang) (0 : Ordinal.{0}) 1 vT vF := by
  refine (BFEquiv.zero _ _).2 fun idx ↦ ?_
  cases idx with
  | eq i j =>
    show vT i = vT j ↔ vF i = vF j
    simp [Subsingleton.elim i j]
  | rel R f =>
    cases R
    show Adj _ _ ↔ Adj _ _
    simp [Adj, Subsingleton.elim (f 0) (f 1)]

/-- `(true, 0)` and `(false, 0)` are not equivalent at level `1`. -/
theorem vT_vF_not_one : ¬ BFEquiv (L := graphLang) (1 : Ordinal.{0}) 1 vT vF := fun h ↦
  absurd ((inv_of_bfEquiv_one h).2 0) (by simp)

/-- The clique point `(true, 0)` has orbit rank exactly `1`. -/
theorem vT_orbitRank : orbitRank (L := graphLang) vT = 1 := by
  refine (graph_orbitRank_le_one vT).antisymm (le_of_not_gt fun hlt ↦ vT_vF_not_one ?_)
  have h0 : orbitRank (L := graphLang) vT = 0 := lt_one_iff.1 hlt
  exact bfEquiv_all_of_bfEquiv_orbitRank (h0 ▸ vT_vF_zero) 1

/-- `0 < 3` in `Ordinal.{0}`. -/
theorem graphLength_pos : (0 : Ordinal.{0}) < 3 := by norm_num

/-- `1 + 1 < 3` in `Ordinal.{0}`: the length condition for stabilization at `1`. -/
theorem one_add_one_lt_three : (1 : Ordinal.{0}) + 1 < 3 := by
  rw [one_add_one_eq_two]
  exact_mod_cast (show (2 : ℕ) < 3 by decide)

/-- The process of the graph of length `3`. -/
abbrev graphProcess := scottProcessOf graphLang (Bool × ℕ) 3 graphLength_pos

/-- **Bound transport on the graph**: orbit ranks at most `1` give stabilization at `1`
(`stabilizesAt_of_orbitRank_le`); stabilization at `0` would bound the orbit rank of `(true, 0)`
by `0` (`orbitRank_le_of_stabilizesAt`). -/
theorem graph_stabilizesAt :
    graphProcess.StabilizesAt 1 ∧ ¬ graphProcess.StabilizesAt 0 := by
  refine ⟨stabilizesAt_of_orbitRank_le one_add_one_lt_three fun _ a ↦ ?_,
    fun h ↦ ?_⟩
  · rw [Ordinal.lift_id]
    exact graph_orbitRank_le_one a
  · have := orbitRank_le_of_stabilizesAt h vT
    rw [vT_orbitRank, Ordinal.lift_id] at this
    exact absurd this (by norm_num)

/-- **The graph of Remark 5.11 has process rank `1`**: it stabilizes at `1` and not at `0`. -/
theorem graph_isRank : graphProcess.IsRank 1 :=
  (ScottProcess.isRank_iff _).2 ⟨graph_stabilizesAt.1, fun _ hγ ↦ lt_one_iff.1 hγ ▸
    graph_stabilizesAt.2⟩

/-- **The per-level statement on the graph** (`stabilizesAt_iff_bfEquiv`): at level `0`, the
tuples `(true, 0)` and `(false, 0)` are equivalent at level `0` and not at level `1`, which is
exactly the failure of stabilization; `stabilizesAt_iff_selfStabilizesCompletely` reads
stabilization at `1` as self-stabilization at `1`. -/
theorem graph_per_level :
    ¬ graphProcess.StabilizesAt 0 ∧
      SelfStabilizesCompletely (L := graphLang) (Bool × ℕ) (1 : Ordinal.{0}) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have := (stabilizesAt_iff_bfEquiv.1 h).2 1 vT vF (by rw [Ordinal.lift_id]; exact vT_vF_zero)
    rw [Ordinal.lift_id, zero_add] at this
    exact vT_vF_not_one this
  · have := (stabilizesAt_iff_selfStabilizesCompletely.1 graph_stabilizesAt.1).2
    rwa [Ordinal.lift_id] at this

/-- **The rank through self-stabilization and the orbit ranks**
(`isRank_iff_isLeast_selfStabilizesCompletely`, `isRank_iff_lift_eq_iSup_orbitRank`,
`sInf_selfStabilizesCompletely_eq_iSup_orbitRank`): `1` is the least self-stabilization level
and the supremum of the orbit ranks. -/
theorem graph_rank_readings :
    IsLeast {γ : Ordinal.{0} | SelfStabilizesCompletely (L := graphLang) (Bool × ℕ)
        (Ordinal.lift.{0} γ)} 1 ∧
      (⨆ x : (Σ n : ℕ, Fin n → Bool × ℕ), orbitRank (L := graphLang) x.2) = 1 ∧
      sInf {α : Ordinal.{0} | SelfStabilizesCompletely (L := graphLang) (Bool × ℕ) α} = 1 := by
  have hR := (isRank_iff_lift_eq_iSup_orbitRank.1 graph_isRank).2
  rw [Ordinal.lift_id] at hR
  exact ⟨(isRank_iff_isLeast_selfStabilizesCompletely.1 graph_isRank).2, hR.symm,
    sInf_selfStabilizesCompletely_eq_iSup_orbitRank.trans hR.symm⟩

/-- **Attained case on the graph**: `(true, 0)` has orbit rank `1 = rank`, so the internal Scott
rank is `rank + 1 = 2` (`lift_rank_add_one_eq_internalScottRank_iff`), in agreement with the
two unconditional bounds and with `isRank_iff_of_not_isSuccLimit`; `rank_le_of_orbitRank_le`
gives `rank ≤ 1` from the orbit bounds. -/
theorem graph_internalScottRank :
    internalScottRank (L := graphLang) (Bool × ℕ) = 2 ∧
      graphProcess.rank graph_isRank.terminating ≤ 1 ∧
      Ordinal.lift.{0} (graphProcess.rank graph_isRank.terminating) ≤
        internalScottRank (L := graphLang) (Bool × ℕ) ∧
      internalScottRank (L := graphLang) (Bool × ℕ) ≤
        Ordinal.lift.{0} (graphProcess.rank graph_isRank.terminating) + 1 ∧
      graphProcess.IsRank 1 := by
  have h := graph_isRank.terminating
  have hr := graph_isRank.rank_eq h
  have hatt := (lift_rank_add_one_eq_internalScottRank_iff h).2
    ⟨1, vT, by rw [vT_orbitRank, hr, Ordinal.lift_id]⟩
  have hS : internalScottRank (L := graphLang) (Bool × ℕ) = 2 := by
    rw [← hatt, hr, Ordinal.lift_id, one_add_one_eq_two]
  refine ⟨hS, rank_le_of_orbitRank_le h fun _ a ↦ by
      rw [Ordinal.lift_id]; exact graph_orbitRank_le_one a,
    lift_rank_le_internalScottRank h, internalScottRank_le_lift_rank_add_one h, ?_⟩
  have hns : ¬ IsSuccLimit (internalScottRank (L := graphLang) (Bool × ℕ)) := by
    rw [hS, ← one_add_one_eq_two, ← succ_eq_add_one]
    exact not_isSuccLimit_succ 1
  exact (isRank_iff_of_not_isSuccLimit hns).2 ⟨one_add_one_lt_three, by
    rw [hS, Ordinal.lift_id, one_add_one_eq_two]⟩

end Graph

end

/-! ### Axiom hygiene -/

/-- The declarations whose axioms are audited. -/
def headline : List Name :=
  [`InfinitaryLogic.ScottProcess.Semantic.selfStabilizesCompletely_iff_orbitRank_le,
   `InfinitaryLogic.ScottProcess.Semantic.sInf_selfStabilizesCompletely_eq_iSup_orbitRank,
   `InfinitaryLogic.ScottProcess.Semantic.stabilizesAt_iff_bfEquiv,
   `InfinitaryLogic.ScottProcess.Semantic.stabilizesAt_iff_selfStabilizesCompletely,
   `InfinitaryLogic.ScottProcess.Semantic.stabilizesAt_iff_orbitRank_le,
   `InfinitaryLogic.ScottProcess.Semantic.isRank_iff_isLeast_selfStabilizesCompletely,
   `InfinitaryLogic.ScottProcess.Semantic.isRank_iff_lift_eq_iSup_orbitRank,
   `InfinitaryLogic.ScottProcess.Semantic.lift_rank_eq_iSup_orbitRank,
   `InfinitaryLogic.ScottProcess.Semantic.lift_rank_le_internalScottRank,
   `InfinitaryLogic.ScottProcess.Semantic.internalScottRank_le_lift_rank_add_one,
   `InfinitaryLogic.ScottProcess.Semantic.lift_rank_add_one_eq_internalScottRank_iff,
   `InfinitaryLogic.ScottProcess.Semantic.lift_rank_eq_internalScottRank_iff,
   `InfinitaryLogic.ScottProcess.Semantic.isRank_iff_of_isSuccLimit,
   `InfinitaryLogic.ScottProcess.Semantic.isRank_iff_of_not_isSuccLimit,
   `InfinitaryLogic.ScottProcess.Semantic.stabilizesAt_of_orbitRank_le,
   `InfinitaryLogic.ScottProcess.Semantic.orbitRank_le_of_stabilizesAt,
   `InfinitaryLogic.ScottProcess.Semantic.rank_le_of_orbitRank_le,
   `nat_isRank_zero, `nat_isRank_zero', `nat_internalScottRank, `ulift_isRank_zero,
   `ulift_internalScottRank, `omega_isRank, `omega_rank_eq, `omega_bounds,
   `omega_bound_transport, `graph_orbitRank_le_one, `vT_orbitRank, `graph_stabilizesAt,
   `graph_isRank, `graph_per_level, `graph_rank_readings, `graph_internalScottRank]

/-- The standard axioms. -/
def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "rank-comparison regression guard: OK (applied: the infinite pure set N has process \
    rank 0 through isRank_iff_lift_eq_iSup_orbitRank and isRank_iff_of_not_isSuccLimit, and \
    internalScottRank 1 read off the rank through the attained comparison, the non-attained one \
    failing; the same on ULift N with Ordinal.lift; the exact-omega carrier has process rank \
    omega through isRank_iff_of_isSuccLimit, non-attainment from the library bounds, \
    internalScottRank omega back through the non-attained comparison, no finite stabilization \
    level; Larson's Remark 5.11 graph has orbit ranks at most 1, process rank 1 through \
    stabilizesAt_iff_bfEquiv, self-stabilization, the least self-stabilization level and the \
    supremum of the orbit ranks, and internalScottRank 2 through the attained comparison; bound \
    transport on the graph and, with strict bounds, on the exact-omega carrier; headline \
    declarations on standard axioms)"
