/-
Regression guard for the rank of a Scott process (`InfinitaryLogic/ScottProcess/Rank.lean`).

Every theorem below is *applied* to a concrete process, not only listed for its axioms.  The
processes are the toy processes `unitProcess δ` over the one-point level-`0` data, whose columns
are singletons, so injectivity itself is trivial there: the checks pin down the statement
shapes, the length conditions and the rank convention, not the combinatorics of the proofs.
`unitProcess` is at present the only constructor of Scott processes, so every test process here
is singleton-column and has rank `0`.  A positive-rank example (such as the graph of Larson's
Remark 5.11, of rank `1`) follows once the Scott process of a structure exists (PR 2c).

* **Rank convention** (no `+ 1`): `unitProcess δ` has rank `0` for every `δ > 1`
  (`unitProcess_isRank_zero`, `unitProcess_rank`, `IsRank.terminating`, `IsRank.rank_eq`,
  `IsRank.unique`, `isRank_iff`, `isRank_rank`).
* **`simp` evaluation**: `unitProcess_stabilizesAt_iff`, `unitProcess_terminating_iff` and
  `unitProcess_rank` are `@[simp]`, and `simp` alone decides the toy statements.
* **Partial rank**: `unitProcess 1` does not terminate (`unitProcess_terminating_iff`), and no
  level at or past the end of a process is a stabilization level.
* **Proposition 5.5** (`stabilizesAt_of_le`): from level `0` to level `ω` in a process of
  length `ω + ω` (through a limit), and `stabilizesAt_iff_rank_le`, `rank_le`.
* **Remark 5.7** (`stabilizesAt_add_nat`) and **Proposition 5.13**
  (`stabilizesAt_of_injectiveBeyond`) at `β = 1`, `n = 2` in the process of length `ω`.
* **The bijection form** (`stabilizesAt_iff_bijOn`).

The headline declarations use only the standard axioms.

Run with: lake env lean scripts/check_scott_rank_regressions.lean
-/
import InfinitaryLogic.ScottProcess.Rank

open Lean InfinitaryLogic InfinitaryLogic.ScottProcess InfinitaryLogic.ScottProcess.FreeArray

noncomputable section

/-- The toy process of length `ω`. -/
abbrev Pω : ScottProcess unitData.{0} Ordinal.omega0 :=
  unitProcess Ordinal.omega0 Ordinal.omega0_pos

/-- `1 < ω`. -/
theorem one_lt_ω : (1 : Ordinal.{0}) < Ordinal.omega0 := Ordinal.one_lt_omega0

/-- A finite ordinal plus one is below `ω`. -/
theorem nat_add_one_lt_ω (k : ℕ) : (k : Ordinal.{0}) + 1 < Ordinal.omega0 := by
  exact_mod_cast Ordinal.natCast_lt_omega0 (k + 1)

/-- `1 + 2 + 1 < ω`. -/
theorem one_add_two_add_one_lt_ω : (1 : Ordinal.{0}) + (2 : ℕ) + 1 < Ordinal.omega0 := by
  exact_mod_cast Ordinal.natCast_lt_omega0 (1 + 2 + 1)

/-- `1 + 1 < ω`. -/
theorem one_add_one_lt_ω : (1 : Ordinal.{0}) + 1 < Ordinal.omega0 := by
  simpa using nat_add_one_lt_ω 1

/-! ### Rank convention -/

/-- **Rank `0`, no `+ 1`** (`unitProcess_rank`): the process of length `ω` over the one-point
data terminates and has rank `0`. -/
theorem unitProcess_rank_zero : ∃ h : Pω.Terminating, Pω.rank h = 0 :=
  have h : Pω.Terminating := (unitProcess_terminating_iff _).2 one_lt_ω
  ⟨h, unitProcess_rank _ h⟩

/-- `IsRank.terminating`, `IsRank.rank_eq` and `IsRank.unique` compute the same rank. -/
theorem unitProcess_rank_eq :
    ∃ h : Pω.Terminating, Pω.rank h = 0 ∧ 0 = Pω.rank h :=
  have hr := unitProcess_isRank_zero Ordinal.omega0_pos one_lt_ω
  ⟨hr.terminating, hr.rank_eq _, hr.unique (Pω.isRank_rank hr.terminating)⟩

/-- `isRank_iff`: rank `0` is stabilization at `0` and at no smaller level. -/
theorem unitProcess_isRank_iff :
    Pω.StabilizesAt 0 ∧ ∀ γ < (0 : Ordinal.{0}), ¬ Pω.StabilizesAt γ :=
  Pω.isRank_iff.1 (unitProcess_isRank_zero Ordinal.omega0_pos one_lt_ω)

/-! ### Partial rank -/

/-- **Non-termination at length `1`**: `unitProcess 1` has no stabilization level. -/
theorem not_terminating_unitProcess_one : ¬ (unitProcess.{0} 1 zero_lt_one).Terminating :=
  fun h ↦ lt_irrefl _ ((unitProcess_terminating_iff zero_lt_one).1 h)

/-- **The length condition is part of stabilization** (`unitProcess_stabilizesAt_iff`):
`unitProcess 2` stabilizes at `0` but not at `1`, although every column of it is a
singleton. -/
theorem unitProcess_two_stabilizesAt :
    (unitProcess.{0} 2 two_pos).StabilizesAt 0 ∧ ¬ (unitProcess.{0} 2 two_pos).StabilizesAt 1 :=
  ⟨(unitProcess_stabilizesAt_iff two_pos 0).2 (by simp),
    (unitProcess_stabilizesAt_iff two_pos 1).not.2 (by simp)⟩

/-- **`simp` evaluation**: the `@[simp]` lemmas `unitProcess_stabilizesAt_iff`,
`unitProcess_terminating_iff` and `unitProcess_rank` decide the toy statements. -/
theorem unitProcess_simp (h : Pω.Terminating) :
    Pω.rank h = 0 ∧ (unitProcess.{0} 2 two_pos).StabilizesAt 0 ∧
      ¬ (unitProcess.{0} 2 two_pos).StabilizesAt 1 ∧
      ¬ (unitProcess.{0} 1 zero_lt_one).Terminating := by
  simp

/-! ### Proposition 5.5 -/

/-- `ω + 1 < ω + ω`. -/
theorem ω_add_one_lt : Ordinal.omega0.{0} + 1 < Ordinal.omega0 + Ordinal.omega0 :=
  (add_lt_add_iff_left _).2 one_lt_ω

/-- `1 < ω + ω`. -/
theorem one_lt_ω_add_ω : (1 : Ordinal.{0}) < Ordinal.omega0 + Ordinal.omega0 :=
  one_lt_ω.trans ((lt_add_one _).trans ω_add_one_lt)

/-- The toy process of length `ω + ω`. -/
abbrev Pω2 : ScottProcess unitData.{0} (Ordinal.omega0 + Ordinal.omega0) :=
  unitProcess _ (zero_lt_one.trans one_lt_ω_add_ω)

/-- **Proposition 5.5** (`stabilizesAt_of_le`): in the process of length `ω + ω`,
stabilization at `0` propagates to the limit level `ω`. -/
theorem unitProcess_stabilizesAt_ω : Pω2.StabilizesAt Ordinal.omega0 :=
  Pω2.stabilizesAt_of_le (unitProcess_isRank_zero _ one_lt_ω_add_ω).1 zero_le ω_add_one_lt

/-- **Proposition 5.5 through the rank** (`stabilizesAt_iff_rank_le`, `rank_le`): in the process
of length `ω`, the stabilization levels are the finite ones, and the rank is at most each. -/
theorem unitProcess_stabilizesAt_nat (h : Pω.Terminating) (k : ℕ) :
    Pω.StabilizesAt k ∧ Pω.rank h ≤ k := by
  have hk : Pω.StabilizesAt k :=
    (Pω.stabilizesAt_iff_rank_le h).2 ⟨by simp, nat_add_one_lt_ω k⟩
  exact ⟨hk, Pω.rank_le h hk⟩

/-! ### Remark 5.7 and Proposition 5.13 -/

/-- **Remark 5.7** (`stabilizesAt_add_nat`): injectivity of `V_{1,2}` on the columns above `2`
gives stabilization at `1 + 2`.  The hypothesis is a bare lambda: no proof of `1 + 1 < ω` has
to be supplied. -/
theorem unitProcess_add_nat : Pω.StabilizesAt (1 + (2 : ℕ)) :=
  Pω.stabilizesAt_add_nat one_add_two_add_one_lt_ω fun _ _ x _ y _ _ ↦ Subsingleton.elim x y

/-- **Definition 5.8 and Proposition 5.13** (`stabilizesAt_of_injectiveBeyond`): the process of
length `ω` is injective beyond any `φ ∈ Φ^2_1`, hence stabilizes at `1 + 2`.  `hinj` is stated
over `one_add_one_lt_ω`, not over the proof of `1 + 1 < ω` derived in the statement. -/
theorem unitProcess_injectiveBeyond (φ : Ψ unitData.{0} 1 2) : Pω.StabilizesAt (1 + (2 : ℕ)) :=
  have hinj : Pω.InjectiveBeyond one_add_one_lt_ω φ := fun _ _ _ _ _ ↦
    ⟨Classical.arbitrary _, ⟨Set.mem_univ _, Subsingleton.elim _ _⟩,
      fun _ _ ↦ Subsingleton.elim _ _⟩
  Pω.stabilizesAt_of_injectiveBeyond one_add_two_add_one_lt_ω (Set.mem_univ φ) hinj

/-! ### The bijection form -/

/-- **`stabilizesAt_iff_bijOn`**: at the stabilization level `1 + 2`, `V_{3,4}` maps every column
of `Φ_{3+1}` bijectively onto the same column of `Φ_3`. -/
theorem unitProcess_bijOn (φ : Ψ unitData.{0} 1 2) (n : ℕ) :
    ∃ h : (1 : Ordinal.{0}) + (2 : ℕ) + 1 < Ordinal.omega0,
      Set.BijOn (V (lt_add_one _).le) (Pω.Φ _ h n) (Pω.Φ _ ((lt_add_one _).trans h) n) := by
  obtain ⟨h, hb⟩ := (Pω.stabilizesAt_iff_bijOn _).1 (unitProcess_injectiveBeyond φ)
  exact ⟨h, hb n⟩

end

/-! ### Axiom hygiene -/

def headline : List Name :=
  [`InfinitaryLogic.ScottProcess.StabilizesAt,
   `InfinitaryLogic.ScottProcess.stabilizesAt_iff_bijOn,
   `InfinitaryLogic.ScottProcess.stabilizesAt_of_le,
   `InfinitaryLogic.ScottProcess.Terminating, `InfinitaryLogic.ScottProcess.IsRank,
   `InfinitaryLogic.ScottProcess.rank, `InfinitaryLogic.ScottProcess.isRank_iff,
   `InfinitaryLogic.ScottProcess.isRank_rank, `InfinitaryLogic.ScottProcess.IsRank.unique,
   `InfinitaryLogic.ScottProcess.IsRank.terminating,
   `InfinitaryLogic.ScottProcess.IsRank.rank_eq, `InfinitaryLogic.ScottProcess.rank_le,
   `InfinitaryLogic.ScottProcess.stabilizesAt_iff_rank_le,
   `InfinitaryLogic.ScottProcess.stabilizesAt_add_nat,
   `InfinitaryLogic.ScottProcess.InjectiveBeyond,
   `InfinitaryLogic.ScottProcess.stabilizesAt_of_injectiveBeyond,
   `InfinitaryLogic.ScottProcess.unitProcess_stabilizesAt_iff,
   `InfinitaryLogic.ScottProcess.unitProcess_terminating_iff,
   `InfinitaryLogic.ScottProcess.unitProcess_isRank_zero,
   `InfinitaryLogic.ScottProcess.unitProcess_rank,
   `unitProcess_rank_zero, `unitProcess_rank_eq, `unitProcess_isRank_iff,
   `not_terminating_unitProcess_one, `unitProcess_two_stabilizesAt, `unitProcess_simp,
   `unitProcess_stabilizesAt_ω, `unitProcess_stabilizesAt_nat, `unitProcess_add_nat,
   `unitProcess_injectiveBeyond, `unitProcess_bijOn]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "scott-rank regression guard: OK (applied: rank 0 of unitProcess via unitProcess_rank, \
    IsRank.terminating, IsRank.rank_eq, IsRank.unique, isRank_iff and isRank_rank; \
    non-termination at length 1 and the length condition at the end of a process; simp \
    evaluation of the toy process; Proposition 5.5 through the limit level omega \
    and via stabilizesAt_iff_rank_le and rank_le; Remark 5.7; Definition 5.8 and Proposition \
    5.13; stabilizesAt_iff_bijOn; headline declarations on standard axioms)"
