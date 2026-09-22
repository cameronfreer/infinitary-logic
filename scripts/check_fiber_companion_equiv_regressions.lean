/-
Regression guard for the companion row bijection and the companion equivalence
(`ModelTheory/FiberCompanionShift.lean`, `ModelTheory/FiberCompanionEquiv.lean`).

Bijection, on the repeated-letter path `π n = n / 2` with every letter allowed: **forward and
inverse equations at `N = 0`** (the path row goes to the empty row and the empty row pulls back to
the path row; `π|₁ ↦ π|₂`) and **at `N = 2`** (`π|₂`, `π|₂ ↦ π|₃`, and back); an **earlier prefix**
`π|₁` and an **off-path row** `[1]` fixed by both directions at `N = 2`.

Fiber pairs at `N = 2`: at the **changed label** `[0, 0, 1]` of the tail prefix `π|₂` the pair is
`(default, B 1)`; at the **long path label** `[0, 0, 1, 1]` of the path row the pair is
`(B 1, default)`, the reversed comparison.

Equivalence endpoint, on the exact-`ω` family (`ℕ`, `Fin (u + 1)`, `{u ≤ n}`) with the
**identity path** `π n = n`: `PathApproxAt` at level `m` with threshold `N = m` from the
pure-set threshold theorem, the one-level endpoint applied, and the **below-`ω` wrapper**.
Headline declarations use only the standard axioms.

Run with: lake env lean scripts/check_fiber_companion_equiv_regressions.lean
-/
import InfinitaryLogic.ModelTheory.FiberCompanionEquiv
import InfinitaryLogic.Scott.PureSetThreshold

open Lean FirstOrder Language FiberAssembly

/-! ### The bijection on the repeated-letter path -/

def Aall : ℕ → Set ℕ := fun _ => Set.univ

/-- The path `0, 0, 1, 1, 2, 2, …`. -/
def πh : ℕ → ℕ := fun n => n / 2

theorem path_regression : IsAllowedPath Aall πh :=
  ⟨fun _ _ h => Nat.div_le_div_right h, fun _ => Set.mem_univ _⟩

/-- The off-path row `[1]`. -/
def rowOne : Row Aall := ⟨[1], ⟨List.pairwise_singleton _ _, fun _ _ => Set.mem_univ _⟩⟩

theorem rowOne_not_tail (N : ℕ) : ¬ IsTailPrefix path_regression N rowOne := by
  rintro ⟨k, -, h⟩
  have := congrArg (fun p : Row Aall => p.1) h
  simp only [rowOne, prefixRow_val] at this
  have hk : k = 1 := by
    have := congrArg List.length this
    simp at this
    omega
  subst hk
  exact absurd this (by decide)

/-- **`N = 0`**: the path row goes to the empty row and back; every prefix is shifted. -/
theorem threshold_zero_regression :
    shiftRows path_regression 0 (Sum.inr ()) = prefixRow path_regression 0 ∧
    (prefixRow path_regression 0).1 = [] ∧
    (shiftRows path_regression 0).symm (prefixRow path_regression 0) = Sum.inr () ∧
    shiftRows path_regression 0 (Sum.inl (prefixRow path_regression 1)) =
      prefixRow path_regression 2 ∧
    (shiftRows path_regression 0).symm (prefixRow path_regression 2) =
      Sum.inl (prefixRow path_regression 1) :=
  ⟨shiftRows_inr _ _, by simp, shiftRows_symm_prefixRow _ _,
    shiftRows_inl_prefixRow _ (Nat.zero_le 1), shiftRows_symm_prefixRow_succ _ (Nat.zero_le 1)⟩

/-- **`N = 2`**: the shifted tail, forward and inverse. -/
theorem threshold_two_regression :
    shiftRows path_regression 2 (Sum.inr ()) = prefixRow path_regression 2 ∧
    (shiftRows path_regression 2).symm (prefixRow path_regression 2) = Sum.inr () ∧
    shiftRows path_regression 2 (Sum.inl (prefixRow path_regression 2)) =
      prefixRow path_regression 3 ∧
    (shiftRows path_regression 2).symm (prefixRow path_regression 3) =
      Sum.inl (prefixRow path_regression 2) :=
  ⟨shiftRows_inr _ _, shiftRows_symm_prefixRow _ _, shiftRows_inl_prefixRow _ le_rfl,
    shiftRows_symm_prefixRow_succ _ le_rfl⟩

/-- **Fixed rows at `N = 2`**: the earlier prefix `π|₁` and the off-path row `[1]`, both
directions. -/
theorem fixed_rows_regression :
    shiftRows path_regression 2 (Sum.inl (prefixRow path_regression 1)) =
      prefixRow path_regression 1 ∧
    (shiftRows path_regression 2).symm (prefixRow path_regression 1) =
      Sum.inl (prefixRow path_regression 1) ∧
    shiftRows path_regression 2 (Sum.inl rowOne) = rowOne ∧
    (shiftRows path_regression 2).symm rowOne = Sum.inl rowOne := by
  have h1 : ¬ IsTailPrefix path_regression 2 (prefixRow path_regression 1) :=
    not_isTailPrefix_of_length_lt _ (by simp)
  exact ⟨shiftRows_inl_of_not _ h1, shiftRows_symm_of_not _ h1,
    shiftRows_inl_of_not _ (rowOne_not_tail 2), shiftRows_symm_of_not _ (rowOne_not_tail 2)⟩

/-! ### Fiber pairs at `N = 2` -/

/-- **Changed label** of the tail prefix `π|₂`: `[0, 0, 1]` gives `(none, some 1)`. -/
theorem changed_label_regression :
    compIndex (pathPrefix πh 2) (prefixLabel πh 2) = none ∧
    compIndex (pathPrefix πh 3) (prefixLabel πh 2) = some 1 ∧
    (prefixLabel πh 2).1 = [0, 0, 1] :=
  ⟨compIndex_pathPrefix_prefixLabel πh 2, compIndex_pathPrefix_succ_prefixLabel πh 2, by decide⟩

/-- **Long path label** of the path row against `π|₂`: `[0, 0, 1, 1]` gives `(some 1, none)`, the
reversed comparison. -/
theorem long_label_regression :
    pathIndex πh (prefixLabel πh 3) = some 1 ∧
    compIndex (pathPrefix πh 2) (prefixLabel πh 3) = none ∧
    (prefixLabel πh 3).1 = [0, 0, 1, 1] :=
  ⟨pathIndex_prefixLabel πh 3, compIndex_pathPrefix_of_lt (by simp), by decide⟩

/-! ### The equivalence endpoint on the exact-`ω` family -/

abbrev Bfin : ℕ → Type := fun u => Fin (u + 1)

def Aiic : ℕ → Set ℕ := fun n => Set.Iic n

/-- The identity path. -/
def πid : ℕ → ℕ := id

theorem idpath_regression : IsAllowedPath Aiic πid :=
  ⟨fun _ _ h => h, fun _ => Set.mem_Iic.mpr le_rfl⟩

/-- **Approximation at level `m` with threshold `m`**, from the pure-set threshold theorem. -/
theorem pathApproxAt_regression (m : ℕ) :
    PathApproxAt Language.empty ℕ Bfin πid ((m : ℕ) : Ordinal.{0}) m := by
  intro k hk
  exact (PureSet.bfEquiv_nat_fin_iff m (k + 1)).mpr (by omega)

/-- **The one-level endpoint applied**: the companion along the identity path is
`m`-equivalent to the base. -/
theorem one_level_regression (m : ℕ) :
    BFEquiv (L := lang ℕ Language.empty) ((m : ℕ) : Ordinal.{0}) 0
      (Fin.elim0 : Fin 0 → CompanionCarrier ℕ Bfin Aiic πid)
      (Fin.elim0 : Fin 0 → PrefixCarrier ℕ Bfin Aiic) :=
  companion_bfEquiv_of_pathApproxAt ℕ Bfin idpath_regression (pathApproxAt_regression m)

/-- **Below `ω`**: the thresholds are chosen per level. -/
theorem pathApprox_regression : PathApprox Language.empty ℕ Bfin πid Ordinal.omega0.{0} := by
  intro β hβ
  obtain ⟨m, rfl⟩ := Ordinal.lt_omega0.mp hβ
  exact ⟨m, pathApproxAt_regression m⟩

theorem below_omega_regression :
    ∀ β < Ordinal.omega0.{0}, BFEquiv (L := lang ℕ Language.empty) β 0
      (Fin.elim0 : Fin 0 → CompanionCarrier ℕ Bfin Aiic πid)
      (Fin.elim0 : Fin 0 → PrefixCarrier ℕ Bfin Aiic) :=
  companion_bfEquiv ℕ Bfin idpath_regression pathApprox_regression

/-! ### Axiom hygiene -/

def headline : List Name :=
  [`FirstOrder.Language.FiberAssembly.shiftRows,
   `FirstOrder.Language.FiberAssembly.isTailPrefix_iff,
   `FirstOrder.Language.FiberAssembly.shiftRows_inl_prefixRow,
   `FirstOrder.Language.FiberAssembly.shiftRows_symm_prefixRow_succ,
   `FirstOrder.Language.FiberAssembly.companion_bfEquiv_of_pathApproxAt,
   `FirstOrder.Language.FiberAssembly.companion_bfEquiv,
   `path_regression, `threshold_zero_regression, `threshold_two_regression,
   `fixed_rows_regression, `changed_label_regression, `long_label_regression,
   `pathApproxAt_regression, `one_level_regression, `below_omega_regression]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "fiber companion-equivalence regression guard: OK (bijection at N = 0 and N = 2, fixed \
    earlier prefix and off-path row, changed-label and reversed long-label pairs, one-level \
    endpoint and below-omega wrapper on the exact-omega family; headline declarations on \
    standard axioms)"
