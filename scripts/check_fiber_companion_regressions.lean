/-
Regression guard for companion carriers (`ModelTheory/FiberCompanion.lean`).

The allowed path `π n = n / 2` over `U = ℕ` with nested allowed sets `A n = {u | u ≤ n}`: its
letters **repeat** (`0, 0, 1, 1, 2, …`), it is nondecreasing, and `n / 2 ≤ n`.

Checked: the **empty prefix** (`π|₀ = []` is the empty allowed row, and every label is off it, so
its component index is the default); **repeated letters** (`[0]` and `[0, 0]` lie on the path
with index `some 0`, `[0, 0, 0]` does not since `π 2 = 1`); **off-path labels** (`[1]` is not on
the path: index `none`, and every prefix row gives the default there); the **consecutive-prefix**
equation at a label of the wrong length; the path row and the prefix row `π|₂` have the same
fiber at `[0, 0]`; distinct prefix rows; and countability of the companion carrier.  Headline
declarations use only the standard axioms.

Run with: lake env lean scripts/check_fiber_companion_regressions.lean
-/
import InfinitaryLogic.ModelTheory.FiberCompanion

open Lean FirstOrder Language FiberAssembly

/-- Nested allowed sets: at position `n`, the letters `≤ n`. -/
def Aiic : ℕ → Set ℕ := fun n => Set.Iic n

/-- The path `0, 0, 1, 1, 2, 2, …`. -/
def π : ℕ → ℕ := fun n => n / 2

theorem path_regression : IsAllowedPath Aiic π :=
  ⟨fun _ _ h => Nat.div_le_div_right h, fun n => Set.mem_Iic.mpr (Nat.div_le_self n 2)⟩

/-- The labels used below. -/
def l0 : Label ℕ := ⟨[0], by decide⟩
def l00 : Label ℕ := ⟨[0, 0], by decide⟩
def l000 : Label ℕ := ⟨[0, 0, 0], by decide⟩
def l1 : Label ℕ := ⟨[1], by decide⟩

/-- **Empty prefix**: `π|₀` is the empty row, and every label is off it. -/
theorem empty_prefix_regression :
    (prefixRow path_regression 0).1 = [] ∧
    ∀ τ : Label ℕ, compIndex (pathPrefix π 0) τ = none :=
  ⟨by simp, fun τ => compIndex_pathPrefix_of_lt (List.length_pos_of_ne_nil τ.2)⟩

/-- **Repeated letters**: `[0]` and `[0, 0]` lie on the path, `[0, 0, 0]` does not. -/
theorem repeated_letters_regression :
    pathIndex π l0 = some 0 ∧ pathIndex π l00 = some 0 ∧ pathIndex π l000 = none := by
  refine ⟨pathIndex_of_isPathPrefix (by decide), pathIndex_of_isPathPrefix (by decide),
    pathIndex_of_not_isPathPrefix (by decide)⟩

/-- **Off-path label**: `[1]` is not on the path, and every prefix row gives the default there. -/
theorem off_path_regression :
    pathIndex π l1 = none ∧ ∀ k, compIndex (pathPrefix π k) l1 = none := by
  refine ⟨pathIndex_of_not_isPathPrefix (by decide), fun k => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact compIndex_pathPrefix_of_lt (by decide)
  · rw [compIndex_pathPrefix_of_le (show l1.1.length ≤ k from hk)]
    exact pathIndex_of_not_isPathPrefix (by decide)

/-- **Consecutive prefixes** agree at `[0]` (length `1 ≠ 2`) and differ at `[0, 0]`. -/
theorem consecutive_regression :
    compIndex (pathPrefix π 2) l0 = compIndex (pathPrefix π 1) l0 ∧
    compIndex (pathPrefix π 2) (prefixLabel π 1) = some 0 ∧
    compIndex (pathPrefix π 1) (prefixLabel π 1) = none :=
  ⟨compIndex_pathPrefix_succ_of_ne (by decide), compIndex_pathPrefix_succ_prefixLabel π 1,
    compIndex_pathPrefix_prefixLabel π 1⟩

/-- The path row and `π|₂` have the same fiber at `[0, 0]`, for any components. -/
theorem same_fiber_regression (Bstar : Type) (B : ℕ → Type) :
    pathFiber Bstar B Aiic π (Sum.inl (prefixRow path_regression 2)) l00 =
      pathFiber Bstar B Aiic π (Sum.inr ()) l00 :=
  pathFiber_inl_prefixRow_of_le Bstar B Aiic π (by decide)

/-- Prefix rows of different lengths are different. -/
theorem distinct_rows_regression : prefixRow path_regression 1 ≠ prefixRow path_regression 2 :=
  fun h => absurd (prefixRow_injective path_regression h) (by decide)

/-- The companion carrier is countable for countable components. -/
theorem countable_regression : Countable (CompanionCarrier ℕ (fun u => Fin (u + 1)) Aiic π) :=
  inferInstance

/-! ### Axiom hygiene -/

def headline : List Name :=
  [`FirstOrder.Language.FiberAssembly.compIndex_pathPrefix_of_le,
   `FirstOrder.Language.FiberAssembly.compIndex_pathPrefix_of_lt,
   `FirstOrder.Language.FiberAssembly.compIndex_pathPrefix_succ_of_ne,
   `FirstOrder.Language.FiberAssembly.isAllowed_pathPrefix,
   `FirstOrder.Language.FiberAssembly.prefixRow_injective,
   `FirstOrder.Language.FiberAssembly.pathFiber_inl_prefixRow_of_le,
   `path_regression, `empty_prefix_regression, `repeated_letters_regression,
   `off_path_regression, `consecutive_regression, `same_fiber_regression,
   `distinct_rows_regression, `countable_regression]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "fiber companion regression guard: OK (empty prefix, repeated letters, off-path label, \
    consecutive prefixes, shared fiber, distinct rows, countability; headline declarations on \
    standard axioms)"
