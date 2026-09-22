/-
Regression guard for companion non-isomorphism (`ModelTheory/FiberCompanionIso.lean`).

On the exact-`ω` family (`ℕ`, `Fin (u + 1)`, empty language) no position is default-like, so
`InfinitelyNonDefault` holds for every path without any allowedness.  Checked:

* **Inadmissible path**: the constant-`1` path is **not allowed** at position `0` under
  `A n = {u | u ≤ n}`, and `companion_not_iso` still applies to it.
* **Identity versus `n / 2`**: `companions_not_iso` for the identity source path against the
  target `n / 2`, and the **differing-coordinate prefix test** at `k₀ = 1`, `k = 3`.
* **Asymmetric non-defaultness**, on a second family where `B' 0 = Fin 1` and `B' (u + 1) = ℕ`:
  the **constant-`0`** source path has every position non-default (so distinct letters are
  unnecessary and positions, not letters, are counted), the target `n + 1` has every position
  default-like, and `companions_not_iso` applies with **no target premise**.

Headline declarations use only the standard axioms.

Run with: lake env lean scripts/check_fiber_companion_iso_regressions.lean
-/
import InfinitaryLogic.ModelTheory.FiberCompanionIso
import InfinitaryLogic.ModelTheory.FiberExactOmega

open Lean FirstOrder Language FiberAssembly

/-! ### The exact-`ω` family: every position is non-default -/

open ExactOmega in
/-- Every path has infinitely many non-default positions: all of them. -/
theorem infinitelyNonDefault_regression (π : ℕ → ℕ) :
    InfinitelyNonDefault Language.empty ℕ Bfin π := by
  have : {k | ¬ DefaultLike Language.empty ℕ ExactOmega.Bfin (π k)} = Set.univ :=
    Set.eq_univ_of_forall fun k => not_defaultLike (π k)
  rw [InfinitelyNonDefault, this]
  exact Set.infinite_univ

/-- **The inadmissible constant-`1` path** is not allowed at position `0`. -/
theorem constant_one_not_allowed : ¬ IsAllowedPath ExactOmega.Aiic (fun _ => 1) :=
  fun h => absurd (h.2 0) (by simp [ExactOmega.Aiic])

/-- **`companion_not_iso` on the inadmissible path.** -/
theorem inadmissible_regression :
    IsEmpty (CompanionCarrier ℕ ExactOmega.Bfin ExactOmega.Aiic (fun _ => 1)
      ≃[lang ℕ Language.empty] PrefixCarrier ℕ ExactOmega.Bfin ExactOmega.Aiic) :=
  companion_not_iso ℕ ExactOmega.Bfin _ (infinitelyNonDefault_regression _)

/-- The path `n / 2`. -/
def πh : ℕ → ℕ := fun n => n / 2

theorem id_ne_half : (id : ℕ → ℕ) ≠ πh := fun h => absurd (congrFun h 1) (by decide)

/-- **Identity versus `n / 2`.** -/
theorem id_half_regression :
    IsEmpty (CompanionCarrier ℕ ExactOmega.Bfin ExactOmega.Aiic id ≃[lang ℕ Language.empty]
      CompanionCarrier ℕ ExactOmega.Bfin ExactOmega.Aiic πh) :=
  companions_not_iso ℕ ExactOmega.Bfin id_ne_half (infinitelyNonDefault_regression _)

/-- **Differing-coordinate prefix test**: the identity and `n / 2` differ at `1`, so the identity's
prefix label of length `4` is not on `n / 2`. -/
theorem differing_coordinate_regression : ¬ IsPathPrefix πh (prefixLabel id 3) :=
  not_isPathPrefix_prefixLabel_of_ne (π := id) (σ := πh) (k₀ := 1) (by decide) (by decide)

/-! ### Asymmetric non-defaultness -/

/-- A second family: a singleton at `0`, the default `ℕ` elsewhere. -/
def B' : ℕ → Type
  | 0 => Fin 1
  | _ + 1 => ℕ

instance : ∀ u, Language.empty.Structure (B' u)
  | 0 => Language.emptyStructure
  | _ + 1 => Language.emptyStructure

/-- Position `0` is non-default: `Fin 1 ≄ ℕ`. -/
theorem B'_zero_nondefault : ¬ DefaultLike Language.empty ℕ B' 0 :=
  fun ⟨e⟩ => (PureSet.isEmpty_equiv_of_infinite_finite (X := ℕ) (Y := Fin 1)).false e.symm

/-- Positions `u + 1` are default-like: `ℕ ≃ ℕ`. -/
theorem B'_succ_default (u : ℕ) : DefaultLike Language.empty ℕ B' (u + 1) :=
  ⟨Language.Equiv.refl _ _⟩

/-- **The constant-`0` source**: every position non-default, with a single repeated letter. -/
theorem constant_source_regression : InfinitelyNonDefault Language.empty ℕ B' (fun _ => 0) := by
  have : {k : ℕ | ¬ DefaultLike Language.empty ℕ B' ((fun _ => 0) k)} = Set.univ :=
    Set.eq_univ_of_forall fun _ => B'_zero_nondefault
  rw [InfinitelyNonDefault, this]
  exact Set.infinite_univ

/-- The target `n + 1` has every position default-like. -/
theorem target_all_default (n : ℕ) : DefaultLike Language.empty ℕ B' ((fun n => n + 1) n) :=
  B'_succ_default n

theorem const_ne_succ : (fun _ : ℕ => (0 : ℕ)) ≠ fun n => n + 1 :=
  fun h => absurd (congrFun h 0) (by decide)

/-- **Asymmetric application**: no premise on the all-default target. -/
theorem asymmetric_regression :
    IsEmpty (CompanionCarrier ℕ B' ExactOmega.Aiic (fun _ => 0) ≃[lang ℕ Language.empty]
      CompanionCarrier ℕ B' ExactOmega.Aiic (fun n => n + 1)) :=
  companions_not_iso ℕ B' const_ne_succ constant_source_regression

/-! ### Axiom hygiene -/

def headline : List Name :=
  [`FirstOrder.Language.FiberAssembly.companion_not_iso,
   `FirstOrder.Language.FiberAssembly.companions_not_iso,
   `FirstOrder.Language.FiberAssembly.not_isPathPrefix_prefixLabel_of_ne,
   `infinitelyNonDefault_regression, `constant_one_not_allowed, `inadmissible_regression,
   `id_half_regression, `differing_coordinate_regression, `constant_source_regression,
   `target_all_default, `asymmetric_regression]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "fiber companion non-isomorphism regression guard: OK (inadmissible constant path, \
    identity versus n / 2 with the differing-coordinate prefix test, asymmetric non-defaultness \
    with a constant source and an all-default target; headline declarations on standard axioms)"
