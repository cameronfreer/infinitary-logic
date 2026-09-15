/-
Regression guard for the finite-level thresholds and the concrete exact-`ω` instance
(`ModelTheory/PureSetThreshold.lean`, `ModelTheory/FiberExactOmega.lean`).

Checked: empty tuples of `ℕ` and `Fin m` are equivalent at `k` iff `k ≤ m`, with failure pinned
at `m + 1`; the **empty finite set** `Fin 0` (level `0` only) and the **singleton** `Fin 1`
(levels `≤ 1`); **repeated coordinates** (`![0, 0]` against `![x, x]` in `Fin (m + 1)` uses one
spare: equivalent at `m`, not at `m + 1`); orbit rank `0` for tuples of a finite pure set with
a repeated coordinate; and the **unconditional endpoint**: the elementary assembled structure has
internal Scott rank exactly `ω`.  Headline declarations use only the standard axioms.

Run with: lake env lean scripts/check_fiber_exact_omega_regressions.lean
-/
import InfinitaryLogic.ModelTheory.FiberExactOmega
import Mathlib.Data.Fin.VecNotation

open Lean FirstOrder Language FiberAssembly PureSet

/-- **Thresholds for `ℕ` against `Fin m`**: `k ≤ m` exactly, failure at `m + 1`. -/
theorem nat_fin_regression (m : ℕ) :
    (∀ k : ℕ, BFEquiv (L := Language.empty) (M := ℕ) (N := Fin m) (k : Ordinal.{0}) 0
      Fin.elim0 Fin.elim0 ↔ k ≤ m) ∧
    ¬ BFEquiv (L := Language.empty) (M := ℕ) (N := Fin m) ((m + 1 : ℕ) : Ordinal.{0}) 0
      Fin.elim0 Fin.elim0 :=
  ⟨fun k => bfEquiv_nat_fin_iff k m, not_bfEquiv_nat_fin_succ m⟩

/-- **Empty finite set**: level `0` only. -/
theorem fin_zero_regression :
    BFEquiv (L := Language.empty) (M := ℕ) (N := Fin 0) ((0 : ℕ) : Ordinal.{0}) 0
      Fin.elim0 Fin.elim0 ∧
    ¬ BFEquiv (L := Language.empty) (M := ℕ) (N := Fin 0) ((1 : ℕ) : Ordinal.{0}) 0
      Fin.elim0 Fin.elim0 :=
  ⟨(bfEquiv_nat_fin_iff 0 0).mpr le_rfl, not_bfEquiv_nat_fin_succ 0⟩

/-- **Singleton**: levels `≤ 1`. -/
theorem fin_one_regression :
    BFEquiv (L := Language.empty) (M := ℕ) (N := Fin 1) ((1 : ℕ) : Ordinal.{0}) 0
      Fin.elim0 Fin.elim0 ∧
    ¬ BFEquiv (L := Language.empty) (M := ℕ) (N := Fin 1) ((2 : ℕ) : Ordinal.{0}) 0
      Fin.elim0 Fin.elim0 :=
  ⟨(bfEquiv_nat_fin_iff 1 1).mpr le_rfl, not_bfEquiv_nat_fin_succ 1⟩

/-- The range of a repeated pair is a singleton. -/
theorem range_pair (m : ℕ) (x : Fin (m + 1)) :
    Set.range (![x, x] : Fin 2 → Fin (m + 1)) = {x} := by
  ext z
  simp only [Set.mem_range, Set.mem_singleton_iff]
  exact ⟨fun ⟨i, hi⟩ => by fin_cases i <;> simpa using hi.symm, fun h => ⟨0, by simp [h]⟩⟩

theorem spare_pair (m : ℕ) (x : Fin (m + 1)) : spare (![x, x] : Fin 2 → Fin (m + 1)) = m := by
  unfold spare
  rw [range_pair]
  have h1 := Set.ncard_add_ncard_compl ({x} : Set (Fin (m + 1)))
  simp only [Set.ncard_singleton, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  omega

/-- **Repeated coordinates** use one spare: equivalent at `m`, not at `m + 1`. -/
theorem repeated_regression (m : ℕ) (x : Fin (m + 1)) :
    BFEquiv (L := Language.empty) (M := ℕ) (N := Fin (m + 1)) (m : Ordinal.{0}) 2
      ![0, 0] ![x, x] ∧
    ¬ BFEquiv (L := Language.empty) (M := ℕ) (N := Fin (m + 1)) ((m + 1 : ℕ) : Ordinal.{0}) 2
      ![0, 0] ![x, x] := by
  have hpat : ∀ i j : Fin 2, (![0, 0] : Fin 2 → ℕ) i = ![0, 0] j ↔
      (![x, x] : Fin 2 → Fin (m + 1)) i = ![x, x] j := by
    intro i j; fin_cases i <;> fin_cases j <;> simp
  constructor
  · exact (bfEquiv_natCast_iff m _ _).mpr ⟨hpat, (spare_pair m x).ge⟩
  · intro h
    have := ((bfEquiv_natCast_iff (m + 1) _ _).mp h).2
    rw [spare_pair] at this
    omega

/-- **Orbit rank `0` in a finite pure set**, with a repeated coordinate. -/
theorem finite_orbit_regression (m : ℕ) (x : Fin (m + 1)) :
    orbitRank (L := Language.empty) (![x, x] : Fin 2 → Fin (m + 1)) = 0 :=
  orbitRank_pure_eq_zero _

/-- **The unconditional endpoint**: internal Scott rank exactly `ω`. -/
theorem exact_omega_regression :
    internalScottRank (L := lang ℕ Language.empty) ExactOmega.Carrier' = Ordinal.omega0.{0} :=
  ExactOmega.internalScottRank_exactOmega

/-! ### Axiom hygiene -/

def headline : List Name :=
  [`FirstOrder.Language.PureSet.bfEquiv_natCast_iff,
   `FirstOrder.Language.PureSet.not_bfEquiv_spare_succ,
   `FirstOrder.Language.PureSet.orbitRank_pure_eq_zero,
   `FirstOrder.Language.PureSet.bfEquiv_nat_fin_iff,
   `FirstOrder.Language.FiberAssembly.ExactOmega.sepBounded,
   `FirstOrder.Language.FiberAssembly.ExactOmega.cofinalApprox,
   `FirstOrder.Language.FiberAssembly.ExactOmega.internalScottRank_exactOmega,
   `nat_fin_regression, `fin_zero_regression, `fin_one_regression, `repeated_regression,
   `finite_orbit_regression, `exact_omega_regression]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "fiber exact-omega regression guard: OK (nat/Fin thresholds with failure at m + 1, empty \
    and singleton finite sets, repeated coordinates, finite orbit rank, unconditional exact \
    omega endpoint; headline declarations on standard axioms)"
