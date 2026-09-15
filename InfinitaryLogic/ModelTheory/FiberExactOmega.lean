/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.FiberExactRank
import InfinitaryLogic.ModelTheory.PureSetThreshold

/-!
# A concrete assembled structure of internal Scott rank exactly `ω`

The elementary family: empty component language, default component `ℕ`, components
`B u := Fin (u + 1)`, allowed sets `A n := {u | u ≤ n}`.  Every hypothesis of the conditional
exact-rank theorem `internalScottRank_eq_of_bounds` is discharged, so the assembled structure
has internal Scott rank exactly `ω` with **no remaining component hypotheses**
(`internalScottRank_exactOmega`).

* No finite component is default-like (`not_defaultLike`), so (H_up) is vacuous.
* (H_sep) at position bound `N` uses level `N + 2`: a component at a position `≤ N` is `Fin (u + 1)`
  with `u ≤ N`, and `ℕ` is equivalent to `Fin (u + 1)` at level `k` iff `k ≤ u + 1`
  (`bfEquiv_nat_fin_iff`).
* (H_orb): every tuple of a pure set has orbit rank `0` (`orbitRank_pure_eq_zero`).
* `AddNatClosed ω` from the limit `ω`.
* Cofinal approximation at level `k`: the allowed row `[0, 1, …, k]` ends in `k`, whose
  component `Fin (k + 1)` is `k`-equivalent to `ℕ` and not isomorphic to it.

This establishes that the whole hypothesis package has a concrete instance.  It does not supply
an effective approximation family.
-/

namespace FirstOrder.Language

namespace FiberAssembly

namespace ExactOmega

open PureSet

/-- The components: `Fin (u + 1)`. -/
abbrev Bfin : ℕ → Type := fun u => Fin (u + 1)

/-- The allowed sets: at position `n`, the letters `≤ n`. -/
def Aiic : ℕ → Set ℕ := fun n => Set.Iic n

/-- The assembled structure. -/
abbrev Carrier' : Type := PrefixCarrier ℕ Bfin Aiic

theorem nested : Nested Aiic := fun n _ hm => le_trans hm (Nat.le_succ n)

/-- No finite component is isomorphic to the default `ℕ`. -/
theorem not_defaultLike (u : ℕ) : ¬ DefaultLike Language.empty ℕ Bfin u :=
  fun ⟨e⟩ => (isEmpty_equiv_of_infinite_finite (X := ℕ) (Y := Fin (u + 1))).false e.symm

theorem upwardClosed : UpwardClosed (DefaultLike Language.empty ℕ Bfin) :=
  fun _ h => (not_defaultLike _ h).elim

/-- (H_sep) at position bound `N`, with level `N + 2`. -/
theorem sepBounded : SepBounded Language.empty ℕ Bfin Aiic Ordinal.omega0.{0} := by
  intro N
  refine ⟨((N + 2 : ℕ) : Ordinal.{0}), Ordinal.natCast_lt_omega0 _, fun n hn u hu _ h => ?_⟩
  have hu' : u ≤ n := hu
  have := (bfEquiv_nat_fin_iff (N + 2) (u + 1)).mp (BFEquiv.symm h)
  omega

/-- (H_orb): every fiber tuple has orbit rank `0 < ω`. -/
theorem orbitBounded : OrbitBounded Language.empty ℕ Bfin Aiic Ordinal.omega0.{0} := by
  intro r τ k t
  rw [orbitRank_pure_eq_zero]
  exact Ordinal.omega0_pos

theorem addNatClosed : AddNatClosed Ordinal.omega0.{0} :=
  AddNatClosed.of_isSuccLimit Ordinal.isSuccLimit_omega0

/-- The allowed row `[0, 1, …, k]`. -/
def rowRange (k : ℕ) : Row Aiic :=
  ⟨List.range (k + 1), List.pairwise_lt_range.imp le_of_lt, fun i hi => by
    rw [List.getElem_range]
    exact Set.mem_Iic.mpr le_rfl⟩

theorem rowRange_ne (k : ℕ) : (rowRange k).1 ≠ [] := by
  simp [rowRange]

theorem rowRange_getLast (k : ℕ) : (rowRange k).1.getLast (rowRange_ne k) = k := by
  simp [rowRange, List.getLast_range]

/-- Cofinal approximation: at level `k`, the row `[0, …, k]`. -/
theorem cofinalApprox : CofinalApprox Language.empty ℕ Bfin Aiic Ordinal.omega0.{0} := by
  intro β hβ
  obtain ⟨k, rfl⟩ := Ordinal.lt_omega0.mp hβ
  refine ⟨rowRange k, rowRange_ne k, ?_, isEmpty_equiv_of_infinite_finite⟩
  have hlast := rowRange_getLast k
  exact (bfEquiv_nat_fin_iff k _).mpr (by omega)

/-- **The assembled structure has internal Scott rank exactly `ω`.** -/
theorem internalScottRank_exactOmega :
    internalScottRank (L := lang ℕ Language.empty) Carrier' = Ordinal.omega0.{0} :=
  internalScottRank_eq_of_bounds nested Ordinal.omega0 sepBounded upwardClosed orbitBounded
    addNatClosed cofinalApprox

end ExactOmega

end FiberAssembly

end FirstOrder.Language
