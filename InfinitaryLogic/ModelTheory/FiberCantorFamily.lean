/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.FiberExactOmega
import InfinitaryLogic.ModelTheory.FiberCompanionEquiv
import InfinitaryLogic.ModelTheory.FiberCompanionIso

/-!
# A Cantor-indexed family of companions of the exact-`ω` base

For a binary sequence `z : ℕ → Bool`, the path `π_z (2n) = n`, `π_z (2n + 1) = n + z n`
(`cantorPath`) is nondecreasing, unbounded, allowed under `A n = {u | u ≤ n}`, and recovers `z`
from its odd coordinates, so distinct sequences give distinct paths (`cantorPath_injective`).
`CantorCompanion z` is the companion of the exact-`ω` base `Carrier'` along `π_z`.

**The family** (`cantorFamily`): the base has internal Scott rank exactly `ω`
(`internalScottRank_exactOmega`, reused as proved); the companions are countable
(`instCountableCompanion` through the abbreviation); each companion is `β`-equivalent to the
base for every `β < ω` (`companion_bfEquiv`, with threshold `2m` at level `m`:
`π_z k ≥ k / 2 ≥ m` for `k ≥ 2m`, so `Fin (π_z k + 1) ≡_m ℕ` by `bfEquiv_nat_fin_iff`); no
companion is isomorphic to the base, and distinct sequences give non-isomorphic companions
(`companion_not_iso`, `companions_not_iso`; every position is non-default since no finite
component is isomorphic to `ℕ`).

"Cantor-indexed" describes the indexing set `ℕ → Bool` only: no continuity, Borelness,
common-carrier coding, or effectiveness is claimed, and **no rank is inferred for any
companion**.
-/

namespace FirstOrder.Language

namespace FiberAssembly

namespace ExactOmega

open PureSet

/-! ### The paths -/

/-- The path of a binary sequence: `π_z (2n) = n`, `π_z (2n + 1) = n + z n`. -/
def cantorPath (z : ℕ → Bool) : ℕ → ℕ :=
  fun k => k / 2 + if k % 2 = 1 ∧ z (k / 2) then 1 else 0

theorem cantorPath_even (z : ℕ → Bool) (n : ℕ) : cantorPath z (2 * n) = n := by
  have h1 : 2 * n / 2 = n := by omega
  have h2 : 2 * n % 2 = 0 := by omega
  simp [cantorPath, h1, h2]

theorem cantorPath_odd (z : ℕ → Bool) (n : ℕ) :
    cantorPath z (2 * n + 1) = n + if z n then 1 else 0 := by
  have h1 : (2 * n + 1) / 2 = n := by omega
  have h2 : (2 * n + 1) % 2 = 1 := by omega
  simp [cantorPath, h1, h2]

/-- The path stays below the identity: allowed positionwise. -/
theorem cantorPath_le (z : ℕ → Bool) (k : ℕ) : cantorPath z k ≤ k := by
  unfold cantorPath
  split <;> omega

/-- The path is unbounded: at least half the position. -/
theorem half_le_cantorPath (z : ℕ → Bool) (k : ℕ) : k / 2 ≤ cantorPath z k := by
  unfold cantorPath
  split <;> omega

theorem cantorPath_monotone (z : ℕ → Bool) : Monotone (cantorPath z) := by
  intro a b hab
  have hq : a / 2 ≤ b / 2 := Nat.div_le_div_right hab
  unfold cantorPath
  split_ifs with h₁ h₂ h₂
  · omega
  · -- `a` odd with its bit set: either the quotient grows, or `b` has the same odd bit
    rcases Nat.lt_or_ge (a / 2) (b / 2) with h | h
    · omega
    · have heq : a / 2 = b / 2 := le_antisymm hq h
      exact absurd ⟨by omega, heq ▸ h₁.2⟩ h₂
  · omega
  · omega

theorem cantorPath_allowed (z : ℕ → Bool) : IsAllowedPath Aiic (cantorPath z) :=
  ⟨cantorPath_monotone z, fun k => Set.mem_Iic.mpr (cantorPath_le z k)⟩

/-- Odd coordinates recover the sequence: distinct sequences give distinct paths. -/
theorem cantorPath_injective : Function.Injective cantorPath := by
  intro z w h
  funext n
  have := congrFun h (2 * n + 1)
  rw [cantorPath_odd, cantorPath_odd] at this
  revert this
  cases z n <;> cases w n <;> simp

/-! ### The companions and the per-path hypotheses -/

/-- The companion of the exact-`ω` base along `π_z`. -/
abbrev CantorCompanion (z : ℕ → Bool) : Type := CompanionCarrier ℕ Bfin Aiic (cantorPath z)

/-- Countability, discharged by the companion instance through the abbreviation. -/
theorem cantorCompanion_countable (z : ℕ → Bool) : Countable (CantorCompanion z) :=
  inferInstance

/-- At level `m` the threshold `2m` works: beyond it the path is at least `m`. -/
theorem cantorPath_pathApproxAt (z : ℕ → Bool) (m : ℕ) :
    PathApproxAt Language.empty ℕ Bfin (cantorPath z) ((m : ℕ) : Ordinal.{0}) (2 * m) := by
  intro k hk
  have := half_le_cantorPath z k
  exact (bfEquiv_nat_fin_iff m _).mpr (by omega)

theorem cantorPath_pathApprox (z : ℕ → Bool) :
    PathApprox Language.empty ℕ Bfin (cantorPath z) Ordinal.omega0.{0} := by
  intro β hβ
  obtain ⟨m, rfl⟩ := Ordinal.lt_omega0.mp hβ
  exact ⟨2 * m, cantorPath_pathApproxAt z m⟩

/-- Every position is non-default. -/
theorem cantorPath_infinitelyNonDefault (z : ℕ → Bool) :
    InfinitelyNonDefault Language.empty ℕ Bfin (cantorPath z) := by
  have : {k : ℕ | ¬ DefaultLike Language.empty ℕ Bfin (cantorPath z k)} = Set.univ :=
    Set.eq_univ_of_forall fun k => not_defaultLike _
  rw [InfinitelyNonDefault, this]
  exact Set.infinite_univ

/-! ### The package -/

/-- Each companion is `β`-equivalent to the base for every `β < ω`. -/
theorem cantorCompanion_bfEquiv (z : ℕ → Bool) :
    ∀ β < Ordinal.omega0.{0}, BFEquiv (L := lang ℕ Language.empty) β 0
      (Fin.elim0 : Fin 0 → CantorCompanion z) (Fin.elim0 : Fin 0 → Carrier') :=
  companion_bfEquiv ℕ Bfin (cantorPath_allowed z) (cantorPath_pathApprox z)

/-- No companion is isomorphic to the base. -/
theorem cantorCompanion_not_iso (z : ℕ → Bool) :
    IsEmpty (CantorCompanion z ≃[lang ℕ Language.empty] Carrier') :=
  companion_not_iso ℕ Bfin _ (cantorPath_infinitelyNonDefault z)

/-- Distinct sequences give non-isomorphic companions. -/
theorem cantorCompanions_not_iso {z w : ℕ → Bool} (h : z ≠ w) :
    IsEmpty (CantorCompanion z ≃[lang ℕ Language.empty] CantorCompanion w) :=
  companions_not_iso ℕ Bfin (cantorPath_injective.ne h) (cantorPath_infinitelyNonDefault z)

/-- **The Cantor-indexed family.**  The base has internal Scott rank exactly `ω` (reused as
proved); the companions indexed by binary sequences are countable, `β`-equivalent to the base for
every `β < ω`, not isomorphic to it, and pairwise non-isomorphic.  No rank is claimed for any
companion. -/
theorem cantorFamily :
    internalScottRank (L := lang ℕ Language.empty) Carrier' = Ordinal.omega0.{0} ∧
    (∀ z, Countable (CantorCompanion z)) ∧
    (∀ z, ∀ β < Ordinal.omega0.{0}, BFEquiv (L := lang ℕ Language.empty) β 0
      (Fin.elim0 : Fin 0 → CantorCompanion z) (Fin.elim0 : Fin 0 → Carrier')) ∧
    (∀ z, IsEmpty (CantorCompanion z ≃[lang ℕ Language.empty] Carrier')) ∧
    (∀ z w, z ≠ w → IsEmpty (CantorCompanion z ≃[lang ℕ Language.empty] CantorCompanion w)) :=
  ⟨internalScottRank_exactOmega, cantorCompanion_countable, cantorCompanion_bfEquiv,
    cantorCompanion_not_iso, fun _ _ h => cantorCompanions_not_iso h⟩

end ExactOmega

end FiberAssembly

end FirstOrder.Language
