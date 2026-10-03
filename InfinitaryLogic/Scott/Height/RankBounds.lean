/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Scott.Height.Defs

/-!
# Rank Bounds: sr, AttainedScottRank, and rank-height relations

This file defines `sr` (the supremum of element ranks without the +1 adjustment)
and `AttainedScottRank`, and proves bounds relating `sr`, `scottRank`, and
`scottHeight`.

## Main Definitions

- `sr`: Supremum of element ranks (without +1), as opposed to `scottRank` (with +1).
- `AttainedScottRank`: Whether the supremum in `sr` is attained by some element.

## Main Results

- `sr_le_scottRank`: sr ≤ scottRank always.
- `sr_le_scottHeight_of`: sr ≤ scottHeight (conditional on CRH), and the unconditional
  `sr_le_scottHeight` (through `countableRefinementHypothesis`).
- `scottRank_le_scottHeight_succ_of`: scottRank ≤ scottHeight + 1 (conditional on CRH), and the
  unconditional `scottRank_le_scottHeight_succ`.
- `stabilizationOrdinal_le_scottHeight`: whole-model recognition happens no later than complete
  stabilization.
-/

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable [Countable (Σ l, L.Relations l)]

open FirstOrder Structure Ordinal

/-- The supremum of element ranks without the +1 adjustment.

Compare with `scottRank`, which is `⨆ m, elementRank m + 1`.  Like `elementRank`, this `sr` is
element-based and cross-structure: each `elementRank m` compares the singleton `![m]` with
tuples of other countable structures.  It is not an internal (orbit) rank defined from the
automorphism orbits of `M` (for that, see `orbitRank` and `internalScottRank` in
`Scott/OrbitRank.lean`); on the infinite pure set `ℕ` every element has `elementRank = ω`
(`scripts/check_rank_convention_regressions.lean`), although every tuple has orbit rank `0`
(`orbitRank_pureSet`).
See the convention table in the module docstring of `Scott/Height/Defs.lean`. -/
noncomputable def sr (M : Type w) [L.Structure M] [Countable M] : Ordinal.{0} :=
  ⨆ (m : M), elementRank (L := L) m

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- sr ≤ scottRank always holds, since scottRank = ⨆ m, elementRank m + 1 ≥ ⨆ m, elementRank m. -/
theorem sr_le_scottRank (M : Type w) [L.Structure M] [Countable M] :
    sr (L := L) M ≤ scottRank (L := L) M := by
  unfold sr scottRank
  have : Small.{0} M := Countable.toSmall M
  apply Ordinal.iSup_le
  intro m
  calc elementRank (L := L) m
      ≤ elementRank (L := L) m + 1 := le_self_add
    _ ≤ ⨆ m, elementRank (L := L) m + 1 := Ordinal.le_iSup _ m

/-- The element-rank supremum `sr` is bounded by `scottHeight`.

Since `scottHeight M` is a complete stabilization ordinal (conditional on
`CountableRefinementHypothesis`), every `elementRank m ≤ scottHeight M`, so
the supremum `sr M = ⨆ m, elementRank m ≤ scottHeight M`. -/
theorem sr_le_scottHeight_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    (M : Type w) [L.Structure M] [Countable M] :
    sr (L := L) M ≤ scottHeight (L := L) M := by
  unfold sr
  have : Small.{0} M := Countable.toSmall M
  apply Ordinal.iSup_le
  intro m
  exact elementRank_le_completeStab (scottHeight_stabilizesCompletely_of hcount M) m

/-- `sr M ≤ scottHeight M`: the unconditional form of `sr_le_scottHeight_of`, through
`countableRefinementHypothesis`. -/
theorem sr_le_scottHeight (M : Type w) [L.Structure M] [Countable M] :
    sr (L := L) M ≤ scottHeight (L := L) M :=
  sr_le_scottHeight_of countableRefinementHypothesis M

/-- `scottRank M ≤ scottHeight M + 1`.

Since `scottRank M = ⨆ m, elementRank m + 1` and each `elementRank m ≤ scottHeight M`
(via `elementRank_le_completeStab` at the complete stabilization ordinal `scottHeight M`),
we get `scottRank M ≤ scottHeight M + 1`. Conditional on
`CountableRefinementHypothesis`. -/
theorem scottRank_le_scottHeight_succ_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    (M : Type w) [L.Structure M] [Countable M] :
    scottRank (L := L) M ≤ scottHeight (L := L) M + 1 := by
  unfold scottRank
  have : Small.{0} M := Countable.toSmall M
  apply Ordinal.iSup_le
  intro m
  have h_bound := elementRank_le_completeStab (scottHeight_stabilizesCompletely_of hcount M) m
  have h := (Ordinal.add_le_add_iff_right 1).mpr h_bound
  convert h using 2 <;> simp [Nat.cast_one]

/-- `scottRank M ≤ scottHeight M + 1`: the unconditional form of
`scottRank_le_scottHeight_succ_of`, through `countableRefinementHypothesis`. -/
theorem scottRank_le_scottHeight_succ (M : Type w) [L.Structure M] [Countable M] :
    scottRank (L := L) M ≤ scottHeight (L := L) M + 1 :=
  scottRank_le_scottHeight_succ_of countableRefinementHypothesis M

/-- Whole-model recognition happens no later than complete stabilization:
`stabilizationOrdinal M ≤ scottHeight M`. -/
theorem stabilizationOrdinal_le_scottHeight (M : Type w) [L.Structure M] [Countable M] :
    stabilizationOrdinal (L := L) M ≤ scottHeight (L := L) M := by
  refine csInf_le' fun N _ _ ↦ ⟨BFEquiv_stabilization_implies_equiv
    (scottHeight_stabilizesCompletely M), fun ⟨e⟩ ↦ ?_⟩
  simpa only [comp_fin_elim0] using equiv_implies_BFEquiv e (scottHeight (L := L) M) 0 Fin.elim0

/-- A structure has attained Scott rank if some element achieves the supremum `sr`.

This is an important distinction in the theory of Scott rank: when the rank is
attained, the structure has a "witness" element of maximal complexity. -/
def AttainedScottRank (M : Type w) [L.Structure M] [Countable M] : Prop :=
  ∃ (m : M), elementRank (L := L) m = sr (L := L) M

end Language

end FirstOrder
