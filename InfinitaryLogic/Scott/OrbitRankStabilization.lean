/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Scott.OrbitRank
import InfinitaryLogic.Scott.Sentence
import InfinitaryLogic.Scott.Stabilization

/-!
# The supremum of the orbit ranks, as a stabilization level

For a structure `M : Type w`, the supremum `R = ⨆ a, orbitRank a` of the orbit ranks of the
tuples of `M` (all tuples `Σ n, Fin n → M`, repeated coordinates included) has two further
descriptions in the Scott layer:

* it is the least level at which `M` self-stabilizes completely, that is, at which
  back-and-forth equivalence of tuples of `M` implies equivalence one level up
  (`selfStabilizesCompletely_iff_orbitRank_le`, `sInf_selfStabilizesCompletely_eq_iSup_orbitRank`);
* it is the stabilization ordinal of `M` with itself, the supremum of the least failure levels
  of pairs of tuples of `M` (`bfStabilizationOrdinal_self_eq_iSup_orbitRank`).

All ordinals live in `Ordinal.{w}`.  Any language, any structure: no relational hypothesis and no
countability.  Against `internalScottRank M = ⨆ a, (orbitRank a + 1)`, always
`R ≤ internalScottRank M ≤ R + 1` (`iSup_orbitRank_le_internalScottRank`,
`internalScottRank_le_iSup_orbitRank_add_one`).  For an infinite structure over a relational
language, a terminating Scott process of `M` has lifted rank `R` (`lift_rank_eq_iSup_orbitRank`,
in `ScottProcess/RankComparison.lean`, which uses the two comparisons above).  The comparisons
with the cross-structure ranks (`stabilizationOrdinal`, `scottHeight`) are in
`Scott/RankConventions.lean`.

## Main results

* `iSup_orbitRank_le_iff` and `orbitRank_le_iSup_orbitRank`: the supremum API.
* `iSup_orbitRank_le_internalScottRank` and `internalScottRank_le_iSup_orbitRank_add_one`:
  `R ≤ internalScottRank M ≤ R + 1`.
* `selfStabilizesCompletely_iff_orbitRank_le`: `M` self-stabilizes completely at `α` iff every
  orbit rank is at most `α`.
* `sInf_selfStabilizesCompletely_eq_iSup_orbitRank`: the least self-stabilization level is `R`.
* `bfStabilizationOrdinal_self_eq_iSup_orbitRank`: `bfStabilizationOrdinal L M M = R`.
-/

universe u v w

namespace FirstOrder.Language

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

/-- `α` bounds the supremum of the orbit ranks iff it bounds each of them. -/
theorem iSup_orbitRank_le_iff {α : Ordinal.{w}} :
    (⨆ x : (Σ n : ℕ, Fin n → M), orbitRank (L := L) x.2) ≤ α ↔
      ∀ n (a : Fin n → M), orbitRank (L := L) a ≤ α :=
  Ordinal.iSup_le_iff.trans ⟨fun h n a ↦ h ⟨n, a⟩, fun h x ↦ h x.1 x.2⟩

/-- Every orbit rank is at most the supremum of the orbit ranks. -/
theorem orbitRank_le_iSup_orbitRank {n : ℕ} (a : Fin n → M) :
    orbitRank (L := L) a ≤ ⨆ x : (Σ n : ℕ, Fin n → M), orbitRank (L := L) x.2 :=
  iSup_orbitRank_le_iff.1 le_rfl n a

/-- `⨆ a, orbitRank a ≤ internalScottRank M`.  Any language, any structure. -/
theorem iSup_orbitRank_le_internalScottRank :
    (⨆ x : (Σ n : ℕ, Fin n → M), orbitRank (L := L) x.2) ≤ internalScottRank (L := L) M :=
  iSup_orbitRank_le_iff.2 fun _ a ↦
    (lt_add_one _).le.trans (orbitRank_add_one_le_internalScottRank a)

/-- `internalScottRank M ≤ (⨆ a, orbitRank a) + 1`.  Any language, any structure. -/
theorem internalScottRank_le_iSup_orbitRank_add_one :
    internalScottRank (L := L) M ≤ (⨆ x : (Σ n : ℕ, Fin n → M), orbitRank (L := L) x.2) + 1 :=
  internalScottRank_le fun _ a ↦ add_le_add_left (orbitRank_le_iSup_orbitRank a) 1

/-- `M` self-stabilizes completely at `α` iff every tuple of `M` has orbit rank at most `α`.
Any structure, any `α : Ordinal.{w}`; no countability. -/
theorem selfStabilizesCompletely_iff_orbitRank_le {α : Ordinal.{w}} :
    SelfStabilizesCompletely (L := L) M α ↔ ∀ n (a : Fin n → M), orbitRank (L := L) a ≤ α := by
  refine ⟨fun h n a ↦ orbitRank_le_of_mem fun b hb γ ↦ ?_, fun h n a b ↦
    ⟨fun hab ↦ mem_orbitStable_iff_orbitRank_le.2 (h n a) b hab _, BFEquiv.of_succ⟩⟩
  rcases le_or_gt α γ with hαγ | hγα
  · exact BFEquiv_upgrade_at_selfStabilization h hb γ hαγ
  · exact BFEquiv.monotone hγα.le hb

/-- **The least self-stabilization level is the supremum of the orbit ranks**, in
`Ordinal.{w}` for `M : Type w`: `sInf {α | SelfStabilizesCompletely M α} = ⨆ a, orbitRank a`.
The set is nonempty (it contains the supremum), so the infimum is attained. -/
theorem sInf_selfStabilizesCompletely_eq_iSup_orbitRank :
    sInf {α : Ordinal.{w} | SelfStabilizesCompletely (L := L) M α} =
      ⨆ x : (Σ n : ℕ, Fin n → M), orbitRank (L := L) x.2 := by
  have hmem : (⨆ x : (Σ n : ℕ, Fin n → M), orbitRank (L := L) x.2) ∈
      {α : Ordinal.{w} | SelfStabilizesCompletely (L := L) M α} :=
    selfStabilizesCompletely_iff_orbitRank_le.2 fun _ a ↦ orbitRank_le_iSup_orbitRank a
  exact le_antisymm (csInf_le' hmem) (iSup_orbitRank_le_iff.2
    (selfStabilizesCompletely_iff_orbitRank_le.1 (csInf_mem ⟨_, hmem⟩)))

/-- **The stabilization ordinal of `M` with itself is the supremum of the orbit ranks**:
`bfStabilizationOrdinal L M M = ⨆ a, orbitRank a` in `Ordinal.{w}`: the supremum of the least
failure levels of pairs of tuples of `M` equals the supremum of the orbit ranks. -/
theorem bfStabilizationOrdinal_self_eq_iSup_orbitRank :
    bfStabilizationOrdinal.{u, v, w} L M M =
      ⨆ x : (Σ n : ℕ, Fin n → M), orbitRank (L := L) x.2 := by
  refine le_antisymm (Ordinal.iSup_le fun ⟨⟨n, a, b⟩, β, hβ⟩ ↦ le_of_not_gt fun hlt ↦ ?_)
    (iSup_orbitRank_le_iff.2 fun _ a ↦ orbitRank_le_of_mem fun _ hb ↦
      bfEquiv_bfStabilizationOrdinal_iff_all.1 hb)
  have hfail := csInf_mem (s := {α : Ordinal.{w} | ¬BFEquiv (L := L) α n a b}) ⟨β, hβ⟩
  have hbf : BFEquiv (L := L) (orbitRank (L := L) a) n a b := by
    by_contra h
    exact (not_le.2 ((orbitRank_le_iSup_orbitRank a).trans_lt hlt)) (csInf_le' h)
  exact hfail (bfEquiv_all_of_bfEquiv_orbitRank hbf _)

end FirstOrder.Language
