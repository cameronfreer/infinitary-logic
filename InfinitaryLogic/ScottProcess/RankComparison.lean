/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ScottProcess.SemanticBridge
import InfinitaryLogic.ScottProcess.Rank
import InfinitaryLogic.Scott.OrbitRankStabilization

/-!
# The rank of the Scott process of a structure, against the orbit and internal Scott ranks

For an infinite structure `M : Type w` over a relational language, the Scott process
`scottProcessOf L M δ hδ` stabilizes at a level `β` exactly when back-and-forth equivalence of
tuples of `M` at level `β` implies equivalence at level `β + 1`, that is, when `M`
self-stabilizes completely at `β`, that is, when every tuple of `M` has orbit rank at most `β`
(each time together with the length condition `β + 1 < δ`).  Hence the rank of the process
(Larson, *Scott processes*, Definition 5.6) is the supremum of the orbit ranks of the tuples of
`M`, and it differs from the internal Scott rank `internalScottRank M` by at most one.  The
comparison is with `internalScottRank` only; `scottRank` (`Scott/Rank.lean`) is not compared.

## Main declarations

* Used from the Scott layer (`Scott/OrbitRankStabilization.lean`, namespace
  `FirstOrder.Language`): `selfStabilizesCompletely_iff_orbitRank_le` and
  `sInf_selfStabilizesCompletely_eq_iSup_orbitRank` (for any structure `M : Type w`, the least
  self-stabilization level in `Ordinal.{w}` is `⨆ a, orbitRank a`).
* Per level: `stabilizesAt_iff_bfEquiv` (equivalence at `β` implies equivalence at `β + 1`, for
  all tuples, repeated coordinates included), `stabilizesAt_iff_selfStabilizesCompletely` and
  `stabilizesAt_iff_orbitRank_le`.
* Rank: `isRank_iff_isLeast_selfStabilizesCompletely`, `isRank_iff_lift_eq_iSup_orbitRank`
  and `lift_rank_eq_iSup_orbitRank` (the lifted rank is `⨆ a, orbitRank a`).
* Against `internalScottRank`: `lift_rank_le_internalScottRank`,
  `internalScottRank_le_lift_rank_add_one`, the attained case
  `lift_rank_add_one_eq_internalScottRank_iff`, the non-attained case
  `lift_rank_eq_internalScottRank_iff`, and the forms
  `isRank_iff_lift_eq_internalScottRank_of_isSuccLimit` and
  `isRank_iff_lift_add_one_eq_internalScottRank_of_not_isSuccLimit`, which read the rank off
  `internalScottRank M` alone.
* Bound transport: `stabilizesAt_of_orbitRank_le`, `orbitRank_le_of_stabilizesAt` and
  `rank_le_of_orbitRank_le`.

## Interpretation choices

* **Two conventions.** `R = ⨆ a, orbitRank a` is the least level at which the class of every
  tuple is its all-levels class; `S = ⨆ a, (orbitRank a + 1)` is `internalScottRank M`.  Both
  suprema range over all tuples `Σ n, Fin n → M`, repeated coordinates included, as in
  `internalScottRank`.  In the Scott layer `R` is also the stabilization ordinal of `M` with
  itself, `bfStabilizationOrdinal L M M` (`bfStabilizationOrdinal_self_eq_iSup_orbitRank`), and
  the least self-stabilization level (`sInf_selfStabilizesCompletely_eq_iSup_orbitRank`).  The
  rank of the process, lifted, is `R` (`lift_rank_eq_iSup_orbitRank`), so the infinite pure set
  has rank `0`.  Larson's remark after Definition 5.6 identifies the rank of a long enough
  initial segment of the Scott process of `M` with the Scott rank of `M`; here that
  identification holds for the convention `R`, while `S` is one more in the attained case.  `R`
  is kept as an explicit supremum in the statements, not as a new definition.
* **Attained and non-attained.** `R ≤ S ≤ R + 1` always.  If some tuple has orbit rank `R`
  (attained), then `S = R + 1`: the infinite pure set (`R = 0`, `S = 1`) and the graph of
  Larson's Remark 5.11 (`R = 1`, `S = 2`).  If every orbit rank is below `R` (non-attained),
  then `S = R`, and `R` is a limit: the exact-`ω` carrier of `FiberExactOmega` (`R = S = ω`).
  Conversely `S` is a limit exactly in the non-attained case, so
  `isRank_iff_lift_eq_internalScottRank_of_isSuccLimit` and
  `isRank_iff_lift_add_one_eq_internalScottRank_of_not_isSuccLimit` decide the rank from `S`
  alone.
* **Pointwise bounds give `≤`.** Strict pointwise bounds `orbitRank a < lift α` (as produced by
  orbit-isolation arguments such as `internalScottRank_le_of_orbits_determined`) give only
  `StabilizesAt α` and `rank ≤ α`, through `stabilizesAt_of_orbitRank_le` and
  `rank_le_of_orbitRank_le` applied to their `le`: on the exact-`ω` carrier every orbit rank is
  finite and the rank is `ω`.
* **Universes and lifts.** Rows are indexed by `Ordinal.{0}`, as in
  `ScottProcess/FreeArray.lean`; `orbitRank` and `internalScottRank` live in `Ordinal.{w}` for
  `M : Type w`, and so does the level of `SelfStabilizesCompletely` compared with them.  Every
  statement is for arbitrary `w`, needs no `Small` hypothesis, and compares through
  `Ordinal.lift.{w}`, with `BFEquiv.ofOrdinalLift`/`BFEquiv.toOrdinalLift` moving equivalence
  between the two ordinal universes.  The row universe is a universe boundary, not a
  countability restriction: every `β : Ordinal.{0}` is a level.  When `R` is not the lift of an
  ordinal of `Ordinal.{0}` (possible only for `w ≠ 0`), no initial segment of the process of `M`
  terminates; the statements are equivalences or take a rank as a hypothesis, so they cover this
  case as it stands.
* **Explicit lengths.** `StabilizesAt β` includes `β + 1 < δ`, so the per-level and rank
  equivalences keep it as a conjunct, and `stabilizesAt_of_orbitRank_le` takes it as a
  hypothesis.  The `rank` statements take a proof of termination, which carries the length.

## References

* Paul B. Larson, *Scott processes*, in *Beyond First Order Model Theory*, vol. I
  (J. Iovino, ed.), CRC Press, 2017, ch. 2, §5.  Numbering follows the book: Definition 5.6
  (the rank of a Scott process, and the remark that the rank of a sufficiently long initial
  segment of the Scott process of `M` is the Scott rank of `M`), Remarks 5.10 and 5.11 (in
  Remark 5.11, the graph with an infinite set of isolated nodes and an infinite clique, of
  rank `1`, which the regression guard computes).
-/

open Order FirstOrder FirstOrder.Language InfinitaryLogic.ScottProcess.FreeArray

universe u v w

namespace InfinitaryLogic.ScottProcess.Semantic

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

/-! ### The two conventions -/

/-- `⨆ a, orbitRank a ≤ internalScottRank M`. -/
private theorem iSup_orbitRank_le_internalScottRank :
    (⨆ x : (Σ n : ℕ, Fin n → M), orbitRank (L := L) x.2) ≤ internalScottRank (L := L) M :=
  iSup_orbitRank_le_iff.2 fun _ a ↦
    (lt_add_one _).le.trans (orbitRank_add_one_le_internalScottRank a)

/-- `internalScottRank M ≤ (⨆ a, orbitRank a) + 1`. -/
private theorem internalScottRank_le_iSup_orbitRank_add_one :
    internalScottRank (L := L) M ≤ (⨆ x : (Σ n : ℕ, Fin n → M), orbitRank (L := L) x.2) + 1 :=
  internalScottRank_le fun _ a ↦ add_le_add_left (orbitRank_le_iSup_orbitRank a) 1

/-- Attained case: `(⨆ a, orbitRank a) + 1 = internalScottRank M` iff some tuple has orbit rank
`⨆ a, orbitRank a`. -/
private theorem iSup_orbitRank_add_one_eq_internalScottRank_iff :
    (⨆ x : (Σ n : ℕ, Fin n → M), orbitRank (L := L) x.2) + 1 = internalScottRank (L := L) M ↔
      ∃ (n : ℕ) (a : Fin n → M),
        orbitRank (L := L) a = ⨆ x : (Σ n : ℕ, Fin n → M), orbitRank (L := L) x.2 := by
  refine ⟨fun h ↦ ?_, fun ⟨n, a, ha⟩ ↦ le_antisymm ?_ internalScottRank_le_iSup_orbitRank_add_one⟩
  · by_contra hna
    push Not at hna
    have hlt : ∀ n (a : Fin n → M), orbitRank (L := L) a <
        ⨆ x : (Σ n : ℕ, Fin n → M), orbitRank (L := L) x.2 :=
      fun n a ↦ (orbitRank_le_iSup_orbitRank a).lt_of_ne (hna n a)
    have := (internalScottRank_le (L := L) (M := M) fun n a ↦ add_one_le_of_lt (hlt n a)).trans_lt
      (lt_add_one _)
    exact this.ne h.symm
  · rw [← ha]
    exact orbitRank_add_one_le_internalScottRank a

/-- Non-attained case: `⨆ a, orbitRank a = internalScottRank M` iff every tuple has orbit rank
below `⨆ a, orbitRank a`. -/
private theorem iSup_orbitRank_eq_internalScottRank_iff :
    (⨆ x : (Σ n : ℕ, Fin n → M), orbitRank (L := L) x.2) = internalScottRank (L := L) M ↔
      ∀ n (a : Fin n → M),
        orbitRank (L := L) a < ⨆ x : (Σ n : ℕ, Fin n → M), orbitRank (L := L) x.2 := by
  refine ⟨fun h n a ↦ ?_, fun h ↦ le_antisymm iSup_orbitRank_le_internalScottRank
    (internalScottRank_le fun n a ↦ add_one_le_of_lt (h n a))⟩
  rw [h]
  exact (lt_add_one _).trans_le (orbitRank_add_one_le_internalScottRank a)

/-- If `internalScottRank M` is a limit, it is `⨆ a, orbitRank a`. -/
private theorem iSup_orbitRank_eq_internalScottRank_of_isSuccLimit
    (hS : IsSuccLimit (internalScottRank (L := L) M)) :
    (⨆ x : (Σ n : ℕ, Fin n → M), orbitRank (L := L) x.2) = internalScottRank (L := L) M := by
  refine iSup_orbitRank_le_internalScottRank.antisymm (le_of_not_gt fun hlt ↦ ?_)
  have := hS.succ_lt hlt
  rw [Order.succ_eq_add_one] at this
  exact this.not_ge internalScottRank_le_iSup_orbitRank_add_one

/-- If `internalScottRank M` is not a limit, the supremum of the orbit ranks is attained. -/
private theorem exists_orbitRank_eq_iSup_of_not_isSuccLimit
    (hS : ¬ IsSuccLimit (internalScottRank (L := L) M)) :
    ∃ (n : ℕ) (a : Fin n → M),
      orbitRank (L := L) a = ⨆ x : (Σ n : ℕ, Fin n → M), orbitRank (L := L) x.2 := by
  rcases Ordinal.zero_or_succ_or_isSuccLimit (internalScottRank (L := L) M) with h0 | ⟨γ, hγ⟩ | hl
  · have := (orbitRank_add_one_le_internalScottRank (L := L) (Fin.elim0 : Fin 0 → M)).trans_eq h0
    exact absurd this (not_le.2 (zero_le.trans_lt (lt_add_one _)))
  · rw [Order.succ_eq_add_one] at hγ
    obtain ⟨n, a, ha⟩ := exists_orbitRank_add_one_gt_of_lt_internalScottRank (L := L) (M := M)
      (hγ ▸ lt_add_one γ)
    have hle : ∀ m (b : Fin m → M), orbitRank (L := L) b ≤ γ := fun m b ↦
      lt_add_one_iff.1 (add_one_le_iff.1 ((orbitRank_add_one_le_internalScottRank b).trans hγ.ge))
    have hγa : γ = orbitRank (L := L) a := (hle n a).antisymm' (lt_add_one_iff.1 ha)
    exact ⟨n, a, (orbitRank_le_iSup_orbitRank a).antisymm (hγa ▸ iSup_orbitRank_le_iff.2 hle)⟩
  · exact absurd hl hS

/-! ### Stabilization of the process of a structure, level by level -/

section Process

variable [L.IsRelational] [Infinite M] {δ : Ordinal.{0}} {hδ : 0 < δ}

/-- Stabilization at `β`, for injective tuples and at `Ordinal.{0}`. -/
private theorem stabilizesAt_iff_injective {β : Ordinal.{0}} :
    (scottProcessOf L M δ hδ).StabilizesAt β ↔ β + 1 < δ ∧
      ∀ n (a b : Fin n ↪ M), BFEquiv (L := L) β n ⇑a ⇑b → BFEquiv (L := L) (β + 1) n ⇑a ⇑b := by
  refine ⟨fun ⟨h, hinj⟩ ↦ ⟨h, fun n a b hab ↦ ?_⟩, fun ⟨h, H⟩ ↦ ⟨h, fun n ↦ ?_⟩⟩
  · rw [← sf_eq_iff_bfEquiv_self] at hab ⊢
    exact hinj n ⟨a, rfl⟩ ⟨b, rfl⟩ (by rw [V_sf, V_sf, hab])
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ he
    rw [V_sf, V_sf, sf_eq_iff_bfEquiv_self] at he
    exact (sf_eq_iff_bfEquiv_self _ a b).2 (H n a b he)

/-- The step from `β` to `β + 1` holds for all tuples iff it holds for injective tuples: the
repeated-coordinate bridge `bfEquiv_iff_exists_sf_eq` and `BFEquiv.relabel`. -/
private theorem forall_bfEquiv_imp_iff_injective (β : Ordinal.{0}) :
    (∀ n (a b : Fin n → M), BFEquiv (L := L) β n a b → BFEquiv (L := L) (β + 1) n a b) ↔
      ∀ n (a b : Fin n ↪ M), BFEquiv (L := L) β n ⇑a ⇑b → BFEquiv (L := L) (β + 1) n ⇑a ⇑b := by
  refine ⟨fun h n a b ↦ h n a b, fun h n a b hab ↦ ?_⟩
  obtain ⟨k, e, e', g, rfl, rfl, he⟩ := (bfEquiv_iff_exists_sf_eq β a b).1 hab
  exact BFEquiv.relabel _ (h k e e' ((sf_eq_iff_bfEquiv_self β e e').1 he)) g

omit [L.IsRelational] [Infinite M] in
/-- Equivalence of tuples of `M` at `Ordinal.lift.{w} β` is equivalence at `β`. -/
private theorem bfEquiv_lift_iff {β : Ordinal.{0}} {n : ℕ} {a b : Fin n → M} :
    BFEquiv (L := L) (Ordinal.lift.{w} β) n a b ↔ BFEquiv (L := L) β n a b :=
  ⟨BFEquiv.toOrdinalLift, BFEquiv.ofOrdinalLift⟩

/-- **Stabilization as a step of back-and-forth equivalence.**  The process of `M` stabilizes at
`β` iff `β + 1 < δ` and any two tuples of `M` of the same length, injective or with repeated
coordinates, that are back-and-forth equivalent at level `β` are equivalent at level `β + 1`,
both levels lifted to `Ordinal.{w}`. -/
theorem stabilizesAt_iff_bfEquiv {β : Ordinal.{0}} :
    (scottProcessOf L M δ hδ).StabilizesAt β ↔ β + 1 < δ ∧
      ∀ n (a b : Fin n → M), BFEquiv (L := L) (Ordinal.lift.{w} β) n a b →
        BFEquiv (L := L) (Ordinal.lift.{w} (β + 1)) n a b := by
  simp only [bfEquiv_lift_iff]
  rw [forall_bfEquiv_imp_iff_injective, stabilizesAt_iff_injective]

/-- **Stabilization as self-stabilization.**  The process of `M` stabilizes at `β` iff
`β + 1 < δ` and `M` self-stabilizes completely at `Ordinal.lift.{w} β`. -/
theorem stabilizesAt_iff_selfStabilizesCompletely {β : Ordinal.{0}} :
    (scottProcessOf L M δ hδ).StabilizesAt β ↔ β + 1 < δ ∧
      SelfStabilizesCompletely (L := L) M (Ordinal.lift.{w} β) := by
  rw [stabilizesAt_iff_bfEquiv, Ordinal.lift_add_one, ← Order.succ_eq_add_one]
  exact and_congr_right fun _ ↦
    ⟨fun h n a b ↦ ⟨h n a b, BFEquiv.of_succ⟩, fun h n a b ↦ (h n a b).1⟩

/-- **Stabilization as a bound on the orbit ranks.**  The process of `M` stabilizes at `β` iff
`β + 1 < δ` and every tuple of `M` has orbit rank at most `Ordinal.lift.{w} β`. -/
theorem stabilizesAt_iff_orbitRank_le {β : Ordinal.{0}} :
    (scottProcessOf L M δ hδ).StabilizesAt β ↔ β + 1 < δ ∧
      ∀ n (a : Fin n → M), orbitRank (L := L) a ≤ Ordinal.lift.{w} β := by
  rw [stabilizesAt_iff_selfStabilizesCompletely, selfStabilizesCompletely_iff_orbitRank_le]

/-! ### The rank of the process of a structure -/

/-- **The rank is the least self-stabilization level**: `β` is the rank of the process of `M`
iff `β + 1 < δ` and `β` is least among the `γ : Ordinal.{0}` at whose lift `M`
self-stabilizes completely. -/
theorem isRank_iff_isLeast_selfStabilizesCompletely {β : Ordinal.{0}} :
    (scottProcessOf L M δ hδ).IsRank β ↔ β + 1 < δ ∧
      IsLeast {γ : Ordinal.{0} | SelfStabilizesCompletely (L := L) M (Ordinal.lift.{w} γ)} β := by
  constructor
  · rintro ⟨hs, hlow⟩
    obtain ⟨hβ, hsβ⟩ := stabilizesAt_iff_selfStabilizesCompletely.1 hs
    refine ⟨hβ, hsβ, fun γ hγ ↦ le_of_not_gt fun hlt ↦ ?_⟩
    have hγδ : γ + 1 < δ := (add_one_le_of_lt hlt).trans_lt ((lt_add_one β).trans hβ)
    exact (hlow (stabilizesAt_iff_selfStabilizesCompletely.2 ⟨hγδ, hγ⟩)).not_gt hlt
  · rintro ⟨hβ, hsβ, hlow⟩
    exact ⟨stabilizesAt_iff_selfStabilizesCompletely.2 ⟨hβ, hsβ⟩,
      fun γ hγ ↦ hlow (stabilizesAt_iff_selfStabilizesCompletely.1 hγ).2⟩

/-- **The rank is the supremum of the orbit ranks**: `β` is the rank of the process of `M` iff
`β + 1 < δ` and `Ordinal.lift.{w} β = ⨆ a, orbitRank a`. -/
theorem isRank_iff_lift_eq_iSup_orbitRank {β : Ordinal.{0}} :
    (scottProcessOf L M δ hδ).IsRank β ↔ β + 1 < δ ∧
      Ordinal.lift.{w} β = ⨆ x : (Σ n : ℕ, Fin n → M), orbitRank (L := L) x.2 := by
  rw [isRank_iff_isLeast_selfStabilizesCompletely]
  refine and_congr_right fun _ ↦ ?_
  simp only [IsLeast, lowerBounds, Set.mem_ofPred_eq, selfStabilizesCompletely_iff_orbitRank_le,
    ← iSup_orbitRank_le_iff]
  refine ⟨fun ⟨hle, hlow⟩ ↦ le_antisymm (le_of_not_gt fun hlt ↦ ?_) hle,
    fun h ↦ ⟨h.ge, fun γ hγ ↦ Ordinal.lift_le.1 (h.trans_le hγ)⟩⟩
  obtain ⟨γ, hγ, hγR⟩ := Ordinal.lt_lift_iff.1 hlt
  exact (hlow hγR.ge).not_gt hγ

/-- **The rank of a terminating process of `M`, lifted, is the supremum of the orbit ranks.** -/
theorem lift_rank_eq_iSup_orbitRank (h : (scottProcessOf L M δ hδ).Terminating) :
    Ordinal.lift.{w} ((scottProcessOf L M δ hδ).rank h) =
      ⨆ x : (Σ n : ℕ, Fin n → M), orbitRank (L := L) x.2 :=
  (isRank_iff_lift_eq_iSup_orbitRank.1 (ScottProcess.isRank_rank _ h)).2

/-! ### Against the internal Scott rank -/

/-- The lifted rank is at most the internal Scott rank. -/
theorem lift_rank_le_internalScottRank (h : (scottProcessOf L M δ hδ).Terminating) :
    Ordinal.lift.{w} ((scottProcessOf L M δ hδ).rank h) ≤ internalScottRank (L := L) M := by
  rw [lift_rank_eq_iSup_orbitRank]
  exact iSup_orbitRank_le_internalScottRank

/-- The internal Scott rank is at most the lifted rank plus one. -/
theorem internalScottRank_le_lift_rank_add_one (h : (scottProcessOf L M δ hδ).Terminating) :
    internalScottRank (L := L) M ≤ Ordinal.lift.{w} ((scottProcessOf L M δ hδ).rank h) + 1 := by
  rw [lift_rank_eq_iSup_orbitRank]
  exact internalScottRank_le_iSup_orbitRank_add_one

/-- **Attained case**: the lifted rank plus one is the internal Scott rank iff some tuple of `M`
has orbit rank equal to the lifted rank (the supremum of the orbit ranks is attained). -/
theorem lift_rank_add_one_eq_internalScottRank_iff (h : (scottProcessOf L M δ hδ).Terminating) :
    Ordinal.lift.{w} ((scottProcessOf L M δ hδ).rank h) + 1 = internalScottRank (L := L) M ↔
      ∃ (n : ℕ) (a : Fin n → M),
        orbitRank (L := L) a = Ordinal.lift.{w} ((scottProcessOf L M δ hδ).rank h) := by
  rw [lift_rank_eq_iSup_orbitRank]
  exact iSup_orbitRank_add_one_eq_internalScottRank_iff

/-- **Non-attained case**: the lifted rank is the internal Scott rank iff every tuple of `M` has
orbit rank below the lifted rank (the supremum of the orbit ranks is not attained; it is then a
limit). -/
theorem lift_rank_eq_internalScottRank_iff (h : (scottProcessOf L M δ hδ).Terminating) :
    Ordinal.lift.{w} ((scottProcessOf L M δ hδ).rank h) = internalScottRank (L := L) M ↔
      ∀ n (a : Fin n → M),
        orbitRank (L := L) a < Ordinal.lift.{w} ((scottProcessOf L M δ hδ).rank h) := by
  rw [lift_rank_eq_iSup_orbitRank]
  exact iSup_orbitRank_eq_internalScottRank_iff

/-- **The rank from a limit internal Scott rank.**  If `internalScottRank M` is a limit, then
`β` is the rank of the process of `M` iff `β + 1 < δ` and `Ordinal.lift.{w} β` is the internal
Scott rank. -/
theorem isRank_iff_lift_eq_internalScottRank_of_isSuccLimit
    (hS : IsSuccLimit (internalScottRank (L := L) M)) {β : Ordinal.{0}} :
    (scottProcessOf L M δ hδ).IsRank β ↔
      β + 1 < δ ∧ Ordinal.lift.{w} β = internalScottRank (L := L) M := by
  rw [isRank_iff_lift_eq_iSup_orbitRank, iSup_orbitRank_eq_internalScottRank_of_isSuccLimit hS]

/-- **The rank from a non-limit internal Scott rank.**  If `internalScottRank M` is not a limit,
then `β` is the rank of the process of `M` iff `β + 1 < δ` and `Ordinal.lift.{w} β + 1` is the
internal Scott rank. -/
theorem isRank_iff_lift_add_one_eq_internalScottRank_of_not_isSuccLimit
    (hS : ¬ IsSuccLimit (internalScottRank (L := L) M)) {β : Ordinal.{0}} :
    (scottProcessOf L M δ hδ).IsRank β ↔
      β + 1 < δ ∧ Ordinal.lift.{w} β + 1 = internalScottRank (L := L) M := by
  rw [isRank_iff_lift_eq_iSup_orbitRank, ← iSup_orbitRank_add_one_eq_internalScottRank_iff.2
    (exists_orbitRank_eq_iSup_of_not_isSuccLimit hS)]
  simp only [← Order.succ_eq_add_one, Order.succ_injective.eq_iff]

/-! ### Bound transport -/

/-- **Orbit-rank bounds give stabilization.**  If `α + 1 < δ` and every tuple of `M` has orbit
rank at most `Ordinal.lift.{w} α`, the process of `M` stabilizes at `α`.  Strict bounds
`orbitRank a < Ordinal.lift.{w} α` enter through their `le` and give the same conclusion, not
stabilization below `α`. -/
theorem stabilizesAt_of_orbitRank_le {α : Ordinal.{0}} (hα : α + 1 < δ)
    (h : ∀ n (a : Fin n → M), orbitRank (L := L) a ≤ Ordinal.lift.{w} α) :
    (scottProcessOf L M δ hδ).StabilizesAt α :=
  stabilizesAt_iff_orbitRank_le.2 ⟨hα, h⟩

/-- **Stabilization gives orbit-rank bounds.**  If the process of `M` stabilizes at `α`, every
tuple of `M` has orbit rank at most `Ordinal.lift.{w} α`. -/
theorem orbitRank_le_of_stabilizesAt {α : Ordinal.{0}}
    (h : (scottProcessOf L M δ hδ).StabilizesAt α) {n : ℕ} (a : Fin n → M) :
    orbitRank (L := L) a ≤ Ordinal.lift.{w} α :=
  (stabilizesAt_iff_orbitRank_le.1 h).2 n a

/-- **Orbit-rank bounds bound the rank.**  If the process of `M` terminates and every tuple of
`M` has orbit rank at most `Ordinal.lift.{w} α`, the rank is at most `α`; no length condition on
`α` is needed.  Strict bounds give the same conclusion, not `rank < α`. -/
theorem rank_le_of_orbitRank_le (h : (scottProcessOf L M δ hδ).Terminating) {α : Ordinal.{0}}
    (hb : ∀ n (a : Fin n → M), orbitRank (L := L) a ≤ Ordinal.lift.{w} α) :
    (scottProcessOf L M δ hδ).rank h ≤ α := by
  rw [← Ordinal.lift_le.{w}, lift_rank_eq_iSup_orbitRank]
  exact iSup_orbitRank_le_iff.2 hb

end Process

end InfinitaryLogic.ScottProcess.Semantic
