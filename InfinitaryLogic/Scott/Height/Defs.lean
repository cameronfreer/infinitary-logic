/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Scott.QuantifierRank
import InfinitaryLogic.Scott.Rank
import InfinitaryLogic.Scott.RefinementCount
import InfinitaryLogic.Karp.PotentialIso
import Architect

/-!
# Scott Height: Definition and Core Properties

The Scott height of a structure M is the least ordinal at which the Scott
formula analysis stabilizes for all tuples simultaneously.

## Main Definitions

- `scottHeight`: The least ordinal where the Scott formulas stabilize for all tuples.

## Main Results

- `scottHeight_lt_omega1`: Scott height is a countable ordinal.
- `scottHeight_stabilizesCompletely`: At Scott height, all tuple sizes have stabilized.
- `scottHeight_eq_of_equiv`: Scott height is invariant under L-isomorphism.

## Rank conventions

The library has two families of Scott-rank ordinals.  The **cross-structure** ones compare
tuples of `M` with tuples of arbitrary countable `N` in `M`'s carrier universe and live in
`Ordinal.{0}`; among them `elementRank`, `scottRank` and `sr` are element-based (singletons),
`scottHeight` ranges over all tuples and `stabilizationOrdinal` over the empty tuple.  The
**internal (orbit)** ones compare tuples of `M` with tuples of `M` itself (automorphism orbits)
and live in `Ordinal.{w}` for `M : Type w`.

| Ordinal | What is compared | Universe | Module |
|---|---|---|---|
| `elementRank m` | the singleton `![m]` against countable partners | `Ordinal.{0}` | `Scott/Rank` |
| `scottRank M` | `⨆ m, elementRank m + 1` | `Ordinal.{0}` | `Scott/Rank` |
| `sr M` | `⨆ m, elementRank m` | `Ordinal.{0}` | `Scott/Height/RankBounds` |
| `scottHeight M` | all tuples of `M` against countable partners | `Ordinal.{0}` | here |
| `stabilizationOrdinal M` | the empty tuple, up to isomorphism | `Ordinal.{0}` | `Scott/Sentence` |
| `orbitRank a` | tuples of `M` against tuples of `M` | `Ordinal.{w}` | `Scott/OrbitRank` |
| `internalScottRank M` | `⨆ a, orbitRank a + 1` | `Ordinal.{w}` | `Scott/OrbitRank` |

Proved relations: `sr M ≤ scottRank M` (`sr_le_scottRank`), `sr M ≤ scottHeight M`
(`sr_le_scottHeight_of`, with `countableRefinementHypothesis`), `scottRank M ≤ scottHeight M + 1`
(`scottRank_le_scottHeight_succ_of`, with `countableRefinementHypothesis`), and
`elementRank m ≤ α` at every complete stabilization level `α` (`elementRank_le_completeStab`);
on the internal side, `orbitRank a + 1 ≤ internalScottRank M`
(`orbitRank_add_one_le_internalScottRank`).  No comparison between the two
families is proved in the library.

Refuted relations (`scripts/check_rank_convention_regressions.lean`):

* on the empty carrier, `scottRank = 0` while `scottHeight = stabilizationOrdinal = 1` and
  `internalScottRank > 0`, so `scottHeight M ≤ scottRank M`,
  `stabilizationOrdinal M ≤ scottRank M` and `internalScottRank M ≤ lift (scottRank M)` all
  fail;
* on the infinite pure set `ℕ`, `scottRank = ω + 1`, `stabilizationOrdinal = ω` and
  `internalScottRank = 1` (`internalScottRank_pureSet`), so
  `lift (stabilizationOrdinal M) ≤ internalScottRank M + n` fails for every finite `n` and
  `lift (scottRank M) ≤ internalScottRank M + ω` fails.

In particular `scottRank` and `stabilizationOrdinal` differ in both directions: one below on the
empty carrier, one above on `ℕ`.
-/

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable [Countable (Σ l, L.Relations l)]

open FirstOrder Structure Ordinal

/-- The Scott height of a structure M: the least ordinal at which the Scott formula
analysis stabilizes for all tuples simultaneously.

This is defined as the least ordinal α such that for all n and all tuples a : Fin n → M,
if a structure N satisfies scottFormula a α, then it also satisfies scottFormula a (α + 1),
and vice versa.

Equivalently, this is the least α where BFEquiv α n a b implies BFEquiv (α + 1) n a b
for all tuples.

The level lives in `Ordinal.{0}`, and the quantification ranges over all tuples `a` of `M` and
all countable `N` in `M`'s carrier universe.  `scottHeight` is neither the element-based
`scottRank`/`sr` (`Scott/Rank.lean`, `Scott/Height/RankBounds.lean`) nor the internal (orbit)
finite-tuple `internalScottRank` (`Scott/OrbitRank.lean`).  Proved relations:
`sr M ≤ scottHeight M` (`sr_le_scottHeight_of`, with `countableRefinementHypothesis`) and
`scottRank M ≤ scottHeight M + 1` (`scottRank_le_scottHeight_succ_of`, with
`countableRefinementHypothesis`).  The reverse `scottHeight M ≤ scottRank M` does **not**
hold in general: on the empty carrier `scottRank = 0` (an empty supremum) while
`scottHeight = 1` (`scripts/check_rank_convention_regressions.lean`).  See the module
docstring for the full convention table. -/
@[blueprint "def:scottHeight"
  (title := /-- Scott height -/)
  (statement := /-- The Scott height of a countable structure $M$: the least ordinal
    $\alpha$ such that $\BFEquiv_\alpha(a,b) \Rightarrow \BFEquiv_{\alpha+1}(a,b)$ for
    all tuples $a$ of $M$ and $b$ of any countable $N$ in the carrier universe of $M$. -/)]
noncomputable def scottHeight (M : Type w) [L.Structure M] [Countable M] : Ordinal.{0} :=
  sInf {α : Ordinal.{0} | ∀ {n : ℕ} (a : Fin n → M)
    (N : Type w) [L.Structure N] [Countable N] (b : Fin n → N),
    BFEquiv (L := L) α n a b → BFEquiv (L := L) (Order.succ α) n a b}

/-- Conditional variant of `scottHeight_lt_omega1`. -/
theorem scottHeight_lt_omega1_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    (M : Type w) [L.Structure M] [Countable M] :
    scottHeight (L := L) M < Ordinal.omega 1 := by
  obtain ⟨α, hα_lt, hstab⟩ := exists_complete_stabilization_of hcount M
  have h_mem : α ∈ {α : Ordinal.{0} | ∀ {n : ℕ} (a : Fin n → M)
      (N : Type w) [L.Structure N] [Countable N] (b : Fin n → N),
      BFEquiv (L := L) α n a b → BFEquiv (L := L) (Order.succ α) n a b} := by
    intro n a N _ _ b hBF
    exact (hstab n N a b).mp hBF
  exact lt_of_le_of_lt (csInf_le ⟨0, fun _ _ => bot_le⟩ h_mem) hα_lt

/-- Conditional variant of `scottHeight_stabilizesCompletely`. -/
theorem scottHeight_stabilizesCompletely_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    (M : Type w) [L.Structure M] [Countable M] :
    StabilizesCompletely (L := L) M (scottHeight (L := L) M) := by
  obtain ⟨α, _, hstab⟩ := exists_complete_stabilization_of hcount M
  intro n N _ _ a b
  constructor
  · intro hBF
    suffices h : ∀ {k : ℕ} (a' : Fin k → M) (N' : Type w) [L.Structure N']
        [Countable N'] (b' : Fin k → N'),
        BFEquiv (L := L) (scottHeight (L := L) M) k a' b' →
        BFEquiv (L := L) (Order.succ (scottHeight (L := L) M)) k a' b' from h a N b hBF
    show scottHeight (L := L) M ∈ {α : Ordinal.{0} | ∀ {n : ℕ} (a : Fin n → M)
        (N : Type w) [L.Structure N] [Countable N] (b : Fin n → N),
        BFEquiv (L := L) α n a b → BFEquiv (L := L) (Order.succ α) n a b}
    apply csInf_mem
    exact ⟨α, fun {k} a' N' _ _ b' hBF' => (hstab k N' a' b').mp hBF'⟩
  · exact BFEquiv.of_succ

/-- At any ordinal ≥ scottHeight, the structure stabilizes completely.
Conditional on `CountableRefinementHypothesis`. -/
theorem scottHeight_le_implies_stabilizesCompletely_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    (M : Type w) [L.Structure M] [Countable M]
    {α : Ordinal.{0}} (hα : scottHeight (L := L) M ≤ α) :
    StabilizesCompletely (L := L) M α := by
  have hstab := scottHeight_stabilizesCompletely_of hcount M
  intro n N _ _ a b
  constructor
  · intro hBF
    -- BFEquiv α → BFEquiv (scottHeight M) by monotonicity
    have hBF_sh := BFEquiv.monotone hα hBF
    -- Upgrade from scottHeight to succ α (succ α ≥ scottHeight M)
    exact BFEquiv_upgrade_at_stabilization hstab hBF_sh (Order.succ α)
      (le_trans hα (Order.le_succ α))
  · exact BFEquiv.of_succ

/-- Scott height is less than ω₁ for countable structures. -/
@[blueprint "thm:scottHeight-lt-omega1"
  (title := /-- Scott height below $\omegaone$ -/)
  (statement := /-- For any countable $L$-structure $M$,
    $\scottHeight(M) < \omegaone$. -/)
  (proof := /-- By the Countable Refinement Hypothesis, the BF-equivalence hierarchy
    stabilizes at a countable ordinal for each tuple size, and the Scott height is
    their supremum. -/)
  (uses := ["def:scottHeight"])
  (proofUses := ["thm:CRH"])]
theorem scottHeight_lt_omega1 (M : Type w) [L.Structure M] [Countable M] :
    scottHeight (L := L) M < Ordinal.omega 1 :=
  scottHeight_lt_omega1_of countableRefinementHypothesis M

/-- At Scott height, all tuple sizes have stabilized (BFEquiv α ↔ BFEquiv (succ α)). -/
theorem scottHeight_stabilizesCompletely (M : Type w) [L.Structure M] [Countable M] :
    StabilizesCompletely (L := L) M (scottHeight (L := L) M) :=
  scottHeight_stabilizesCompletely_of countableRefinementHypothesis M

/-- Scott height is invariant under L-isomorphism. -/
theorem scottHeight_eq_of_equiv
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N]
    (e : M ≃[L] N) :
    scottHeight (L := L) M = scottHeight (L := L) N := by
  unfold scottHeight
  apply le_antisymm
  · -- scottHeight M ≤ scottHeight N: show S_N ⊆ S_M
    apply csInf_le_csInf
    · -- S_M is BddBelow
      exact ⟨0, fun _ _ => bot_le⟩
    · -- S_N is nonempty: exists_complete_stabilization N gives a member
      obtain ⟨α, _, hstab⟩ := exists_complete_stabilization (L := L) N
      exact ⟨α, fun {n} a P _ _ b hBF => (hstab n P a b).mp hBF⟩
    · -- S_N ⊆ S_M
      intro α hα_N
      simp only [Set.mem_ofPred_eq] at hα_N ⊢
      intro n a P _ _ b hBF
      -- Translate a to N via e: BFEquiv α (e ∘ a) b
      have h1 : BFEquiv (L := L) α n (e ∘ a) b :=
        (equiv_implies_BFEquiv e α n a).symm.trans hBF
      -- Use α ∈ S_N to upgrade: BFEquiv (succ α) (e ∘ a) b
      have h2 : BFEquiv (L := L) (Order.succ α) n (e ∘ a) b :=
        hα_N (e ∘ a) P b h1
      -- Translate back: BFEquiv (succ α) a b
      exact (equiv_implies_BFEquiv e (Order.succ α) n a).trans h2
  · -- scottHeight N ≤ scottHeight M: show S_M ⊆ S_N
    apply csInf_le_csInf
    · exact ⟨0, fun _ _ => bot_le⟩
    · obtain ⟨α, _, hstab⟩ := exists_complete_stabilization (L := L) M
      exact ⟨α, fun {n} a P _ _ b hBF => (hstab n P a b).mp hBF⟩
    · intro α hα_M
      simp only [Set.mem_ofPred_eq] at hα_M ⊢
      intro n a P _ _ b hBF
      have h1 : BFEquiv (L := L) α n (e.symm ∘ a) b :=
        (equiv_implies_BFEquiv e.symm α n a).symm.trans hBF
      have h2 : BFEquiv (L := L) (Order.succ α) n (e.symm ∘ a) b :=
        hα_M (e.symm ∘ a) P b h1
      exact (equiv_implies_BFEquiv e.symm (Order.succ α) n a).trans h2

end Language

end FirstOrder
