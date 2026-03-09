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
# Scott Height and Canonical Scott Sentence

This file defines the Scott height of a structure (the ordinal at which its Scott
analysis stabilizes) and the canonical Scott sentence (the Scott formula at Scott height).

## Main Definitions

- `scottHeight`: The least ordinal where the Scott formulas stabilize for all tuples.
- `canonicalScottSentence`: The Scott formula at Scott height level for the empty tuple.
- `sr`: The supremum of element ranks (without +1), as opposed to `scottRank` (with +1).
- `AttainedScottRank`: Whether the supremum in `sr` is attained by some element.

## Main Results

- `canonicalScottSentence_iff_potentialIso`: The canonical Scott sentence characterizes
  potential isomorphism.
- `canonicalScottSentence_characterizes`: For countable structures, the canonical Scott
  sentence characterizes isomorphism.

## References

- [Keisler-Knight, "Barwise: Infinitary Logic and Admissible Sets", 2004], §1.3
- [Marker, "Lectures on Infinitary Model Theory", 2016]
-/

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable [Countable (Σ l, L.Relations l)]

open FirstOrder Structure Fin Ordinal

/-! ### Scott Height -/

/-- The Scott height of a structure M: the least ordinal at which the Scott formula
analysis stabilizes for all tuples simultaneously.

This is defined as the least ordinal α such that for all n and all tuples a : Fin n → M,
if a structure N satisfies scottFormula a α, then it also satisfies scottFormula a (α + 1),
and vice versa.

Equivalently, this is the least α where BFEquiv α n a b implies BFEquiv (α + 1) n a b
for all tuples.

Scott height is related to but may differ from Scott rank. We always have
scottHeight ≤ scottRank. -/
@[blueprint "def:scottHeight"
  (title := /-- Scott height -/)
  (statement := /-- The Scott height of a countable structure $M$: the least ordinal
    $\alpha$ such that $\BFEquiv_\alpha(a,b) \Rightarrow \BFEquiv_{\alpha+1}(a,b)$ for
    all tuples $a,b$ in any countable structures. -/)]
noncomputable def scottHeight (M : Type w) [L.Structure M] [Countable M] : Ordinal.{0} :=
  sInf {α : Ordinal.{0} | ∀ {n : ℕ} (a : Fin n → M)
    (N : Type w) [L.Structure N] [Countable N] (b : Fin n → N),
    BFEquiv (L := L) α n a b → BFEquiv (L := L) (Order.succ α) n a b}

/-- Conditional variant of `scottHeight_lt_omega1`. Sorry-free. -/
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
  exact lt_of_le_of_lt (csInf_le ⟨0, fun _ _ => zero_le _⟩ h_mem) hα_lt

/-- Conditional variant of `scottHeight_stabilizesCompletely`. Sorry-free.
Public so that downstream consumers (e.g., CountingModels.lean) can use it. -/
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
Conditional on `CountableRefinementHypothesis`. Sorry-free.

This replaces the sorry-bearing `scottRank_le_implies_stabilizesCompletely` for downstream
consumers that need `StabilizesCompletely` from a bound. -/
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

/-! ### Canonical Scott Sentence -/

/-- The canonical Scott sentence of a structure M, defined as the Scott formula at Scott
height level for the empty tuple.

This is the "optimal" Scott sentence in the sense that its quantifier rank is minimized
(among Scott formulas). It characterizes the structure up to potential isomorphism,
and for countable structures, up to isomorphism. -/
noncomputable def canonicalScottSentence (M : Type w) [L.Structure M] [Countable M] :
    L.Formulaω (Fin 0) :=
  scottFormula (L := L) (M := M) Fin.elim0 (scottHeight (L := L) M)

/-! ### Conditional Canonical Scott Sentence Pipeline -/

/-- Conditional variant of `canonicalScottSentence_iff_potentialIso`. Sorry-free. -/
theorem canonicalScottSentence_iff_potentialIso_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N] :
    (canonicalScottSentence (L := L) M).realize_as_sentence N ↔
    Nonempty (PotentialIso L M N) := by
  constructor
  · intro h
    unfold canonicalScottSentence Formulaω.realize_as_sentence at h
    rw [realize_scottFormula_iff_BFEquiv _ _ _ (scottHeight_lt_omega1_of hcount M)] at h
    have hstab := scottHeight_stabilizesCompletely_of hcount M
    exact ⟨{
      family := { p | BFEquiv (L := L) (scottHeight (L := L) M) p.1 p.2.1 p.2.2 }
      empty_mem := h
      compatible := fun p hp =>
        (BFEquiv.zero p.2.1 p.2.2).mp (BFEquiv.monotone (zero_le _) hp)
      forth := fun ⟨k, a, b⟩ hp m => by
        simp only [Set.mem_setOf_eq] at hp ⊢
        obtain ⟨n', hn'⟩ := BFEquiv.forth ((hstab k N a b).mp hp) m
        exact ⟨n', hn'⟩
      back := fun ⟨k, a, b⟩ hp n' => by
        simp only [Set.mem_setOf_eq] at hp ⊢
        obtain ⟨m, hm⟩ := BFEquiv.back ((hstab k N a b).mp hp) n'
        exact ⟨m, hm⟩
    }⟩
  · intro ⟨P⟩
    unfold canonicalScottSentence Formulaω.realize_as_sentence
    rw [realize_scottFormula_iff_BFEquiv _ _ _ (scottHeight_lt_omega1_of hcount M)]
    exact P.implies_BFEquiv_all (scottHeight (L := L) M)

/-- Conditional variant of `canonicalScottSentence_characterizes`. Sorry-free. -/
theorem canonicalScottSentence_characterizes_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N] :
    (canonicalScottSentence (L := L) M).realize_as_sentence N ↔
    Nonempty (M ≃[L] N) := by
  unfold canonicalScottSentence Formulaω.realize_as_sentence
  rw [realize_scottFormula_iff_BFEquiv _ _ _ (scottHeight_lt_omega1_of hcount M)]
  constructor
  · exact BFEquiv_stabilization_implies_equiv (scottHeight_stabilizesCompletely_of hcount M)
  · intro ⟨e⟩
    have h : (e : M → N) ∘ Fin.elim0 = Fin.elim0 := funext (fun i => i.elim0)
    rw [← h]
    exact equiv_implies_BFEquiv e _ 0 Fin.elim0

/-- Conditional variant of `canonicalScottSentence_equiv_scottSentence`. Sorry-free. -/
theorem canonicalScottSentence_equiv_scottSentence_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N] :
    (canonicalScottSentence (L := L) M).realize_as_sentence N ↔
    (scottSentence (L := L) M).realize_as_sentence N := by
  rw [canonicalScottSentence_characterizes_of hcount, scottSentence_characterizes_of hcount]

/-! ### sr and SR -/

/-- The supremum of element ranks without the +1 adjustment.

This is denoted `sr(M)` in some references (e.g., Marker). Compare with `scottRank`
which is `⨆ m, elementRank m + 1` (denoted `SR(M)` or `α(M)`). -/
noncomputable def sr (M : Type w) [L.Structure M] [Countable M] : Ordinal.{0} :=
  ⨆ (m : M), elementRank (L := L) m

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- sr ≤ scottRank always holds, since scottRank = ⨆ m, elementRank m + 1 ≥ ⨆ m, elementRank m. -/
theorem sr_le_scottRank (M : Type w) [L.Structure M] [Countable M] :
    sr (L := L) M ≤ scottRank (L := L) M := by
  unfold sr scottRank
  haveI : Small.{0} M := Countable.toSmall M
  apply Ordinal.iSup_le
  intro m
  calc elementRank (L := L) m
      ≤ elementRank (L := L) m + 1 := le_self_add
    _ ≤ ⨆ m, elementRank (L := L) m + 1 := Ordinal.le_iSup _ m

/-- The element-rank supremum `sr` is bounded by `scottHeight`.

Since `scottHeight M` is a complete stabilization ordinal (conditional on
`CountableRefinementHypothesis`), every `elementRank m ≤ scottHeight M`, so
the supremum `sr M = ⨆ m, elementRank m ≤ scottHeight M`. Sorry-free. -/
theorem sr_le_scottHeight_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    (M : Type w) [L.Structure M] [Countable M] :
    sr (L := L) M ≤ scottHeight (L := L) M := by
  unfold sr
  haveI : Small.{0} M := Countable.toSmall M
  apply Ordinal.iSup_le
  intro m
  exact elementRank_le_completeStab (scottHeight_stabilizesCompletely_of hcount M) m

/-- `scottRank M ≤ scottHeight M + 1`.

Since `scottRank M = ⨆ m, elementRank m + 1` and each `elementRank m ≤ scottHeight M`
(via `elementRank_le_completeStab` at the complete stabilization ordinal `scottHeight M`),
we get `scottRank M ≤ scottHeight M + 1`. Sorry-free, conditional on
`CountableRefinementHypothesis`. -/
theorem scottRank_le_scottHeight_succ_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    (M : Type w) [L.Structure M] [Countable M] :
    scottRank (L := L) M ≤ scottHeight (L := L) M + 1 := by
  unfold scottRank
  haveI : Small.{0} M := Countable.toSmall M
  apply Ordinal.iSup_le
  intro m
  have h_bound := elementRank_le_completeStab (scottHeight_stabilizesCompletely_of hcount M) m
  have h := (Ordinal.add_le_add_iff_right 1).mpr h_bound
  convert h using 2 <;> simp [Nat.cast_one]

/-! ### Attained Scott Rank -/

/-- A structure has attained Scott rank if some element achieves the supremum `sr`.

This is an important distinction in the theory of Scott rank: when the rank is
attained, the structure has a "witness" element of maximal complexity. -/
def AttainedScottRank (M : Type w) [L.Structure M] [Countable M] : Prop :=
  ∃ (m : M), elementRank (L := L) m = sr (L := L) M

/-- Conditional variant of `canonicalScottSentence_qrank`. Sorry-free. -/
theorem canonicalScottSentence_qrank_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    (M : Type w) [L.Structure M] [Countable M] :
    (canonicalScottSentence (L := L) M).qrank ≤
    scottHeight (L := L) M + Ordinal.omega0 :=
  le_trans
    (scottFormula_qrank_le Fin.elim0 _ (scottHeight_lt_omega1_of hcount M))
    le_self_add

/-! ### Unconditional Wrappers (via CRH) -/

/-- Scott height is less than ω₁ for countable structures. -/
@[blueprint "thm:scottHeight-lt-omega1"
  (title := /-- Scott height below $\omegaone$ -/)
  (statement := /-- For any countable $L$-structure $M$,
    $\scottHeight(M) < \omegaone$. -/)]
theorem scottHeight_lt_omega1 (M : Type w) [L.Structure M] [Countable M] :
    scottHeight (L := L) M < Ordinal.omega 1 :=
  scottHeight_lt_omega1_of countableRefinementHypothesis M

/-- At Scott height, all tuple sizes have stabilized (BFEquiv α ↔ BFEquiv (succ α)). -/
theorem scottHeight_stabilizesCompletely (M : Type w) [L.Structure M] [Countable M] :
    StabilizesCompletely (L := L) M (scottHeight (L := L) M) :=
  scottHeight_stabilizesCompletely_of countableRefinementHypothesis M

/-- The canonical Scott sentence characterizes potential isomorphism. -/
theorem canonicalScottSentence_iff_potentialIso
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N] :
    (canonicalScottSentence (L := L) M).realize_as_sentence N ↔
    Nonempty (PotentialIso L M N) :=
  canonicalScottSentence_iff_potentialIso_of countableRefinementHypothesis

/-- For countable structures, the canonical Scott sentence characterizes isomorphism. -/
theorem canonicalScottSentence_characterizes
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N] :
    (canonicalScottSentence (L := L) M).realize_as_sentence N ↔
    Nonempty (M ≃[L] N) :=
  canonicalScottSentence_characterizes_of countableRefinementHypothesis

/-- The canonical Scott sentence is semantically equivalent to the standard Scott sentence. -/
theorem canonicalScottSentence_equiv_scottSentence
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N] :
    (canonicalScottSentence (L := L) M).realize_as_sentence N ↔
    (scottSentence (L := L) M).realize_as_sentence N :=
  canonicalScottSentence_equiv_scottSentence_of countableRefinementHypothesis

/-- The quantifier rank of the canonical Scott sentence is bounded. -/
theorem canonicalScottSentence_qrank
    (M : Type w) [L.Structure M] [Countable M] :
    (canonicalScottSentence (L := L) M).qrank ≤
    scottHeight (L := L) M + Ordinal.omega0 :=
  canonicalScottSentence_qrank_of countableRefinementHypothesis M

end Language

end FirstOrder
