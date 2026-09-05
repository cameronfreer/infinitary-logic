/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.FragmentType
import InfinitaryLogic.Karp.CarrierTheorem
import InfinitaryLogic.Scott.Formula
import InfinitaryLogic.Lomega1omega.QuantifierRank

/-!
# Fragment types and bounded back-and-forth: the two minimal adapters

The comparison audit (roadmap step 2) found the existing machinery sufficient except for two
small adapters between realized fragment types (`Fragment.realizedType`) and back-and-forth
equivalence (`BFEquiv`).  Both are stated at the exact rank the underlying theorems use, `≤ α`,
with no successor.

* **A. `Fragment.realizedType_eq_of_bfEquiv`**: if every member of the arity-`n` slice of `F`
  has quantifier rank `≤ α`, then `BFEquiv α n a b` gives equal realized `F`-types.  This is the
  carrier-generic forward transfer `BFEquiv_implies_agreeQR` read through `openBounds`
  (`qrank_openBounds`), so it holds for any carriers in any universes and needs no countability.

* **B. `Fragment.bfEquiv_of_realizedType_eq`**: at a countable source carrier and a countable
  relational signature, if the bounded form `scottBounded a α` of the Scott formula of `a` at
  level `α < ω₁` belongs to `F`, then equal realized `F`-types give `BFEquiv α n a b`.  One source
  tuple's Scott formula suffices for the pairwise implication.  Membership is a *sufficient*
  hypothesis: other formula families can separate the same classes, and the hypothesis is not
  to be replaced by countability or generation of `F`.

Neither adapter promotes a bounded level to fragment elementarity or to an extension theorem,
and neither shortens "all levels" to "countable levels".  The pairwise adapters do not supply
countability of realized extension spectra; that second counting input is separate
(`FragmentBFSuccessor.lean`).  B needs countability of the source carrier only, not of the
target, and the two carriers may live in different universes.

Classical background: Marker, *Lectures on Infinitary Model Theory* (Cambridge, 2016),
Theorem 2.1.4 and Theorem 2.1.13 (agreement up to quantifier rank `≤ α` and back-and-forth
at level `α`); Gao, *Invariant Descriptive Set Theory* (CRC Press, 2009), Definitions
12.1.1–12.1.2.  The fragment-slice packaging is as implemented here.
-/

namespace FirstOrder.Language

variable {L : Language.{u, v}} [L.IsRelational]

namespace Fragment

/-- **A. Bounded back-and-forth gives fragment agreement.**  Every member of the arity-`n` slice
has quantifier rank `≤ α`; then `BFEquiv α n a b` forces the realized `F`-types to coincide.
Carrier-generic, any universes, no countability. -/
theorem realizedType_eq_of_bfEquiv (F : Fragment L) {M : Type w} {N : Type w'} [L.Structure M]
    [L.Structure N] {α : Ordinal.{0}} {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (h : BFEquiv (L := L) α n a b) (hF : ∀ φ : F.slice n, φ.1.qrank ≤ α) :
    F.realizedType M a = F.realizedType N b := by
  funext φ
  apply decide_eq_decide.mpr
  have := BFEquiv_implies_agreeQR α a b h φ.1.openBounds
    ((qrank_openBounds φ.1).le.trans (hF φ))
  exact (realize_openBounds φ.1 a).symm.trans (this.trans (realize_openBounds φ.1 b))

variable [Countable (Σ l, L.Relations l)]

/-- The bounded form of the Scott formula of `a` at level `α`: its free variables rebound. -/
noncomputable def scottBounded {M : Type w} [L.Structure M] [Countable M] {n : ℕ} (a : Fin n → M)
    (α : Ordinal) : L.BoundedFormulaω Empty n :=
  (scottFormula (L := L) a α).relabel (Sum.inr : Fin n → Empty ⊕ Fin n)

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
theorem realize_scottBounded_iff {M : Type w} [L.Structure M] [Countable M]
    [L.IsRelational] [Countable (Σ l, L.Relations l)]
    {N : Type w'} [L.Structure N] {n : ℕ} (a : Fin n → M) (b : Fin n → N) (α : Ordinal)
    (hα : α < Ordinal.omega 1) :
    (scottBounded (L := L) a α).Realize (Empty.elim : Empty → N) b ↔ BFEquiv (L := L) α n a b :=
  (BoundedFormulaω.realize_relabel_sumInr_zero _ _).trans
    (realize_scottFormula_iff_BFEquiv a b α hα)

/-- **B. Fragment agreement gives bounded back-and-forth**, when the bounded Scott formula of the
source tuple at level `α < ω₁` is a member of `F`.  Countable source carrier and countable
relational signature, as the Scott formula's construction requires.  The membership is
sufficient, not necessary. -/
theorem bfEquiv_of_realizedType_eq (F : Fragment L) {M : Type w} [L.Structure M] [Countable M]
    {N : Type w'} [L.Structure N] {α : Ordinal} (hα : α < Ordinal.omega 1) {n : ℕ}
    {a : Fin n → M} {b : Fin n → N}
    (hmem : (⟨n, scottBounded (L := L) a α⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ F)
    (h : F.realizedType M a = F.realizedType N b) : BFEquiv (L := L) α n a b := by
  have ha : F.realizedType M a ⟨_, hmem⟩ = true :=
    (realizedType_apply_iff F M a _).mpr
      ((realize_scottBounded_iff a a α hα).mpr (BFEquiv.refl α a))
  rw [h] at ha
  exact (realize_scottBounded_iff a b α hα).mp ((realizedType_apply_iff F N b _).mp ha)

end Fragment

end FirstOrder.Language
