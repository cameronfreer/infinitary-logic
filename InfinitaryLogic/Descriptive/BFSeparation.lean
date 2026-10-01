/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.BFTree
import InfinitaryLogic.Descriptive.AnalyticTreeBoundedness
import InfinitaryLogic.Descriptive.G0Dichotomy

/-!
# Uniform back-and-forth separation of analytic sets of non-isomorphic pairs

If `A` is an analytic set of pairs of codes of countable relational structures and no pair in
`A` is isomorphic, then a single countable back-and-forth level separates every pair of `A`:
there is `α < ω₁` with `¬ CodeBFEquiv α c d` for every `(c, d) ∈ A`.  The proof is descriptive
boundedness applied to the forced back-and-forth trees: the trees `bfTree c d` with
`(c, d) ∈ A` form an analytic family of well-founded trees with closed node sets, so their
heights are bounded by one `α < ω₁`, and `CodeBFEquiv α c d` would put `α` strictly below the
height of `bfTree c d`.  No sentence, coding of sentences, or boundedness theorem for
well-orders is involved.

## Main declarations

* `exists_uniform_bfSeparation`: an analytic isomorphism-free set of pairs is separated at one
  back-and-forth level `α < ω₁`.
* `exists_uniform_bfSeparation_forall_ge`: the same level separates at every higher level.
* `exists_uniform_bfSeparation_of_analyticSets`: for analytic `B` and `C` with no element of `B`
  isomorphic to an element of `C`, one level `α < ω₁` separates every `x ∈ B` from every
  `y ∈ C`.

## Interpretation choices

* **Universes.**  `L : Language.{u, v}` is arbitrary and only `[L.IsRelational]` is assumed.
  The carrier is `ℕ`, so tree heights, the bound and the back-and-forth levels are all
  `Ordinal.{0}`, and no lift appears.
* **No countability of symbols.**  Analyticity refers to the product topology on
  `StructureSpace L × StructureSpace L`, which exists for every `L` (`AnalyticSet` needs only a
  topology), and the node conditions of `bfTree` are closed for every relational `L`
  (`isClosed_setOf_mem_bfTree`).  Countably many relation symbols are needed only to *produce*
  analytic sets from Borel ones, which is not done here.
* **Rank convention.**  Inherited from `BFTree`: ranks are those of strict extension and
  `treeHeight T = ⨆ x, succ (rank x)`, so `CodeBFEquiv α c d` gives
  `α < treeHeight (bfTree c d)` (`lt_treeHeight_bfTree_of_codeBFEquiv`); with the strict
  height bound `treeHeight (bfTree c d) < α` from `KleeneBrouwer.analytic_tree_rank_bounded`,
  the level `α` itself separates, with no offset.
* **Isomorphism.**  Non-isomorphism is stated through `structureIsoSetoid L`; no invariance
  predicate is assumed or produced.
* **Products of analytic sets.**  Mathlib has no product lemma for analytic sets; the
  two-set form uses `MeasureTheory.AnalyticSet.prod` from `G0Dichotomy` (Mathlib-only imports),
  stated there for arbitrary topological spaces.

## References

* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156,
  Springer, 1995, §31.A (the Boundedness Theorem for well-founded trees, Theorem 31.2) and
  §14.A (analytic sets as continuous images of Baire space).
-/

universe u v

namespace FirstOrder.Language

open Descriptive KleeneBrouwer MeasureTheory

variable {L : Language.{u, v}} [L.IsRelational]

/-- **Uniform back-and-forth separation.**  If `A` is an analytic set of pairs of codes and no
pair in `A` is isomorphic, then one countable back-and-forth level separates every pair of `A`.
No countability of the relation symbols is assumed. -/
theorem exists_uniform_bfSeparation {A : Set (StructureSpace L × StructureSpace L)}
    (hA : AnalyticSet A) (hA_noniso : ∀ p ∈ A, ¬ (structureIsoSetoid L).r p.1 p.2) :
    ∃ α : Ordinal.{0}, α < Ordinal.omega 1 ∧ ∀ p ∈ A, ¬ CodeBFEquiv α p.1 p.2 := by
  have hwf : ∀ p ∈ A, WellFounded (extBelow (bfTree p.1 p.2)) := fun p hp ↦
    (wellFounded_extBelow_iff_not_hasInfiniteBranch _).mpr fun hb ↦
      hA_noniso p hp ((hasInfiniteBranch_bfTree_iff _ _).mp hb)
  obtain ⟨α, hα, hbound⟩ := analytic_tree_rank_bounded hA (fun p ↦ bfTree p.1 p.2)
    isClosed_setOf_mem_bfTree hwf
  refine ⟨α, hα, fun p hp h ↦ ?_⟩
  have := hwf p hp
  exact ((lt_treeHeight_bfTree_of_codeBFEquiv h).trans (hbound p hp)).false

/-- `CodeBFEquiv` is antitone in the level. -/
theorem CodeBFEquiv.monotone {α β : Ordinal.{0}} (hαβ : α ≤ β) {c d : StructureSpace L}
    (h : CodeBFEquiv β c d) : CodeBFEquiv α c d :=
  @BFEquiv.monotone L ℕ c.toStructure ℕ d.toStructure _ _ _ hαβ _ _ h

/-- **Uniform separation persists upward**: the separating level of
`exists_uniform_bfSeparation` separates every pair of `A` at every higher level too, since
back-and-forth equivalence is antitone in the level. -/
theorem exists_uniform_bfSeparation_forall_ge {A : Set (StructureSpace L × StructureSpace L)}
    (hA : AnalyticSet A) (hA_noniso : ∀ p ∈ A, ¬ (structureIsoSetoid L).r p.1 p.2) :
    ∃ α : Ordinal.{0}, α < Ordinal.omega 1 ∧
      ∀ β, α ≤ β → ∀ p ∈ A, ¬ CodeBFEquiv β p.1 p.2 := by
  obtain ⟨α, hα, hsep⟩ := exists_uniform_bfSeparation hA hA_noniso
  exact ⟨α, hα, fun β hαβ p hp h ↦ hsep p hp (CodeBFEquiv.monotone hαβ h)⟩

/-- **Uniform separation of two analytic sets.**  If `B` and `C` are analytic and no element of
`B` is isomorphic to an element of `C`, then one countable back-and-forth level separates every
element of `B` from every element of `C`.  This is `exists_uniform_bfSeparation` for the
analytic product `B ×ˢ C` (`MeasureTheory.AnalyticSet.prod`). -/
theorem exists_uniform_bfSeparation_of_analyticSets {B C : Set (StructureSpace L)}
    (hB : AnalyticSet B) (hC : AnalyticSet C)
    (hdisj : ∀ x ∈ B, ∀ y ∈ C, ¬ (structureIsoSetoid L).r x y) :
    ∃ α : Ordinal.{0}, α < Ordinal.omega 1 ∧ ∀ x ∈ B, ∀ y ∈ C, ¬ CodeBFEquiv α x y := by
  obtain ⟨α, hα, hsep⟩ :=
    exists_uniform_bfSeparation (hB.prod hC) fun p hp ↦ hdisj p.1 hp.1 p.2 hp.2
  exact ⟨α, hα, fun x hx y hy ↦ hsep (x, y) ⟨hx, hy⟩⟩

end FirstOrder.Language
