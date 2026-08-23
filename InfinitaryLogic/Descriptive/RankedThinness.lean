/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.PerfectAntichain
import InfinitaryLogic.OrdinalUtil
import Architect

/-!
# Thinness from a countable-ordinal rank

The standard route to thinness: equip the points with a rank below `ω₁`, know that each
fixed-rank antichain is countable, and know that a Cantor antichain has bounded rank.  Then a
Cantor antichain would be a countable union of countable sets while being of size continuum.

`ThinRankAnalysis` bundles exactly that **evidence**.  `no_cantorAntichain` and `isThinOn` are
derived from it, not fields: a structure whose fields already asserted the conclusion would
prove nothing.

`Setoid.countable_antichain` is the elementary quotient step, factored out because it is
independent of any rank and useful on its own.
-/

open Set

universe u

/-- An antichain injects into the quotient, so a countable quotient forces a countable
antichain.  No topology and no rank. -/
theorem Setoid.countable_antichain {X : Type u} (r : Setoid X) [Countable (Quotient r)]
    {B : Set X} (hB : ∀ x ∈ B, ∀ y ∈ B, r.r x y → x = y) : B.Countable := by
  have hinj : Function.Injective (fun x : B => Quotient.mk r x.1) := by
    intro x y hxy
    exact Subtype.ext (hB x.1 x.2 y.1 y.2 (Quotient.exact hxy))
  exact Set.countable_coe_iff.mp (Function.Injective.countable hinj)

variable {X : Type u} [TopologicalSpace X]

/-- The evidence that a rank witnesses thinness of `A` for `r`. -/
@[blueprint "def:thin-rank-analysis"
  (title := /-- Ranked thinness analysis -/)
  (statement := /-- A \emph{ranked thinness analysis} of $A$ for $r$ is a rank
    $\rho : X \to \mathrm{Ord}$ together with the evidence that $\rho$ is $< \omegaone$ on $A$,
    that each fixed-rank antichain inside $A$ is countable, and that any Cantor antichain in $A$
    has ranks bounded below $\omegaone$.  It packages hypotheses only; it asserts no conclusion. -/)
  (uses := ["def:cantor-antichain"])]
structure ThinRankAnalysis (r : Setoid X) (A : Set X) where
  /-- The rank function. -/
  rank : X → Ordinal.{0}
  /-- Ranks of points of `A` are countable ordinals. -/
  rank_lt_omega1 : ∀ x ∈ A, rank x < Ordinal.omega 1
  /-- Each fixed-rank antichain inside `A` is countable. -/
  fixedRankAntichains_countable :
    ∀ α < Ordinal.omega 1, ∀ B : Set X, B ⊆ A → (∀ x ∈ B, rank x = α) →
      (∀ x ∈ B, ∀ y ∈ B, r.r x y → x = y) → B.Countable
  /-- A Cantor antichain has ranks bounded below `ω₁`. -/
  bounded_on_cantor_antichains :
    ∀ f : (ℕ → Bool) → X, Continuous f → (∀ x, f x ∈ A) →
      (∀ x y, x ≠ y → ¬r.r (f x) (f y)) → ∃ β < Ordinal.omega 1, ∀ x, rank (f x) < β

namespace ThinRankAnalysis

variable {r : Setoid X} {A : Set X}

/-- **No Cantor antichain.**  A Cantor antichain would be the union, over the countably many
ordinals below its rank bound, of fixed-rank antichains — each countable — hence countable;
but it is a continuous injective image of Cantor space. -/
theorem no_cantorAntichain (T : ThinRankAnalysis r A) : ¬HasCantorAntichainOn r A := by
  rintro hC
  obtain ⟨f, hcont, hmem, hineq⟩ := hC
  -- injectivity from reflexivity, as in `HasCantorAntichainOn.injective`
  have hinj : Function.Injective f := by
    intro x y hxy
    by_contra hne
    exact hineq x y hne (hxy ▸ r.refl (f x))
  obtain ⟨β, hβ, hbound⟩ := T.bounded_on_cantor_antichains f hcont hmem hineq
  -- any subset of the range is an antichain: distinct points come from distinct arguments
  have hanti : ∀ B : Set X, B ⊆ Set.range f → ∀ x ∈ B, ∀ y ∈ B, r.r x y → x = y := by
    rintro B hBsub x hx y hy hr
    obtain ⟨a, rfl⟩ := hBsub hx
    obtain ⟨b, rfl⟩ := hBsub hy
    by_contra hne
    exact hineq a b (fun h => hne (congrArg f h)) hr
  -- slice the range by rank
  have hcov : Set.range f ⊆ ⋃ α : Set.Iio β, {y ∈ Set.range f | T.rank y = α.1} := by
    rintro _ ⟨a, rfl⟩
    exact Set.mem_iUnion.mpr ⟨⟨T.rank (f a), hbound a⟩, ⟨a, rfl⟩, rfl⟩
  have : Countable (Set.Iio β) := InfinitaryLogic.countable_Iio_of_lt_omega1 β hβ
  have hpiece : ∀ α : Set.Iio β, ({y ∈ Set.range f | T.rank y = α.1} : Set X).Countable := by
    intro α
    refine T.fixedRankAntichains_countable α.1 (lt_trans α.2 hβ) _ ?_ (fun y hy => hy.2) ?_
    · rintro y ⟨⟨a, rfl⟩, -⟩; exact hmem a
    · exact hanti _ (fun y hy => hy.1)
  have hcount : (Set.range f).Countable :=
    Set.Countable.mono hcov (Set.countable_iUnion hpiece)
  -- but the range is an injective image of Cantor space, which is uncountable by diagonalization
  have huncount : ¬(Set.range f).Countable := by
    intro h
    let _ : Countable (Set.range f) := Set.countable_coe_iff.mpr h
    have hCantor : Countable (ℕ → Bool) :=
      Function.Injective.countable
        (f := fun x => (⟨f x, ⟨x, rfl⟩⟩ : Set.range f))
        (fun x y hxy => hinj (Subtype.mk.inj hxy))
    let _ : Countable (ℕ → Bool) := hCantor
    obtain ⟨g, hg⟩ := exists_surjective_nat (ℕ → Bool)
    let d : ℕ → Bool := fun n => !(g n n)
    obtain ⟨n, hn⟩ := hg d
    have hdiag := congrFun hn n
    simp [d] at hdiag
  exact huncount hcount

/-- **Thinness.**  Immediate from `no_cantorAntichain`, since a perfect antichain would give a
Cantor antichain. -/
@[blueprint "thm:ranked-thinness"
  (title := /-- Ranked thinness criterion -/)
  (statement := /-- If $A$ admits a ranked thinness analysis for $r$ in a complete metric space,
    then $A$ is thin for $r$. -/)
  (proof := /-- A Cantor antichain would have ranks bounded by some $\beta < \omegaone$, so it
    would be the union of the countably many fixed-rank antichains below $\beta$, each countable,
    hence countable.  But it is an injective image of $2^{\mathbb{N}}$, which is uncountable by
    diagonalization.  So there is no Cantor antichain, and therefore no perfect antichain. -/)
  (uses := ["def:thin-rank-analysis", "def:thin-on", "def:cantor-antichain"])]
theorem isThinOn {α : Type u} [MetricSpace α] [CompleteSpace α] {r : Setoid α} {A : Set α}
    (T : ThinRankAnalysis r A) : IsThinOn r A :=
  IsThinOn.of_no_cantorAntichain T.no_cantorAntichain

end ThinRankAnalysis
