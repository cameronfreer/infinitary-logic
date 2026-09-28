/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Set.Countable

/-!
# Countably many predicates with countable truth sides

Set-theoretic counting with no topology, nonemptiness, or uncountability assumption.  For
countably many predicates `P i` on `X`, each with a countable truth side (`{x | P i x}` or
`{x | ¬ P i x}` countable):

* `exists_countable_exceptions_of_splits`: outside one countable exceptional set every `P i` is
  constant, so all the predicates are decided simultaneously off that set.
* `countable_range_of_splits`: any map out of `X` that depends only on the truth values of the
  `P i` has countable range: the countable exceptional set contributes countably many values,
  and its complement contributes at most one.
* `constant_off_countable_of_splits`: on an uncountable `X`, a map whose values are separated by
  countably many tests, each with a countable side, is constant outside a countable set.

The descriptive consumer is the sentence-splits bridge (`Descriptive/SentenceSplits.lean`), where
the predicates are the truths of countably many sentences on a presentation of isomorphism
classes.
-/

universe u v w

section CountableSplits

variable {X : Type u} {ι : Type v} [Countable ι] (P : ι → X → Prop)

/-- **Simultaneous constancy off a countable set.**  If each of countably many predicates has a
countable truth side, then outside one countable set every predicate takes a single value. -/
theorem exists_countable_exceptions_of_splits
    (hsplit : ∀ i, ({x | P i x} : Set X).Countable ∨ ({x | ¬ P i x} : Set X).Countable) :
    ∃ E : Set X, E.Countable ∧ ∀ x ∉ E, ∀ y ∉ E, ∀ i, P i x ↔ P i y := by
  classical
  -- the countable side of each predicate
  let S : ι → Set X := fun i => if h : ({x | P i x} : Set X).Countable then {x | P i x}
    else {x | ¬ P i x}
  have hS : ∀ i, (S i).Countable := fun i => by
    by_cases h : ({x | P i x} : Set X).Countable
    · simp [S, h]
    · simpa [S, h] using (hsplit i).resolve_left h
  -- off the countable side, the predicate takes the other value
  have hoff : ∀ i, ∀ x ∉ S i, ∀ y ∉ S i, (P i x ↔ P i y) := fun i x hx y hy => by
    by_cases h : ({x | P i x} : Set X).Countable
    · simp only [S, h, dite_true] at hx hy
      exact iff_of_false hx hy
    · simp only [S, h, dite_false] at hx hy
      exact iff_of_true (not_not.mp hx) (not_not.mp hy)
  refine ⟨⋃ i, S i, Set.countable_iUnion hS, fun x hx y hy i => ?_⟩
  exact hoff i x (fun h => hx (Set.mem_iUnion.mpr ⟨i, h⟩)) y
    (fun h => hy (Set.mem_iUnion.mpr ⟨i, h⟩))

/-- **Countable range.**  A map that depends only on the truth values of countably many
predicates, each with a countable truth side, has countable range. -/
theorem countable_range_of_splits {Y : Type w} (g : X → Y)
    (hg : ∀ x y, (∀ i, P i x ↔ P i y) → g x = g y)
    (hsplit : ∀ i, ({x | P i x} : Set X).Countable ∨ ({x | ¬ P i x} : Set X).Countable) :
    (Set.range g).Countable := by
  obtain ⟨E, hE, hconst⟩ := exists_countable_exceptions_of_splits P hsplit
  by_cases h : ∃ x₀, x₀ ∉ E
  · obtain ⟨x₀, hx₀⟩ := h
    refine ((hE.image g).union (Set.countable_singleton (g x₀))).mono ?_
    rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ E
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr (hg x x₀ (hconst x hx x₀ hx₀))
  · refine (hE.image g).mono ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨x, by_contra fun hx => h ⟨x, hx⟩, rfl⟩

/-- **Constant off a countable set.**  On an uncountable domain, a map whose values are separated
by countably many tests, each with a countable truth side along the map, agrees with one of its
values outside a countable set. -/
theorem constant_off_countable_of_splits {Y : Type w} (hX : ¬ Countable X) (f : X → Y)
    (test : ι → Y → Prop) (hsep : ∀ y z, (∀ i, test i y ↔ test i z) → y = z)
    (hsplit : ∀ i, ({x | test i (f x)} : Set X).Countable ∨
      ({x | ¬ test i (f x)} : Set X).Countable) :
    ∃ x₀, ({x | f x ≠ f x₀} : Set X).Countable := by
  obtain ⟨E, hE, hconst⟩ := exists_countable_exceptions_of_splits (fun i x => test i (f x)) hsplit
  have : ∃ x₀, x₀ ∉ E := by
    by_contra h
    exact hX (Set.countable_univ_iff.mp (hE.mono fun x _ => by_contra fun hx => h ⟨x, hx⟩))
  obtain ⟨x₀, hx₀⟩ := this
  refine ⟨x₀, hE.mono fun x hx => ?_⟩
  by_contra hxE
  exact hx (hsep _ _ (hconst x hxE x₀ hx₀))

end CountableSplits
