/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.AnalyticWellOrderBoundedness
import InfinitaryLogic.Descriptive.RankedThinness

/-!
# Ranked thinness from well-order presentations (issue #64)

The adapter between analytic boundedness and the thinness package: a rank that is *computed by
coded well-orders*, presented continuously on each Cantor antichain, satisfies
`ThinRankAnalysis`'s bounded-on-Cantor-antichains field.

## The quantifier order is the content

The presentation is supplied **inside** the antichain callback:

```
∀ f, Continuous f → … → ∃ code : (ℕ → Bool) → StructureSpace L, …
```

not as a global `X → StructureSpace L` field.  Each Cantor antichain gets to choose its own
coding, which is what the intended consumers can actually produce — a uniform coding of all of `X`
is a much stronger and usually unavailable demand.  Producing that per-antichain presentation is
the hard downstream mathematics; boundedness itself, once a presentation exists, is this file.

The boundedness field is then four lines: the antichain's coding domain is all of Cantor space,
which is analytic because it is closed in a Polish space, so
`analytic_rank_bounded_of_continuousOn_wellOrderPresentation` applies at `B := Set.univ`.

`ThinRankAnalysis` measures against `Ordinal.omega 1` and the boundedness layer against
`(Cardinal.aleph 1).ord`; `Cardinal.ord_aleph` identifies them.
-/

namespace FirstOrder.Language

open FirstOrder Structure Set

universe w

variable {L : Language.{0, 0}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

/-- **Ranked thinness from per-antichain well-order presentations**: a rank whose value on each
continuous Cantor antichain is realized as the order type of a continuously-presented family of
coded well-orders is a `ThinRankAnalysis`.

The first two hypotheses are `ThinRankAnalysis`'s own fields, passed through unchanged.  Only
`bounded_on_cantor_antichains` is derived, and `present` is exactly what it needs: given an
antichain `f`, a continuous coding of Cantor space by well-orders whose order types are the ranks
along `f`.

`ThinRankAnalysis` is *evidence*, not a proposition, so this is a `def`. -/
def ThinRankAnalysis.of_wellOrderPresentations {X : Type w} [TopologicalSpace X]
    {r : Setoid X} {A : Set X} (lt : L.Relations 2) (rank : X → Ordinal.{0})
    (rank_lt_omega1 : ∀ x ∈ A, rank x < Ordinal.omega 1)
    (fixedRankAntichains_countable :
      ∀ α < Ordinal.omega 1, ∀ B : Set X, B ⊆ A → (∀ x ∈ B, rank x = α) →
        (∀ x ∈ B, ∀ y ∈ B, r.r x y → x = y) → B.Countable)
    (present : ∀ f : (ℕ → Bool) → X, Continuous f → (∀ x, f x ∈ A) →
      (∀ x y, x ≠ y → ¬r.r (f x) (f y)) →
      ∃ code : (ℕ → Bool) → StructureSpace L, Continuous code ∧
        (∀ x, code x ∈ wellOrderClass lt) ∧
        ∀ (x : ℕ → Bool) (h : IsWellOrder ℕ fun a b : ℕ =>
            @Structure.RelMap L ℕ (code x).toStructure 2 lt ![a, b]),
          rank (f x) = @Ordinal.type ℕ
            (fun a b : ℕ => @Structure.RelMap L ℕ (code x).toStructure 2 lt ![a, b]) h) :
    ThinRankAnalysis r A where
  rank := rank
  rank_lt_omega1 := rank_lt_omega1
  fixedRankAntichains_countable := fixedRankAntichains_countable
  bounded_on_cantor_antichains := by
    intro f hcont hmem hineq
    obtain ⟨code, hcodecont, hcodeWO, hcoderank⟩ := present f hcont hmem hineq
    -- Cantor space is a countable product of copies of `Bool`: compact, metrizable, second
    -- countable, hence Polish — the same `PolishSpace.mk` route `StructureSpace L` takes
    have : PolishSpace (ℕ → Bool) := PolishSpace.mk
    obtain ⟨β, hβ, hbound⟩ := analytic_rank_bounded_of_continuousOn_wellOrderPresentation
      (B := (Set.univ : Set (ℕ → Bool))) lt isClosed_univ.analyticSet code
      hcodecont.continuousOn (fun x _ => hcodeWO x) (fun x => rank (f x))
      (fun x _ h => hcoderank x h)
    exact ⟨β, by rwa [← Cardinal.ord_aleph], fun x => hbound x (Set.mem_univ x)⟩

end FirstOrder.Language
