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

The presentation is supplied **inside** the antichain callback, and only on a Cantor **subcopy**:

```
∀ f, Continuous f → … → ∃ e, Continuous e ∧ Injective e ∧
                          ∃ code : (ℕ → Bool) → StructureSpace L, …
```

not as a global `X → StructureSpace L` field.  Each Cantor antichain gets to choose its own coding,
and need only present a subcopy of itself.  A global presentation would impose an unwanted global
rank bound and is stronger than intended consumers can supply; requiring the whole antichain to be
presented is likewise stronger than the thinness argument needs, since that argument runs on any
Cantor subcopy.  Producing the per-antichain presentation is the hard downstream mathematics;
boundedness itself, once a presentation exists, is this file.

`ThinRankAnalysis.of_full_wellOrderPresentations` recovers the whole-antichain form for producers
that have it, by taking the subcopy to be the identity.

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
`bounded_on_refined_cantor_antichains` is derived, and `present` is exactly what it needs: given an
antichain `f`, a Cantor subcopy `e` together with a continuous coding of Cantor space by
well-orders whose order types are the ranks along `f ∘ e`.

`ThinRankAnalysis` is *evidence*, not a proposition, so this is a `def`. -/
@[blueprint "def:wellorder-presentation-thinness"
  (title := /-- Ranked thinness from well-order presentations -/)
  (statement := /-- Suppose a rank $\rho$ is $< \omegaone$ on $A$ and each of its fixed-rank
    antichains inside $A$ is countable, and suppose further that every continuous Cantor antichain
    $f$ in $A$ admits, on some continuously and injectively embedded Cantor \emph{subcopy} $e$, a
    \emph{presentation}: a continuous map from $2^{\mathbb{N}}$ to codes, all of them
    well-orders, whose order types are the ranks along $f \circ e$.  Then $\rho$ is a ranked
    thinness analysis of $A$ for $r$. -/)
  (proof := /-- Only the refined Cantor-antichain bound needs proving.  Given an antichain, take
    its subcopy and presentation; the coding is continuous on all of $2^{\mathbb{N}}$, which is
    analytic because it is closed in a Polish space, so boundedness for analytic families of coded
    well-orders bounds the order types --- that is, the ranks along $f \circ e$ --- by a single
    countable ordinal.  Return that same subcopy with the bound. -/)
  (uses := ["thm:analytic-wellorder-boundedness", "def:thin-rank-analysis"])]
def ThinRankAnalysis.of_wellOrderPresentations {X : Type w} [TopologicalSpace X]
    {r : Setoid X} {A : Set X} (lt : L.Relations 2) (rank : X → Ordinal.{0})
    (rank_lt_omega1 : ∀ x ∈ A, rank x < Ordinal.omega 1)
    (fixedRankAntichains_countable :
      ∀ α < Ordinal.omega 1, ∀ B : Set X, B ⊆ A → (∀ x ∈ B, rank x = α) →
        (∀ x ∈ B, ∀ y ∈ B, r.r x y → x = y) → B.Countable)
    (present : ∀ f : (ℕ → Bool) → X, Continuous f → (∀ x, f x ∈ A) →
      (∀ x y, x ≠ y → ¬r.r (f x) (f y)) →
      ∃ e : (ℕ → Bool) → (ℕ → Bool), Continuous e ∧ Function.Injective e ∧
        ∃ code : (ℕ → Bool) → StructureSpace L, Continuous code ∧
          (∀ x, code x ∈ wellOrderClass lt) ∧
          ∀ (x : ℕ → Bool) (h : IsWellOrder ℕ fun a b : ℕ =>
              @Structure.RelMap L ℕ (code x).toStructure 2 lt ![a, b]),
            rank (f (e x)) = @Ordinal.type ℕ
              (fun a b : ℕ => @Structure.RelMap L ℕ (code x).toStructure 2 lt ![a, b]) h) :
    ThinRankAnalysis r A where
  rank := rank
  rank_lt_omega1 := rank_lt_omega1
  fixedRankAntichains_countable := fixedRankAntichains_countable
  bounded_on_refined_cantor_antichains := by
    intro f hcont hmem hineq
    obtain ⟨e, hecont, heinj, code, hcodecont, hcodeWO, hcoderank⟩ := present f hcont hmem hineq
    -- Both parents synthesize, but `PolishSpace (ℕ → Bool)` currently does not.
    -- Construct it explicitly with `PolishSpace.mk`, as for `StructureSpace L`.
    have : PolishSpace (ℕ → Bool) := PolishSpace.mk
    obtain ⟨β, hβ, hbound⟩ := analytic_rank_bounded_of_continuousOn_wellOrderPresentation
      (B := (Set.univ : Set (ℕ → Bool))) lt isClosed_univ.analyticSet code
      hcodecont.continuousOn (fun x _ => hcodeWO x) (fun x => rank (f (e x)))
      (fun x _ h => hcoderank x h)
    exact ⟨e, hecont, heinj, β, by rwa [← Cardinal.ord_aleph],
      fun x => hbound x (Set.mem_univ x)⟩

/-- **Compatibility with a presentation of the whole antichain.**  A producer that can present
*every* point of a Cantor antichain — the stronger, older hypothesis — still yields a
`ThinRankAnalysis`: take the subcopy to be the identity.

Delegates to `ThinRankAnalysis.of_wellOrderPresentations`; the analytic-boundedness argument lives
there and is not repeated.  Only this direction is supplied, and no converse is claimed. -/
def ThinRankAnalysis.of_full_wellOrderPresentations {X : Type w} [TopologicalSpace X]
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
    ThinRankAnalysis r A :=
  ThinRankAnalysis.of_wellOrderPresentations lt rank rank_lt_omega1
    fixedRankAntichains_countable
    fun f hcont hmem hineq =>
      let ⟨code, hc, hwo, hrk⟩ := present f hcont hmem hineq
      ⟨id, continuous_id, Function.injective_id, code, hc, hwo, hrk⟩

/-! ## Regression: the former hypotheses still construct an analysis -/

section Compatibility

variable {X : Type w} [TopologicalSpace X] {r : Setoid X} {A : Set X}

/-- A bound on the **whole** antichain still gives a `ThinRankAnalysis`, via the identity subcopy. -/
example (rank : X → Ordinal.{0}) (h1 : ∀ x ∈ A, rank x < Ordinal.omega 1)
    (h2 : ∀ α < Ordinal.omega 1, ∀ B : Set X, B ⊆ A → (∀ x ∈ B, rank x = α) →
      (∀ x ∈ B, ∀ y ∈ B, r.r x y → x = y) → B.Countable)
    (h3 : ∀ f : (ℕ → Bool) → X, Continuous f → (∀ x, f x ∈ A) →
      (∀ x y, x ≠ y → ¬r.r (f x) (f y)) → ∃ β < Ordinal.omega 1, ∀ x, rank (f x) < β) :
    ThinRankAnalysis r A :=
  ThinRankAnalysis.of_bounded_on_cantor_antichains rank h1 h2 h3

/-- A presentation of the **whole** antichain still gives a `ThinRankAnalysis`, likewise. -/
example (lt : L.Relations 2) (rank : X → Ordinal.{0}) (h1 : ∀ x ∈ A, rank x < Ordinal.omega 1)
    (h2 : ∀ α < Ordinal.omega 1, ∀ B : Set X, B ⊆ A → (∀ x ∈ B, rank x = α) →
      (∀ x ∈ B, ∀ y ∈ B, r.r x y → x = y) → B.Countable)
    (h3 : ∀ f : (ℕ → Bool) → X, Continuous f → (∀ x, f x ∈ A) →
      (∀ x y, x ≠ y → ¬r.r (f x) (f y)) →
      ∃ code : (ℕ → Bool) → StructureSpace L, Continuous code ∧
        (∀ x, code x ∈ wellOrderClass lt) ∧
        ∀ (x : ℕ → Bool) (h : IsWellOrder ℕ fun a b : ℕ =>
            @Structure.RelMap L ℕ (code x).toStructure 2 lt ![a, b]),
          rank (f x) = @Ordinal.type ℕ
            (fun a b : ℕ => @Structure.RelMap L ℕ (code x).toStructure 2 lt ![a, b]) h) :
    ThinRankAnalysis r A :=
  ThinRankAnalysis.of_full_wellOrderPresentations lt rank h1 h2 h3

end Compatibility

end FirstOrder.Language
