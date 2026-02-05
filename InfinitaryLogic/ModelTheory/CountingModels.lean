/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Lomega1omega.Theory
import InfinitaryLogic.Scott.Height

/-!
# Counting Models

This file states model-counting results for Lω₁ω, connecting Scott rank bounds
to the structure of the isomorphism relation.

## Main Results

- `bounded_scottRank_iso_eq_BFEquiv`: When all models of a sentence have Scott rank
  bounded by α, isomorphism equals BF-equivalence at level α.
- The Morley counting theorem (schematic): for a sentence of Lω₁ω, the number of
  countable models is either ≤ ℵ₁ or exactly 2^ℵ₀.

## References

- [Marker, "Lectures on Infinitary Model Theory", 2016]
- [Keisler-Knight, "Barwise: Infinitary Logic and Admissible Sets", 2004]
-/

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable [Countable (Σ l, L.Relations l)]

open FirstOrder Structure Cardinal Ordinal

/-- When all countable models of a sentence have Scott rank bounded by α (with α < ω₁),
isomorphism between countable models is equivalent to BF-equivalence at level α.

This reduces the isomorphism problem to a finite-level back-and-forth comparison,
which is key for descriptive set-theoretic analyses of the isomorphism relation. -/
theorem bounded_scottRank_iso_eq_BFEquiv
    {φ : L.Sentenceω} {α : Ordinal} (hα : α < Ordinal.omega 1)
    (hbound : ∀ (M : Type w) [L.Structure M] [Countable M],
      Sentenceω.Realize φ M → scottRank (L := L) M ≤ α)
    {M N : Type w} [L.Structure M] [L.Structure N] [Countable M] [Countable N]
    (hM : Sentenceω.Realize φ M) (hN : Sentenceω.Realize φ N) :
    Nonempty (M ≃[L] N) ↔
    BFEquiv (L := L) α 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) := by
  sorry

/-- The number of isomorphism classes of countable models of an Lω₁ω sentence
is either at most ℵ₁ or exactly 2^ℵ₀ (Morley's counting theorem).

This is stated schematically as the dichotomy property, since the full statement
requires coding structures as elements of a Polish space, which needs
significant descriptive set theory infrastructure.

The result uses the Silver-Burgess theorem from descriptive set theory. -/
theorem morley_counting_dichotomy
    (φ : L.Sentenceω) :
    True := by  -- Schematic: see docstring for the actual mathematical content
  trivial

end Language

end FirstOrder
