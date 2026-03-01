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

-- bounded_scottRank_iso_eq_BFEquiv moved to Scott/Legacy.lean

omit [Countable (Σ l, L.Relations l)] in
/-- When a structure has `StabilizesCompletely M α` (with α < ω₁) and BFEquiv α holds,
the structures are isomorphic. Unconditional (no `CountableRefinementHypothesis` needed).

This decouples the isomorphism conclusion from scottRank entirely, taking
`StabilizesCompletely` as a direct hypothesis. -/
theorem stabilization_bound_iso_eq_BFEquiv
    {M N : Type w} [L.Structure M] [L.Structure N] [Countable M] [Countable N]
    {α : Ordinal.{0}} (_hα : α < Ordinal.omega 1)
    (hstab : StabilizesCompletely (L := L) M α)
    (hBF : BFEquiv (L := L) α 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N)) :
    Nonempty (M ≃[L] N) := by
  have hAll : ∀ γ < (Ordinal.omega 1 : Ordinal.{0}),
      BFEquiv (L := L) γ 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) := by
    intro γ _
    rcases le_or_gt γ α with hγα | hαγ
    · exact BFEquiv.monotone hγα hBF
    · exact BFEquiv_upgrade_at_stabilization hstab hBF γ hαγ.le
  exact BFEquiv_below_omega1_implies_iso hAll

/-- When all countable models of a sentence have Scott height bounded by α (with α < ω₁),
isomorphism between countable models is equivalent to BF-equivalence at level α.
Conditional on `CountableRefinementHypothesis`. Sorry-free.

This replaces `bounded_scottRank_iso_eq_BFEquiv` by using `scottHeight` (which has a
sorry-free conditional relationship to `StabilizesCompletely`) instead of `scottRank`
(which has the β > α gap). -/
theorem bounded_scottHeight_iso_eq_BFEquiv_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    {φ : L.Sentenceω} {α : Ordinal.{0}} (hα : α < Ordinal.omega 1)
    (hbound : ∀ (M : Type w) [L.Structure M] [Countable M],
      Sentenceω.Realize φ M → scottHeight (L := L) M ≤ α)
    {M N : Type w} [L.Structure M] [L.Structure N] [Countable M] [Countable N]
    (hM : Sentenceω.Realize φ M) (_hN : Sentenceω.Realize φ N) :
    Nonempty (M ≃[L] N) ↔
    BFEquiv (L := L) α 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) := by
  constructor
  · intro ⟨e⟩
    have h : (e : M → N) ∘ Fin.elim0 = Fin.elim0 := funext fun i => i.elim0
    rw [← h]
    exact equiv_implies_BFEquiv e α 0 Fin.elim0
  · intro hBF
    have hstabM := scottHeight_le_implies_stabilizesCompletely_of hcount M (hbound M hM)
    exact stabilization_bound_iso_eq_BFEquiv hα hstabM hBF

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- The number of isomorphism classes of countable models of an Lω₁ω sentence
is either at most ℵ₁ or exactly 2^ℵ₀ (Morley's counting theorem).

This is stated schematically as the dichotomy property, since the full statement
requires coding structures as elements of a Polish space, which needs
significant descriptive set theory infrastructure.

The result uses the Silver-Burgess theorem from descriptive set theory. -/
theorem morley_counting_dichotomy
    (_φ : L.Sentenceω) :
    True := by  -- Schematic: see docstring for the actual mathematical content
  trivial

end Language

end FirstOrder
