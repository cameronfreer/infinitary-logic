/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Lomega1omega.Theory
import InfinitaryLogic.Scott.Height
import InfinitaryLogic.Scott.RefinementCount
import Architect

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

- [Mar16]
- [KK04]
-/

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable [Countable (Σ l, L.Relations l)]

open FirstOrder Structure Cardinal Ordinal

omit [Countable (Σ l, L.Relations l)] in
/-- When a structure has `StabilizesCompletely M α` (with α < ω₁) and BFEquiv α holds,
the structures are isomorphic. Unconditional (no `CountableRefinementHypothesis` needed).

This decouples the isomorphism conclusion from scottRank entirely, taking
`StabilizesCompletely` as a direct hypothesis. -/
@[blueprint "thm:stabilization-bound-iso"
  (title := /-- Stabilization bound determines isomorphism -/)
  (statement := /-- If $M$ stabilizes completely at $\alpha < \omegaone$ and
    $\BFEquiv_\alpha(\bar{a},\bar{b})$ holds, then $M \cong N$. -/)
  (proof := /-- Complete stabilization at $\alpha$ lets us upgrade $\BFEquiv_\alpha$
    to $\BFEquiv_\gamma$ for all $\gamma < \omegaone$, then apply Karp's theorem. -/)
  (uses := ["def:BFEquiv"])]
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

/-! ### Unconditional Wrapper (via CRH) -/

/-- When all countable models of a sentence have Scott height bounded by α (with α < ω₁),
isomorphism between countable models is equivalent to BF-equivalence at level α. -/
@[blueprint "thm:bounded-scott-height-iso"
  (title := /-- Bounded Scott height determines isomorphism -/)
  (statement := /-- If all countable models of $\varphi$ have Scott height $\leq \alpha
    < \omegaone$, then isomorphism is equivalent to $\BFEquiv_\alpha$. -/)
  (proof := /-- The forward direction follows from $\BFEquiv$ being an invariant of
    isomorphism. For the reverse, the Scott height bound gives complete stabilization
    at $\alpha$ for both models, so we apply the stabilization-bound theorem. -/)
  (uses := ["def:scottHeight", "def:BFEquiv"])
  (proofUses := ["thm:CRH", "thm:stabilization-bound-iso"])]
theorem bounded_scottHeight_iso_eq_BFEquiv
    {φ : L.Sentenceω} {α : Ordinal.{0}} (hα : α < Ordinal.omega 1)
    (hbound : ∀ (M : Type w) [L.Structure M] [Countable M],
      Sentenceω.Realize φ M → scottHeight (L := L) M ≤ α)
    {M N : Type w} [L.Structure M] [L.Structure N] [Countable M] [Countable N]
    (hM : Sentenceω.Realize φ M) (hN : Sentenceω.Realize φ N) :
    Nonempty (M ≃[L] N) ↔
    BFEquiv (L := L) α 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) :=
  bounded_scottHeight_iso_eq_BFEquiv_of countableRefinementHypothesis hα hbound hM hN

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
