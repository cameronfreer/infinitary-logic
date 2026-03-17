/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Karp.Theorem
import InfinitaryLogic.Lomega1omega.Theory
import InfinitaryLogic.Lomega1omega.Embedding
import InfinitaryLogic.Scott.Sentence
import InfinitaryLogic.Scott.RefinementCount

/-!
# Countable Corollary to Karp's Theorem

This file proves that for countable structures, Lω₁ω-elementary equivalence (and hence
L∞ω-elementary equivalence) implies isomorphism.

## Main Results

- `countable_LomegaEquiv_implies_iso`: For countable structures in a countable relational
  language, Lω₁ω-elementary equivalence implies isomorphism (KK04 Corollary 1.2.2).
- `countable_LinfEquiv_implies_iso`: Same result for L∞ω-elementary equivalence.

## References

- [KK04], Corollary 1.2.2
-/

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable [Countable (Σ l, L.Relations l)]

open FirstOrder Structure Fin Ordinal

/-- Conditional variant of `countable_LomegaEquiv_implies_iso`. -/
theorem countable_LomegaEquiv_implies_iso_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N] :
    LomegaEquiv L M N → Nonempty (M ≃[L] N) := by
  intro hEquiv
  apply scottSentence_realizes_implies_equiv_of hcount
  rw [Formulaω.realize_as_sentence_iff_toSentenceω]
  exact (hEquiv _).mp ((Formulaω.realize_as_sentence_iff_toSentenceω _ _).mp
    (scottSentence_self_of hcount M))

/-- Conditional variant of `countable_LinfEquiv_implies_iso`. -/
theorem countable_LinfEquiv_implies_iso_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N] :
    LinfEquiv L M N → Nonempty (M ≃[L] N) := by
  intro hLinf
  apply countable_LomegaEquiv_implies_iso_of hcount
  intro φ
  simpa only [Sentenceω.realize_toLinf] using hLinf (Sentenceω.toLinf φ)

omit [Countable (Σ l, L.Relations l)] in
/-- For countable structures, potential isomorphism implies actual isomorphism.

This is proved by direct back-and-forth construction on the PotentialIso family,
avoiding the need for Scott sentences or Karp's theorem. -/
theorem countable_PotentialIso_implies_iso
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N] :
    Nonempty (PotentialIso L M N) → Nonempty (M ≃[L] N) := by
  intro ⟨P⟩
  exact P.countable_toEquiv

/-- For countable structures, BFEquiv at all ordinals implies isomorphism. -/
theorem countable_BFEquiv_all_implies_iso
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N]
    (h : ∀ α : Ordinal.{w}, BFEquiv (L := L) α 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N)) :
    Nonempty (M ≃[L] N) := by
  apply countable_PotentialIso_implies_iso
  exact potentialIso_iff_BFEquiv_all.mpr h

/-! ### Unconditional Wrappers (via CRH) -/

/-- For countable structures in a countable relational language, Lω₁ω-elementary
equivalence implies isomorphism. -/
theorem countable_LomegaEquiv_implies_iso
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N] :
    LomegaEquiv L M N → Nonempty (M ≃[L] N) :=
  countable_LomegaEquiv_implies_iso_of countableRefinementHypothesis

/-- For countable structures in a countable relational language, L∞ω-elementary
equivalence implies isomorphism. -/
theorem countable_LinfEquiv_implies_iso
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N] :
    LinfEquiv L M N → Nonempty (M ≃[L] N) :=
  countable_LinfEquiv_implies_iso_of countableRefinementHypothesis

end Language

end FirstOrder
