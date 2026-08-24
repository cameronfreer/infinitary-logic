/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Karp.CarrierTheorem
import InfinitaryLogic.Lomega1omega.Theory
import InfinitaryLogic.Scott.Sentence
import InfinitaryLogic.Scott.RefinementCount

/-!
# Countable Corollary to Karp's Theorem

This file proves that for countable structures, elementary equivalence in the infinitary
logics implies isomorphism.

The two results take genuinely different routes, and the `L∞ω` one is the stronger.
`L∞ω`-equivalence goes straight through Karp's theorem to a potential isomorphism and then to
an isomorphism by back-and-forth on countable structures — no Scott sentence, no refinement
counting, and no countable-language hypothesis. `Lω₁ω`-equivalence has no such route: it is
weaker than `L∞ω`-equivalence, so it must go through the Scott sentence, which is what drags
in `CountableRefinementHypothesis` and the countable relational language.

## Main Results

- `countable_InfEquivW_implies_iso`: for countable structures, `L∞ω`-elementary equivalence
  implies isomorphism. Unconditional — no refinement hypothesis, no countable language.
- `countable_LomegaEquiv_implies_iso`: for countable structures in a countable relational
  language, `Lω₁ω`-elementary equivalence implies isomorphism (KK04 Corollary 1.2.2).

## References

- [KK04], Corollary 1.2.2
-/

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable [Countable (Σ l, L.Relations l)]

open FirstOrder Structure Ordinal

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

omit [Countable (Σ l, L.Relations l)] in
/-- **For countable structures, `L∞ω`-elementary equivalence implies isomorphism.**

Unconditional: Karp's theorem turns the equivalence into a potential isomorphism, and
back-and-forth on countable structures turns that into an isomorphism. Neither step needs a
refinement hypothesis or a countable language, so unlike the `Lω₁ω` statement below this one
has no `_of` variant to discharge. -/
theorem countable_InfEquivW_implies_iso
    {M N : Type w} [L.Structure M] [L.Structure N]
    [Countable M] [Countable N] :
    InfEquivW L M N → Nonempty (M ≃[L] N) :=
  fun h => countable_PotentialIso_implies_iso (karp_theorem_w.mpr h)

omit [Countable ((l : ℕ) × L.Relations l)] in
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

end Language

end FirstOrder
