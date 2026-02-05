/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Karp.Theorem
import InfinitaryLogic.Lomega1omega.Theory
import InfinitaryLogic.Scott.Sentence

/-!
# Countable Corollary to Karp's Theorem

This file proves that for countable structures, Lω₁ω-elementary equivalence (and hence
L∞ω-elementary equivalence) implies isomorphism.

## Main Results

- `countable_LomegaEquiv_implies_iso`: For countable structures in a countable relational
  language, Lω₁ω-elementary equivalence implies isomorphism (KK04 Corollary 1.2.2).
- `countable_LinfEquiv_implies_iso`: Same result for L∞ω-elementary equivalence.

## References

- [Keisler-Knight, "Barwise: Infinitary Logic and Admissible Sets", 2004], Corollary 1.2.2
-/

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable [Countable (Σ l, L.Relations l)]

open FirstOrder Structure Fin Ordinal

/-- For countable structures in a countable relational language, Lω₁ω-elementary
equivalence implies isomorphism.

This is a fundamental result in infinitary model theory: for countable structures,
satisfying the same countable infinitary sentences is as strong as being isomorphic.
The proof uses Scott sentences: since each countable structure has a Scott sentence
that characterizes it up to isomorphism, and Lω₁ω-equivalent structures satisfy the
same Scott sentences, they must be isomorphic. -/
theorem countable_LomegaEquiv_implies_iso
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N] :
    LomegaEquiv L M N → Nonempty (M ≃[L] N) := by
  sorry

/-- For countable structures in a countable relational language, L∞ω-elementary
equivalence implies isomorphism.

This follows from the Lω₁ω version since L∞ω-equivalence is stronger than
Lω₁ω-equivalence. -/
theorem countable_LinfEquiv_implies_iso
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N] :
    LinfEquiv L M N → Nonempty (M ≃[L] N) := by
  sorry

/-- For countable structures, potential isomorphism implies actual isomorphism.

This is a consequence of Karp's theorem and the countable corollary:
potential isomorphism ↔ L∞ω-equivalence → isomorphism for countable structures. -/
theorem countable_PotentialIso_implies_iso
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N] :
    Nonempty (PotentialIso L M N) → Nonempty (M ≃[L] N) := by
  intro hp
  apply countable_LinfEquiv_implies_iso
  exact karp_theorem.mp hp

/-- For countable structures, BFEquiv at all ordinals implies isomorphism. -/
theorem countable_BFEquiv_all_implies_iso
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N]
    (h : ∀ α, BFEquiv (L := L) α 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N)) :
    Nonempty (M ≃[L] N) := by
  apply countable_PotentialIso_implies_iso
  exact potentialIso_iff_BFEquiv_all.mpr h

end Language

end FirstOrder
