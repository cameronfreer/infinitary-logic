/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Scott.QuantifierRank
import InfinitaryLogic.Scott.Rank
import InfinitaryLogic.Karp.PotentialIso

/-!
# Scott Height and Canonical Scott Sentence

This file defines the Scott height of a structure (the ordinal at which its Scott
analysis stabilizes) and the canonical Scott sentence (the Scott formula at Scott height).

## Main Definitions

- `scottHeight`: The least ordinal where the Scott formulas stabilize for all tuples.
- `canonicalScottSentence`: The Scott formula at Scott height level for the empty tuple.
- `sr`: The supremum of element ranks (without +1), as opposed to `scottRank` (with +1).
- `AttainedScottRank`: Whether the supremum in `sr` is attained by some element.

## Main Results

- `canonicalScottSentence_iff_potentialIso`: The canonical Scott sentence characterizes
  potential isomorphism.
- `canonicalScottSentence_characterizes`: For countable structures, the canonical Scott
  sentence characterizes isomorphism.
- `scottHeight_le_scottRank`: Scott height is at most Scott rank.

## References

- [Keisler-Knight, "Barwise: Infinitary Logic and Admissible Sets", 2004], §1.3
- [Marker, "Lectures on Infinitary Model Theory", 2016]
-/

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable [Countable (Σ l, L.Relations l)]

open FirstOrder Structure Fin Ordinal

/-! ### Scott Height -/

/-- The Scott height of a structure M: the least ordinal at which the Scott formula
analysis stabilizes for all tuples simultaneously.

This is defined as the least ordinal α such that for all n and all tuples a : Fin n → M,
if a structure N satisfies scottFormula a α, then it also satisfies scottFormula a (α + 1),
and vice versa.

Equivalently, this is the least α where BFEquiv α n a b implies BFEquiv (α + 1) n a b
for all tuples.

Scott height is related to but may differ from Scott rank. We always have
scottHeight ≤ scottRank. -/
noncomputable def scottHeight (M : Type w) [L.Structure M] [Countable M] : Ordinal.{0} :=
  sInf {α : Ordinal.{0} | ∀ {n : ℕ} (a : Fin n → M)
    (N : Type w) [L.Structure N] [Countable N] (b : Fin n → N),
    BFEquiv (L := L) α n a b → BFEquiv (L := L) (Order.succ α) n a b}

/-- Scott height is less than ω₁ for countable structures. -/
theorem scottHeight_lt_omega1 (M : Type w) [L.Structure M] [Countable M] :
    scottHeight (L := L) M < Ordinal.omega 1 := by
  sorry

/-! ### Canonical Scott Sentence -/

/-- The canonical Scott sentence of a structure M, defined as the Scott formula at Scott
height level for the empty tuple.

This is the "optimal" Scott sentence in the sense that its quantifier rank is minimized
(among Scott formulas). It characterizes the structure up to potential isomorphism,
and for countable structures, up to isomorphism. -/
noncomputable def canonicalScottSentence (M : Type w) [L.Structure M] [Countable M] :
    L.Formulaω (Fin 0) :=
  scottFormula (L := L) (M := M) Fin.elim0 (scottHeight (L := L) M)

/-- The canonical Scott sentence characterizes potential isomorphism.

A structure N satisfies the canonical Scott sentence of M if and only if M and N are
potentially isomorphic. -/
theorem canonicalScottSentence_iff_potentialIso
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N] :
    (canonicalScottSentence (L := L) M).realize_as_sentence N ↔
    Nonempty (PotentialIso L M N) := by
  sorry

/-- For countable structures, the canonical Scott sentence characterizes isomorphism.

This combines `canonicalScottSentence_iff_potentialIso` with the fact that potential
isomorphism implies isomorphism for countable structures. -/
theorem canonicalScottSentence_characterizes
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N] :
    (canonicalScottSentence (L := L) M).realize_as_sentence N ↔
    Nonempty (M ≃[L] N) := by
  sorry

/-- The canonical Scott sentence is semantically equivalent to the standard Scott sentence.

Both characterize isomorphism for countable structures, so they have the same
realizations. Note: this is semantic equivalence, not syntactic equality. -/
theorem canonicalScottSentence_equiv_scottSentence
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N] :
    (canonicalScottSentence (L := L) M).realize_as_sentence N ↔
    (scottSentence (L := L) M).realize_as_sentence N := by
  rw [canonicalScottSentence_characterizes, scottSentence_characterizes]

/-! ### sr and SR -/

/-- The supremum of element ranks without the +1 adjustment.

This is denoted `sr(M)` in some references (e.g., Marker). Compare with `scottRank`
which is `⨆ m, elementRank m + 1` (denoted `SR(M)` or `α(M)`). -/
noncomputable def sr (M : Type w) [L.Structure M] [Countable M] : Ordinal.{0} :=
  ⨆ (m : M), elementRank (L := L) m

/-- sr ≤ scottRank always holds, since scottRank = ⨆ m, elementRank m + 1 ≥ ⨆ m, elementRank m. -/
theorem sr_le_scottRank (M : Type w) [L.Structure M] [Countable M] :
    sr (L := L) M ≤ scottRank (L := L) M := by
  sorry

/-- scottHeight ≤ scottRank.

The Scott height is at most the Scott rank because the Scott rank bounds the
element ranks, and the element ranks bound the stabilization levels. -/
theorem scottHeight_le_scottRank (M : Type w) [L.Structure M] [Countable M] :
    scottHeight (L := L) M ≤ scottRank (L := L) M := by
  sorry

/-! ### Attained Scott Rank -/

/-- A structure has attained Scott rank if some element achieves the supremum `sr`.

This is an important distinction in the theory of Scott rank: when the rank is
attained, the structure has a "witness" element of maximal complexity. -/
def AttainedScottRank (M : Type w) [L.Structure M] [Countable M] : Prop :=
  ∃ (m : M), elementRank (L := L) m = sr (L := L) M

/-- The quantifier rank of the canonical Scott sentence is bounded.

The canonical Scott sentence has quantifier rank ≤ scottHeight M + ω, which for
countable structures gives a bound below ω₁. -/
theorem canonicalScottSentence_qrank
    (M : Type w) [L.Structure M] [Countable M] :
    (canonicalScottSentence (L := L) M).qrank ≤
    scottHeight (L := L) M + Ordinal.omega0 := by
  sorry

end Language

end FirstOrder
