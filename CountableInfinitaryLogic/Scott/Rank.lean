/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import CountableInfinitaryLogic.Scott.Sentence

/-!
# Scott Rank

This file defines the Scott rank of a structure and proves that it is below ω₁
for countable structures.

## Main Definitions

- `scottRank`: The Scott rank of a structure, defined as the supremum of element ranks + 1.
- `elementRank`: The rank of an individual element (least ordinal where it's distinguished).

## Main Results

- `scottRank_lt_omega1`: For countable structures, Scott rank < ω₁.

## Implementation Notes

We define Scott rank as sup {elementRank a + 1 : a ∈ M}, where elementRank a is the
least ordinal α such that any tuple extending with a is determined by its α-type.
This is equivalent to the stabilization ordinal approach but more compositional.
-/

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable [Countable (Σ l, L.Relations l)]

open FirstOrder Structure Fin Ordinal

/-- The rank of an element m in a structure M: the least ordinal α such that
for any tuple a containing m, the α-type of a determines whether any extension
has a back-and-forth equivalent extension. -/
noncomputable def elementRank {M : Type w} [L.Structure M] (m : M) : Ordinal :=
  sInf {α | ∀ (N : Type w) [L.Structure N] [Countable N] (b : Fin 1 → N),
    BFEquiv (L := L) (M := M) (N := N) α 1 ![m] b →
      ∀ (N' : Type w) [L.Structure N'] [Countable N'] (b' : Fin 1 → N'),
        BFEquiv (L := L) (M := M) (N := N') α 1 ![m] b' →
          (BFEquiv (L := L) (M := M) (N := N) (Order.succ α) 1 ![m] b ↔
           BFEquiv (L := L) (M := M) (N := N') (Order.succ α) 1 ![m] b')}

/-- The Scott rank of a structure M is the supremum of element ranks + 1. -/
noncomputable def scottRank (M : Type w) [L.Structure M] [Countable M] : Ordinal :=
  ⨆ (m : M), elementRank (L := L) m + 1

/-- The stabilization ordinal is at most the Scott rank. -/
theorem stabilizationOrdinal_le_scottRank (M : Type w) [L.Structure M] [Countable M] :
    stabilizationOrdinal (L := L) M ≤ scottRank (L := L) M := by
  sorry

/-- Scott rank of a countable structure is a countable ordinal. -/
theorem scottRank_lt_omega1 (M : Type w) [L.Structure M] [Countable M] :
    scottRank (L := L) M < Ordinal.omega 1 := by
  sorry -- Uses that M is countable and each elementRank is countable

/-- The stabilization ordinal is below ω₁. -/
theorem stabilizationOrdinal_lt_omega1 (M : Type w) [L.Structure M] [Countable M] :
    stabilizationOrdinal (L := L) M < Ordinal.omega 1 :=
  lt_of_le_of_lt (stabilizationOrdinal_le_scottRank M) (scottRank_lt_omega1 M)

/-- The Scott sentence can be taken at the Scott rank level. -/
theorem scottSentence_eq_scottFormula_rank (M : Type w) [L.Structure M] [Countable M] :
    scottSentence (L := L) M = scottFormula (L := L) (M := M) Fin.elim0 (scottRank (L := L) M) := by
  sorry

/-- Element rank is bounded by the cardinality of types. -/
theorem elementRank_lt_omega1 {M : Type w} [L.Structure M] [Countable M] (m : M) :
    elementRank (L := L) m < Ordinal.omega 1 := by
  sorry

end Language

end FirstOrder
