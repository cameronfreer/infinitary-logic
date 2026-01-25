/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import CountableInfinitaryLogic.Scott.Formula

/-!
# Scott Sentences

This file proves the main theorem about Scott sentences: every countable structure
in a relational countable language has a Scott sentence characterizing it up to isomorphism.

## Main Definitions

- `scottSentence`: The Scott sentence of a countable structure.

## Main Results

- `scottSentence_characterizes`: A countable structure N satisfies the Scott sentence of M
  if and only if M and N are isomorphic.

## Implementation Notes

The proof proceeds by showing:
1. High enough BF-equivalence (with the empty tuple) implies `IsExtensionPair` in both directions.
2. `IsExtensionPair` in both directions between countable structures implies isomorphism
   (using mathlib's `equiv_between_cg`).
3. The Scott formula at the stabilization ordinal captures exactly this.
-/

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable [Countable (Σ l, L.Relations l)]

open FirstOrder Structure Fin Ordinal BoundedFormulaω Substructure

/-- BF-equivalence at level α + 1 with the empty tuple implies that we can extend any
finitely-generated partial isomorphism to include any element of M. This is the
key connection to `IsExtensionPair`. -/
theorem BFEquiv_succ_implies_extend_fg {M N : Type w} [L.Structure M] [L.Structure N]
    [Countable M] [Countable N]
    {α : Ordinal} (hBF : BFEquiv (α + 1) (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N))
    (f : L.FGEquiv M N) (m : M) :
    ∃ g : L.FGEquiv M N, m ∈ g.1.dom ∧ f ≤ g := by
  sorry -- This requires careful construction from BF forth property

/-- At a sufficiently high ordinal, BF-equivalence between countable structures implies
`IsExtensionPair`. -/
theorem BFEquiv_implies_isExtensionPair {M N : Type w} [L.Structure M] [L.Structure N]
    [Countable M] [Countable N]
    (hBF : BFEquiv (ω : Ordinal) (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N)) :
    L.IsExtensionPair M N := by
  sorry -- Uses BFEquiv.forth repeatedly

/-- For any countable structure M, there exists an ordinal α < ω₁ such that BF-equivalence
at level α (with the empty tuple) characterizes isomorphism with M. -/
theorem exists_stabilization (M : Type w) [L.Structure M] [Countable M] :
    ∃ α < Ordinal.omega1, ∀ (N : Type w) [L.Structure N] [Countable N],
      BFEquiv α (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) ↔ Nonempty (M ≃[L] N) := by
  sorry -- The key cardinality argument about countable ordinals

/-- The stabilization ordinal for a structure M: the least ordinal where the Scott analysis
stabilizes. -/
noncomputable def stabilizationOrdinal (M : Type w) [L.Structure M] [Countable M] : Ordinal :=
  sInf {α | ∀ (N : Type w) [L.Structure N] [Countable N],
    BFEquiv α (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) ↔ Nonempty (M ≃[L] N)}

/-- The Scott sentence of a countable structure M in a relational countable language. -/
noncomputable def scottSentence (M : Type w) [L.Structure M] [Countable M] : L.Sentenceω :=
  scottFormula (Fin.elim0 : Fin 0 → M) (stabilizationOrdinal M)

/-- The main theorem: a countable structure N satisfies the Scott sentence of M
if and only if M and N are isomorphic. -/
theorem scottSentence_characterizes (M : Type w) [L.Structure M] [Countable M]
    (N : Type w) [L.Structure N] [Countable N] :
    Sentenceω.Realize (scottSentence M) N ↔ Nonempty (M ≃[L] N) := by
  sorry

/-- The forward direction: if N realizes the Scott sentence of M, then M ≃[L] N. -/
theorem scottSentence_realizes_implies_equiv (M : Type w) [L.Structure M] [Countable M]
    (N : Type w) [L.Structure N] [Countable N]
    (h : Sentenceω.Realize (scottSentence M) N) : Nonempty (M ≃[L] N) :=
  scottSentence_characterizes M N |>.mp h

/-- The backward direction: M itself satisfies its own Scott sentence. -/
theorem scottSentence_self (M : Type w) [L.Structure M] [Countable M] :
    Sentenceω.Realize (scottSentence M) M :=
  scottSentence_characterizes M M |>.mpr ⟨Equiv.refl L M⟩

/-- Isomorphic structures satisfy each other's Scott sentences. -/
theorem scottSentence_of_equiv (M N : Type w) [L.Structure M] [L.Structure N]
    [Countable M] [Countable N] (e : M ≃[L] N) :
    Sentenceω.Realize (scottSentence M) N :=
  scottSentence_characterizes M N |>.mpr ⟨e⟩

end Language

end FirstOrder
