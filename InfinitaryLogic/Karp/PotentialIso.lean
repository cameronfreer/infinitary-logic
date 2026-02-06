/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Linf.Theory
import InfinitaryLogic.Scott.BackAndForth

/-!
# Potential Isomorphism

This file defines potential isomorphism between structures and connects it to
back-and-forth equivalence at all ordinal levels.

## Main Definitions

- `PotentialIso`: A potential isomorphism between structures M and N is a family of
  finite partial maps containing the empty map and closed under extension in both directions.

## Main Results

- `potentialIso_iff_BFEquiv_all`: Potential isomorphism is equivalent to BF-equivalence
  at all ordinal levels (for the empty tuple).

## References

- [Keisler-Knight, "Barwise: Infinitary Logic and Admissible Sets", 2004], Theorem 1.2.1
-/

universe u v w w'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]

open FirstOrder Structure Fin Ordinal

/-- A potential isomorphism between structures M and N is a family of finite partial
maps (given as pairs of compatible tuples) that contains the empty map and is closed
under extension in both directions.

This is the model-theoretic notion corresponding to "back-and-forth system" or
"winning strategy in the infinite EF game." -/
structure PotentialIso (L : Language.{u, v}) [L.IsRelational]
    (M : Type w) (N : Type w') [L.Structure M] [L.Structure N] where
  /-- The family of partial maps, represented as pairs of tuples of equal length. -/
  family : Set (Σ n : ℕ, (Fin n → M) × (Fin n → N))
  /-- The family contains the empty map. -/
  empty_mem : ⟨0, Fin.elim0, Fin.elim0⟩ ∈ family
  /-- Each pair in the family preserves atomic type. -/
  compatible : ∀ p ∈ family, SameAtomicType (L := L) p.2.1 p.2.2
  /-- Forth: for any pair and any element of M, there's an extension in the family. -/
  forth : ∀ p ∈ family, ∀ m : M, ∃ n' : N,
    ⟨p.1 + 1, Fin.snoc p.2.1 m, Fin.snoc p.2.2 n'⟩ ∈ family
  /-- Back: for any pair and any element of N, there's an extension in the family. -/
  back : ∀ p ∈ family, ∀ n' : N, ∃ m : M,
    ⟨p.1 + 1, Fin.snoc p.2.1 m, Fin.snoc p.2.2 n'⟩ ∈ family

namespace PotentialIso

variable {M : Type w} [L.Structure M]
variable {N : Type w'} [L.Structure N]

/-- The trivial potential isomorphism from M to itself via the identity. -/
noncomputable def refl (M : Type w) [L.Structure M] : PotentialIso L M M where
  family := { p | SameAtomicType (L := L) p.2.1 p.2.2 ∧ p.2.1 = p.2.2 }
  empty_mem := by simp only [Set.mem_setOf_eq]; exact ⟨SameAtomicType.refl _, trivial⟩
  compatible := fun p hp => hp.1
  forth := fun p hp m => by
    simp only [Set.mem_setOf_eq] at hp ⊢
    use m
    constructor
    · simp only [hp.2]
      exact SameAtomicType.refl _
    · simp only [hp.2]
  back := fun p hp n' => by
    simp only [Set.mem_setOf_eq] at hp ⊢
    use n'
    constructor
    · simp only [hp.2]
      exact SameAtomicType.refl _
    · simp only [hp.2]

/-- Potential isomorphism is symmetric. -/
noncomputable def symm (p : PotentialIso L M N) : PotentialIso L N M where
  family := { q | ⟨q.1, q.2.2, q.2.1⟩ ∈ p.family }
  empty_mem := by
    simp only [Set.mem_setOf_eq]
    exact p.empty_mem
  compatible := fun q hq => by
    simp only [Set.mem_setOf_eq] at hq
    exact (p.compatible ⟨q.1, q.2.2, q.2.1⟩ hq).symm
  forth := fun ⟨n, b, a⟩ hq n' => by
    simp only [Set.mem_setOf_eq] at hq ⊢
    obtain ⟨m, hm⟩ := p.back ⟨n, a, b⟩ hq n'
    exact ⟨m, hm⟩
  back := fun ⟨n, b, a⟩ hq m => by
    simp only [Set.mem_setOf_eq] at hq ⊢
    obtain ⟨n', hn'⟩ := p.forth ⟨n, a, b⟩ hq m
    exact ⟨n', hn'⟩

end PotentialIso

/-- Given a potential isomorphism, BFEquiv holds at every ordinal level for any pair
in the family. This is the key inductive step for the (→) direction of the
potential isomorphism characterization.

The proof proceeds by ordinal induction: the zero case uses atomic type preservation,
the successor case uses the forth/back extension properties, and the limit case
follows from the induction hypothesis. -/
theorem potentialIso_family_BFEquiv [Countable (Σ l, L.Relations l)]
    {M : Type w} [L.Structure M]
    {N : Type w} [L.Structure N]
    (P : PotentialIso L M N) (α : Ordinal)
    {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (hab : ⟨n, a, b⟩ ∈ P.family) : BFEquiv (L := L) α n a b := by
  induction α using Ordinal.limitRecOn generalizing n a b with
  | zero =>
    exact (BFEquiv.zero a b).mpr (P.compatible _ hab)
  | succ β ih =>
    rw [BFEquiv.succ]
    refine ⟨ih hab, ?_, ?_⟩
    · intro m
      obtain ⟨n', hn'⟩ := P.forth _ hab m
      exact ⟨n', ih hn'⟩
    · intro n'
      obtain ⟨m, hm⟩ := P.back _ hab n'
      exact ⟨m, ih hm⟩
  | limit β hβ ih =>
    rw [BFEquiv.limit β hβ]
    exact fun γ hγ => ih γ hγ hab

/-- A potential isomorphism implies BF-equivalence at all ordinals for the empty tuple. -/
theorem PotentialIso.implies_BFEquiv_all [Countable (Σ l, L.Relations l)]
    {M : Type w} [L.Structure M]
    {N : Type w} [L.Structure N]
    (P : PotentialIso L M N) (α : Ordinal) :
    BFEquiv (L := L) α 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) :=
  potentialIso_family_BFEquiv P α P.empty_mem

/-- BF-equivalence at all ordinals implies potential isomorphism.

TODO: Requires quantifier swap argument — a decreasing transfinite chain of nonempty
finite subsets must stabilize. -/
theorem BFEquiv_all_implies_potentialIso [Countable (Σ l, L.Relations l)]
    {M : Type w} [L.Structure M]
    {N : Type w} [L.Structure N]
    (hBF : ∀ α : Ordinal, BFEquiv (L := L) α 0
      (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N)) :
    Nonempty (PotentialIso L M N) := by
  sorry

/-- A potential isomorphism exists if and only if BFEquiv holds at all ordinals
for the empty tuple. This is the main characterization theorem for potential isomorphism.

The (→) direction is fully proved in `PotentialIso.implies_BFEquiv_all`.
The (←) direction (`BFEquiv_all_implies_potentialIso`) requires a quantifier swap
argument and remains sorry. -/
theorem potentialIso_iff_BFEquiv_all [Countable (Σ l, L.Relations l)]
    {M : Type w} [L.Structure M]
    {N : Type w} [L.Structure N] :
    Nonempty (PotentialIso L M N) ↔
    ∀ α : Ordinal, BFEquiv (L := L) α 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) :=
  ⟨fun ⟨P⟩ α => P.implies_BFEquiv_all α, BFEquiv_all_implies_potentialIso⟩

end Language

end FirstOrder
