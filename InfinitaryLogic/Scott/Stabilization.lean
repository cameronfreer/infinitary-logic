/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Scott.BackAndForth
import Mathlib.SetTheory.Ordinal.Family

/-!
# The back-and-forth stabilization ordinal

The back-and-forth hierarchy of any pair of structures collapses at a set-sized ordinal, with
no countability hypothesis anywhere: `bfStabilizationOrdinal L M N` is the supremum, over the
triples that fail somewhere, of their least failure level, so equivalence at that one ordinal
already implies equivalence at every ordinal
(`bfEquiv_bfStabilizationOrdinal_iff_all`).

The argument is purely cardinal: each failing triple has a least failure level by well-ordering
of the ordinals (`csInf_mem`), and the family of triples is small, so those least levels are
bounded (`Ordinal.bddAbove_of_small`). Nothing about the language or the structures enters.

## Relation to `ModelTheory/ArbitraryStabilization.lean`

That file solves a different problem and its results are not comparable to these. It transfers
stabilization *from a countable source to arbitrary targets*, upgrading `BFEquiv α` to
`BFEquiv (succ α)` at a level supplied externally (`StabilizesCompletely`, itself obtained from
the countable refinement hypothesis), and it pays for arbitrary targets with the fragment
Löwenheim–Skolem machinery. Here there is no source/target asymmetry, no fragment machinery and
no countability: the collapse level is produced outright from the two structures. The price is
that the level is a supremum with no bound better than smallness — in particular this does not
give the `< ω₁` bound that Scott rank needs for countable structures, which remains the business
of the refinement-counting route.

## Main definitions

- `bfStabilizationOrdinal`: the level at which the hierarchy between two structures collapses.

## Main results

- `bfEquiv_bfStabilizationOrdinal_iff_all`: equivalence at the stabilization ordinal is
  equivalence at every ordinal.
- `bfEquiv_bfStabilizationOrdinal_succ`: the self-stability form, propagating level-`bfStab`
  equivalence of two tuples of one structure to the successor level.
-/

universe u v uι w w'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable {M : Type w} [L.Structure M]
variable {N : Type w'} [L.Structure N]

open FirstOrder Structure Fin Ordinal

variable (L M N) in
/-- The stabilization ordinal of the back-and-forth hierarchy between `M` and `N`: the
supremum, over all triples that fail somewhere, of their least failure level. -/
noncomputable def bfStabilizationOrdinal
    [Small.{uι} ((n : ℕ) × ((Fin n → M) × (Fin n → N)))] : Ordinal.{uι} :=
  ⨆ x : {x : (n : ℕ) × ((Fin n → M) × (Fin n → N)) //
      ∃ α : Ordinal.{uι}, ¬BFEquiv (L := L) α x.1 x.2.1 x.2.2},
    sInf {α : Ordinal.{uι} | ¬BFEquiv (L := L) α x.1.1 x.1.2.1 x.1.2.2}

omit [L.IsRelational] in
/-- **Stabilization**: back-and-forth equivalence at the stabilization level already implies
equivalence at every level. The equivalence hierarchy of an arbitrary pair of structures
collapses at a set-sized ordinal. -/
theorem bfEquiv_bfStabilizationOrdinal_iff_all
    [Small.{uι} ((n : ℕ) × ((Fin n → M) × (Fin n → N)))]
    {n : ℕ} {a : Fin n → M} {b : Fin n → N} :
    BFEquiv (L := L) (bfStabilizationOrdinal.{u, v, uι} L M N) n a b ↔
      ∀ β : Ordinal.{uι}, BFEquiv (L := L) β n a b := by
  constructor
  · intro h β
    by_contra hβ
    have hne : {α : Ordinal.{uι} | ¬BFEquiv (L := L) α n a b}.Nonempty := ⟨β, hβ⟩
    have hfail : ¬BFEquiv (L := L) (sInf {α : Ordinal.{uι} | ¬BFEquiv (L := L) α n a b})
        n a b := csInf_mem hne
    have hle : sInf {α : Ordinal.{uι} | ¬BFEquiv (L := L) α n a b} ≤
        bfStabilizationOrdinal.{u, v, uι} L M N :=
      le_ciSup (f := fun x : {x : (n : ℕ) × ((Fin n → M) × (Fin n → N)) //
          ∃ α : Ordinal.{uι}, ¬BFEquiv (L := L) α x.1 x.2.1 x.2.2} =>
        sInf {α : Ordinal.{uι} | ¬BFEquiv (L := L) α x.1.1 x.1.2.1 x.1.2.2})
        Ordinal.bddAbove_of_small ⟨⟨n, a, b⟩, β, hβ⟩
    exact hfail (BFEquiv.monotone hle h)
  · intro h
    exact h _

omit [L.IsRelational] in
/-- Self-stability of `M` at its own stabilization ordinal: level-`bfStabilizationOrdinal`
equivalence of two `M`-tuples propagates to the successor level. This is the form the backward
direction of a Scott sentence consumes. -/
theorem bfEquiv_bfStabilizationOrdinal_succ
    [Small.{uι} ((n : ℕ) × ((Fin n → M) × (Fin n → M)))]
    {n : ℕ} {a a' : Fin n → M}
    (h : BFEquiv (L := L) (bfStabilizationOrdinal.{u, v, uι} L M M) n a a') :
    BFEquiv (L := L) (bfStabilizationOrdinal.{u, v, uι} L M M + 1) n a a' :=
  (bfEquiv_bfStabilizationOrdinal_iff_all.mp h) _

end Language

end FirstOrder
