/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.BFSeparation

/-!
# Thinness from countably many back-and-forth classes at every level

A set `K` of codes of countable relational structures is **back-and-forth scattered**
(`BFScattered K`) when, for every countable level `η < ω₁`, the restriction of `CodeBFEquiv η` to
`K` has only countably many classes.  Such a `K` is thin: it contains no nonempty perfect set of
pairwise non-isomorphic codes (`isThinOn_of_bfScattered`), and so it carries no Cantor antichain
for isomorphism (`not_hasCantorAntichainOn_of_bfScattered`).  The class `K` is arbitrary; no
analyticity, Borelness or isomorphism invariance of `K` is assumed.

## Main declarations

* `codeBFEquivSetoid L η`: `CodeBFEquiv η` as an equivalence relation on all codes.
* `BFScattered K`: every level `η < ω₁` has countably many classes on `K`.
* `exists_forall_not_codeBFEquiv_of_isClosed`: a closed set of pairwise non-isomorphic codes is
  separated pairwise at one level `η < ω₁`.
* `not_countable_of_perfect`: a nonempty perfect set of codes is uncountable.
* `isThinOn_of_bfScattered`, `not_hasCantorAntichainOn_of_bfScattered`: the thinness theorem
  and its Cantor-antichain form.

The form for the models of a sentence, with the hypothesis read through `bfEquivSetoid φ η`, is
`isThinOnNatModels_of_bfScattered` in `Descriptive/BFScatteredSentence.lean`, kept apart so that
this module does not import the counting theory.

## The proof

Let `P ⊆ K` be nonempty, perfect, and pairwise non-isomorphic.

1. The pairs of distinct points of `P` form the off-diagonal `P.offDiag`, which is analytic
   because `P` is closed (`MeasureTheory.analyticSet_offDiag`), and which contains no isomorphic
   pair (`offDiag_noniso`).
2. Uniform back-and-forth separation (`exists_uniform_bfSeparation`) applied to `P.offDiag`
   gives one level `η < ω₁` at which no two distinct points of `P` are back-and-forth
   equivalent.
3. Hence the class map of `codeBFEquivSetoid L η` is injective on `P`.  Its image lies among the
   classes met by `K`, which correspond to the classes of the restriction to `K` by the second
   isomorphism theorem (`Setoid.comapQuotientEquiv`); these are countable by hypothesis, so `P`
   is countable.
4. A nonempty perfect set of codes is uncountable (`not_countable_of_perfect`, from
   `Perfect.mk_eq_continuum`), a contradiction.

## Interpretation choices

* **Classes, not codes.**  The hypothesis counts the classes of the restriction of
  `CodeBFEquiv η` to `K` (the quotient of the subtype `K` by the pulled-back relation).  A single
  class can contain uncountably many codes, so this is weaker than countability of `K`.
* **Equivalence convention.**  The level-`η` relation is this library's `CodeBFEquiv η`:
  back-and-forth equivalence of the empty tuples, with single-element extension steps.  No
  comparison with other hierarchies of infinitary equivalence is made or used.
* **Levels.**  The separating level is exactly the one returned by
  `exists_uniform_bfSeparation`: an `Ordinal.{0}` below `Ordinal.omega 1`, with no lift and no
  offset.
* **Countability of the language.**  `[Countable (Σ l, L.Relations l)]` is used only through the
  Polish structure of the space of codes: for the analyticity of the off-diagonal (step 1) and
  for the uncountability of nonempty perfect sets (step 4).  The setoid, the definition of
  `BFScattered`, and `offDiag_noniso` need no countability.
* **No definability of `K`.**  The analytic set fed to the separation theorem is the off-diagonal
  of the closed set `P`, not anything built from `K`.

## References

* A. Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, draft, §XII.1 (scattered
  sentences: countably many classes at every countable level).
* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156,
  Springer, 1995, §31.A (the boundedness theorem behind `exists_uniform_bfSeparation`).

The composition was offered for upstreaming by a consumer of this library.
-/

universe u v

namespace FirstOrder.Language

open Cardinal Set MeasureTheory

variable {L : Language.{u, v}} [L.IsRelational]

/-! ### Back-and-forth equivalence of codes as a setoid -/

variable (L) in
/-- **Back-and-forth equivalence at level `η`** on all codes: `CodeBFEquiv η`, an equivalence
relation by reflexivity, symmetry and transitivity of `BFEquiv`. -/
def codeBFEquivSetoid (η : Ordinal.{0}) : Setoid (StructureSpace L) where
  r := CodeBFEquiv η
  iseqv :=
    { refl := fun c ↦ @BFEquiv.refl L ℕ c.toStructure 0 η Fin.elim0
      symm := fun {c d} h ↦ @BFEquiv.symm L ℕ c.toStructure ℕ d.toStructure 0 η
        Fin.elim0 Fin.elim0 h
      trans := fun {c d e} h₁ h₂ ↦ @BFEquiv.trans L ℕ c.toStructure ℕ d.toStructure
        ℕ e.toStructure (n := 0) (α := η) (a := Fin.elim0) (b := Fin.elim0) (c := Fin.elim0)
        h₁ h₂ }

/-- Membership in `codeBFEquivSetoid L η` is `CodeBFEquiv η`. -/
theorem codeBFEquivSetoid_r_iff {η : Ordinal.{0}} {c d : StructureSpace L} :
    (codeBFEquivSetoid L η).r c d ↔ CodeBFEquiv η c d := Iff.rfl

/-- `K` is **back-and-forth scattered**: for every level `η < ω₁`, the restriction of
`CodeBFEquiv η` to `K` has countably many classes.  The count is of classes of the restricted
relation, not of codes; the relation is this library's `CodeBFEquiv η` (single-element
back-and-forth steps from the empty tuples), and no comparison with other hierarchies of
infinitary equivalence is made. -/
def BFScattered (K : Set (StructureSpace L)) : Prop :=
  ∀ η : Ordinal.{0}, η < Ordinal.omega 1 →
    Countable (Quotient ((codeBFEquivSetoid L η).comap (Subtype.val : K → StructureSpace L)))

/-! ### The off-diagonal of a pairwise non-isomorphic set -/

/-- **The off-diagonal of a pairwise non-isomorphic set of codes has no isomorphic pair.**  The
hypothesis is the antichain clause of `HasPerfectAntichainOn`. -/
theorem offDiag_noniso {P : Set (StructureSpace L)}
    (hP : ∀ x ∈ P, ∀ y ∈ P, (structureIsoSetoid L).r x y → x = y) :
    ∀ p ∈ P.offDiag, ¬ (structureIsoSetoid L).r p.1 p.2 :=
  fun _ hp hr ↦ hp.2.2 (hP _ hp.1 _ hp.2.1 hr)

/-! ### Thinness -/

variable [Countable (Σ l, L.Relations l)]

omit [L.IsRelational] in
/-- **A nonempty perfect set of codes is uncountable**: it has the cardinality of the continuum
(`Perfect.mk_eq_continuum`, for a complete metric inducing the Polish topology of the codes). -/
theorem not_countable_of_perfect {P : Set (StructureSpace L)} (hperf : Perfect P)
    (hne : P.Nonempty) : ¬ P.Countable := by
  -- a complete metric compatible with the topology; `hperf` is unaffected
  let := TopologicalSpace.upgradeIsCompletelyMetrizable (StructureSpace L)
  rw [← le_aleph0_iff_set_countable, hperf.mk_eq_continuum hne, not_le]
  exact aleph0_lt_continuum

/-- **One back-and-forth level separates a closed antichain**: for a closed set `P` of pairwise
non-isomorphic codes there is `η < ω₁` at which no two distinct points of `P` are back-and-forth
equivalent.  This is `exists_uniform_bfSeparation` for the off-diagonal of `P`, and the level is
the one it returns. -/
theorem exists_forall_not_codeBFEquiv_of_isClosed {P : Set (StructureSpace L)}
    (hP : IsClosed P) (hanti : ∀ x ∈ P, ∀ y ∈ P, (structureIsoSetoid L).r x y → x = y) :
    ∃ η : Ordinal.{0}, η < Ordinal.omega 1 ∧
      ∀ x ∈ P, ∀ y ∈ P, x ≠ y → ¬ CodeBFEquiv η x y := by
  obtain ⟨η, hη, hsep⟩ :=
    exists_uniform_bfSeparation (analyticSet_offDiag hP) (offDiag_noniso hanti)
  exact ⟨η, hη, fun x hx y hy hxy ↦ hsep (x, y) (mem_offDiag.mpr ⟨hx, hy, hxy⟩)⟩

/-- **Thinness from countably many back-and-forth classes at every level**: a back-and-forth
scattered set of codes contains no nonempty perfect set of pairwise non-isomorphic codes.  No
definability of `K` is assumed. -/
theorem isThinOn_of_bfScattered {K : Set (StructureSpace L)} (hK : BFScattered K) :
    IsThinOn (structureIsoSetoid L) K := by
  rintro ⟨P, hperf, hne, hPK, hanti⟩
  obtain ⟨η, hη, hsep⟩ := exists_forall_not_codeBFEquiv_of_isClosed hperf.closed hanti
  -- the classes met by `K` are the classes of the restriction (second isomorphism theorem)
  have hcount := (Setoid.comapQuotientEquiv (Subtype.val : K → StructureSpace L)
    (codeBFEquivSetoid L η)).symm.countable_iff.mpr (hK η hη)
  rw [countable_coe_iff, range_comp, Subtype.range_coe] at hcount
  refine not_countable_of_perfect hperf hne
    (MapsTo.countable_of_injOn (fun x hx ↦ mem_image_of_mem _ (hPK hx))
      (fun x hx y hy hxy ↦ ?_) hcount)
  by_contra hne
  exact hsep x hx y hy hne (Quotient.exact hxy)

/-- **No Cantor antichain on a back-and-forth scattered set**: the Cantor-antichain form of
`isThinOn_of_bfScattered`, through `IsThinOn.no_cantorAntichain`. -/
theorem not_hasCantorAntichainOn_of_bfScattered {K : Set (StructureSpace L)}
    (hK : BFScattered K) : ¬ HasCantorAntichainOn (structureIsoSetoid L) K :=
  (isThinOn_of_bfScattered hK).no_cantorAntichain

end FirstOrder.Language
