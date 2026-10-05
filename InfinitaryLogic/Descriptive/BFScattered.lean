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
`K` has only countably many classes.  Such a `K` carries no Cantor antichain for isomorphism
(`not_hasCantorAntichainOn_of_bfScattered`, for every relational language), and, for countably
many relation symbols, it is thin: it contains no nonempty perfect set of pairwise
non-isomorphic codes (`isThinOn_of_bfScattered`).  The class `K` is arbitrary; no analyticity,
Borelness or isomorphism invariance of `K` is assumed.

## Main declarations

* `codeBFEquivSetoid L η`: `CodeBFEquiv η` as an equivalence relation on all codes.
* `BFScattered K`: every level `η < ω₁` has countably many classes on `K`; it passes to subsets
  (`BFScattered.mono`).
* `exists_forall_not_codeBFEquiv_of_analyticSet`: an analytic set of pairwise non-isomorphic
  codes is separated pairwise at one level `η < ω₁`.
* `not_hasCantorAntichainOn_of_bfScattered`: no Cantor antichain, with no countability of the
  language.
* `isThinOn_of_bfScattered`: thinness, for countably many relation symbols.
* `bfScattered_of_countable_bfObservations`: observation maps with countably many realized
  values at every level, whose equal values imply `CodeBFEquiv`, give `BFScattered`; with the
  two endpoints `not_hasCantorAntichainOn_of_countable_bfObservations` and
  `isThinOn_of_countable_bfObservations`.  These are adapters over `BFScattered`, not a new
  proof of the separation route.

The form for the models of a sentence, with the hypothesis read through `bfEquivSetoid φ η`, is
`Sentenceω.isThinOnNatModels_of_bfScattered` in `Descriptive/BFScatteredSentence.lean`, kept
apart so that this module does not import the counting theory.

## The proof

Let `f` be a continuous map from Cantor space into `K` sending distinct points to
non-isomorphic codes.

1. The range of `f` is analytic (a continuous image of the Polish space `ℕ → Bool`), so its
   off-diagonal, the pairs of distinct points of the range, is analytic
   (`MeasureTheory.AnalyticSet.offDiag`, in the Hausdorff space of codes), and it contains no
   isomorphic pair (`not_structureIso_of_mem_offDiag`).
2. Uniform back-and-forth separation (`exists_uniform_bfSeparation`) applied to that off-diagonal
   gives one level `η < ω₁` at which no two distinct points of the range are back-and-forth
   equivalent (`exists_forall_not_codeBFEquiv_of_analyticSet`).
3. Hence `x ↦ [f x]`, the class of `f x` in the quotient of `K` by the restriction of
   `codeBFEquivSetoid L η`, is injective.  That quotient is countable by hypothesis, while Cantor
   space is not.

Thinness follows: a perfect antichain in a complete metric space yields a Cantor antichain
(`IsThinOn.of_no_cantorAntichain`).

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
* **Countability of the language.**  `[Countable (Σ l, L.Relations l)]` is used once, in
  `isThinOn_of_bfScattered` (and passed on by its adapter
  `isThinOn_of_countable_bfObservations`), to equip the space of codes with a complete metric
  (it is Polish) so that a perfect antichain yields a Cantor antichain.  The Cantor-antichain
  theorem, the separation lemma, the setoid and `BFScattered` need no countability: analyticity
  of the off-diagonal needs only that the space of codes is Hausdorff, and
  `exists_uniform_bfSeparation` assumes no countability; nor do the observation bridge and its
  Cantor-antichain corollary.
* **Observations.**  The observation adapters use only that equal observations imply
  `CodeBFEquiv η` and that the realized values are countable: no measurable structure on the
  target, no invariance, no surjectivity, no countability of the whole target type.
* **No definability of `K`.**  The analytic set fed to the separation theorem is built from the
  Cantor antichain, not from `K`.

## References

* A. Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, draft, Chapter XII,
  §XII.1 (scattered sentences: countably many classes at every countable level).
* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156,
  Springer, 1995, §31.A (the boundedness theorem behind `exists_uniform_bfSeparation`).

The composition was offered for upstreaming by a consumer of this library.
-/

universe u v w'

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

/-- **`BFScattered` passes to subsets**: at each level the class map of `J` factors through that
of `K`, and equal classes in `K` mean `CodeBFEquiv η` of the underlying codes. -/
theorem BFScattered.mono {J K : Set (StructureSpace L)} (hK : BFScattered K) (hJK : J ⊆ K) :
    BFScattered J := fun η hη ↦
  have := hK η hη
  countable_quotient_of_countable_range _
    (fun x : J ↦ (Quotient.mk _ ⟨x.1, hJK x.2⟩ :
      Quotient ((codeBFEquivSetoid L η).comap (Subtype.val : K → StructureSpace L))))
    -- `Quotient.exact h` is the pulled-back relation on `K`, which unfolds to `CodeBFEquiv η`
    -- of the underlying codes, the relation pulled back to `J`
    (Set.to_countable _) fun _ _ h ↦ by have := Quotient.exact h; exact this

/-! ### Uniform separation of an analytic antichain -/

/-- **The off-diagonal of a pairwise non-isomorphic set of codes has no isomorphic pair.**  The
hypothesis is the antichain clause of `HasPerfectAntichainOn`. -/
theorem not_structureIso_of_mem_offDiag {P : Set (StructureSpace L)}
    (hP : ∀ x ∈ P, ∀ y ∈ P, (structureIsoSetoid L).r x y → x = y) :
    ∀ p ∈ P.offDiag, ¬ (structureIsoSetoid L).r p.1 p.2 :=
  fun _ hp hr ↦ hp.2.2 (hP _ hp.1 _ hp.2.1 hr)

omit [L.IsRelational] in
/-- The space of codes is Hausdorff for every language (a product of discrete spaces); with
countably many relation symbols this also follows from the Polish instance. -/
private theorem t2Space_structureSpace : T2Space (StructureSpace L) :=
  inferInstanceAs (T2Space (StructureSpaceOn L ℕ))

attribute [local instance] t2Space_structureSpace

/-- **One back-and-forth level separates an analytic antichain**: for an analytic set `P` of
pairwise non-isomorphic codes there is `η < ω₁` at which no two distinct points of `P` are
back-and-forth equivalent.  This is `exists_uniform_bfSeparation` for the off-diagonal of `P`,
and the level is the one it returns.  No countability of the relation symbols is assumed. -/
theorem exists_forall_not_codeBFEquiv_of_analyticSet {P : Set (StructureSpace L)}
    (hP : AnalyticSet P) (hanti : ∀ x ∈ P, ∀ y ∈ P, (structureIsoSetoid L).r x y → x = y) :
    ∃ η : Ordinal.{0}, η < Ordinal.omega 1 ∧
      ∀ x ∈ P, ∀ y ∈ P, x ≠ y → ¬ CodeBFEquiv η x y := by
  obtain ⟨η, hη, hsep⟩ :=
    exists_uniform_bfSeparation hP.offDiag (not_structureIso_of_mem_offDiag hanti)
  exact ⟨η, hη, fun x hx y hy hxy ↦ hsep (x, y) (mem_offDiag.mpr ⟨hx, hy, hxy⟩)⟩

/-! ### No Cantor antichain, and thinness -/

/-- Cantor space is uncountable. -/
private theorem not_countable_natBool : ¬ Countable (ℕ → Bool) := by
  rw [← Cardinal.mk_le_aleph0_iff, not_le]
  simp [Cardinal.aleph0_lt_continuum]

/-- **No Cantor antichain on a back-and-forth scattered set**, for every relational language:
the range of a Cantor antichain is analytic, so one level `η < ω₁` separates its points
(`exists_forall_not_codeBFEquiv_of_analyticSet`), and the class map at that level injects Cantor
space into the countable quotient of the restriction to `K`.  No countability of the relation
symbols and no definability of `K` is assumed. -/
theorem not_hasCantorAntichainOn_of_bfScattered {K : Set (StructureSpace L)}
    (hK : BFScattered K) : ¬ HasCantorAntichainOn (structureIsoSetoid L) K := by
  rintro ⟨f, hcont, hmem, hineq⟩
  -- `PolishSpace (ℕ → Bool)` does not synthesize; both parents do
  have : PolishSpace (ℕ → Bool) := PolishSpace.mk
  have hanti : ∀ x ∈ range f, ∀ y ∈ range f, (structureIsoSetoid L).r x y → x = y := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ h
    by_contra hne
    exact hineq a b (fun hab ↦ hne (congrArg f hab)) h
  obtain ⟨η, hη, hsep⟩ :=
    exists_forall_not_codeBFEquiv_of_analyticSet (analyticSet_range_of_polishSpace hcont) hanti
  -- the class map at level `η` is injective on the Cantor copy
  have := hK η hη
  refine not_countable_natBool (Function.Injective.countable
    (f := fun x ↦ (⟦⟨f x, hmem x⟩⟧ :
      Quotient ((codeBFEquivSetoid L η).comap (Subtype.val : K → StructureSpace L)))) ?_)
  intro x y hxy
  by_contra hne
  have hfne : f x ≠ f y := fun h ↦ hineq x y hne (h ▸ (structureIsoSetoid L).refl _)
  exact hsep _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hfne (Quotient.exact hxy)

/-- **Thinness from countably many back-and-forth classes at every level**: with countably many
relation symbols, a back-and-forth scattered set of codes contains no nonempty perfect set of
pairwise non-isomorphic codes.  Countability is used only to give the space of codes a complete
metric, in which a perfect antichain yields a Cantor antichain. -/
theorem isThinOn_of_bfScattered [Countable (Σ l, L.Relations l)] {K : Set (StructureSpace L)}
    (hK : BFScattered K) : IsThinOn (structureIsoSetoid L) K := by
  -- a complete metric compatible with the topology; the statement is unaffected
  let := TopologicalSpace.upgradeIsCompletelyMetrizable (StructureSpace L)
  exact IsThinOn.of_no_cantorAntichain (not_hasCantorAntichainOn_of_bfScattered hK)

/-! ### Countable observations -/

/-- **Countably many observed values at every level give back-and-forth scatteredness.**  For
each `η < ω₁`, let `obs η : C → Q η` be an observation whose realized values on `C` form a
countable set, and suppose that equal observations at level `η` imply `CodeBFEquiv η`.  Then `C`
is back-and-forth scattered.

Only the forward implication (equal observations imply back-and-forth equivalence) is used; the
converse is not assumed, so `obs η` need not descend to the back-and-forth classes.  At each
level this is `countable_quotient_of_countable_range` for the restriction of
`codeBFEquivSetoid L η` to `C`: the countable set of realized values surjects onto its classes,
each class being hit by the observation of any of its members.

Hypotheses deliberately absent:
* No countability of the relation symbols.
* No measurability or analyticity of `C`.
* No measurable structure on `Q η`, and no measurability of `obs η`.
* No invariance of observations under isomorphism.
* No countability of the whole target type: only its realized image is countable.
* No surjectivity, nonemptiness, sentence recovery, or orbit definability.
* No assertion that equality of observations is equivalent to BF equivalence: only the
  displayed forward implication is needed.

The target universe `w'` is independent of the universes of the language. -/
theorem bfScattered_of_countable_bfObservations (C : Set (StructureSpace L))
    {Q : Ordinal.{0} → Type w'} (obs : ∀ η, C → Q η)
    (hc : ∀ η < Ordinal.omega 1, (Set.range (obs η)).Countable)
    (hobs : ∀ η < Ordinal.omega 1, ∀ c d : C, obs η c = obs η d → CodeBFEquiv η c.1 d.1) :
    BFScattered C := fun η hη ↦
  countable_quotient_of_countable_range _ (obs η) (hc η hη) (hobs η hη)

/-- **No Cantor antichain from countable back-and-forth observations**, for every relational
language: `not_hasCantorAntichainOn_of_bfScattered` through
`bfScattered_of_countable_bfObservations`.  The hypotheses on `obs` are those of the bridge, and
none of the hypotheses listed there as absent is assumed; in particular no countability of the
relation symbols. -/
theorem not_hasCantorAntichainOn_of_countable_bfObservations (C : Set (StructureSpace L))
    {Q : Ordinal.{0} → Type w'} (obs : ∀ η, C → Q η)
    (hc : ∀ η < Ordinal.omega 1, (Set.range (obs η)).Countable)
    (hobs : ∀ η < Ordinal.omega 1, ∀ c d : C, obs η c = obs η d → CodeBFEquiv η c.1 d.1) :
    ¬ HasCantorAntichainOn (structureIsoSetoid L) C :=
  not_hasCantorAntichainOn_of_bfScattered (bfScattered_of_countable_bfObservations C obs hc hobs)

/-- **Thinness from countable back-and-forth observations**: `isThinOn_of_bfScattered` through
`bfScattered_of_countable_bfObservations`.  Countability of the relation symbols enters only
here, as in `isThinOn_of_bfScattered`: it makes the space of codes Polish, so that a perfect
antichain yields a Cantor antichain.  The bridge and the Cantor-antichain conclusion need no
countability. -/
theorem isThinOn_of_countable_bfObservations [Countable (Σ l, L.Relations l)]
    (C : Set (StructureSpace L)) {Q : Ordinal.{0} → Type w'} (obs : ∀ η, C → Q η)
    (hc : ∀ η < Ordinal.omega 1, (Set.range (obs η)).Countable)
    (hobs : ∀ η < Ordinal.omega 1, ∀ c d : C, obs η c = obs η d → CodeBFEquiv η c.1 d.1) :
    IsThinOn (structureIsoSetoid L) C :=
  isThinOn_of_bfScattered (bfScattered_of_countable_bfObservations C obs hc hobs)

end FirstOrder.Language
