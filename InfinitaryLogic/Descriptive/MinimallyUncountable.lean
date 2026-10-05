/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.BFConcentration
import InfinitaryLogic.Descriptive.ModelsOfGDelta
import InfinitaryLogic.Lomega1omega.Theory
import InfinitaryLogic.Scott.Formula

/-!
# Minimally uncountable classes of codes, and cuts by sentences

This module is the contract-free half (no isolating rank) of an analogue of the minimality
notion of [Mon, §XII.2] (Def XII.4).  A set `K` of codes of countable relational structures
is **minimally uncountable** (`MinimallyUncountableOn K`) when it meets uncountably many
isomorphism classes, but every **sentence cut** of `K`, the pair `K ∩ ModelsOf θ` /
`K \ ModelsOf θ` for a sentence `θ`, has a side meeting only countably many.  For a sentence `Θ`,
`Sentenceω.MinimallyUncountable Θ` is the case `K = ModelsOf Θ`, and
`Sentenceω.minimallyUncountable_iff_inf` restates it with the literal sentences `Θ ⊓ θ` and
`Θ ⊓ θ.not`.

The cut ranges over sentences, not over arbitrary isomorphism-invariant subsets: splitting by
arbitrary invariant subsets would make the rank-parametric form unsatisfiable (if an
isomorphism-invariant `ρ` takes values below `ω₁` and is unbounded on `K`, some set of its values
cuts `K` into two unbounded sides; see the regression guard).

## Main declarations

* `BoundedRankOn ρ K`, `UnboundedRankOn ρ K`: for a map `ρ : StructureSpace L → Ordinal.{0}`,
  some `β < ω₁` exceeds every value of `ρ` on `K`, or every threshold `β < ω₁` is met or
  exceeded by the value of some member of `K` (the shape of [Mon, Def XII.1]; the values
  themselves need not be below `ω₁`); with `mono`, the empty class, and countable unions.
  These definitions take an arbitrary `ρ`, with no isolating-rank contract, and no relational
  instance.
* Sentence cuts are read through `modelsOf_inf` and `modelsOf_inf_not`
  (`Descriptive/ModelsOfGDelta.lean`): `ModelsOf (Θ ⊓ θ) = ModelsOf Θ ∩ ModelsOf θ` and
  `ModelsOf (Θ ⊓ θ.not) = ModelsOf Θ \ ModelsOf θ`.
* `MinimallyUncountableOn K`, `Sentenceω.MinimallyUncountable Θ`, and the literal form
  `Sentenceω.minimallyUncountable_iff_inf`.
* `modelsOf_scottSentenceAt` (an analogue of [Mon, Lemma XII.5] on codes): for `α < ω₁`, the
  codes of the models of `scottSentenceAt` of the structure decoded from `c`, at level `α`, are
  exactly the codes `CodeBFEquiv α`-equivalent to `c`.  Every back-and-forth class is therefore
  a sentence cut (`MinimallyUncountableOn.countable_bfClass_or_compl`).
* `exists_bfClass_compl_of_sentence_cuts`: for any notion of smallness closed under subsets and
  countable unions, if `K` is not small but every sentence cut has a small side, then at a level
  `α < ω₁` where `K` has countably many `CodeBFEquiv α`-classes, one class is not small and its
  complement in `K` is small.  `MinimallyUncountableOn.exists_bfClass_compl_countable` is the
  case "meets countably many isomorphism classes" (the first half of [Mon, Lemma XII.8], in this
  form); `MinimallyUnboundedOn.exists_bfClass_compl_bounded` (`Descriptive/MinimallyUnbounded.lean`)
  is the case "`ρ` is bounded".
* `MinimallyUncountableOn.concentratedAtBFLevels`: a minimally uncountable, back-and-forth
  scattered class is concentrated at back-and-forth levels; conversely
  `ConcentratedAtBFLevels.minimallyUncountableOn`: an analytic concentrated class meeting
  uncountably many isomorphism classes is minimally uncountable.  Together:
  `bfScattered_and_minimallyUncountableOn_iff` (no hypothesis beyond analyticity) and
  `minimallyUncountableOn_iff` (for a back-and-forth scattered analytic class).

## Where hypotheses enter

* `[L.IsRelational]` enters with `ModelsOf`.  The rank definitions do not need it.
* `[Countable (Σ l, L.Relations l)]` enters through `scottSentenceAt` (in
  `modelsOf_scottSentenceAt`, the cut by a back-and-forth class, the generic engine and its
  consumers), and through the Borel step of `ConcentratedAtBFLevels.countable_isoClasses_or` (in
  the converse and the two equivalences).  The definitions and the rank lemmas need no
  countability of the relation symbols.
* The first half of [Mon, Lemma XII.8] is stated with the per-level hypothesis
  `Countable (Quotient ((codeBFEquivSetoid L α).comap Subtype.val))`.  The book's statement
  omits a scatteredness hypothesis that its proof uses (countably many classes at the level,
  so that one of them is not small); it is carried here explicitly.

## Boundary

This module uses no isolating rank (`IsIsolatingRank`), and its import closure contains no
`Karp` module and none of `Descriptive.ScatteredCounting`, `Scott.Sentence`,
`Scott.RefinementCount` or `Scott.IsolatingLevel`; the regression guard pins the closure.  The
rank-parametric analogue of Def XII.4 (`MinimallyUnboundedOn ρ`) and its rank independence on
back-and-forth scattered classes are in `Descriptive/MinimallyUnbounded.lean`, which imports
the isolating-rank contract.  Thinness of a minimally uncountable class, with no scatteredness
hypothesis, is in `Descriptive/MinimallyUncountableThin.lean`; its proof reaches López–Escobar.

## Conventions

The level-`α` relation is this library's `CodeBFEquiv α` (single-element back-and-forth steps
from the empty tuples).  No identification with the book's tuple relations `≡_α`, or with any
Scott rank of the book, is made or used.

## References

* [Mon] A. Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, draft, Chapter XII,
  §XII.1–XII.2 (Def XII.1, Def XII.4, Lemma XII.5, Lemma XII.8).

The composition was offered for upstreaming by a consumer of this library.
-/

universe u v

namespace FirstOrder.Language

open Cardinal Set MeasureTheory

/-! ### Bounded and unbounded rank -/

section Bounded

variable {L : Language.{u, v}} (ρ : StructureSpace L → Ordinal.{0})

/-- The map `ρ` is **bounded below `ω₁` on `K`**: some threshold `β < ω₁` exceeds `ρ c` for
every member `c ∈ K`, so in particular every value of `ρ` on `K` is below `ω₁`.  The empty class
is bounded.  This is the negation of `UnboundedRankOn ρ K`
(`unboundedRankOn_iff_not_boundedRankOn`). -/
def BoundedRankOn (K : Set (StructureSpace L)) : Prop :=
  ∃ β < Ordinal.omega 1, ∀ c ∈ K, ρ c < β

/-- The map `ρ` is **unbounded below `ω₁` on `K`**: every threshold `β < ω₁` is met or exceeded
by some member, `β ≤ ρ c` for some `c ∈ K` (the shape of [Mon, Def XII.1]).  Only the thresholds
range below `ω₁`: the values `ρ c` themselves need not be below `ω₁`, and a single member with
`ω₁ ≤ ρ c` already makes `ρ` unbounded on `K`.  For an isolating rank (`IsIsolatingRank`, in
`Descriptive/ScatteredCounting.lean`) every value is below `ω₁` (its field `lt_omega1`), so
there the two readings agree: `K` has members of arbitrarily high value below `ω₁`. -/
def UnboundedRankOn (K : Set (StructureSpace L)) : Prop :=
  ∀ β < Ordinal.omega 1, ∃ c ∈ K, β ≤ ρ c

variable {ρ}

theorem unboundedRankOn_iff_not_boundedRankOn {K : Set (StructureSpace L)} :
    UnboundedRankOn ρ K ↔ ¬ BoundedRankOn ρ K := by
  simp only [UnboundedRankOn, BoundedRankOn, not_exists, not_and, not_forall, not_lt, exists_prop]

theorem BoundedRankOn.mono {J K : Set (StructureSpace L)} (h : BoundedRankOn ρ K)
    (hJK : J ⊆ K) : BoundedRankOn ρ J :=
  let ⟨β, hβ, hb⟩ := h; ⟨β, hβ, fun c hc ↦ hb c (hJK hc)⟩

theorem boundedRankOn_empty : BoundedRankOn ρ ∅ :=
  ⟨0, Ordinal.omega_pos 1, fun _ h ↦ h.elim⟩

/-- **Countable unions of bounded classes are bounded** (regularity of `ℵ₁`). -/
theorem boundedRankOn_sUnion {S : Set (Set (StructureSpace L))} (hS : S.Countable)
    (h : ∀ s ∈ S, BoundedRankOn ρ s) : BoundedRankOn ρ (⋃₀ S) := by
  have := hS.to_subtype
  choose β hβ hb using fun s : S ↦ h s.1 s.2
  refine ⟨⨆ s, β s, Ordinal.iSup_lt_omega_one hβ, fun c hc ↦ ?_⟩
  obtain ⟨s, hs, hcs⟩ := hc
  exact (hb ⟨s, hs⟩ c hcs).trans_le (le_ciSup (f := β) Ordinal.bddAbove_of_small ⟨s, hs⟩)

theorem BoundedRankOn.union {J K : Set (StructureSpace L)} (hJ : BoundedRankOn ρ J)
    (hK : BoundedRankOn ρ K) : BoundedRankOn ρ (J ∪ K) := by
  rw [← sUnion_pair]
  exact boundedRankOn_sUnion ((countable_singleton _).insert _) (by simp [hJ, hK])

end Bounded

/-! ### Sentence cuts and minimal uncountability -/

section Minimal

variable {L : Language.{u, v}} [L.IsRelational]

/-- **Minimally uncountable on `K`**: `K` meets uncountably many isomorphism classes, and every
sentence cut `K ∩ ModelsOf θ` / `K \ ModelsOf θ` has a side meeting only countably many.  The
cut ranges over sentences, not arbitrary invariant subsets. -/
def MinimallyUncountableOn (K : Set (StructureSpace L)) : Prop :=
  ¬ (Quotient.mk (structureIsoSetoid L) '' K).Countable ∧
    ∀ θ : L.Sentenceω, (Quotient.mk (structureIsoSetoid L) '' (K ∩ ModelsOf θ)).Countable ∨
      (Quotient.mk (structureIsoSetoid L) '' (K \ ModelsOf θ)).Countable

/-- **A minimally uncountable sentence**: its `ℕ`-coded models are minimally uncountable. -/
def Sentenceω.MinimallyUncountable (Θ : L.Sentenceω) : Prop :=
  MinimallyUncountableOn (ModelsOf Θ)

/-- **The literal form for a sentence**: uncountably many models, and for every sentence `θ`,
`Θ ⊓ θ` or `Θ ⊓ θ.not` has countably many models up to isomorphism. -/
theorem Sentenceω.minimallyUncountable_iff_inf (Θ : L.Sentenceω) :
    Θ.MinimallyUncountable ↔ ¬ (Quotient.mk (structureIsoSetoid L) '' ModelsOf Θ).Countable ∧
      ∀ θ : L.Sentenceω, (Quotient.mk (structureIsoSetoid L) '' ModelsOf (Θ ⊓ θ)).Countable ∨
        (Quotient.mk (structureIsoSetoid L) '' ModelsOf (Θ ⊓ θ.not)).Countable := by
  simp only [Sentenceω.MinimallyUncountable, MinimallyUncountableOn, modelsOf_inf, modelsOf_not,
    Set.sdiff_eq]

-- The public form is `modelsOf_mem_iff_of_equiv` (`Descriptive/LopezEscobarEasy.lean`).  While
-- `realize_equiv` lives in `Lomega1omega.Theory`, no other module of this closure has both it
-- and `ModelsOf` in scope.  Moving `realize_equiv` down to `Lomega1omega/Semantics.lean` would
-- let `modelsOf_mem_iff_of_equiv` move to `SatisfactionBorel` with no import or closure change,
-- retiring this copy; that relocation is a recorded follow-up.
/-- Isomorphic codes satisfy the same sentences (`BoundedFormulaω.realize_equiv`).  Private, so
that this module reaches `Lomega1omega.Theory` and no López–Escobar module. -/
private theorem modelsOf_mem_of_iso (θ : L.Sentenceω) {c d : StructureSpace L}
    (h : (structureIsoSetoid L).r c d) (hc : c ∈ ModelsOf θ) : d ∈ ModelsOf θ := by
  obtain ⟨e⟩ := h
  have key := @BoundedFormulaω.realize_equiv L ℕ ℕ c.toStructure d.toStructure e Empty 0 θ
    Empty.elim Fin.elim0
  rw [show (⇑e ∘ Empty.elim : Empty → ℕ) = Empty.elim from funext fun x ↦ x.elim,
    show (⇑e ∘ Fin.elim0 : Fin 0 → ℕ) = Fin.elim0 from funext fun i ↦ i.elim0] at key
  exact key.mp hc

end Minimal

/-! ### Back-and-forth classes are sentence cuts -/

section BFClasses

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

/-- **Every back-and-forth class below `ω₁` is the set of models of a sentence** (an analogue
of [Mon, Lemma XII.5] on codes, for this library's `CodeBFEquiv`): for `α < ω₁`, the codes of
the models of `scottSentenceAt c α` are the codes `CodeBFEquiv α`-equivalent to `c`. -/
theorem modelsOf_scottSentenceAt (c : StructureSpace L) {α : Ordinal.{0}}
    (hα : α < Ordinal.omega 1) :
    ModelsOf (@scottSentenceAt L _ ℕ c.toStructure _ α) = {d | CodeBFEquiv α c d} := by
  ext d
  rw [mem_modelsOf_iff_realize]
  exact @realize_scottSentenceAt_iff_BFEquiv L _ ℕ c.toStructure _ ℕ d.toStructure α hα

variable {K : Set (StructureSpace L)}

/-- **The cut by a back-and-forth class**: in a minimally uncountable class, the class of any
code at any level `α < ω₁`, or its complement, meets only countably many isomorphism
classes. -/
theorem MinimallyUncountableOn.countable_bfClass_or_compl (h : MinimallyUncountableOn K)
    (c : StructureSpace L) {α : Ordinal.{0}} (hα : α < Ordinal.omega 1) :
    (Quotient.mk (structureIsoSetoid L) '' (K ∩ {d | CodeBFEquiv α c d})).Countable ∨
      (Quotient.mk (structureIsoSetoid L) '' (K \ {d | CodeBFEquiv α c d})).Countable := by
  rw [← modelsOf_scottSentenceAt c hα]; exact h.2 _

/-- **One back-and-forth class with a small complement** (generic engine).

* **Parameter.**  A smallness predicate `P` on sets of codes, closed under subsets (`hmono`) and
  under countable unions (`hU`).
* **Hypotheses.**  `K` is not small (`hK`), and every sentence cut of `K` has a small side
  (`hcut`: `P (K ∩ ModelsOf θ) ∨ P (K \ ModelsOf θ)` for every sentence `θ`).  At the level
  `α < ω₁`, the restriction of `CodeBFEquiv α` to `K` has countably many classes (`hKα`).
* **Conclusion.**  For some `a ∈ K`, the class `K ∩ {d | CodeBFEquiv α a d}` is not small and
  its complement in `K` is small.

The two instantiations are `MinimallyUncountableOn.exists_bfClass_compl_countable` (`P` = "meets
countably many isomorphism classes", below) and
`MinimallyUnboundedOn.exists_bfClass_compl_bounded` (`P` = "`ρ` is bounded below `ω₁`", in
`Descriptive/MinimallyUnbounded.lean`).

The per-level countability is a hypothesis, used to cover `K` by countably many classes; whether
it can be dropped in general is not settled here.  For the models of a minimally uncountable
sentence it is dischargeable: `MinimallyUncountableOn.isThinOn`
(`Descriptive/MinimallyUncountableThin.lean`) with the landed
`Sentenceω.bfScattered_of_isThinOnNatModels` (`Conditional/BFScatteredSilver.lean`) gives
`BFScattered`; that composition is the sentence headline
`Sentenceω.minimallyUncountable_iff` (`Conditional/MinimallyUncountableHeadline.lean`). -/
theorem exists_bfClass_compl_of_sentence_cuts (P : Set (StructureSpace L) → Prop)
    (hmono : ∀ ⦃s t : Set (StructureSpace L)⦄, s ⊆ t → P t → P s)
    (hU : ∀ S : Set (Set (StructureSpace L)), S.Countable → (∀ s ∈ S, P s) → P (⋃₀ S))
    (hK : ¬ P K) (hcut : ∀ θ : L.Sentenceω, P (K ∩ ModelsOf θ) ∨ P (K \ ModelsOf θ))
    {α : Ordinal.{0}} (hα : α < Ordinal.omega 1)
    (hKα : Countable (Quotient ((codeBFEquivSetoid L α).comap
      (Subtype.val : K → StructureSpace L)))) :
    ∃ a ∈ K, ¬ P (K ∩ {d | CodeBFEquiv α a d}) ∧ P (K \ {d | CodeBFEquiv α a d}) := by
  by_contra hne
  push Not at hne
  -- every class of a member of `K` is small
  have hcls : ∀ a ∈ K, P (K ∩ {d | CodeBFEquiv α a d}) := by
    intro a ha
    rcases hcut (@scottSentenceAt L _ ℕ a.toStructure _ α) with h | h <;>
      rw [modelsOf_scottSentenceAt a hα] at h
    · exact h
    · by_contra hP; exact hne a ha hP h
  -- `K` is the union of the classes of countably many representatives
  apply hK
  refine hmono ?_ (hU (range fun q : Quotient ((codeBFEquivSetoid L α).comap
      (Subtype.val : K → StructureSpace L)) ↦ K ∩ {d | CodeBFEquiv α q.out.1 d})
    (countable_range _) (forall_mem_range.mpr fun q ↦ hcls _ q.out.2))
  intro x hx
  exact mem_sUnion.mpr ⟨_, ⟨Quotient.mk _ ⟨x, hx⟩, rfl⟩, hx,
    Quotient.mk_out (s := (codeBFEquivSetoid L α).comap (Subtype.val : K → StructureSpace L))
      ⟨x, hx⟩⟩

/-- **One class meets uncountably many isomorphism classes, its complement countably many**
(the first half of [Mon, Lemma XII.8], rank-free form): at a level `α < ω₁` where a minimally
uncountable `K` has countably many `CodeBFEquiv α`-classes.  The per-level countability is the
scatteredness hypothesis that the book's statement omits. -/
theorem MinimallyUncountableOn.exists_bfClass_compl_countable (h : MinimallyUncountableOn K)
    {α : Ordinal.{0}} (hα : α < Ordinal.omega 1)
    (hKα : Countable (Quotient ((codeBFEquivSetoid L α).comap
      (Subtype.val : K → StructureSpace L)))) :
    ∃ a ∈ K, ¬ (Quotient.mk (structureIsoSetoid L) '' (K ∩ {d | CodeBFEquiv α a d})).Countable ∧
      (Quotient.mk (structureIsoSetoid L) '' (K \ {d | CodeBFEquiv α a d})).Countable :=
  exists_bfClass_compl_of_sentence_cuts
    (fun s ↦ (Quotient.mk (structureIsoSetoid L) '' s).Countable)
    (fun _ _ hJK h ↦ h.mono (image_mono hJK))
    (fun _ hS h ↦ by rw [sUnion_eq_biUnion, image_iUnion₂]; exact hS.biUnion h) h.1 h.2 hα hKα

end BFClasses

/-! ### Minimal uncountability and concentration -/

section Concentration

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ l, L.Relations l)]
  {K : Set (StructureSpace L)}

/-- **Minimal and scattered gives concentration**: a minimally uncountable, back-and-forth
scattered class is concentrated at back-and-forth levels. -/
theorem MinimallyUncountableOn.concentratedAtBFLevels (h : MinimallyUncountableOn K)
    (hK : BFScattered K) : ConcentratedAtBFLevels K := by
  intro α hα
  obtain ⟨a, -, -, hc⟩ := h.exists_bfClass_compl_countable hα (hK α hα)
  exact ⟨a, hc.mono (image_mono fun _ hx ↦ by
    exact ⟨hx.1, fun hax ↦ hx.2 ((codeBFEquivSetoid L α).iseqv.symm hax)⟩)⟩

/-- **Concentration and uncountably many classes give minimal uncountability**, for an analytic
class: the cut `K ∩ ModelsOf θ` is relatively Borel and isomorphism invariant, so the landed
`ConcentratedAtBFLevels.countable_isoClasses_or` applies to it. -/
theorem ConcentratedAtBFLevels.minimallyUncountableOn (hC : ConcentratedAtBFLevels K)
    (hKa : AnalyticSet K) (hunc : ¬ (Quotient.mk (structureIsoSetoid L) '' K).Countable) :
    MinimallyUncountableOn K := by
  refine ⟨hunc, fun θ ↦ ?_⟩
  have := hC.countable_isoClasses_or hKa ⟨ModelsOf θ, modelsOf_measurableSet θ, rfl⟩
    fun x hx y hy hxy ↦ ⟨hy, modelsOf_mem_of_iso θ hxy hx.2⟩
  rwa [sdiff_self_inter] at this

/-- **The concentration equivalence**, for an analytic class and with no other hypothesis:
back-and-forth scattered and minimally uncountable iff concentrated at back-and-forth levels and
meeting uncountably many isomorphism classes. -/
theorem bfScattered_and_minimallyUncountableOn_iff (hKa : AnalyticSet K) :
    BFScattered K ∧ MinimallyUncountableOn K ↔
      ConcentratedAtBFLevels K ∧ ¬ (Quotient.mk (structureIsoSetoid L) '' K).Countable :=
  ⟨fun ⟨hK, h⟩ ↦ ⟨h.concentratedAtBFLevels hK, h.1⟩,
    fun ⟨hC, hunc⟩ ↦ ⟨hC.bfScattered, hC.minimallyUncountableOn hKa hunc⟩⟩

/-- **The concentration equivalence on a back-and-forth scattered analytic class**: minimally
uncountable iff concentrated and meeting uncountably many isomorphism classes. -/
theorem minimallyUncountableOn_iff (hKa : AnalyticSet K) (hK : BFScattered K) :
    MinimallyUncountableOn K ↔
      ConcentratedAtBFLevels K ∧ ¬ (Quotient.mk (structureIsoSetoid L) '' K).Countable :=
  (and_iff_right hK).symm.trans (bfScattered_and_minimallyUncountableOn_iff hKa)

end Concentration

end FirstOrder.Language
