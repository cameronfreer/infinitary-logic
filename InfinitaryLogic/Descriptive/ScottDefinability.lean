/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.SmallVocabularyTransport
import InfinitaryLogic.Scott.RefinementCount
import InfinitaryLogic.OrdinalCountability

/-!
# Scott isolation and countable/cocountable definability on a presentation

For a presentation `truth : L.Sentenceω → Q → Prop` of a family of isomorphism classes:

* `IsolatedPresentation truth`: every value of `Q` is picked out by one sentence.
* **Abstract layer** (no relationality or signature countability): from isolation and the closure
  of `truth` under countable disjunction and falsum, every countable set of presentation values
  is sentence-definable (`exists_sentence_of_countable`, the empty and finite cases included);
  with negation and single-sentence splits, the sentence-definable sets are exactly the countable
  and the cocountable ones (`sentence_definable_iff`).
* **Presentation layer**: for a surjective `classOf : X → Q` with `truth` actual satisfaction of
  the codes (`htruth`), the closure conditions hold (`truth_esup_of_presentation`,
  `not_truth_falsum_of_presentation`, `truth_not_of_presentation`), and when isomorphic codes have
  equal presentation values, the presentation is isolated by Scott sentences
  (`isolatedPresentation_of_surjective`): the Scott sentence of `ℕ` under the decoded structure of a
  representative isolates its class.  No reverse-isomorphism premise, no measurable structure on
  `Q`, no Borelness of the family.  The corollaries `exists_sentence_of_countable_of_presentation`
  and `sentence_definable_iff_of_presentation` assemble the two layers.
* **Strict stage bounds** (abstract layer): on an isolated presentation, the isolating sentences
  have countable quantifier rank (`IsolatedPresentation.exists_qrank_lt`, from
  `Sentenceω.qrank_lt_omega1`), so antitone domains of presentation values that are nonsingleton
  and agree on every sentence of quantifier rank at most `η` at every countable `η` bound every
  value's stages strictly by a countable ordinal
  (`IsolatedPresentation.exists_countable_strict_stage_bound`, the instance of
  `InfinitaryLogic.exists_countable_strict_stage_bound_of_isolation` in `OrdinalCountability`).

## Strict stage bounds: what is and is not claimed

* The bound is the quantifier rank of *some* isolating sentence.  It is not identified with an
  internal Scott rank, nor with the stabilization ordinal of a representative, and it is not an
  attained stage (attainment is `exists_greatest_stage_lt_omega1` in `OrdinalUtil`, under further
  closure hypotheses).
* Agreement at stage `η` is for sentences of quantifier rank **at most** `η`, the convention of
  `EquivQRω`; exclusion is at the isolating sentence's own rank.
* Nonsingletonness of the domains is essential, and no countability of exceptional classes is
  assumed.  The hypotheses force the presentation type to be uncountable, so the bound applies
  to a countable presentation only vacuously.
* **Where Scott theory enters.**  Only through `IsolatedPresentation`.  The generic layer in
  `OrdinalCountability` mentions no logic: its proofs use no `FirstOrder` constant.  The wrapper
  over an abstract `IsolatedPresentation` adds only the syntactic fact
  `Sentenceω.qrank_lt_omega1`: its proof uses no Scott, Karp or back-and-forth constant, although
  this module imports them.  A consumer that obtains isolation from
  `isolatedPresentation_of_surjective` does reach `scottSentence_characterizes` and the Karp
  theory in its proof.
* Isolation concerns the given presentation, a space of isomorphism classes of countable codes;
  a Scott sentence is not claimed to isolate a structure among arbitrary uncountable ones.

The strict stage bounds were offered for upstreaming by a consumer of this library.
-/

universe u v w x

namespace FirstOrder.Language

open Set

/-! ### The abstract layer -/

section Abstract

variable {L : Language.{u, v}} {Q : Type w}

/-- A presentation is **Scott-isolated**: every value is picked out by one sentence. -/
def IsolatedPresentation (truth : L.Sentenceω → Q → Prop) : Prop :=
  ∀ q, ∃ σ : L.Sentenceω, ∀ s, truth σ s ↔ s = q

/-- **Countable sets are sentence-definable** on an isolated presentation closed under countable
disjunction and falsum.  The empty set is defined by falsum; a nonempty countable set is the range of
a sequence, and the countable disjunction of the isolating sentences defines it (finite sets are
ranges with repetition). -/
theorem exists_sentence_of_countable {truth : L.Sentenceω → Q → Prop}
    (hisol : IsolatedPresentation truth)
    (hesup : ∀ (φs : ℕ → L.Sentenceω) q,
      truth (BoundedFormulaω.esup φs) q ↔ ∃ n, truth (φs n) q)
    (hbot : ∀ q, ¬ truth BoundedFormulaω.falsum q) {S : Set Q} (hS : S.Countable) :
    ∃ φ : L.Sentenceω, ∀ q, truth φ q ↔ q ∈ S := by
  choose σ hσ using hisol
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨BoundedFormulaω.falsum, fun q => ⟨fun h => (hbot q h).elim, fun h => h.elim⟩⟩
  · obtain ⟨g, rfl⟩ := hS.exists_eq_range hne
    refine ⟨BoundedFormulaω.esup fun n => σ (g n), fun q => ?_⟩
    rw [hesup]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, ((hσ (g n) q).mp hn).symm⟩
    · rintro ⟨n, rfl⟩
      exact ⟨n, (hσ (g n) (g n)).mpr rfl⟩

/-- **Sentence-definable sets are exactly the countable and the cocountable ones** on an isolated
presentation closed under countable disjunction, falsum, and negation, with single-sentence
splits. -/
theorem sentence_definable_iff {truth : L.Sentenceω → Q → Prop}
    (hisol : IsolatedPresentation truth)
    (hesup : ∀ (φs : ℕ → L.Sentenceω) q,
      truth (BoundedFormulaω.esup φs) q ↔ ∃ n, truth (φs n) q)
    (hbot : ∀ q, ¬ truth BoundedFormulaω.falsum q)
    (hnot : ∀ φ q, truth φ.not q ↔ ¬ truth φ q)
    (hsplit : ∀ φ, ({q | truth φ q} : Set Q).Countable ∨ ({q | ¬ truth φ q} : Set Q).Countable)
    (S : Set Q) :
    (∃ φ : L.Sentenceω, ∀ q, truth φ q ↔ q ∈ S) ↔ S.Countable ∨ Sᶜ.Countable := by
  constructor
  · rintro ⟨φ, hφ⟩
    have hS : S = {q | truth φ q} := Set.ext fun q => (hφ q).symm
    have hSc : Sᶜ = {q | ¬ truth φ q} := Set.ext fun q => not_congr (hφ q).symm
    rcases hsplit φ with h | h
    · exact Or.inl (hS ▸ h)
    · exact Or.inr (hSc ▸ h)
  · rintro (h | h)
    · exact exists_sentence_of_countable hisol hesup hbot h
    · obtain ⟨φ, hφ⟩ := exists_sentence_of_countable hisol hesup hbot h
      exact ⟨φ.not, fun q => by rw [hnot, hφ, Set.mem_compl_iff, not_not]⟩

/-- **Isolating sentences have countable quantifier rank**: on an isolated presentation every
value is isolated by a sentence of rank below `ω₁` (every `Lω₁ω` sentence has countable rank,
`Sentenceω.qrank_lt_omega1`).  The `hisolate` premise of
`InfinitaryLogic.exists_countable_strict_stage_bound_of_isolation`. -/
theorem IsolatedPresentation.exists_qrank_lt {truth : L.Sentenceω → Q → Prop}
    (hisol : IsolatedPresentation truth) (q : Q) :
    ∃ σ : L.Sentenceω, σ.qrank < Ordinal.omega 1 ∧ ∀ s, truth σ s ↔ s = q :=
  let ⟨σ, hσ⟩ := hisol q
  ⟨σ, Sentenceω.qrank_lt_omega1 σ, hσ⟩

/-- **Strict stage bounds on an isolated presentation.**  Antitone domains `D` of presentation
values that are nonsingleton below `ω₁` and agree, at every countable `η`, on every sentence of
quantifier rank at most `η`, bound the stages of every value `q` strictly by a countable ordinal
`θ`, the quantifier rank of a sentence isolating `q`.  The bound covers every stage, countable or
not.  It is not an internal Scott rank and not an attained stage; the hypotheses force `Q` to be
uncountable.  Scott theory enters only through `hisol`. -/
theorem IsolatedPresentation.exists_countable_strict_stage_bound
    {truth : L.Sentenceω → Q → Prop} (hisol : IsolatedPresentation truth)
    (D : Ordinal.{0} → Set Q) (hanti : Antitone D)
    (huniform : ∀ η, η < Ordinal.omega 1 → ∀ φ : L.Sentenceω, φ.qrank ≤ η →
      ∀ ⦃x y⦄, x ∈ D η → y ∈ D η → (truth φ x ↔ truth φ y))
    (htwo : ∀ η, η < Ordinal.omega 1 → (D η).Nontrivial) (q : Q) :
    ∃ θ, θ < Ordinal.omega 1 ∧ ∀ η, q ∈ D η → η < θ :=
  InfinitaryLogic.exists_countable_strict_stage_bound_of_isolation truth (fun φ ↦ φ.qrank) D hanti
    huniform htwo hisol.exists_qrank_lt q

end Abstract

/-! ### The presentation layer -/

section Presentation

variable {L : Language.{u, v}} [L.IsRelational] {X : Type x} {Q : Type w}

/-- Countable disjunction on a presentation with actual satisfaction. -/
theorem truth_esup_of_presentation (codes : X → StructureSpace L) (classOf : X → Q)
    (honto : Function.Surjective classOf) (truth : L.Sentenceω → Q → Prop)
    (htruth : ∀ φ x, truth φ (classOf x) ↔ codes x ∈ ModelsOf φ)
    (φs : ℕ → L.Sentenceω) (q : Q) :
    truth (BoundedFormulaω.esup φs) q ↔ ∃ n, truth (φs n) q := by
  obtain ⟨x, rfl⟩ := honto q
  simp only [htruth]
  change @BoundedFormulaω.Realize L ℕ (codes x).toStructure Empty 0 (BoundedFormulaω.esup φs)
      Empty.elim Fin.elim0 ↔ ∃ n, @BoundedFormulaω.Realize L ℕ (codes x).toStructure Empty 0 (φs n)
      Empty.elim Fin.elim0
  exact @BoundedFormulaω.realize_esup L ℕ (codes x).toStructure Empty 0 Empty.elim Fin.elim0 ℕ _ φs

/-- Falsum on a presentation with actual satisfaction. -/
theorem not_truth_falsum_of_presentation (codes : X → StructureSpace L) (classOf : X → Q)
    (honto : Function.Surjective classOf) (truth : L.Sentenceω → Q → Prop)
    (htruth : ∀ φ x, truth φ (classOf x) ↔ codes x ∈ ModelsOf φ) (q : Q) :
    ¬ truth BoundedFormulaω.falsum q := by
  obtain ⟨x, rfl⟩ := honto q
  rw [htruth]
  exact fun h => h

/-- Negation on a presentation with actual satisfaction. -/
theorem truth_not_of_presentation (codes : X → StructureSpace L) (classOf : X → Q)
    (honto : Function.Surjective classOf) (truth : L.Sentenceω → Q → Prop)
    (htruth : ∀ φ x, truth φ (classOf x) ↔ codes x ∈ ModelsOf φ) (φ : L.Sentenceω) (q : Q) :
    truth φ.not q ↔ ¬ truth φ q := by
  obtain ⟨x, rfl⟩ := honto q
  simp only [htruth]
  change @BoundedFormulaω.Realize L ℕ (codes x).toStructure Empty 0 φ.not Empty.elim Fin.elim0 ↔
    ¬ @BoundedFormulaω.Realize L ℕ (codes x).toStructure Empty 0 φ Empty.elim Fin.elim0
  exact @BoundedFormulaω.realize_not L ℕ (codes x).toStructure Empty 0 Empty.elim Fin.elim0 φ

variable [Countable (Σ l, L.Relations l)]

/-- **Isolation from a surjective, satisfaction-compatible, isomorphism-preserving presentation.**
The isolating sentence of the class of `x` is the Scott sentence of `ℕ` under the decoded structure
of `codes x`.  No reverse-isomorphism premise is used. -/
theorem isolatedPresentation_of_surjective (codes : X → StructureSpace L) (classOf : X → Q)
    (honto : Function.Surjective classOf)
    (hiso : ∀ x y, (structureIsoSetoid L).r (codes x) (codes y) → classOf x = classOf y)
    (truth : L.Sentenceω → Q → Prop)
    (htruth : ∀ φ x, truth φ (classOf x) ↔ codes x ∈ ModelsOf φ) :
    IsolatedPresentation truth := by
  intro q
  obtain ⟨x, rfl⟩ := honto q
  refine ⟨(@scottSentence L _ ℕ (codes x).toStructure _).toSentenceω, fun s => ⟨fun h => ?_,
    fun h => ?_⟩⟩
  · obtain ⟨y, rfl⟩ := honto s
    rw [htruth, SmallVocabulary.mem_modelsOf_iff_realize,
      ← Formulaω.realize_as_sentence_iff_toSentenceω] at h
    exact (hiso x y (@scottSentence_realizes_implies_equiv L _ _ ℕ (codes x).toStructure _
      ℕ (codes y).toStructure _ h)).symm
  · rw [h, htruth, SmallVocabulary.mem_modelsOf_iff_realize,
      ← Formulaω.realize_as_sentence_iff_toSentenceω]
    exact @scottSentence_self L _ _ ℕ (codes x).toStructure _

/-- Countable sets of presentation values are sentence-definable, from the presentation data. -/
theorem exists_sentence_of_countable_of_presentation (codes : X → StructureSpace L)
    (classOf : X → Q) (honto : Function.Surjective classOf)
    (hiso : ∀ x y, (structureIsoSetoid L).r (codes x) (codes y) → classOf x = classOf y)
    (truth : L.Sentenceω → Q → Prop)
    (htruth : ∀ φ x, truth φ (classOf x) ↔ codes x ∈ ModelsOf φ)
    {S : Set Q} (hS : S.Countable) : ∃ φ : L.Sentenceω, ∀ q, truth φ q ↔ q ∈ S :=
  exists_sentence_of_countable (isolatedPresentation_of_surjective codes classOf honto hiso truth
    htruth) (truth_esup_of_presentation codes classOf honto truth htruth)
    (not_truth_falsum_of_presentation codes classOf honto truth htruth) hS

/-- The countable-or-cocountable characterization, from the presentation data and single-sentence
splits. -/
theorem sentence_definable_iff_of_presentation (codes : X → StructureSpace L)
    (classOf : X → Q) (honto : Function.Surjective classOf)
    (hiso : ∀ x y, (structureIsoSetoid L).r (codes x) (codes y) → classOf x = classOf y)
    (truth : L.Sentenceω → Q → Prop)
    (htruth : ∀ φ x, truth φ (classOf x) ↔ codes x ∈ ModelsOf φ)
    (hsplit : ∀ φ, ({q | truth φ q} : Set Q).Countable ∨ ({q | ¬ truth φ q} : Set Q).Countable)
    (S : Set Q) :
    (∃ φ : L.Sentenceω, ∀ q, truth φ q ↔ q ∈ S) ↔ S.Countable ∨ Sᶜ.Countable :=
  sentence_definable_iff (isolatedPresentation_of_surjective codes classOf honto hiso truth htruth)
    (truth_esup_of_presentation codes classOf honto truth htruth)
    (not_truth_falsum_of_presentation codes classOf honto truth htruth)
    (truth_not_of_presentation codes classOf honto truth htruth) hsplit S

end Presentation

end FirstOrder.Language
