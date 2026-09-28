/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.SmallVocabularyTransport
import InfinitaryLogic.Scott.RefinementCount

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
