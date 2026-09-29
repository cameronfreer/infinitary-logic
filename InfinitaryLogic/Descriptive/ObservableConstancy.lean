/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.CountableSplits
import InfinitaryLogic.Descriptive.SmallVocabularyTransport

/-!
# Borel observations are constant off countably many presentation values

On a surjective map `classOf : X → Q` from a standard Borel family of codes
`codes : X → StructureSpace L` to a type `Q` of **presentation values**, with `truth` actual
satisfaction read back through `classOf`.  The determination lemma needs nothing more; the
constancy results additionally assume that every single sentence has a countable truth side on `Q`
(single-sentence splits) and, in the nonempty form, that `Q` is nonempty:

* `sentences_constant_off_countable` (under splits): a countable family of sentences is
  simultaneously constant outside one countable set of presentation values
  (`exists_countable_exceptions_of_splits`).
* `sentences_determine_borel_observation`: an observation `f : Q → Y` into a countably separated
  space whose **composite with `classOf` is measurable** and which is invariant under isomorphism
  of the codes is determined by the truth values of countably many sentences.  No split or
  cardinality premise.  The proof encodes the composite by sentences
  (`SmallVocabulary.sentences_encode_observable`, for every countable relational
  `L : Language.{u, v}`) and reads the encoding bits back to `Q` through surjectivity of `classOf`
  and `htruth`.
* `constant_off_countable_of_borel_observation_of_nonempty`: with single-sentence splits and a
  nonempty `Q`, such an observation agrees with one of its values outside a countable set of
  presentation values (`exists_countable_exceptions_of_splits`).  Invariance is required of the
  observation only, not of the labels, and no uncountability is used.
* `constant_off_countable_of_borel_observation`: the earlier form (label compatibility,
  uncountable `Q`), statement unchanged, as a corollary.

The parameter space `X` and the target `Y` live in arbitrary universes; only the underlying language
restriction remains, handled through the small-vocabulary transport.  Measurability is imposed on the
composite `f ∘ classOf` only.  **No measurable structure on `Q` is
assumed or produced**; `Q` is not claimed to be standard Borel.  Surjectivity of `classOf` is what
transfers the recovered truth to every presentation value.  Surjectivity, invariance of the
observation, countable separation of the target, and nonemptiness of `Q` cannot be dropped.
-/

universe u v w x y

namespace FirstOrder.Language

open Set

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ n, L.Relations n)]

omit [L.IsRelational] [Countable (Σ n, L.Relations n)] in
/-- **Simultaneous constancy** of countably many sentences outside a countable set of presentation
values. -/
theorem sentences_constant_off_countable {Q : Type w} (truth : L.Sentenceω → Q → Prop)
    (hsplit : ∀ φ, ({q | truth φ q} : Set Q).Countable ∨ ({q | ¬ truth φ q} : Set Q).Countable)
    (φs : ℕ → L.Sentenceω) :
    ∃ E : Set Q, E.Countable ∧ ∀ q ∉ E, ∀ q' ∉ E, ∀ n, truth (φs n) q ↔ truth (φs n) q' :=
  exists_countable_exceptions_of_splits (fun n q => truth (φs n) q) fun n => hsplit (φs n)

/-- **A Borel observation is determined by countably many sentences.**  No split or cardinality
premise: the observation `f` on the presentation, measurable as a composite on codes and invariant
under isomorphism of the codes, is a function of the truth values of countably many sentences. -/
theorem sentences_determine_borel_observation
    {X : Type x} {Y : Type y} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [MeasurableSpace.CountablySeparated Y]
    (codes : X → StructureSpace L) (hcodes : Measurable codes)
    {Q : Type w} (classOf : X → Q) (honto : Function.Surjective classOf)
    (truth : L.Sentenceω → Q → Prop)
    (htruth : ∀ φ x, truth φ (classOf x) ↔ codes x ∈ ModelsOf φ)
    (f : Q → Y) (hf : Measurable (f ∘ classOf))
    (hobs : ∀ x y, (structureIsoSetoid L).r (codes x) (codes y) →
      f (classOf x) = f (classOf y)) :
    ∃ θ : ℕ → L.Sentenceω, ∀ q s : Q, (∀ i, truth (θ i) q ↔ truth (θ i) s) → f q = f s := by
  classical
  obtain ⟨e, θ, _he, hinj, hθ⟩ := SmallVocabulary.sentences_encode_observable L codes hcodes
    (f ∘ classOf) hf hobs
  -- the encoding bits read back on `Q`
  have hbit : ∀ (i : ℕ) (q : Q), truth (θ i) q ↔ e (f q) i = true := by
    intro i q
    obtain ⟨x, rfl⟩ := honto q
    rw [htruth]
    have := congrFun (hθ x) i
    simp only [sentenceTheory, Function.comp_apply] at this
    rw [← this]
    exact ⟨fun h => decide_eq_true h, fun h => of_decide_eq_true h⟩
  refine ⟨θ, fun q s h => hinj (funext fun i => ?_)⟩
  have hi := (hbit i q).symm.trans ((h i).trans (hbit i s))
  cases hq : e (f q) i <;> cases hs : e (f s) i <;> simp_all

/-- **Borel observations are constant off countably many presentation values.**  Premises:
surjectivity of the presentation, actual satisfaction through it, single-sentence splits,
measurability of the composite `f ∘ classOf`, invariance of the **observation** under isomorphism
of the codes (not of the labels), and a nonempty presentation type.  `Q` carries no measurable
structure.  No uncountability is used: on a countable `Q` every disagreement set is countable. -/
theorem constant_off_countable_of_borel_observation_of_nonempty
    {X : Type x} {Y : Type y} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [MeasurableSpace.CountablySeparated Y]
    (codes : X → StructureSpace L) (hcodes : Measurable codes)
    {Q : Type w} (classOf : X → Q) (honto : Function.Surjective classOf)
    (hQ : Nonempty Q) (truth : L.Sentenceω → Q → Prop)
    (htruth : ∀ φ x, truth φ (classOf x) ↔ codes x ∈ ModelsOf φ)
    (hsplit : ∀ φ, ({q | truth φ q} : Set Q).Countable ∨ ({q | ¬ truth φ q} : Set Q).Countable)
    (f : Q → Y) (hf : Measurable (f ∘ classOf))
    (hobs : ∀ x y, (structureIsoSetoid L).r (codes x) (codes y) →
      f (classOf x) = f (classOf y)) :
    ∃ q₀, ({q | f q ≠ f q₀} : Set Q).Countable := by
  classical
  obtain ⟨θ, hθ⟩ := sentences_determine_borel_observation codes hcodes classOf honto truth htruth
    f hf hobs
  obtain ⟨E, hE, hconst⟩ := exists_countable_exceptions_of_splits (fun i q => truth (θ i) q)
    fun i => hsplit (θ i)
  by_cases h : ∃ q₀, q₀ ∉ E
  · obtain ⟨q₀, hq₀⟩ := h
    refine ⟨q₀, hE.mono fun q hq => ?_⟩
    by_contra hqE
    exact hq (hθ q q₀ (hconst q hqE q₀ hq₀))
  · -- every point is exceptional: `Q` is countable, and any point serves
    obtain ⟨q₀⟩ := hQ
    exact ⟨q₀, hE.mono fun q _ => by_contra fun hq => h ⟨q, hq⟩⟩

/-- **The label-compatible, uncountable form**, unchanged in statement: a corollary of the
nonempty form (an uncountable type is nonempty, and equal labels give equal observations). -/
theorem constant_off_countable_of_borel_observation
    {X : Type x} {Y : Type y} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [MeasurableSpace.CountablySeparated Y]
    (codes : X → StructureSpace L) (hcodes : Measurable codes)
    {Q : Type w} (classOf : X → Q) (honto : Function.Surjective classOf)
    (hiso : ∀ x y, (structureIsoSetoid L).r (codes x) (codes y) → classOf x = classOf y)
    (hQ : ¬ Countable Q) (truth : L.Sentenceω → Q → Prop)
    (htruth : ∀ φ x, truth φ (classOf x) ↔ codes x ∈ ModelsOf φ)
    (hsplit : ∀ φ, ({q | truth φ q} : Set Q).Countable ∨ ({q | ¬ truth φ q} : Set Q).Countable)
    (f : Q → Y) (hf : Measurable (f ∘ classOf)) :
    ∃ q₀, ({q | f q ≠ f q₀} : Set Q).Countable :=
  constant_off_countable_of_borel_observation_of_nonempty codes hcodes classOf honto
    (not_isEmpty_iff.mp fun hempty => hQ (@Finite.to_countable Q (@Finite.of_subsingleton Q
      (@IsEmpty.instSubsingleton Q hempty)))) truth htruth hsplit f hf
    (fun x y h => congrArg f (hiso x y h))

end FirstOrder.Language
