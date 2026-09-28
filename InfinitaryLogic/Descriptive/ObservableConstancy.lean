/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.CountableSplits
import InfinitaryLogic.Descriptive.SmallVocabularyTransport

/-!
# Borel observations are constant off countably many classes

On a presentation `classOf : X → Q` of the isomorphism classes of a standard Borel family of codes
`codes : X → StructureSpace L`, with `truth` actual satisfaction read back through `classOf`
and every single sentence having a countable truth side on `Q`:

* `sentences_constant_off_countable`: a countable family of sentences is simultaneously constant
  outside one countable set of presentation values (`exists_countable_exceptions_of_splits`).
* `constant_off_countable_of_borel_observation`: an observation `f : Q → Y` into a countably
  separated space whose **composite with `classOf` is measurable** agrees with one of its values
  outside a countable set of presentation values, when `Q` is uncountable.  The proof encodes
  the composite by sentences (`SmallVocabulary.sentences_encode_observable`, for every countable
  relational `L : Language.{u, v}`), reads the encoding bits back to `Q` through surjectivity of
  `classOf` and `htruth`, and applies `constant_off_countable_of_splits`.

Measurability is imposed on the composite `f ∘ classOf` only.  **No measurable structure on `Q` is
assumed or produced**; `Q` is not claimed to be standard Borel.  Surjectivity of `classOf` is what
transfers the recovered truth to every presentation value; isomorphism implying equal presentation
values (`hiso`) is what makes the composite isomorphism-compatible.
-/

universe u v w

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

/-- **Borel observations are constant off countably many classes.**  Measurability is on the
composite `f ∘ classOf`; `Q` carries no measurable structure. -/
theorem constant_off_countable_of_borel_observation
    {X Y : Type} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [MeasurableSpace.CountablySeparated Y]
    (codes : X → StructureSpace L) (hcodes : Measurable codes)
    {Q : Type w} (classOf : X → Q) (honto : Function.Surjective classOf)
    (hiso : ∀ x y, (structureIsoSetoid L).r (codes x) (codes y) → classOf x = classOf y)
    (hQ : ¬ Countable Q) (truth : L.Sentenceω → Q → Prop)
    (htruth : ∀ φ x, truth φ (classOf x) ↔ codes x ∈ ModelsOf φ)
    (hsplit : ∀ φ, ({q | truth φ q} : Set Q).Countable ∨ ({q | ¬ truth φ q} : Set Q).Countable)
    (f : Q → Y) (hf : Measurable (f ∘ classOf)) :
    ∃ q₀, ({q | f q ≠ f q₀} : Set Q).Countable := by
  classical
  obtain ⟨e, θ, _he, hinj, hθ⟩ := SmallVocabulary.sentences_encode_observable L codes hcodes
    (f ∘ classOf) hf (fun x y h => congrArg f (hiso x y h))
  -- the encoding bits read back on `Q`
  have hbit : ∀ (i : ℕ) (q : Q), truth (θ i) q ↔ e (f q) i = true := by
    intro i q
    obtain ⟨x, rfl⟩ := honto q
    rw [htruth]
    have := congrFun (hθ x) i
    simp only [sentenceTheory, Function.comp_apply] at this
    rw [← this]
    exact ⟨fun h => decide_eq_true h, fun h => of_decide_eq_true h⟩
  -- the tests are the encoding bits on `Y`; they separate values since `e` is injective
  refine constant_off_countable_of_splits hQ f (fun i y => e y i = true)
    (fun y z h => hinj (funext fun i => ?_)) fun i => ?_
  · have := h i
    cases hy : e y i <;> cases hz : e z i <;> simp_all
  · have hset : ({q | e (f q) i = true} : Set Q) = {q | truth (θ i) q} :=
      Set.ext fun q => (hbit i q).symm
    have hset' : ({q | ¬ e (f q) i = true} : Set Q) = {q | ¬ truth (θ i) q} :=
      Set.ext fun q => not_congr (hbit i q).symm
    rw [hset, hset']
    exact hsplit (θ i)

end FirstOrder.Language
