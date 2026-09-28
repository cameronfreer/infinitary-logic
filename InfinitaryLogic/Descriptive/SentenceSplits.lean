/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.CountableSplits
import InfinitaryLogic.Descriptive.SentenceRecovery

/-!
# Thinness from single-sentence splits on a presentation of the classes

`thin_of_countable_sentence_spectra` derives thinness from countably many realized truth
sequences for every countable list of sentences, on codes.  A classification argument
naturally delivers something stated on a **presentation** of the isomorphism classes rather
than on codes: a type `Q`, a map `classOf : C → Q`, and a truth predicate `truth` that is actual
satisfaction read back through `classOf`, such that for each single sentence one of its two
truth sides contains only countably many points of `Q`.

* `countable_sentenceTheory_image_of_splits` (the bridge): single-sentence splits on the
  presentation give countably many realized truth sequences on `C` for every sentence list.
  Off the countable union of the exceptional sides, the whole truth sequence is constant
  (`countable_range_of_splits`), and `htruth` transfers the count to the codes.
* `isThinOn_of_countable_sentence_splits`: thinness of `C`, through the arbitrary-class
  recovery argument `isThinOn_of_countable_sentence_spectra`.
* `Sentenceω.isThinOnNatModels_of_countable_sentence_splits`: the sentence-specific corollary.

`Q` is any type presenting `C`.  `classOf` need not be surjective, injective, or measurable; no
σ-algebra on `Q` is assumed or produced.  No hypothesis that equality in `Q` reflects or preserves
isomorphism is imposed or used (under the countable-signature endpoint's assumptions, satisfaction
compatibility does imply reflection through Scott sentences; the proof neither establishes nor
uses that).  Only `htruth` and `hsplit` are used.  Nothing here needs Silver, ranks, Scott
isolation, or Borelness of `C`.
-/

universe u v w

namespace FirstOrder.Language

open Set

section Bridge

variable {L : Language.{u, v}} [L.IsRelational]

/-- **The bridge.**  If each single sentence has a countable truth side on a presentation of the
classes of `C`, then every countable sentence list realizes countably many truth sequences
on `C`.  Stated for every `L : Language.{u, v}`; no countability of the signature is consumed. -/
theorem countable_sentenceTheory_image_of_splits (C : Set (StructureSpace L)) {Q : Type w}
    (classOf : C → Q) (truth : L.Sentenceω → Q → Prop)
    (htruth : ∀ θ c, truth θ (classOf c) ↔ c.1 ∈ ModelsOf θ)
    (hsplit : ∀ θ, ({q | truth θ q} : Set Q).Countable ∨
      ({q | ¬ truth θ q} : Set Q).Countable)
    (θ : ℕ → L.Sentenceω) : (sentenceTheory θ '' C).Countable := by
  classical
  let g : Q → ℕ → Bool := fun q n => decide (truth (θ n) q)
  have hrange : (Set.range g).Countable :=
    countable_range_of_splits (fun n q => truth (θ n) q) g
      (fun q q' h => funext fun n => decide_eq_decide.mpr (h n)) (fun n => hsplit (θ n))
  refine hrange.mono ?_
  rintro _ ⟨c, hc, rfl⟩
  refine ⟨classOf ⟨c, hc⟩, funext fun n => ?_⟩
  exact decide_eq_decide.mpr (htruth (θ n) ⟨c, hc⟩)

end Bridge

variable {L : Language.{0, 0}} [L.IsRelational] [Countable (Σ n, L.Relations n)]

/-- **Thinness from single-sentence splits** on a presentation of the classes of `C`. -/
theorem isThinOn_of_countable_sentence_splits (C : Set (StructureSpace L)) {Q : Type w}
    (classOf : C → Q) (truth : L.Sentenceω → Q → Prop)
    (htruth : ∀ θ c, truth θ (classOf c) ↔ c.1 ∈ ModelsOf θ)
    (hsplit : ∀ θ, ({q | truth θ q} : Set Q).Countable ∨
      ({q | ¬ truth θ q} : Set Q).Countable) :
    IsThinOn (structureIsoSetoid L) C :=
  isThinOn_of_countable_sentence_spectra C
    (countable_sentenceTheory_image_of_splits C classOf truth htruth hsplit)

/-- The sentence-specific corollary: single-sentence splits on a presentation of the countable
models of `φ` give thinness of `φ`. -/
theorem Sentenceω.isThinOnNatModels_of_countable_sentence_splits (φ : L.Sentenceω) {Q : Type w}
    (classOf : ModelsOf φ → Q) (truth : L.Sentenceω → Q → Prop)
    (htruth : ∀ θ c, truth θ (classOf c) ↔ c.1 ∈ ModelsOf θ)
    (hsplit : ∀ θ, ({q | truth θ q} : Set Q).Countable ∨
      ({q | ¬ truth θ q} : Set Q).Countable) :
    φ.IsThinOnNatModels :=
  isThinOn_of_countable_sentence_splits (ModelsOf φ) classOf truth htruth hsplit

end FirstOrder.Language
