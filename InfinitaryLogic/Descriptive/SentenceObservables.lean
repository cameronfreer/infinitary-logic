/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.SentenceRecovery

/-!
# Borel observables are sentence truths

Relative López–Escobar for Borel families of structures, allowing repetitions and
non-isomorphic members with the same observable.  Everything here is below Silver: the only
input is `sentence_pullback_of_iso_compatible`.

* `sentences_recover_observable`: a measurable Cantor-valued invariant `p` of a Borel family `f`
  is exactly `sentenceTheory θ (f x)` for some countable sentence list `θ`.
* `sentences_encode_observable`: the target may be any countably separated measurable space,
  through a measurable injection into Cantor space.
* `sentence_classification_iff_borel_classification`: on a Borel class, a Borel complete
  invariant exists iff a complete countable list of sentences does.

No selector of representatives is built, and no Borel map into the syntax of sentences is
claimed: the sentence list exists for the chosen observable, by classical choice.  The
thinness corollary (a Borel complete invariant on a thin class forces countably many classes)
needs the spectrum characterization and lives in `Conditional/SentenceSpectrum.lean`.

## Classical background

Marker, *Lectures on Infinitary Model Theory* (Fall 2013 notes,
https://homepages.math.uic.edu/~marker/math512-F13/512_lecture_notes1.pdf): Corollary 4.24 and
Theorem 4.25 for invariant separation and López–Escobar; Definition 3.11 and Corollary 3.20 for
scatteredness. The observable-recovery statements are derived from the project's sentence-recovery
API. No claim is made that these exact formulations occur in the notes.
-/

namespace FirstOrder.Language

open MeasureTheory Set

variable {L : Language.{0, 0}} [L.IsRelational] [Countable (Σ n, L.Relations n)]

/-- **A Borel Cantor-valued invariant of a Borel family is a sequence of sentence truths** on
that family.  The invariant need not be complete. -/
theorem sentences_recover_observable {X : Type} [MeasurableSpace X] [StandardBorelSpace X]
    (f : X → StructureSpace L) (hf : Measurable f) (p : X → (ℕ → Bool)) (hp : Measurable p)
    (hiso : ∀ x y, (structureIsoSetoid L).r (f x) (f y) → p x = p y) :
    ∃ θ : ℕ → L.Sentenceω, ∀ x, sentenceTheory θ (f x) = p x := by
  have h (n : ℕ) : ∃ θ : L.Sentenceω, ∀ x, f x ∈ ModelsOf θ ↔ p x n = true := by
    apply sentence_pullback_of_iso_compatible f hf {x | p x n = true}
      ((measurable_pi_apply n).comp hp (measurableSet_singleton true))
    intro x y hxy
    change p x n = true ↔ p y n = true
    rw [hiso x y hxy]
  choose θ hθ using h
  refine ⟨θ, fun x => ?_⟩
  funext n
  simp only [sentenceTheory, hθ]
  cases p x n <;> rfl

/-- Countably separated targets: the chosen measurable injection encodes observables, not
representatives of isomorphism classes. -/
theorem sentences_encode_observable {X Y : Type} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [MeasurableSpace.CountablySeparated Y]
    (f : X → StructureSpace L) (hf : Measurable f) (p : X → Y) (hp : Measurable p)
    (hiso : ∀ x y, (structureIsoSetoid L).r (f x) (f y) → p x = p y) :
    ∃ (e : Y → (ℕ → Bool)) (θ : ℕ → L.Sentenceω),
      Measurable e ∧ Function.Injective e ∧ ∀ x, sentenceTheory θ (f x) = e (p x) := by
  obtain ⟨e, he, hi⟩ := MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated Y
  obtain ⟨θ, hθ⟩ := sentences_recover_observable f hf (e ∘ p) (he.comp hp)
    (fun x y h => congrArg e (hiso x y h))
  exact ⟨e, θ, he, hi, hθ⟩

/-- **Smooth classification is sentence classification** on a Borel class: a Borel complete
invariant with Cantor target exists iff a complete countable list of sentences does. -/
theorem sentence_classification_iff_borel_classification (C : Set (StructureSpace L))
    (hC : MeasurableSet C) :
    (∃ θ : ℕ → L.Sentenceω, ∀ c d : C,
      (structureIsoSetoid L).r c.val d.val ↔ sentenceTheory θ c.val = sentenceTheory θ d.val) ↔
    (∃ p : C → (ℕ → Bool), Measurable p ∧ ∀ c d : C,
      (structureIsoSetoid L).r c.val d.val ↔ p c = p d) := by
  constructor
  · rintro ⟨θ, hθ⟩
    exact ⟨fun c => sentenceTheory θ c.val,
      (measurable_sentenceTheory θ).comp measurable_subtype_coe, hθ⟩
  · rintro ⟨p, hp, hi⟩
    have : StandardBorelSpace C := hC.standardBorel
    obtain ⟨θ, hθ⟩ := sentences_recover_observable (fun c : C => c.val)
      measurable_subtype_coe p hp (fun x y h => (hi x y).mp h)
    exact ⟨θ, fun c d => by rw [hθ c, hθ d]; exact hi c d⟩

end FirstOrder.Language
