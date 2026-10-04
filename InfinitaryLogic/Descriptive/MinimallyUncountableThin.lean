/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.MinimallyUncountable
import InfinitaryLogic.Descriptive.SmallVocabularyTransport

/-!
# Thinness from sentence cuts

A set `K` of codes in which every sentence cut `K ∩ ModelsOf θ` / `K \ ModelsOf θ` has a side
meeting only countably many isomorphism classes is thin: it contains no nonempty perfect set of
pairwise non-isomorphic codes (`isThinOn_of_sentence_cuts`).  In particular a minimally
uncountable class is thin (`MinimallyUncountableOn.isThinOn`).  No back-and-forth scatteredness,
analyticity or invariance of `K` is assumed, and the language is any countable relational
`L : Language.{u, v}`.

When `BFScattered K` is available, use the landed `isThinOn_of_bfScattered`
(`Descriptive/BFScattered.lean`) instead; it does not need this module.

## Dependency

The proof goes through `SmallVocabulary.isThinOn_of_countable_sentence_splits`
(`Descriptive/SmallVocabularyTransport.lean`), the single-sentence splits criterion transported
to every countable relational language.  Its proof cone contains the López–Escobar theorem
`lopez_escobar` (through sentence recovery), and the import closure of this module contains the
López–Escobar modules, the Henkin and Ehrenfeucht–Mostowski methods and `ModelTheory` modules.
That is why this module is separate from `Descriptive/MinimallyUncountable.lean`, and why it does
not import `Descriptive/MinimallyUnbounded.lean`.
-/

universe u v

namespace FirstOrder.Language

open Set

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ l, L.Relations l)]
  {K : Set (StructureSpace L)}

/-- **Thinness from sentence cuts with a countable side**: if every sentence cut of `K` has a
side meeting only countably many isomorphism classes, then `K` is thin.  No scatteredness,
analyticity or invariance of `K` is assumed. -/
theorem isThinOn_of_sentence_cuts
    (h : ∀ θ : L.Sentenceω, (Quotient.mk (structureIsoSetoid L) '' (K ∩ ModelsOf θ)).Countable ∨
      (Quotient.mk (structureIsoSetoid L) '' (K \ ModelsOf θ)).Countable) :
    IsThinOn (structureIsoSetoid L) K := by
  have hinv : ∀ θ c d, (structureIsoSetoid L).r c d → (c ∈ ModelsOf θ ↔ d ∈ ModelsOf θ) :=
    fun θ c d h ↦ isomorphismInvariant_modelsOf θ c d h
  refine SmallVocabulary.isThinOn_of_countable_sentence_splits L K
    (Q := ↥(Quotient.mk (structureIsoSetoid L) '' K))
    (fun c ↦ ⟨Quotient.mk _ c.1, c.1, c.2, rfl⟩)
    (fun θ q ↦ q.1 ∈ Quotient.mk (structureIsoSetoid L) '' ModelsOf θ) ?_ ?_
  · intro θ c
    exact ⟨fun ⟨d, hd, hdc⟩ ↦ (hinv θ d c.1 (Quotient.exact hdc)).mp hd,
      fun hc ↦ ⟨c.1, hc, rfl⟩⟩
  · intro θ
    rcases h θ with h1 | h1
    · left
      refine (h1.preimage Subtype.val_injective).mono ?_
      rintro ⟨q, c, hcK, rfl⟩ ⟨d, hd, hdc⟩
      exact ⟨c, ⟨hcK, (hinv θ d c (Quotient.exact hdc)).mp hd⟩, rfl⟩
    · right
      refine (h1.preimage Subtype.val_injective).mono ?_
      rintro ⟨q, c, hcK, rfl⟩ hq
      exact ⟨c, ⟨hcK, fun hc ↦ hq ⟨c, hc, rfl⟩⟩, rfl⟩

/-- **A minimally uncountable class is thin**, with no scatteredness hypothesis. -/
theorem MinimallyUncountableOn.isThinOn (h : MinimallyUncountableOn K) :
    IsThinOn (structureIsoSetoid L) K :=
  isThinOn_of_sentence_cuts h.2

end FirstOrder.Language
