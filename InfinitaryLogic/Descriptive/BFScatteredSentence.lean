/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.BFScattered
import InfinitaryLogic.ModelTheory.MorleyCounting

/-!
# Thinness of a sentence from countably many back-and-forth classes at every level

The sentence form of `isThinOn_of_bfScattered` (`Descriptive/BFScattered.lean`): if for every
`η < ω₁` the coded models of `φ` fall into countably many classes of `bfEquivSetoid φ η`, then
`φ` is thin on its coded models (`isThinOnNatModels_of_bfScattered`).

`bfEquivSetoid φ η` (from `ModelTheory/MorleyCounting.lean`) is the restriction of
`codeBFEquivSetoid L η` to the codes of models of `φ` (`bfEquivSetoid_eq_comap`, true by
definition), just as `isoSetoid φ` is the restriction of `structureIsoSetoid L`.  This module is
separate from `BFScattered` only because `bfEquivSetoid` lives in the counting theory, which the
arbitrary-class theorem does not import.
-/

universe u v

namespace FirstOrder.Language

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

omit [Countable (Σ l, L.Relations l)] in
/-- `bfEquivSetoid φ η` is the restriction of `codeBFEquivSetoid L η` to the codes of models of
`φ`.  True by definition; stated so consumers can rewrite with it without unfolding. -/
theorem bfEquivSetoid_eq_comap (φ : L.Sentenceω) (η : Ordinal.{0}) :
    bfEquivSetoid φ η =
      (codeBFEquivSetoid L η).comap (Subtype.val : ↥(ModelsOf φ) → StructureSpace L) :=
  rfl

/-- **Thinness of a sentence from countably many back-and-forth classes at every level**: if for
every `η < ω₁` the coded models of `φ` fall into countably many classes of `bfEquivSetoid φ η`,
then `φ` is thin on its coded models.  This is `isThinOn_of_bfScattered` for `ModelsOf φ`. -/
theorem isThinOnNatModels_of_bfScattered {φ : L.Sentenceω}
    (h : ∀ η : Ordinal.{0}, η < Ordinal.omega 1 → Countable (Quotient (bfEquivSetoid φ η))) :
    φ.IsThinOnNatModels :=
  isThinOn_of_bfScattered fun η hη ↦ bfEquivSetoid_eq_comap φ η ▸ h η hη

end FirstOrder.Language
