/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.Polish
import InfinitaryLogic.Descriptive.SatisfactionBorel
import Architect

/-!
# Standard Borel Structure on the Model Class

This file shows that `ModelsOf φ` (the set of coded ℕ-models of an Lω₁ω sentence φ)
inherits `StandardBorelSpace` as a measurable subspace of the structure space.

## Main Results

- `modelsOf_isClopenable`: `ModelsOf φ` is clopenable (admits a finer Polish
  topology making it clopen).
- `modelsOf_standardBorel`: The subtype `↥(ModelsOf φ)` is standard Borel.
-/

universe u v

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

/-- `ModelsOf φ` is clopenable in the structure space: there exists a finer Polish
topology making it both open and closed. This follows from `ModelsOf φ` being
measurable in a Polish + Borel space. -/
@[blueprint "thm:models-clopenable"
  (title := /-- Model class is clopenable -/)
  (statement := /-- For any $\Lomegaone$ sentence $\varphi$, the set $\mathrm{Mod}(\varphi)$ is clopenable in the structure space. -/)
  (proof := /-- $\mathrm{Mod}(\varphi)$ is measurable (by satisfaction is Borel) and the structure space is Polish + Borel, so any measurable set is clopenable. -/)
  (uses := ["thm:satisfaction-borel", "thm:structure-space-polish"])]
theorem modelsOf_isClopenable (φ : L.Sentenceω) :
    PolishSpace.IsClopenable (ModelsOf φ) :=
  (modelsOf_measurableSet φ).isClopenable

/-- The subtype of coded ℕ-models of φ is standard Borel: it inherits a
standard Borel structure as a measurable subspace of the standard Borel
structure space. -/
@[blueprint "thm:models-standard-borel"
  (title := /-- Model class is standard Borel -/)
  (statement := /-- For any $\Lomegaone$ sentence $\varphi$, the subtype $\mathrm{Mod}(\varphi)$ is a standard Borel space. -/)
  (proof := /-- A measurable subset of a standard Borel space is standard Borel. -/)
  (uses := ["thm:satisfaction-borel", "thm:structure-space-polish"])]
instance modelsOf_standardBorel (φ : L.Sentenceω) :
    StandardBorelSpace ↥(ModelsOf φ) :=
  (modelsOf_measurableSet φ).standardBorel

/-- The space of coded ℕ-models of φ, as a standard Borel space. -/
abbrev ModelSpace (φ : L.Sentenceω) := ↥(ModelsOf φ)

end Language

end FirstOrder
