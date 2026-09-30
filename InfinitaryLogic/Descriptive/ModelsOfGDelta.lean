/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.Polish
import InfinitaryLogic.Descriptive.SatisfactionBorel
import InfinitaryLogic.Descriptive.GDeltaPolish

/-!
# A Gδ set of coded models is Polish in the inherited topology

For a countable relational language `L` and a sentence `φ` whose coded model set
`ModelsOf φ ⊆ StructureSpace L` is Gδ, that set is a Polish space in the topology it **inherits**
from the code space (`polishSpace_modelsOf_of_isGδ`, from `IsGδ.polishSpace`).  This is
**conditional on the Gδ hypothesis**: not every sentence has a Gδ model set (see below).

The existing `modelsOf_standardBorel` already equips every model set with the **inherited
measurable structure** as a standard Borel space, obtained by refining the topology of the code
space.  What is new is Polishness of the **inherited topology** itself, in which the atomic
conditions are clopen and convergence of codes is convergence of each relation on each tuple.
The two are not compared here, and nothing is said about isomorphism classes, the logic action,
or orbits.

Closure lemmas make the hypothesis dischargeable clause by clause: `modelsOf_inf`,
`modelsOf_inf_isGδ`, `modelsOf_iInf`, `modelsOf_iInf_isGδ` (and the `einf` forms over an
encodable index).  They need no countability of the language; only the Polish corollary does,
through the instance `PolishSpace (StructureSpace L)`.

**The hypothesis is not automatic.**  In the language of one unary relation `P`, the sentence
"only finitely many elements satisfy `P`" has as coded models the codes with finitely many `P`-true
elements.  That set is countable and dense in the code space, a perfect Polish space, so by the
Baire category theorem it is not Gδ.  The regression guard records this example.
-/

namespace FirstOrder.Language

open scoped Lomega1omega

universe u v

variable {L : Language.{u, v}} [L.IsRelational]

/-- If the coded models of a sentence form a Gδ set, they form a Polish space in the subspace
topology of the code space. -/
theorem polishSpace_modelsOf_of_isGδ [Countable (Σ l, L.Relations l)] {φ : L.Sentenceω}
    (h : IsGδ (ModelsOf φ)) : PolishSpace ↥(ModelsOf φ) :=
  h.polishSpace

/-- The coded models of a conjunction are the intersection. -/
theorem modelsOf_inf (φ ψ : L.Sentenceω) : ModelsOf (φ ⊓ ψ) = ModelsOf φ ∩ ModelsOf ψ :=
  Set.ext fun c => @BoundedFormulaω.realize_inf L ℕ c.toStructure Empty 0 Empty.elim
    Fin.elim0 φ ψ

/-- Finite conjunction preserves the Gδ property of the coded model set. -/
theorem modelsOf_inf_isGδ {φ ψ : L.Sentenceω} (hφ : IsGδ (ModelsOf φ))
    (hψ : IsGδ (ModelsOf ψ)) : IsGδ (ModelsOf (φ ⊓ ψ)) := by
  rw [modelsOf_inf]
  exact hφ.inter hψ

/-- The coded models of a countable conjunction are the intersection. -/
theorem modelsOf_iInf (φs : ℕ → L.Sentenceω) :
    ModelsOf (BoundedFormulaω.iInf φs) = ⋂ n, ModelsOf (φs n) := by
  ext c
  simp only [Set.mem_iInter]
  exact @BoundedFormulaω.realize_iInf L ℕ c.toStructure Empty 0 Empty.elim Fin.elim0 φs

/-- Countable conjunction preserves the Gδ property of the coded model set. -/
theorem modelsOf_iInf_isGδ {φs : ℕ → L.Sentenceω} (h : ∀ n, IsGδ (ModelsOf (φs n))) :
    IsGδ (ModelsOf (BoundedFormulaω.iInf φs)) := by
  rw [modelsOf_iInf]
  exact IsGδ.iInter h

/-- The coded models of an encodable-indexed conjunction are the intersection. -/
theorem modelsOf_einf {ι : Type*} [Encodable ι] (φs : ι → L.Sentenceω) :
    ModelsOf (BoundedFormulaω.einf φs) = ⋂ i, ModelsOf (φs i) := by
  ext c
  simp only [Set.mem_iInter]
  exact @BoundedFormulaω.realize_einf L ℕ c.toStructure Empty 0 Empty.elim Fin.elim0 ι _ φs

/-- Encodable-indexed conjunction preserves the Gδ property of the coded model set. -/
theorem modelsOf_einf_isGδ {ι : Type*} [Encodable ι] {φs : ι → L.Sentenceω}
    (h : ∀ i, IsGδ (ModelsOf (φs i))) : IsGδ (ModelsOf (BoundedFormulaω.einf φs)) := by
  rw [modelsOf_einf]
  exact IsGδ.iInter h

end FirstOrder.Language
