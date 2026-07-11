/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.SatisfactionBorel
import InfinitaryLogic.Lomega1omega.Theory

/-!
# López-Escobar, the easy direction

For arbitrary relational vocabularies the model class of an `L_ω₁ω`-sentence is
PRODUCT-MEASURABLE and ISOMORPHISM-INVARIANT (`modelsOf_measurable_invariant`); for countable
relational vocabularies — where the repository's `BorelSpace`/`StandardBorelSpace
(StructureSpace L)` instances apply — this is an invariant BOREL subset of the standard Borel
structure space (`lopezEscobar_easy`, the literature statement).

Invariance is the named isomorphism-closed predicate `IsomorphismInvariant` (an
`L`-isomorphism of the decoded structures transports membership) — equivalent, for this
purpose, to invariance under the logic action; an `Equiv.Perm ℕ`-action formulation can be
added later as an optional descriptive-set-theoretic lemma, and is not needed by the planned
proof of the converse.

The hard converse — every isomorphism-invariant Borel class is `L_ω₁ω`-definable, by Marker's
route through Craig interpolation and PC-separation — is issue #10.
-/

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]

/-- **Isomorphism invariance** of a class of coded structures, in isomorphism-closed form: an
`L`-isomorphism of the decoded structures transports membership. -/
def IsomorphismInvariant (B : Set (StructureSpace L)) : Prop :=
  ∀ c d : StructureSpace L,
    Nonempty (@Language.Equiv L ℕ ℕ c.toStructure d.toStructure) → (c ∈ B ↔ d ∈ B)

/-- Membership in a sentence's model class is isomorphism-invariant: an `L`-isomorphism of the
decoded structures transports satisfaction. -/
theorem modelsOf_mem_iff_of_equiv (φ : L.Sentenceω) {c d : StructureSpace L}
    (e : @Language.Equiv L ℕ ℕ c.toStructure d.toStructure) :
    c ∈ ModelsOf φ ↔ d ∈ ModelsOf φ := by
  letI : L.Structure ℕ := c.toStructure
  show @BoundedFormulaω.Realize L ℕ c.toStructure Empty 0 φ Empty.elim Fin.elim0
    ↔ @BoundedFormulaω.Realize L ℕ d.toStructure Empty 0 φ Empty.elim Fin.elim0
  have h := @BoundedFormulaω.realize_equiv L ℕ ℕ c.toStructure d.toStructure e Empty 0 φ
    Empty.elim Fin.elim0
  rwa [show (⇑e ∘ Empty.elim : Empty → ℕ) = Empty.elim from funext fun x => x.elim,
    show (⇑e ∘ Fin.elim0 : Fin 0 → ℕ) = Fin.elim0 from funext fun i => i.elim0] at h

theorem isomorphismInvariant_modelsOf (φ : L.Sentenceω) :
    IsomorphismInvariant (ModelsOf φ) :=
  fun _ _ ⟨e⟩ => modelsOf_mem_iff_of_equiv φ e

/-- **The general form** (arbitrary relational vocabularies): the model class of a sentence is
product-measurable and isomorphism-invariant. -/
theorem modelsOf_measurable_invariant (φ : L.Sentenceω) :
    MeasurableSet (ModelsOf φ) ∧ IsomorphismInvariant (ModelsOf φ) :=
  ⟨modelsOf_measurableSet φ, isomorphismInvariant_modelsOf φ⟩

variable [Countable (Σ l, L.Relations l)]

set_option linter.unusedSectionVars false in
/-- **López-Escobar, easy direction** (countable relational vocabularies): every
`L_ω₁ω`-sentence defines an isomorphism-invariant BOREL class of coded countable structures —
here `MeasurableSet` is Borel for the Polish topology, by the `BorelSpace (StructureSpace L)`
instance, which is what the countable-relations hypothesis activates. (The converse —
invariant Borel classes are `L_ω₁ω`-definable — is issue #10.) -/
@[blueprint "thm:lopez-escobar-easy"
  (title := /-- López-Escobar, easy direction -/)
  (statement := /-- Over a countable relational vocabulary, the class of coded countable
    models of an $\Lomegaone$-sentence is an isomorphism-invariant Borel subset of the
    standard Borel space of structures. -/)
  (proof := /-- Measurability is formula induction on the standard Borel structure space
    (the satisfaction-measurability theorem); invariance is transport of realization along an
    isomorphism of the decoded structures. -/)
  (uses := ["thm:satisfaction-borel"])]
theorem lopezEscobar_easy (φ : L.Sentenceω) :
    MeasurableSet (ModelsOf φ) ∧ IsomorphismInvariant (ModelsOf φ) :=
  modelsOf_measurable_invariant φ

end Language

end FirstOrder
