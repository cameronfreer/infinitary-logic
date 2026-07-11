/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.SatisfactionBorel
import InfinitaryLogic.Lomega1omega.Theory

/-!
# López-Escobar, the easy direction

Every `L_ω₁ω`-sentence defines an ISOMORPHISM-INVARIANT BOREL class of coded countable
structures. Both halves were already in the tree — Borel-ness is `modelsOf_measurableSet`
(formula induction on the standard Borel `StructureSpace L`), and invariance is a corollary of
`BoundedFormulaω.realize_equiv` read through the decoding — this file packages them as the
named literature statement (`lopezEscobar_easy`). Invariance is stated in the
isomorphism-closed form (an `L`-isomorphism of the decoded structures transports membership),
which for this purpose is equivalent to invariance under the logic action.

The hard converse — every isomorphism-invariant Borel class is `L_ω₁ω`-definable, via Vaught
transforms — is issue #10.
-/

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]

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

/-- **López-Escobar, easy direction**: every `L_ω₁ω`-sentence defines an
isomorphism-invariant Borel class of coded countable structures. (The converse — invariant
Borel classes are `L_ω₁ω`-definable — is the López-Escobar theorem proper, issue #10.) -/
theorem lopezEscobar_easy (φ : L.Sentenceω) :
    MeasurableSet (ModelsOf φ) ∧
      ∀ c d : StructureSpace L,
        Nonempty (@Language.Equiv L ℕ ℕ c.toStructure d.toStructure) →
        (c ∈ ModelsOf φ ↔ d ∈ ModelsOf φ) :=
  ⟨modelsOf_measurableSet φ, fun _ _ ⟨e⟩ => modelsOf_mem_iff_of_equiv φ e⟩

end Language

end FirstOrder
