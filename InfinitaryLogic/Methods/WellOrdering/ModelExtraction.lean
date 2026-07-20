/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Methods.WellOrdering.WOConsistency
import InfinitaryLogic.Methods.Interpolation.QuotientTruthLemma

/-!
# Model extraction from the completed well-ordering set (issue #12, step 5)

The completion endpoint hands step 5 a Henkin-complete `S` containing the base diagram
`Bφ = {φ̂} ∪ {d_q < d_r : q < r}` opaquely; the quotient term model of the forward truth
lemma then realizes every member of `S`, hence every member of `Bφ`.

This file is the **relational/countable** extraction: `[L.IsRelational]` is consumed by the
quotient term model (the relational-core collapse of closed terms to constants), and
`[Countable (Σ l, L.Relations l)]` by the fair enumeration.  Removing both restrictions is
the later transport step, not done here.
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}} (φ : L.Sentenceω) (lt : L.Relations 2)

/-- **Model extraction** (relational/countable form): under the well-ordered-chains
hypothesis, some nonempty `L[[ℕ]]`-structure realizes every member of the base diagram —
the lifted root and the full positive rational diagram.  Composition of the completion
endpoint with the forward-truth-lemma model existence theorem; the Henkin-complete set is
consumed opaquely. -/
theorem exists_model_baseDiagram [L.IsRelational] [Countable (Σ l, L.Relations l)]
    (h : HasWellOrderedChains φ lt) :
    ∃ (M : Type) (_ : L[[ℕ]].Structure M) (_ : Nonempty M),
      ∀ χ ∈ baseDiagram φ lt, Sentenceω.Realize χ M := by
  obtain ⟨S, hsub, hcomp⟩ := exists_henkinComplete_baseDiagram φ lt h
  obtain ⟨M, instM, hne, hpos, -⟩ := exists_model_of_henkinComplete hcomp
  exact ⟨M, instM, hne, fun χ hχ => hpos χ (hsub hχ)⟩

end FirstOrder.Language
