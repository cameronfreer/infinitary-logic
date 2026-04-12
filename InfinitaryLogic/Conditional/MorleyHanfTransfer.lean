/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.Hanf

/-!
# Morley-Hanf Transfer Hypothesis (Conditional)

This file isolates the deep combinatorial transfer hypothesis needed for the
Morley-Hanf theorem. The hypothesis encapsulates Erdős-Rado extraction +
Ehrenfeucht-Mostowski stretching, which require infrastructure not currently
formalized in Lean or Mathlib.

## Conditional Status

`MorleyHanfTransfer` is a `Prop`-valued definition, not a theorem. The
conditional theorem `morley_hanf_of_transfer` takes it as a hypothesis.
Both are placed in `Conditional/` to make the external dependency visible.

## References

- [Mar16], §5
- [KK04], §1.6
-/

universe u v

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

open FirstOrder Structure

/-- **Deep set-theoretic/model-theoretic transfer hypothesis** for the Morley-Hanf theorem.

This encapsulates the combined content of:
1. **Erdős-Rado extraction**: Models of size ≥ ℶ_{ω₁} in a countable language
   contain Lω₁ω-indiscernible sequences of uncountable length.
2. **Ehrenfeucht-Mostowski stretching**: Such indiscernible sequences can be
   stretched to produce models of arbitrary size satisfying the same Lω₁ω sentences.

These deep combinatorial arguments (Ramsey/partition calculus + EM functors)
require infrastructure not currently formalized in Lean or Mathlib.

See [Mar16], §5; [KK04], §1.6. -/
def MorleyHanfTransfer (L : Language.{u, v}) [Countable (Σ l, L.Relations l)] : Prop :=
  ∀ (φ : L.Sentenceω) (M : Type) [L.Structure M],
    Sentenceω.Realize φ M → Cardinal.mk M ≥ Cardinal.beth (Ordinal.omega 1) →
    HasArbLargeModels φ

/-- **Morley-Hanf Theorem** (conditional on transfer hypothesis).

For a countable language, the Hanf number of any Lω₁ω sentence is bounded
by ℶ_ω₁ (the ω₁-th beth number), assuming the deep combinatorial transfer
principle `MorleyHanfTransfer`.

The unconditional version requires formalizing Erdős-Rado partition calculus
and Ehrenfeucht-Mostowski functors for Lω₁ω, which are not currently available
in Lean or Mathlib.

**Boundary**: The hypothesis `htransfer` captures exactly the deep
set-theoretic/model-theoretic transfer step. All other reasoning is formalized. -/
@[blueprint "thm:morley-hanf"
  (title := /-- Morley-Hanf bound -/)
  (statement := /-- Conditional on the Morley-Hanf transfer hypothesis,
    $\beth_{\omegaone}$ is a Hanf bound for every $\Lomegaone$ sentence. -/)
  (proof := /-- Given a model of size $\geq \beth_{\omegaone}$, the transfer
    hypothesis directly yields arbitrarily large models. -/)
  (uses := ["def:hanf-bound", "def:arb-large-models"])]
theorem morley_hanf_of_transfer [Countable (Σ l, L.Relations l)]
    (htransfer : MorleyHanfTransfer L) (φ : L.Sentenceω) :
    IsHanfBound φ (Cardinal.beth (Ordinal.omega 1)) := by
  intro ⟨M, hStr, hφ, hsize⟩
  exact htransfer φ M hφ hsize

end Language

end FirstOrder
