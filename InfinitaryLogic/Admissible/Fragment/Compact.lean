/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Admissible.Fragment.Core
import Architect

/-!
# Admissible Fragment with Compact Field

Extends `AdmissibleFragmentCore` with a finite-subset compactness axiom.
This is the HF-style compactness principle (stronger than the standard
Barwise theorem). See `BarwiseCompactnessData` for the literature-faithful
version.

Retained for backward compatibility with existing consumers.
-/

universe u v

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

open FirstOrder Structure Ordinal

/-- An abstract admissible fragment of Lω₁ω, extending `AdmissibleFragmentCore`
with a finite-subset compactness axiom.

**Important**: the `compact` field uses ordinary finite satisfiability, which
matches the Barwise compactness theorem only for the case A = HF (hereditarily
finite sets, i.e., first-order logic). For Lω₁ω with a general admissible set,
the standard Barwise theorem restricts to Σ₁-on-A theories with A-finite
subsets (where "A-finite" = ∈ A, not ordinary finiteness). See
`BarwiseCompactnessData` for the literature-faithful version.

This structure is retained for backward compatibility with existing consumers
(`barwise_compactness`, `ConsistencyBridge`, `EMRealization`). -/
@[blueprint "def:admissible-fragment"
  (title := /-- Admissible fragment -/)
  (statement := /-- An admissible fragment of $\Lomegaone$: a collection of sentences
    closed under subformulas, negation, quantification, and countable conjunction/disjunction,
    with a compactness axiom for finite subsets. -/)]
structure FiniteCompactFragment (L : Language.{u, v}) extends AdmissibleFragmentCore L where
  /-- The height is > ω. This constraint is specific to the legacy compact
  wrapper (not imposed by `AdmissibleFragmentCore`). It excludes the HF case
  but is needed by some downstream consumers (e.g., `admissibleFragmentOfUniv`). -/
  height_gt_omega : Ordinal.omega0 < height
  /-- **Finite-subset compactness** (stronger than the standard Barwise theorem).
  If every finite subset of S ⊆ formulas has a model, then S has a model.
  This is the HF-style compactness principle; the standard Barwise compactness
  restricts to Σ₁-on-A theories and A-finite subsets. -/
  compact : ∀ S ⊆ formulas,
    (∀ F, F ⊆ formulas → F.Finite → F ⊆ S →
      ∃ (M : Type) (_ : L.Structure M), Theoryω.Model F M) →
    ∃ (M : Type) (_ : L.Structure M), Theoryω.Model S M

/-- A set of sentences is A-finite (finite and contained in the fragment).

**Note**: this uses ordinary finiteness, matching the HF case. For the standard
Barwise notion "T₀ ∈ A" (which includes hyperarithmetical sets for
A = L(ω₁^CK)), see `BarwiseCompactnessData.isAFinite`. -/
def FiniteCompactFragment.AFinite (A : FiniteCompactFragment L) (S : Set L.Sentenceω) : Prop :=
  S ⊆ A.formulas ∧ S.Finite

end Language

end FirstOrder
