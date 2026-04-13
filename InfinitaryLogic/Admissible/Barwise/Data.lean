/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Admissible.Fragment.Core

/-!
# Barwise Compactness Data

This file defines `BarwiseCompactnessData`, the literature-faithful interface
for the Barwise compactness theorem (Theorem 3.1.3 of [KK04], Theorem 5.6
of [Bar75]). Unlike the project's existing `FiniteCompactFragment.compact` field
(which demands unrestricted finite-subset compactness on arbitrary theories),
this structure uses:

- **A-coded subtheories** via a `Code` type with a `decode` map, capturing the
  standard notion "T₀ ∈ A" (subtheories that are elements of the admissible
  set) without requiring a full formalization of KP set theory.
- **Σ₁-on-A definability** as a predicate on theories, restricting compactness
  to the Σ₁-definable theories (rather than all theories in the fragment).

## Design Notes

The standard Barwise compactness theorem:
> Let A be a countable admissible set. If Γ is Σ₁-on-A and Γ ⊆ L_A, and
> every T₀ ∈ A with T₀ ⊆ Γ has a model, then Γ has a model.

The key internality: "T₀ ∈ A" means the subtheory is literally an element of
the admissible set, not just an externally-finite subset. This internality is
what lets the proof use Σ-reflection and Δ₀-separation inside A. A bare
`isAFinite : Set Sentenceω → Prop` predicate would lose that structure; hence
we use a `Code` type with `decode`.

The `barwiseHeight` field represents o(A), the ordinal of the admissible set.
No lower bound is imposed: the case o(A) = ω (A = HF, hereditarily finite sets)
is the structurally important case where A-coded = finite and L_A = first-order
logic (classical compactness as a special case of Barwise compactness).
(`AdmissibleFragmentCore.height` likewise carries no lower bound.)

The `isSigma1` predicate is currently abstract (Prop-valued). A future
refinement could carry witness data (the Σ formula defining the theory in
(A, ∈)), but that would require formalizing the Σ/Δ₀ formula hierarchy for
the ∈-language, which is a separate substantial project.

## References

- [KK04] Keisler–Knight, "Barwise: Infinitary Logic and Admissible Sets" (2004)
- [Bar75] Barwise, *Admissible Sets and Structures* (1975), Ch. III, V
- [Bar69] Barwise, "Infinitary Logic and Admissible Sets" (JSL 1969)
-/

universe u v

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

/-- The data for a literature-faithful statement of the Barwise compactness
theorem. Extends `AdmissibleFragmentCore` with A-coded subtheories and
Σ₁-on-A definability.

The `Code` type represents elements of the admissible set A that are sets of
sentences (the "A-coded subtheories" / "A-finite subtheories"). The `decode`
map sends a code to its actual set of sentences. The `compact` field then
says: if Γ is Σ₁-on-A and every A-coded subtheory of Γ has a model, then Γ
has a model. -/
structure BarwiseCompactnessData (L : Language.{u, v})
    extends AdmissibleFragmentCore L where
  /-- Type of codes for subtheories in A (the "A-coded" / "A-finite" sets). -/
  Code : Type
  /-- Decode a code to the set of sentences it represents. -/
  decode : Code → Set L.Sentenceω
  /-- Every decoded set is contained in the fragment. -/
  decode_sub_formulas : ∀ c, decode c ⊆ formulas
  /-- The ordinal height o(A) of the admissible set. No lower bound is
  imposed: o(A) = ω (the HF case) is the structurally important special
  case where A-coded = finite and L_A = first-order logic. -/
  barwiseHeight : Ordinal
  /-- Every finite subset of the fragment has an A-code. This holds for all
  admissible sets A ⊇ ω (including HF, L(ω₁^CK), etc.). -/
  finite_has_code : ∀ S, S.Finite → S ⊆ formulas → ∃ c, decode c = S
  /-- Sigma-1-on-A definability predicate for theories. A set of sentences is
  Sigma-1-on-A if it is definable in (A, membership) by a Sigma formula.
  Currently abstract (Prop-valued); a future refinement could carry the
  defining Sigma formula as witness data. -/
  isSigma1 : Set L.Sentenceω → Prop
  /-- **Barwise compactness**: for Σ₁-on-A theories contained in the fragment,
  if every A-coded subtheory has a model, then the whole theory has a model.
  This is the standard Barwise compactness theorem (Thm 3.1.3, [KK04];
  Thm 5.6, [Bar75]). -/
  compact : ∀ Γ, isSigma1 Γ → Γ ⊆ formulas →
    (∀ c : Code, decode c ⊆ Γ →
      ∃ (M : Type) (_ : L.Structure M), Theoryω.Model (decode c) M) →
    ∃ (M : Type) (_ : L.Structure M), Theoryω.Model Γ M

/-- Barwise compactness theorem, stated as a standalone theorem using
`BarwiseCompactnessData`. -/
theorem barwise_compactness_of_data (B : BarwiseCompactnessData L)
    {Γ : Set L.Sentenceω} (hSigma : B.isSigma1 Γ) (hΓ : Γ ⊆ B.formulas)
    (hfin : ∀ c : B.Code, B.decode c ⊆ Γ →
      ∃ (M : Type) (_ : L.Structure M), Theoryω.Model (B.decode c) M) :
    ∃ (M : Type) (_ : L.Structure M), Theoryω.Model Γ M :=
  B.compact Γ hSigma hΓ hfin

end Language

end FirstOrder
