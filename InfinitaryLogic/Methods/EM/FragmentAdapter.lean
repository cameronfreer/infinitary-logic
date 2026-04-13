/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Methods.EM.Realization
import InfinitaryLogic.Admissible.Compactness
import InfinitaryLogic.Admissible.Barwise.ConsistencyBridge
import InfinitaryLogic.Admissible.WithConstants

/-!
# EM Realization: Admissible/Barwise Adapter Layer

This file contains the theorems that connect the EM template-theory machinery
(from `Realization.lean`) to the admissible-fragment infrastructure. These are
the `_of_fragment`, `_of_fullFragment`, and `_of_compact` endpoints that take
`AdmissibleFragment`, `FullBarwiseFragment`, or bare compactness hypotheses.

Separated from `Realization.lean` so that the `Countable` import bundle can
import the core EM machinery without transitively pulling in admissible-fragment
infrastructure. The adapter layer lives in the `Admissible` bundle instead.
-/

universe u v w

namespace FirstOrder.Language

variable {L : Language.{u, v}}

/-! ### Model of `templateTheoryOn` via Barwise compactness -/

/-- Abstract Barwise wrapper for the restricted template theory. -/
theorem Lomega1omegaTemplate.templateTheoryOn_model_of_fragment
    (T : Lomega1omegaTemplate L)
    (Γ : Set (Σ n, L.BoundedFormulaω Empty n))
    {J : Type u} [LinearOrder J]
    (A : AdmissibleFragment L[[J]])
    (hSub : T.templateTheoryOn Γ J ⊆ A.formulas)
    (hfin : ∀ F : Set L[[J]].Sentenceω, F.Finite → F ⊆ T.templateTheoryOn Γ J →
      ∃ (N : Type) (_ : L[[J]].Structure N), Theoryω.Model F N) :
    ∃ (N : Type) (_ : L[[J]].Structure N),
      Theoryω.Model (T.templateTheoryOn Γ J) N := by
  apply barwise_compactness A hSub
  rintro F ⟨_, hFfinite⟩ hFsub
  exact hfin F hFfinite hFsub

/-- Indiscernible specialization of `templateTheoryOn_model_of_fragment`. -/
theorem IsLomega1omegaIndiscernible.templateTheoryOn_model_of_fragment
    {I : Type w} [LinearOrder I] [Infinite I]
    {M : Type} [L.Structure M] {a : I → M}
    (h : IsLomega1omegaIndiscernible (L := L) a)
    {J : Type u} [LinearOrder J]
    (Γ : Set (Σ n, L.BoundedFormulaω Empty n))
    (A : AdmissibleFragment L[[J]])
    (hSub : h.template.templateTheoryOn Γ J ⊆ A.formulas) :
    ∃ (N : Type) (_ : L[[J]].Structure N),
      Theoryω.Model (h.template.templateTheoryOn Γ J) N := by
  apply h.template.templateTheoryOn_model_of_fragment Γ A hSub
  intro F hFfinite hFsub
  obtain ⟨σ, hσ⟩ := h.templateTheoryOn_finitelySatisfiable Γ hFfinite hFsub
  letI : (constantsOn J).Structure M := constantsOn.structure σ
  exact ⟨M, inferInstance, hσ⟩

/-! ### Sequence-indexed adapter wrappers -/

namespace Lomega1omegaTemplate

variable {J : Type u} [LinearOrder J]

/-- Abstract Barwise wrapper for `templateTheoryOfSeq`. -/
theorem templateTheoryOfSeq_model_of_fragment
    (T : Lomega1omegaTemplate L)
    (s : ℕ → Σ n, L.BoundedFormulaω Empty n)
    (A : AdmissibleFragment L[[J]])
    (hSub : T.templateTheoryOfSeq s J ⊆ A.formulas)
    (hfin : ∀ F : Set L[[J]].Sentenceω, F.Finite → F ⊆ T.templateTheoryOfSeq s J →
      ∃ (N : Type) (_ : L[[J]].Structure N), Theoryω.Model F N) :
    ∃ (N : Type) (_ : L[[J]].Structure N),
      Theoryω.Model (T.templateTheoryOfSeq s J) N :=
  T.templateTheoryOn_model_of_fragment (Set.range s) A hSub hfin

/-- Full-Barwise-fragment specialization. -/
theorem templateTheoryOfSeq_model_of_fullFragment
    (T : Lomega1omegaTemplate L)
    (s : ℕ → Σ n, L.BoundedFormulaω Empty n)
    (B : FullBarwiseFragment L[[J]])
    (hfin : ∀ F : Set L[[J]].Sentenceω, F.Finite → F ⊆ T.templateTheoryOfSeq s J →
      ∃ (N : Type) (_ : L[[J]].Structure N), Theoryω.Model F N) :
    ∃ (N : Type) (_ : L[[J]].Structure N),
      Theoryω.Model (T.templateTheoryOfSeq s J) N :=
  T.templateTheoryOfSeq_model_of_fragment s B.toAdmissibleFragment
    (fun σ _ => B.complete σ) hfin

end Lomega1omegaTemplate

/-- Sequence-indexed model_of_fragment for indiscernible source. -/
theorem IsLomega1omegaIndiscernible.templateTheoryOfSeq_model_of_fragment
    {I : Type w} [LinearOrder I] [Infinite I]
    {M : Type} [L.Structure M] {a : I → M}
    (h : IsLomega1omegaIndiscernible (L := L) a)
    {J : Type u} [LinearOrder J]
    (s : ℕ → Σ n, L.BoundedFormulaω Empty n)
    (A : AdmissibleFragment L[[J]])
    (hSub : h.template.templateTheoryOfSeq s J ⊆ A.formulas) :
    ∃ (N : Type) (_ : L[[J]].Structure N),
      Theoryω.Model (h.template.templateTheoryOfSeq s J) N :=
  h.templateTheoryOn_model_of_fragment (Set.range s) A hSub

/-- Caller-ready EM-realization from a full Barwise fragment. -/
theorem IsLomega1omegaIndiscernible.templateTheoryOfSeq_model_of_fullFragment
    {I : Type w} [LinearOrder I] [Infinite I]
    {M : Type} [L.Structure M] {a : I → M}
    (h : IsLomega1omegaIndiscernible (L := L) a)
    {J : Type u} [LinearOrder J]
    (s : ℕ → Σ n, L.BoundedFormulaω Empty n)
    (B : FullBarwiseFragment L[[J]]) :
    ∃ (N : Type) (_ : L[[J]].Structure N),
      Theoryω.Model (h.template.templateTheoryOfSeq s J) N := by
  apply h.template.templateTheoryOfSeq_model_of_fullFragment s B
  intro F hFfinite hFsub
  obtain ⟨σ, hσ⟩ := h.templateTheoryOfSeq_finitelySatisfiable s hFfinite hFsub
  letI : (constantsOn J).Structure M := constantsOn.structure σ
  exact ⟨M, inferInstance, hσ⟩

/-- EM realization from a bare compactness hypothesis. -/
theorem IsLomega1omegaIndiscernible.templateTheoryOfSeq_model_of_compact
    {I : Type w} [LinearOrder I] [Infinite I]
    {M : Type} [L.Structure M] {a : I → M}
    (h : IsLomega1omegaIndiscernible (L := L) a)
    {J : Type u} [LinearOrder J]
    (s : ℕ → Σ n, L.BoundedFormulaω Empty n)
    (height : Ordinal) (h_height : Ordinal.omega0 < height)
    (hCompact : ∀ S : Set L[[J]].Sentenceω,
      (∀ F : Set L[[J]].Sentenceω, F.Finite → F ⊆ S →
        ∃ (N : Type) (_ : L[[J]].Structure N), Theoryω.Model F N) →
      ∃ (N : Type) (_ : L[[J]].Structure N), Theoryω.Model S N) :
    ∃ (N : Type) (_ : L[[J]].Structure N),
      Theoryω.Model (h.template.templateTheoryOfSeq s J) N := by
  apply h.template.templateTheoryOfSeq_model_of_fragment s
    (admissibleFragmentOfUniv height h_height hCompact)
    (Set.subset_univ _)
  intro F hFfinite hFsub
  obtain ⟨σ, hσ⟩ := h.templateTheoryOfSeq_finitelySatisfiable s hFfinite hFsub
  letI : (constantsOn J).Structure M := constantsOn.structure σ
  exact ⟨M, inferInstance, hσ⟩

end FirstOrder.Language
