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
`FiniteCompactFragment`, `FullBarwiseFragment`, or bare compactness hypotheses.

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
    (A : FiniteCompactFragment L[[J]])
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
    (A : FiniteCompactFragment L[[J]])
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
    (A : FiniteCompactFragment L[[J]])
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
  T.templateTheoryOfSeq_model_of_fragment s B.toFiniteCompactFragment
    (fun σ _ => B.complete σ) hfin

end Lomega1omegaTemplate

/-- Sequence-indexed model_of_fragment for indiscernible source. -/
theorem IsLomega1omegaIndiscernible.templateTheoryOfSeq_model_of_fragment
    {I : Type w} [LinearOrder I] [Infinite I]
    {M : Type} [L.Structure M] {a : I → M}
    (h : IsLomega1omegaIndiscernible (L := L) a)
    {J : Type u} [LinearOrder J]
    (s : ℕ → Σ n, L.BoundedFormulaω Empty n)
    (A : FiniteCompactFragment L[[J]])
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

/-! ### Stretching along a countable target order

These theorems package the existing `templateTheoryOfSeq` pipeline into
caller-ready form: from an indiscernible template they produce a target
`L[[J]]`-structure `N` whose constants satisfy the template on formulas in
`Set.range s` (the countable family named by the enumeration `s`).

Two forms are provided:

  - `stretch_restricted_of_fullFragment` / `_of_compact` use
    `Sentenceω.Realize (templateSentence φ t) N` as the conclusion — this is
    the form the template theory literally delivers.
  - `stretch_restricted_sequence_of_fullFragment` / `_of_compact` produce an
    explicit `b : J → N` sequence and conclude
    `φ.Realize Empty.elim (b ∘ t) ↔ h.template.truth φ`, via the bridge
    `realize_templateSentence_of_structure`.

**Scope**: these theorems do NOT claim full `IsLomega1omegaIndiscernible` for
any extracted sequence — that would require enumerating all Lω₁ω formulas,
which is not currently formalized. They also do NOT narrow the conditional
boundary of `MorleyHanfTransfer`, which needs stretching along uncountable
target orders. -/

/-- **EM stretching along a countable target order (full Barwise fragment).**

Given an Lω₁ω-indiscernible sequence `a : I → M` over an infinite linear order
`I`, a formula enumeration `s : ℕ → Σ n, L.BoundedFormulaω Empty n`, and a
countable target order `J` with a full Barwise fragment for `L[[J]]`, there
exists a target `L[[J]]`-structure `N` such that for every index `i : ℕ` and
every strictly-increasing tuple `t : Fin (s i).1 ↪o J`, the realization of
`templateSentence (s i).2 t` in `N` matches the truth value of `(s i).2` in
the source template.

The conclusion is quantified over `i : ℕ` (equivalently, over formulas in
`Set.range s`) — this is restricted indiscernibility. Full Lω₁ω-indiscernibility
of the `J`-indexed constants would additionally require a countable enumeration
of all Lω₁ω formulas. -/
@[blueprint "thm:em-stretch-countable"
  (title := /-- EM stretching along a countable target order -/)
  (statement := /-- From an Lω₁ω-indiscernible sequence and a countable formula
    family $s$, the restricted template theory has a model in any countable
    target order $J$; the constant interpretations satisfy the template on
    formulas in $\operatorname{range}(s)$. -/)
  (proof := /-- Apply `templateTheoryOfSeq_model_of_fullFragment` to obtain the
    model, then read off the truth equivalence from the template theory's
    positive/negative sentences. -/)
  (uses := ["def:admissible-fragment"])]
theorem IsLomega1omegaIndiscernible.stretch_restricted_of_fullFragment
    {I : Type w} [LinearOrder I] [Infinite I]
    {M : Type} [L.Structure M] {a : I → M}
    (h : IsLomega1omegaIndiscernible (L := L) a)
    (s : ℕ → Σ n, L.BoundedFormulaω Empty n)
    {J : Type u} [LinearOrder J] [Countable J]
    (B : FullBarwiseFragment L[[J]]) :
    ∃ (N : Type) (_ : L[[J]].Structure N),
      ∀ (i : ℕ) (t : Fin (s i).1 ↪o J),
        Sentenceω.Realize (Lomega1omegaTemplate.templateSentence (s i).2 t) N ↔
          h.template.truth (s i).2 := by
  obtain ⟨N, _, hModel⟩ := h.templateTheoryOfSeq_model_of_fullFragment s B
  refine ⟨N, inferInstance, ?_⟩
  intro i t
  have hmem : ⟨(s i).1, (s i).2⟩ ∈ Set.range s := ⟨i, rfl⟩
  by_cases htruth : h.template.truth (s i).2
  · refine ⟨fun _ => htruth, fun _ => ?_⟩
    exact hModel _ ⟨(s i).1, (s i).2, t, hmem, Or.inl ⟨htruth, rfl⟩⟩
  · refine ⟨fun hreal => ?_, fun hT => absurd hT htruth⟩
    exact absurd hreal
      (hModel _ ⟨(s i).1, (s i).2, t, hmem, Or.inr ⟨htruth, rfl⟩⟩)

/-- **Generalized `realize_templateSentence`.**

Like `realize_templateSentence` (`InfinitaryLogic/Methods/EM/Realization.lean:97`),
but takes an arbitrary `[L[[J]].Structure N]` instead of requiring the
`L[[J]]`-structure to be built from a specific `σ : J → M` via
`constantsOn.structure σ`. The `L`-structure on `N` is derived from the
`L[[J]]`-structure via the canonical reduct along `lhomWithConstants L J`.

The right-hand side realizes `φ` on the sequence `fun i => b (t i)`, where
`b j` is the closed-term realization of the constant symbol `Sum.inr j`
(i.e., the interpretation of the `J`-indexed constant in the given
`L[[J]]`-structure on `N`). -/
theorem realize_templateSentence_of_structure
    {J : Type u} [LinearOrder J]
    {N : Type*} [L[[J]].Structure N]
    {n : ℕ} (φ : L.BoundedFormulaω Empty n) (t : Fin n ↪o J) :
    letI : L.Structure N := (L.lhomWithConstants J).reduct N
    Sentenceω.Realize (Lomega1omegaTemplate.templateSentence φ t) N ↔
      φ.Realize (Empty.elim : Empty → N)
        (fun i => (Term.func (Sum.inr (t i) : L[[J]].Functions 0)
            Fin.elim0 : L[[J]].Term Empty).realize (Empty.elim : Empty → N)) := by
  letI : L.Structure N := (L.lhomWithConstants J).reduct N
  haveI : (L.lhomWithConstants J).IsExpansionOn N := LHom.isExpansionOn_reduct _ _
  show BoundedFormulaω.Realize _ Empty.elim Fin.elim0 ↔ _
  rw [Lomega1omegaTemplate.templateSentence, BoundedFormulaω.realize_subst]
  exact (realize_openBounds _ _).trans
        (BoundedFormulaω.realize_mapLanguage _ _ _ _)

/-- **EM stretching along a countable target order — sequence form
(full Barwise fragment).**

Corollary of `stretch_restricted_of_fullFragment` via the bridge
`realize_templateSentence_of_structure`: produces an explicit `b : J → N`
sequence such that for every `i : ℕ` and every strictly-increasing tuple
`t : Fin (s i).1 ↪o J`, the realization of `(s i).2` on `b ∘ t` matches
`h.template.truth (s i).2`.

The sequence `b` is defined as the interpretation of the `J`-indexed constant
symbol under the `L[[J]]`-structure. The `L`-structure used for `.Realize` is
the reduct along `lhomWithConstants L J`, introduced via `letI` inside the
existential body. -/
theorem IsLomega1omegaIndiscernible.stretch_restricted_sequence_of_fullFragment
    {I : Type w} [LinearOrder I] [Infinite I]
    {M : Type} [L.Structure M] {a : I → M}
    (h : IsLomega1omegaIndiscernible (L := L) a)
    (s : ℕ → Σ n, L.BoundedFormulaω Empty n)
    {J : Type u} [LinearOrder J] [Countable J]
    (B : FullBarwiseFragment L[[J]]) :
    ∃ (N : Type) (_ : L[[J]].Structure N) (b : J → N),
      letI : L.Structure N := (L.lhomWithConstants J).reduct N
      ∀ (i : ℕ) (t : Fin (s i).1 ↪o J),
        ((s i).2).Realize (Empty.elim : Empty → N) (b ∘ t) ↔
          h.template.truth (s i).2 := by
  obtain ⟨N, _inst, hBase⟩ := h.stretch_restricted_of_fullFragment s B
  let b : J → N := fun j =>
    (Term.func (Sum.inr j : L[[J]].Functions 0) Fin.elim0 : L[[J]].Term Empty).realize
      (Empty.elim : Empty → N)
  refine ⟨N, inferInstance, b, ?_⟩
  letI : L.Structure N := (L.lhomWithConstants J).reduct N
  intro i t
  have hBridge :=
    realize_templateSentence_of_structure (L := L) (J := J) (N := N) (s i).2 t
  exact hBridge.symm.trans (hBase i t)

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

/-- **EM stretching along a countable target order (bare compactness oracle).**

Same content as `stretch_restricted_of_fullFragment`, but driven by a bare
compactness hypothesis on `L[[J]]` instead of a `FullBarwiseFragment`. -/
theorem IsLomega1omegaIndiscernible.stretch_restricted_of_compact
    {I : Type w} [LinearOrder I] [Infinite I]
    {M : Type} [L.Structure M] {a : I → M}
    (h : IsLomega1omegaIndiscernible (L := L) a)
    (s : ℕ → Σ n, L.BoundedFormulaω Empty n)
    {J : Type u} [LinearOrder J] [Countable J]
    (height : Ordinal) (h_height : Ordinal.omega0 < height)
    (hCompact : ∀ S : Set L[[J]].Sentenceω,
      (∀ F : Set L[[J]].Sentenceω, F.Finite → F ⊆ S →
        ∃ (N : Type) (_ : L[[J]].Structure N), Theoryω.Model F N) →
      ∃ (N : Type) (_ : L[[J]].Structure N), Theoryω.Model S N) :
    ∃ (N : Type) (_ : L[[J]].Structure N),
      ∀ (i : ℕ) (t : Fin (s i).1 ↪o J),
        Sentenceω.Realize (Lomega1omegaTemplate.templateSentence (s i).2 t) N ↔
          h.template.truth (s i).2 := by
  obtain ⟨N, _, hModel⟩ :=
    h.templateTheoryOfSeq_model_of_compact s height h_height hCompact
  refine ⟨N, inferInstance, ?_⟩
  intro i t
  have hmem : ⟨(s i).1, (s i).2⟩ ∈ Set.range s := ⟨i, rfl⟩
  by_cases htruth : h.template.truth (s i).2
  · refine ⟨fun _ => htruth, fun _ => ?_⟩
    exact hModel _ ⟨(s i).1, (s i).2, t, hmem, Or.inl ⟨htruth, rfl⟩⟩
  · refine ⟨fun hreal => ?_, fun hT => absurd hT htruth⟩
    exact absurd hreal
      (hModel _ ⟨(s i).1, (s i).2, t, hmem, Or.inr ⟨htruth, rfl⟩⟩)

/-- **EM stretching along a countable target order — sequence form
(bare compactness oracle).**

Compact-oracle variant of `stretch_restricted_sequence_of_fullFragment`. -/
theorem IsLomega1omegaIndiscernible.stretch_restricted_sequence_of_compact
    {I : Type w} [LinearOrder I] [Infinite I]
    {M : Type} [L.Structure M] {a : I → M}
    (h : IsLomega1omegaIndiscernible (L := L) a)
    (s : ℕ → Σ n, L.BoundedFormulaω Empty n)
    {J : Type u} [LinearOrder J] [Countable J]
    (height : Ordinal) (h_height : Ordinal.omega0 < height)
    (hCompact : ∀ S : Set L[[J]].Sentenceω,
      (∀ F : Set L[[J]].Sentenceω, F.Finite → F ⊆ S →
        ∃ (N : Type) (_ : L[[J]].Structure N), Theoryω.Model F N) →
      ∃ (N : Type) (_ : L[[J]].Structure N), Theoryω.Model S N) :
    ∃ (N : Type) (_ : L[[J]].Structure N) (b : J → N),
      letI : L.Structure N := (L.lhomWithConstants J).reduct N
      ∀ (i : ℕ) (t : Fin (s i).1 ↪o J),
        ((s i).2).Realize (Empty.elim : Empty → N) (b ∘ t) ↔
          h.template.truth (s i).2 := by
  obtain ⟨N, _inst, hBase⟩ :=
    h.stretch_restricted_of_compact s height h_height hCompact
  let b : J → N := fun j =>
    (Term.func (Sum.inr j : L[[J]].Functions 0) Fin.elim0 : L[[J]].Term Empty).realize
      (Empty.elim : Empty → N)
  refine ⟨N, inferInstance, b, ?_⟩
  letI : L.Structure N := (L.lhomWithConstants J).reduct N
  intro i t
  have hBridge :=
    realize_templateSentence_of_structure (L := L) (J := J) (N := N) (s i).2 t
  exact hBridge.symm.trans (hBase i t)

end FirstOrder.Language
