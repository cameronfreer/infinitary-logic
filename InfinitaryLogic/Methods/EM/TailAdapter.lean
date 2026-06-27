/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Methods.EM.FragmentAdapter

/-!
# Tail-indiscernibility: the eventually-form EM adapter

The EM stretching pipeline consumes source-side indiscernibility in exactly one place: the
finite-satisfiability lemma interprets the finitely many constants of a finite piece of the
template theory by a **freely chosen** strictly monotone tuple of the source sequence, and
collapses template truth to realization at that tuple. Consequently full indiscernibility
(all tuples agree) is more than is needed: it suffices that for each formula of the family
there is a cutoff beyond which all strictly monotone tuples agree — **tail
indiscernibility** — because the interpreting tuple may simply be chosen beyond the maximum
cutoff of the finitely many formulas involved.

This matters for Morley–Hanf: the classical Erdős–Rado extraction from a model of size
`≥ ℶ_ω₁` produces (per arity, after finitely many partition steps) exactly tail
indiscernibility of an ℕ-indexed sequence, while full simultaneous indiscernibility across
all arities is not what the classical argument yields in the source model. This file
weakens the EM interface accordingly:

* `IsLomega1omegaIndiscernibleOnTail a Γ` — per-formula cutoffs beyond which strictly
  monotone tuples agree (`ℕ`-indexed sequences);
* `tailTemplateOfSeq a` — the eventually-form template: a formula is true if all
  sufficiently deep strictly monotone tuples realize it;
* `tailTemplateOfSeq_truth_iff` — the truth collapse at any tuple beyond a cutoff;
* `IsLomega1omegaIndiscernibleOnTail.templateTheoryOn_finitelySatisfiable` — the deep-tuple
  finite-satisfiability lemma (mirroring the full-indiscernibility proof, with the
  interpreting embedding placed beyond the joint cutoff);
* `…templateTheoryOfSeq_model_of_compact`, `…stretch_restricted_of_compact`,
  `…stretch_restricted_sequence_of_compact` — the compact-oracle stretching pipeline,
  verbatim mirrors against the tail template.

The downstream consumer is `hasArbLargeModels_of_tail_extraction` in
`InfinitaryLogic/Conditional/MorleyHanfTransfer.lean`.
-/

universe u v

namespace FirstOrder.Language

open Lomega1omegaTemplate

variable {L : Language.{u, v}}

/-! ### Tail indiscernibility and the eventually-form template -/

section TailTemplate

variable {M : Type*} [L.Structure M]

/-- **Tail-restricted indiscernibility**: for every formula of the family there is a cutoff
beyond which all strictly monotone tuples of the sequence agree. Weaker than
`IsLomega1omegaIndiscernibleOn` (which is the cutoff-`0` case), and the form actually
produced by Erdős–Rado extraction arguments. -/
def IsLomega1omegaIndiscernibleOnTail (a : ℕ → M)
    (Γ : Set (Σ n, L.BoundedFormulaω Empty n)) : Prop :=
  ∀ {n : ℕ} {φ : L.BoundedFormulaω Empty n}, ⟨n, φ⟩ ∈ Γ →
    ∃ N : ℕ, ∀ s t : Fin n → ℕ, StrictMono s → StrictMono t →
      (∀ k, N ≤ s k) → (∀ k, N ≤ t k) →
      (φ.Realize (Empty.elim : Empty → M) (a ∘ s) ↔
       φ.Realize (Empty.elim : Empty → M) (a ∘ t))

/-- Full restricted indiscernibility gives tail indiscernibility (cutoff `0`). -/
theorem IsLomega1omegaIndiscernibleOn.isLomega1omegaIndiscernibleOnTail {a : ℕ → M}
    {Γ : Set (Σ n, L.BoundedFormulaω Empty n)}
    (h : IsLomega1omegaIndiscernibleOn (L := L) a Γ) :
    IsLomega1omegaIndiscernibleOnTail (L := L) a Γ :=
  fun hφ => ⟨0, fun s t hs ht _ _ => h hφ s t hs ht⟩

/-- Strictly monotone tuples exist above any cutoff. -/
theorem exists_strictMono_of_le (n N : ℕ) :
    ∃ s : Fin n → ℕ, StrictMono s ∧ ∀ k, N ≤ s k := by
  refine ⟨fun k => N + k, fun p q hpq => ?_, fun k => Nat.le_add_right _ _⟩
  have h : (p : ℕ) < q := hpq
  show N + (p : ℕ) < N + (q : ℕ)
  omega

/-- The **eventually-form template** of a sequence: a formula is true if all sufficiently
deep strictly monotone tuples realize it. For a tail-indiscernible sequence this is
well-defined in the sense of `tailTemplateOfSeq_truth_iff`. -/
def tailTemplateOfSeq (a : ℕ → M) : Lomega1omegaTemplate L where
  truth {n} φ :=
    letI := ‹L.Structure M›
    ∃ N : ℕ, ∀ s : Fin n → ℕ, StrictMono s → (∀ k, N ≤ s k) →
      φ.Realize (Empty.elim : Empty → M) (a ∘ s)

/-- **Truth collapse for the tail template**: beyond a suitable cutoff, the template's value
at a formula of the family equals the truth value at any strictly monotone tuple. -/
theorem IsLomega1omegaIndiscernibleOnTail.tailTemplateOfSeq_truth_iff {a : ℕ → M}
    {Γ : Set (Σ n, L.BoundedFormulaω Empty n)}
    (h : IsLomega1omegaIndiscernibleOnTail (L := L) a Γ)
    {n : ℕ} {φ : L.BoundedFormulaω Empty n} (hφ : ⟨n, φ⟩ ∈ Γ) :
    ∃ N : ℕ, ∀ s : Fin n → ℕ, StrictMono s → (∀ k, N ≤ s k) →
      ((tailTemplateOfSeq (L := L) a).truth φ ↔
        φ.Realize (Empty.elim : Empty → M) (a ∘ s)) := by
  obtain ⟨N, hN⟩ := h hφ
  refine ⟨N, fun s hs hdeep => ⟨?_, ?_⟩⟩
  · rintro ⟨N', hN'⟩
    obtain ⟨t, ht, htdeep⟩ := exists_strictMono_of_le n (max N N')
    exact (hN t s ht hs (fun k => le_trans (le_max_left _ _) (htdeep k)) hdeep).mp
      (hN' t ht (fun k => le_trans (le_max_right _ _) (htdeep k)))
  · intro hr
    exact ⟨N, fun t ht htdeep => (hN s t hs ht hdeep htdeep).mp hr⟩

end TailTemplate

/-! ### Deep-tuple finite satisfiability -/

/-- **Finite satisfiability in the source model from tail indiscernibility**: every finite
subset of the tail-template theory is satisfiable in the source model. Mirrors
`IsLomega1omegaIndiscernibleOn.templateTheoryOn_finitelySatisfiable`, with the interpreting
order embedding placed beyond the joint cutoff of the finitely many formulas involved. -/
theorem IsLomega1omegaIndiscernibleOnTail.templateTheoryOn_finitelySatisfiable
    {M : Type*} [L.Structure M] {a : ℕ → M}
    {Γ : Set (Σ n, L.BoundedFormulaω Empty n)}
    (h : IsLomega1omegaIndiscernibleOnTail (L := L) a Γ)
    {J : Type u} [LinearOrder J]
    {F : Set L[[J]].Sentenceω}
    (hFin : F.Finite) (hSub : F ⊆ (tailTemplateOfSeq (L := L) a).templateTheoryOn Γ J) :
    ∃ σ : J → M,
      letI : (constantsOn J).Structure M := constantsOn.structure σ
      ∀ τ ∈ F, Sentenceω.Realize τ M := by
  classical
  let m₀ : M := a 0
  -- Witness extraction carrying membership in Γ
  have witness : ∀ τ : F, ∃ (n : ℕ) (φ : L.BoundedFormulaω Empty n)
      (t : Fin n ↪o J), ⟨n, φ⟩ ∈ Γ ∧
      (((tailTemplateOfSeq (L := L) a).truth φ ∧
        (τ : L[[J]].Sentenceω) = Lomega1omegaTemplate.templateSentence φ t) ∨
       (¬ (tailTemplateOfSeq (L := L) a).truth φ ∧
        (τ : L[[J]].Sentenceω) = (Lomega1omegaTemplate.templateSentence φ t).not)) := by
    intro τ
    obtain ⟨n, φ, t, hΓmem, hcase⟩ := hSub τ.property
    exact ⟨n, φ, t, hΓmem, hcase⟩
  choose nOf phiOf tOf hΓOf hOf using witness
  haveI : Fintype ↥F := hFin.fintype
  -- Per-formula truth-collapse cutoffs, and their joint maximum
  choose cutOf hcutOf using fun τ : F => h.tailTemplateOfSeq_truth_iff (hΓOf τ)
  let N₀ : ℕ := (Finset.univ : Finset ↥F).sup cutOf
  have hN₀ : ∀ τ : ↥F, cutOf τ ≤ N₀ := fun τ => Finset.le_sup (Finset.mem_univ τ)
  -- The finitely many constants mentioned by F
  let S : Finset J := (Finset.univ : Finset ↥F).biUnion
    (fun τ => (Finset.univ : Finset (Fin (nOf τ))).image (fun i => tOf τ i))
  let k : ℕ := S.card
  let orderIso : Fin k ≃o ↥S := S.orderIsoOfFin rfl
  -- The deep interpreting embedding
  let f : Fin k ↪o ℕ := OrderEmbedding.ofStrictMono (fun i => N₀ + i)
    (fun p q hpq => by
      have h : (p : ℕ) < q := hpq
      show N₀ + (p : ℕ) < N₀ + (q : ℕ)
      omega)
  have hf_deep : ∀ i : Fin k, N₀ ≤ f i := fun i => Nat.le_add_right _ _
  let σ : J → M := fun j =>
    if hj : j ∈ S then a (f (orderIso.symm ⟨j, hj⟩)) else m₀
  refine ⟨σ, ?_⟩
  letI : (constantsOn J).Structure M := constantsOn.structure σ
  have htS : ∀ (τ : ↥F) (i : Fin (nOf τ)), tOf τ i ∈ S := by
    intro τ i
    exact Finset.mem_biUnion.mpr ⟨τ, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  let t'Of : ∀ (τ : ↥F), Fin (nOf τ) → Fin k :=
    fun τ i => orderIso.symm ⟨tOf τ i, htS τ i⟩
  have t'Of_strictMono : ∀ (τ : ↥F), StrictMono (t'Of τ) := by
    intro τ i j hij
    have h1 : (tOf τ i : J) < tOf τ j := (tOf τ).strictMono hij
    show orderIso.symm ⟨tOf τ i, htS τ i⟩ < orderIso.symm ⟨tOf τ j, htS τ j⟩
    rw [orderIso.symm.lt_iff_lt]
    exact h1
  have ft'_strictMono : ∀ (τ : ↥F), StrictMono (fun i => f (t'Of τ i)) :=
    fun τ => f.strictMono.comp (t'Of_strictMono τ)
  have ft'_deep : ∀ (τ : ↥F) (i : Fin (nOf τ)), cutOf τ ≤ f (t'Of τ i) :=
    fun τ i => le_trans (hN₀ τ) (hf_deep _)
  have sigma_eq : ∀ (τ : ↥F),
      (σ ∘ (fun i => tOf τ i) : Fin (nOf τ) → M) =
      (fun i => a (f (t'Of τ i))) := by
    intro τ
    funext i
    show σ (tOf τ i) = a (f (t'Of τ i))
    show (if hj : tOf τ i ∈ S then a (f (orderIso.symm ⟨tOf τ i, hj⟩)) else m₀) =
         a (f (orderIso.symm ⟨tOf τ i, htS τ i⟩))
    rw [dif_pos (htS τ i)]
  intro τ hτ
  let τ' : ↥F := ⟨τ, hτ⟩
  show Sentenceω.Realize (↑τ' : L[[J]].Sentenceω) M
  rcases hOf τ' with ⟨hpos, heq⟩ | ⟨hneg, heq⟩
  · rw [heq, realize_templateSentence σ (phiOf τ') (tOf τ')]
    rw [show (σ ∘ ⇑(tOf τ') : Fin (nOf τ') → M) = (fun i => a (f (t'Of τ' i))) from
        sigma_eq τ']
    show (phiOf τ').Realize (Empty.elim : Empty → M) (a ∘ (fun i => f (t'Of τ' i)))
    exact (hcutOf τ' _ (ft'_strictMono τ') (ft'_deep τ')).mp hpos
  · rw [heq]
    show ¬ Sentenceω.Realize (Lomega1omegaTemplate.templateSentence (phiOf τ') (tOf τ')) M
    rw [realize_templateSentence σ (phiOf τ') (tOf τ')]
    rw [show (σ ∘ ⇑(tOf τ') : Fin (nOf τ') → M) = (fun i => a (f (t'Of τ' i))) from
        sigma_eq τ']
    show ¬ (phiOf τ').Realize (Empty.elim : Empty → M) (a ∘ (fun i => f (t'Of τ' i)))
    intro hrealize
    apply hneg
    exact (hcutOf τ' _ (ft'_strictMono τ') (ft'_deep τ')).mpr hrealize

/-- Sequence-indexed wrapper. -/
theorem IsLomega1omegaIndiscernibleOnTail.templateTheoryOfSeq_finitelySatisfiable
    {M : Type*} [L.Structure M] {a : ℕ → M}
    (s : ℕ → Σ n, L.BoundedFormulaω Empty n)
    (h : IsLomega1omegaIndiscernibleOnTail (L := L) a (Set.range s))
    {J : Type u} [LinearOrder J]
    {F : Set L[[J]].Sentenceω}
    (hFin : F.Finite)
    (hSub : F ⊆ (tailTemplateOfSeq (L := L) a).templateTheoryOfSeq s J) :
    ∃ σ : J → M,
      letI : (constantsOn J).Structure M := constantsOn.structure σ
      ∀ τ ∈ F, Sentenceω.Realize τ M :=
  h.templateTheoryOn_finitelySatisfiable hFin hSub

/-! ### Compact-oracle stretching from tail indiscernibility -/

/-- Compact-oracle adapter under tail indiscernibility. -/
theorem IsLomega1omegaIndiscernibleOnTail.templateTheoryOfSeq_model_of_compact
    {M : Type} [L.Structure M] {a : ℕ → M}
    (s : ℕ → Σ n, L.BoundedFormulaω Empty n)
    (h : IsLomega1omegaIndiscernibleOnTail (L := L) a (Set.range s))
    {J : Type u} [LinearOrder J]
    (height : Ordinal.{0}) (h_height : Ordinal.omega0 < height)
    (hCompact : ∀ S : Set L[[J]].Sentenceω,
      (∀ F : Set L[[J]].Sentenceω, F.Finite → F ⊆ S →
        ∃ (N : Type) (_ : L[[J]].Structure N), Theoryω.Model F N) →
      ∃ (N : Type) (_ : L[[J]].Structure N), Theoryω.Model S N) :
    ∃ (N : Type) (_ : L[[J]].Structure N),
      Theoryω.Model
        ((tailTemplateOfSeq a : Lomega1omegaTemplate L).templateTheoryOfSeq s J) N := by
  apply (tailTemplateOfSeq a : Lomega1omegaTemplate L).templateTheoryOfSeq_model_of_fragment
    s (admissibleFragmentOfUniv height h_height hCompact) (Set.subset_univ _)
  intro F hFfinite hFsub
  obtain ⟨σ, hσ⟩ := h.templateTheoryOfSeq_finitelySatisfiable s hFfinite hFsub
  letI : (constantsOn J).Structure M := constantsOn.structure σ
  exact ⟨M, inferInstance, hσ⟩

/-- **EM stretching (sentence form, compact oracle, tail-indiscernible source).** -/
theorem IsLomega1omegaIndiscernibleOnTail.stretch_restricted_of_compact
    {M : Type} [L.Structure M] {a : ℕ → M}
    (s : ℕ → Σ n, L.BoundedFormulaω Empty n)
    (h : IsLomega1omegaIndiscernibleOnTail (L := L) a (Set.range s))
    {J : Type u} [LinearOrder J]
    (height : Ordinal.{0}) (h_height : Ordinal.omega0 < height)
    (hCompact : ∀ S : Set L[[J]].Sentenceω,
      (∀ F : Set L[[J]].Sentenceω, F.Finite → F ⊆ S →
        ∃ (N : Type) (_ : L[[J]].Structure N), Theoryω.Model F N) →
      ∃ (N : Type) (_ : L[[J]].Structure N), Theoryω.Model S N) :
    ∃ (N : Type) (_ : L[[J]].Structure N),
      ∀ (i : ℕ) (t : Fin (s i).1 ↪o J),
        Sentenceω.Realize (Lomega1omegaTemplate.templateSentence (s i).2 t) N ↔
          (tailTemplateOfSeq a : Lomega1omegaTemplate L).truth (s i).2 := by
  classical
  obtain ⟨N, _, hModel⟩ :=
    h.templateTheoryOfSeq_model_of_compact s height h_height hCompact
  refine ⟨N, inferInstance, ?_⟩
  intro i t
  have hmem : ⟨(s i).1, (s i).2⟩ ∈ Set.range s := ⟨i, rfl⟩
  by_cases htruth : (tailTemplateOfSeq a : Lomega1omegaTemplate L).truth (s i).2
  · refine ⟨fun _ => htruth, fun _ => ?_⟩
    exact hModel _ ⟨(s i).1, (s i).2, t, hmem, Or.inl ⟨htruth, rfl⟩⟩
  · refine ⟨fun hreal => ?_, fun hT => absurd hT htruth⟩
    exact absurd hreal
      (hModel _ ⟨(s i).1, (s i).2, t, hmem, Or.inr ⟨htruth, rfl⟩⟩)

/-- **EM stretching (sequence form, compact oracle, tail-indiscernible source).** -/
theorem IsLomega1omegaIndiscernibleOnTail.stretch_restricted_sequence_of_compact
    {M : Type} [L.Structure M] {a : ℕ → M}
    (s : ℕ → Σ n, L.BoundedFormulaω Empty n)
    (h : IsLomega1omegaIndiscernibleOnTail (L := L) a (Set.range s))
    {J : Type u} [LinearOrder J]
    (height : Ordinal.{0}) (h_height : Ordinal.omega0 < height)
    (hCompact : ∀ S : Set L[[J]].Sentenceω,
      (∀ F : Set L[[J]].Sentenceω, F.Finite → F ⊆ S →
        ∃ (N : Type) (_ : L[[J]].Structure N), Theoryω.Model F N) →
      ∃ (N : Type) (_ : L[[J]].Structure N), Theoryω.Model S N) :
    ∃ (N : Type) (_ : L[[J]].Structure N) (b : J → N),
      letI : L.Structure N := (L.lhomWithConstants J).reduct N
      ∀ (i : ℕ) (t : Fin (s i).1 ↪o J),
        ((s i).2).Realize (Empty.elim : Empty → N) (b ∘ t) ↔
          (tailTemplateOfSeq a : Lomega1omegaTemplate L).truth (s i).2 := by
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

/-! ### Stretching from a model of the tail-template theory (honest residual)

The compact-oracle lemmas above assume full `L_{ω₁ω}` compactness for `L[[J]]` (false in general).
But the pipeline only ever needs that the *specific* tail-template theory — which is finitely
satisfiable by `templateTheoryOn_finitelySatisfiable` — has *some* model. The lemmas below take
exactly that model as input; the broad compactness oracle factors through them. -/

/-- **EM stretching (sentence form) from a model of the tail-template theory.** Needs only that
the (proved finitely-satisfiable) tail-template theory over `J` has a model — not a compactness
oracle. -/
theorem IsLomega1omegaIndiscernibleOnTail.stretch_restricted_of_model
    {M : Type} [L.Structure M] {a : ℕ → M}
    (s : ℕ → Σ n, L.BoundedFormulaω Empty n)
    {J : Type u} [LinearOrder J]
    (hModel : ∃ (N : Type) (_ : L[[J]].Structure N),
      Theoryω.Model ((tailTemplateOfSeq a : Lomega1omegaTemplate L).templateTheoryOfSeq s J) N) :
    ∃ (N : Type) (_ : L[[J]].Structure N),
      ∀ (i : ℕ) (t : Fin (s i).1 ↪o J),
        Sentenceω.Realize (Lomega1omegaTemplate.templateSentence (s i).2 t) N ↔
          (tailTemplateOfSeq a : Lomega1omegaTemplate L).truth (s i).2 := by
  classical
  obtain ⟨N, _, hModel⟩ := hModel
  refine ⟨N, inferInstance, ?_⟩
  intro i t
  have hmem : ⟨(s i).1, (s i).2⟩ ∈ Set.range s := ⟨i, rfl⟩
  by_cases htruth : (tailTemplateOfSeq a : Lomega1omegaTemplate L).truth (s i).2
  · refine ⟨fun _ => htruth, fun _ => ?_⟩
    exact hModel _ ⟨(s i).1, (s i).2, t, hmem, Or.inl ⟨htruth, rfl⟩⟩
  · refine ⟨fun hreal => ?_, fun hT => absurd hT htruth⟩
    exact absurd hreal
      (hModel _ ⟨(s i).1, (s i).2, t, hmem, Or.inr ⟨htruth, rfl⟩⟩)

/-- **EM stretching (sequence form) from a model of the tail-template theory.** -/
theorem IsLomega1omegaIndiscernibleOnTail.stretch_restricted_sequence_of_model
    {M : Type} [L.Structure M] {a : ℕ → M}
    (s : ℕ → Σ n, L.BoundedFormulaω Empty n)
    {J : Type u} [LinearOrder J]
    (hModel : ∃ (N : Type) (_ : L[[J]].Structure N),
      Theoryω.Model ((tailTemplateOfSeq a : Lomega1omegaTemplate L).templateTheoryOfSeq s J) N) :
    ∃ (N : Type) (_ : L[[J]].Structure N) (b : J → N),
      letI : L.Structure N := (L.lhomWithConstants J).reduct N
      ∀ (i : ℕ) (t : Fin (s i).1 ↪o J),
        ((s i).2).Realize (Empty.elim : Empty → N) (b ∘ t) ↔
          (tailTemplateOfSeq a : Lomega1omegaTemplate L).truth (s i).2 := by
  obtain ⟨N, _inst, hBase⟩ :=
    IsLomega1omegaIndiscernibleOnTail.stretch_restricted_of_model s hModel
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
