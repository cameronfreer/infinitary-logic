/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Admissible.Barwise.Soundness
import InfinitaryLogic.Methods.Henkin.ModelExistence
import Architect

/-!
# Consistency Bridge: From AConsistent to ConsistencyPropertyEq

This file constructs a `ConsistencyPropertyEq` from `AConsistent`, enabling the
model existence theorem for proof-theoretically consistent theories in admissible
fragments.

## Main Results

- `consistencyPropertyOfFullFragment`: Constructs a `ConsistencyPropertyEq` from
  A-consistent sets in a `FullBarwiseFragment` (all sentences in the fragment).
- `barwise_completeness_II_syntactic_full`: A countable A-consistent theory in a
  full Barwise fragment of a countable language has a countable model.

## Design Notes

The chain closure axiom for `AConsistent` does not follow from the proof-theoretic
definition alone (infinitary derivations can draw premises from scattered chain
elements). It is taken as an explicit hypothesis, factored via `BarwiseFragment`.

The `FullBarwiseFragment` wrapper isolates the strong hypothesis that ALL Lω₁ω
sentences belong to the fragment. This matches the global Henkin/maximal-consistent
API (e.g., `extension` requires deciding arbitrary sentences) without modifying
the existing `ConsistencyProperty` infrastructure.

The verification of each consistency property axiom follows a uniform pattern:
assume the relevant extension is inconsistent, use proof rules to derive ⊥ from
the original set, contradicting its consistency.
-/

universe u v

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

open FirstOrder Structure BoundedFormulaω

/-- A Barwise fragment extends an admissible fragment with the chain closure property
for proof-theoretic consistency. -/
structure BarwiseFragment (L : Language.{u, v}) extends FiniteCompactFragment L where
  chain_closure_consistent :
    ∀ (chain : Set (Set L.Sentenceω)),
      chain ⊆ {S | S ⊆ formulas ∧ AConsistent toFiniteCompactFragment S} →
      IsChain (· ⊆ ·) chain → chain.Nonempty →
      AConsistent toFiniteCompactFragment (⋃₀ chain)

/-- A full Barwise fragment: an admissible fragment containing ALL Lω₁ω sentences.
This is a strong wrapper introduced to match the global Henkin/maximal-consistent
API (ConsistencyProperty.extension requires deciding arbitrary sentences). We
isolate this hypothesis here rather than modifying the global API. -/
@[blueprint "def:full-barwise-fragment"
  (title := /-- Full Barwise fragment -/)
  (statement := /-- A full Barwise fragment: an admissible fragment containing all $\Lomegaone$ sentences, equipped with the chain closure property for consistency. -/)
  (uses := ["def:admissible-fragment"])]
structure FullBarwiseFragment (L : Language.{u, v}) extends BarwiseFragment L where
  complete : ∀ φ : L.Sentenceω, φ ∈ formulas

/-- The family of A-consistent subsets of the fragment's formulas. -/
def consistentSets (A : FiniteCompactFragment L) : Set (Set L.Sentenceω) :=
  {S | S ⊆ A.formulas ∧ AConsistent A S}

private theorem mem_consistentSets_iff {A : FiniteCompactFragment L} {S : Set L.Sentenceω} :
    S ∈ consistentSets A ↔ S ⊆ A.formulas ∧ AConsistent A S :=
  Iff.rfl

/-- Extract inconsistency from non-membership in consistentSets, given subset condition. -/
private theorem not_AConsistent_of_not_mem_consistentSets {A : FiniteCompactFragment L}
    {S : Set L.Sentenceω} (hSA : S ⊆ A.formulas) (h : S ∉ consistentSets A) :
    ¬AConsistent A S := by
  intro hc; exact h ⟨hSA, hc⟩

/-- Any extension of a set by a formula in the full fragment stays within the fragment. -/
private theorem union_singleton_subset_of_complete (B : FullBarwiseFragment L)
    {S : Set L.Sentenceω} (hS : S ⊆ B.formulas) (φ : L.Sentenceω) :
    S ∪ {φ} ⊆ B.formulas := by
  intro τ hτ; rcases hτ with hτ_S | hτ_eq
  · exact hS hτ_S
  · rw [Set.mem_singleton_iff.mp hτ_eq]; exact B.complete φ

/-- Construct a `ConsistencyPropertyEq` from A-consistent sets in a full Barwise fragment.

Each C0-C7 axiom is verified by assuming the extension is inconsistent and deriving
a contradiction with the original set's consistency via rules of `Derivable`. The
`complete` hypothesis ensures all formula membership checks are trivial. -/
@[blueprint "thm:consistency-property-full-fragment"
  (title := /-- Consistency property from a full Barwise fragment -/)
  (statement := /-- The family of $A$-consistent subsets of a full Barwise fragment forms a \texttt{ConsistencyPropertyEq}. -/)
  (proof := /-- Each consistency property axiom (C0--C7) is verified by assuming the extension is inconsistent and deriving a contradiction via the proof system rules. -/)
  (uses := ["def:full-barwise-fragment"])
  (proofUses := ["def:derivable", "def:a-consistent"])]
noncomputable def consistencyPropertyOfFullFragment (B : FullBarwiseFragment L) :
    ConsistencyPropertyEq L where
  toConsistencyProperty := {
    sets := consistentSets B.toFiniteCompactFragment
    C0_no_falsum := by
      intro S ⟨hS, hc⟩ hf
      exact hc (.assumption hf (hS hf))
    C0_no_contradiction := by
      intro S ⟨hS, hc⟩ φ ⟨hφ, hφn⟩
      exact hc (.neg_elim (.assumption hφ (hS hφ)) (.assumption hφn (hS hφn)))
    C1_imp := by
      intro S ⟨hS, hc⟩ φ ψ himp
      by_contra h; push_neg at h
      have hSA₁ := union_singleton_subset_of_complete B hS φ.not
      have hSA₂ := union_singleton_subset_of_complete B hS ψ
      have hinc₁ := not_AConsistent_of_not_mem_consistentSets hSA₁ h.1
      have hinc₂ := not_AConsistent_of_not_mem_consistentSets hSA₂ h.2
      unfold AConsistent at hinc₁ hinc₂; push_neg at hinc₁ hinc₂
      have hφ_deriv := Derivable.not_not_elim (.neg_intro (B.complete _) hinc₁)
      have hψn := Derivable.neg_intro (B.complete _) hinc₂
      exact hc (.neg_elim (.imp_elim (.assumption himp (hS himp)) hφ_deriv) hψn)
    C1_neg_imp := by
      -- ¬(φ → ψ) ∈ S → S ∪ {φ} ∈ sets ∧ S ∪ {¬ψ} ∈ sets
      intro S ⟨hS, hc⟩ φ ψ hnimp
      have hφA := B.complete φ
      have hψA := B.complete ψ
      constructor
      · -- S ∪ {φ} is consistent
        refine ⟨union_singleton_subset_of_complete B hS φ, ?_⟩
        intro hd
        -- S ∪ {φ} ⊢ ⊥, so S ⊢ ¬φ
        have hnφ := Derivable.neg_intro hφA hd
        -- From ¬φ, derive φ → ψ (ex falso)
        have himp := Derivable.imp_intro_from_neg hnφ hφA hψA
        -- But ¬(φ → ψ) ∈ S
        exact hc (.neg_elim himp (.assumption hnimp (hS hnimp)))
      · -- S ∪ {¬ψ} is consistent
        refine ⟨union_singleton_subset_of_complete B hS ψ.not, ?_⟩
        intro hd
        -- S ∪ {¬ψ} ⊢ ⊥, so S ⊢ ¬¬ψ, so S ⊢ ψ
        have hψ := Derivable.not_not_elim (.neg_intro (B.complete _) hd)
        -- From ψ, derive φ → ψ
        have himp := Derivable.imp_intro hφA (.weaken Set.subset_union_left hψ)
        exact hc (.neg_elim himp (.assumption hnimp (hS hnimp)))
    C2_not_not := by
      intro S ⟨hS, hc⟩ φ hnn
      refine ⟨union_singleton_subset_of_complete B hS φ, ?_⟩
      intro hd
      have h_neg := Derivable.neg_intro (B.complete _) hd
      exact hc (.neg_elim (.not_not_elim (.assumption hnn (hS hnn))) h_neg)
    C3_iInf := by
      intro S ⟨hS, hc⟩ φs hinf k
      refine ⟨union_singleton_subset_of_complete B hS (φs k), ?_⟩
      intro hd
      have h_neg := Derivable.neg_intro (B.complete _) hd
      exact hc (.neg_elim (.iInf_elim k (.assumption hinf (hS hinf))) h_neg)
    C3_neg_iInf := by
      intro S ⟨hS, hc⟩ φs hninf
      by_contra h; push_neg at h
      have hall : ∀ k, Derivable B.toFiniteCompactFragment S (φs k) := by
        intro k
        have hSAk := union_singleton_subset_of_complete B hS (φs k).not
        have := not_AConsistent_of_not_mem_consistentSets hSAk (h k)
        unfold AConsistent at this; push_neg at this
        exact .not_not_elim (.neg_intro (B.complete _) this)
      have hinf_deriv := Derivable.iInf_intro hall (B.complete _)
      exact hc (.neg_elim hinf_deriv (.assumption hninf (hS hninf)))
    C4_iSup := by
      intro S ⟨hS, hc⟩ φs hsup
      by_contra h; push_neg at h
      have hnegs : ∀ k, Derivable B.toFiniteCompactFragment S (φs k).not := by
        intro k
        have hSAk := union_singleton_subset_of_complete B hS (φs k)
        have := not_AConsistent_of_not_mem_consistentSets hSAk (h k)
        unfold AConsistent at this; push_neg at this
        exact .neg_intro (B.complete _) this
      apply hc
      apply Derivable.iSup_elim (.assumption hsup (hS hsup))
      intro k
      exact .neg_elim
        (.assumption (Set.mem_union_right S rfl) (B.complete _))
        (.weaken Set.subset_union_left (hnegs k))
    C4_neg_iSup := by
      intro S ⟨hS, hc⟩ φs hnsup k
      refine ⟨union_singleton_subset_of_complete B hS (φs k).not, ?_⟩
      intro hd
      have hφk := Derivable.not_not_elim (.neg_intro (B.complete _) hd)
      have hsup_d := Derivable.iSup_intro (k := k) hφk (B.complete _)
      exact hc (.neg_elim hsup_d (.assumption hnsup (hS hnsup)))
    extension := by
      intro S ⟨hS, hc⟩ φ
      rcases AConsistent.extension_of_mem_formulas hS hc (B.complete φ) with h | h
      · exact Or.inl ⟨union_singleton_subset_of_complete B hS φ, h⟩
      · exact Or.inr ⟨union_singleton_subset_of_complete B hS φ.not, h⟩
    chain_closure := by
      intro chain hchain hischain hne
      refine ⟨?_, ?_⟩
      · intro τ hτ
        obtain ⟨S, hS_chain, hτ_S⟩ := Set.mem_sUnion.mp hτ
        exact (hchain hS_chain).1 hτ_S
      · exact B.chain_closure_consistent chain hchain hischain hne
  }
  C5_eq_refl := by
    intro S ⟨hS, hc⟩ t
    refine ⟨union_singleton_subset_of_complete B hS _, ?_⟩
    intro hd
    exact hc (Derivable.derivable_collapses_extension (.eq_refl t (B.complete _))
      (B.complete _) hd)
  C6_eq_subst := by
    intro S ⟨hS, hc⟩ t₁ t₂ φ heq hφ
    refine ⟨union_singleton_subset_of_complete B hS _, ?_⟩
    intro hd
    exact hc (Derivable.derivable_collapses_extension
      (.eq_subst t₁ t₂ φ (.assumption heq (hS heq)) (.assumption hφ (hS hφ)) (B.complete _))
      (B.complete _) hd)
  C7_all := by
    -- (φ.relabel Sum.inr).all ∈ S → S ∪ {φ.subst t} consistent
    intro S ⟨hS, hc⟩ φ hall t
    refine ⟨union_singleton_subset_of_complete B hS _, ?_⟩
    intro hd
    -- S ∪ {φ.subst t} ⊢ ⊥, so S ⊢ ¬(φ.subst t)
    -- By all_elim on (φ.relabel Sum.inr): S ⊢ ((φ.relabel Sum.inr).openBounds).subst t
    -- By bridge lemma: (φ.relabel Sum.inr).openBounds = φ
    -- So S ⊢ φ.subst t, contradiction
    have hd_all := Derivable.all_elim (φ.relabel Sum.inr) t
      (.assumption hall (hS hall))
    rw [openBounds_relabel_sumInr] at hd_all
    exact hc (Derivable.derivable_collapses_extension hd_all (B.complete _) hd)
  C7_neg_all := by
    -- ¬(φ.relabel Sum.inr).all ∈ S → ∃ t, S ∪ {¬(φ.subst t)} consistent
    intro S ⟨hS, hc⟩ φ hnall
    by_contra h; push_neg at h
    -- For all t, S ∪ {(φ.subst t).not} is not in sets
    have hderiv : ∀ t, Derivable B.toFiniteCompactFragment S (φ.subst (fun _ => t)) := by
      intro t
      have hSAt := union_singleton_subset_of_complete B hS (φ.subst (fun _ => t)).not
      have := not_AConsistent_of_not_mem_consistentSets hSAt (h t)
      unfold AConsistent at this; push_neg at this
      exact .not_not_elim (.neg_intro (B.complete _) this)
    -- For all t, S ⊢ φ.subst t. By bridge: φ.subst t = (φ.relabel Sum.inr).openBounds.subst t
    -- So for all t, S ⊢ (φ.relabel Sum.inr).openBounds.subst t
    -- By all_intro: S ⊢ (φ.relabel Sum.inr).all
    have hall_intro : Derivable B.toFiniteCompactFragment S (φ.relabel Sum.inr).all := by
      apply Derivable.all_intro
      · intro t
        have := hderiv t
        rw [show (φ.relabel Sum.inr).openBounds = φ from openBounds_relabel_sumInr φ]
        exact this
      · exact B.complete _
    exact hc (.neg_elim hall_intro (.assumption hnall (hS hnall)))
  C7_neg_ex := by
    -- ¬∃x.φ(x) ∈ S → ∀t, S ∪ {¬(φ.subst t)} consistent
    -- Since ex = not.all.not, hnex is ¬¬(∀x.¬φ(x)) ∈ S
    intro S ⟨hS, hc⟩ φ hnex t
    refine ⟨union_singleton_subset_of_complete B hS _, ?_⟩
    intro hd
    have hφt := Derivable.not_not_elim (.neg_intro (B.complete _) hd)
    have hall := Derivable.not_not_elim (.assumption hnex (hS hnex))
    have hnφt := Derivable.all_elim (φ.relabel Sum.inr).not t hall
    -- Bridge: ((φ.relabel Sum.inr).not.openBounds).subst t = (φ.subst t).not
    have key : ((φ.relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)).not.openBounds).subst (fun _ => t) =
        (φ.subst (fun _ => t)).not := by
      change (((φ.imp .falsum).relabel Sum.inr).openBounds).subst (fun _ => t) =
        (φ.subst (fun _ => t)).imp .falsum
      simp only [openBounds_relabel_sumInr, subst]
    rw [key] at hnφt
    exact hc (.neg_elim hφt hnφt)
  C7_quantifier := by
    -- ∃x.φ(x) ∈ S → ∃ t, S ∪ {φ.subst t} consistent
    -- Since ex = not.all.not, hex is ¬(∀x.¬φ(x)) ∈ S
    intro S ⟨hS, hc⟩ φ hex
    by_contra h; push_neg at h
    have hnegs : ∀ t, Derivable B.toFiniteCompactFragment S (φ.subst (fun _ => t)).not := by
      intro t
      have hSAt := union_singleton_subset_of_complete B hS (φ.subst (fun _ => t))
      have := not_AConsistent_of_not_mem_consistentSets hSAt (h t)
      unfold AConsistent at this; push_neg at this
      exact .neg_intro (B.complete _) this
    -- By bridge + all_intro on (φ.relabel Sum.inr).not: S ⊢ (φ.relabel Sum.inr).not.all
    have hall_intro : Derivable B.toFiniteCompactFragment S (φ.relabel Sum.inr).not.all := by
      apply Derivable.all_intro
      · intro t
        have key : ((φ.relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)).not.openBounds).subst (fun _ => t) =
            (φ.subst (fun _ => t)).not := by
          change (((φ.imp .falsum).relabel Sum.inr).openBounds).subst (fun _ => t) =
            (φ.subst (fun _ => t)).imp .falsum
          simp only [openBounds_relabel_sumInr, subst]
        rw [key]; exact hnegs t
      · exact B.complete _
    -- hex says (φ.relabel Sum.inr).not.all.not ∈ S; neg_elim gives ⊥
    exact hc (.neg_elim hall_intro (.assumption hex (hS hex)))
  C7_all_bound := by
    -- ψ.all ∈ S → S ∪ {ψ.openBounds.subst t} consistent
    intro S ⟨hS, hc⟩ ψ hall t
    refine ⟨union_singleton_subset_of_complete B hS _, ?_⟩
    intro hd
    exact hc (Derivable.derivable_collapses_extension
      (.all_elim ψ t (.assumption hall (hS hall))) (B.complete _) hd)
  C7_neg_all_bound := by
    -- ¬(ψ.all) ∈ S → ∃ t, S ∪ {(ψ.openBounds.subst t).not} consistent
    intro S ⟨hS, hc⟩ ψ hnall
    by_contra h; push_neg at h
    -- For all t, S ∪ {(ψ.openBounds.subst t).not} is not in sets
    -- So for all t, S ⊢ ψ.openBounds.subst t
    have hderiv : ∀ t, Derivable B.toFiniteCompactFragment S (ψ.openBounds.subst (fun _ => t)) := by
      intro t
      have hSAt := union_singleton_subset_of_complete B hS (ψ.openBounds.subst (fun _ => t)).not
      have := not_AConsistent_of_not_mem_consistentSets hSAt (h t)
      unfold AConsistent at this; push_neg at this
      exact .not_not_elim (.neg_intro (B.complete _) this)
    -- By all_intro: S ⊢ ψ.all
    have hall_intro := Derivable.all_intro ψ hderiv (B.complete _)
    -- But ¬(ψ.all) ∈ S, so S ⊢ ¬(ψ.all)
    exact hc (.neg_elim hall_intro (.assumption hnall (hS hnall)))

/-- **Barwise Completeness II (syntactic, full fragment)**: A countable A-consistent theory
in a full Barwise fragment of a countable language has a countable model. -/
@[blueprint "thm:barwise-completeness-ii-syntactic"
  (title := /-- Barwise completeness II (syntactic, full fragment) -/)
  (statement := /-- A countable $A$-consistent theory in a full Barwise fragment of a countable language has a countable model. -/)
  (proof := /-- Construct a \texttt{ConsistencyPropertyEq} from the full Barwise fragment, then apply the model existence theorem. -/)
  (uses := ["thm:consistency-property-full-fragment", "thm:model-existence"])
  (proofUses := ["thm:consistency-property-full-fragment", "thm:model-existence"])]
theorem barwise_completeness_II_syntactic_full
    [Countable (Σ l, L.Functions l)] [Countable (Σ l, L.Relations l)]
    (B : FullBarwiseFragment L)
    {T : Set L.Sentenceω} (hT : T ⊆ B.formulas) (hT_countable : T.Countable)
    (hcons : AConsistent B.toFiniteCompactFragment T) :
    ∃ (M : Type u) (_ : L.Structure M) (_ : Countable M),
      Theoryω.Model T M := by
  let hC := consistencyPropertyOfFullFragment B
  have hT_in : T ∈ hC.toConsistencyProperty.sets := ⟨hT, hcons⟩
  exact consistent_theory_has_model hC T hT_in hT_countable

end Language

end FirstOrder
