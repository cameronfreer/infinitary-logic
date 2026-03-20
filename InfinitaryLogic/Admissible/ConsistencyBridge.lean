/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Admissible.Soundness
import InfinitaryLogic.ModelExistence.Theorem

/-!
# Consistency Bridge: From AConsistent to ConsistencyPropertyEq

This file constructs a `ConsistencyPropertyEq` from `AConsistent`, enabling the
model existence theorem for proof-theoretically consistent theories in admissible
fragments.

## Main Results

- `consistencyPropertyOfFragment`: Constructs a `ConsistencyPropertyEq` from the
  family `{S | S ⊆ A.formulas ∧ AConsistent A S}`.
- `barwise_completeness_II_syntactic`: A countable A-consistent theory in an
  admissible fragment has a countable model.

## Design Notes

The chain closure axiom for `AConsistent` does not follow from the proof-theoretic
definition alone (infinitary derivations can draw premises from scattered chain
elements). It is taken as an explicit hypothesis, factored via `BarwiseFragment`.

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
structure BarwiseFragment (L : Language.{u, v}) extends AdmissibleFragment L where
  chain_closure_consistent :
    ∀ (chain : Set (Set L.Sentenceω)),
      chain ⊆ {S | S ⊆ formulas ∧ AConsistent toAdmissibleFragment S} →
      IsChain (· ⊆ ·) chain → chain.Nonempty →
      AConsistent toAdmissibleFragment (⋃₀ chain)

/-- The family of A-consistent subsets of the fragment's formulas. -/
def consistentSets (A : AdmissibleFragment L) : Set (Set L.Sentenceω) :=
  {S | S ⊆ A.formulas ∧ AConsistent A S}

private theorem mem_consistentSets_iff {A : AdmissibleFragment L} {S : Set L.Sentenceω} :
    S ∈ consistentSets A ↔ S ⊆ A.formulas ∧ AConsistent A S :=
  Iff.rfl

/-- Extract inconsistency from non-membership in consistentSets, given subset condition. -/
private theorem not_AConsistent_of_not_mem_consistentSets {A : AdmissibleFragment L}
    {S : Set L.Sentenceω} (hSA : S ⊆ A.formulas) (h : S ∉ consistentSets A) :
    ¬AConsistent A S := by
  intro hc; exact h ⟨hSA, hc⟩

/-- Construct a `ConsistencyPropertyEq` from A-consistent sets in a Barwise fragment.

Each C0-C7 axiom is verified by assuming the extension is inconsistent and deriving
a contradiction with the original set's consistency. The proofs use the rules of
`Derivable` to construct derivations of `⊥`.

Several axioms (C1', C5-C7, extension) are left as `sorry` pending detailed
proof-theoretic arguments involving negated implications, equality, and quantifiers. -/
noncomputable def consistencyPropertyOfFragment (B : BarwiseFragment L) :
    ConsistencyPropertyEq L where
  toConsistencyProperty := {
    sets := consistentSets B.toAdmissibleFragment
    C0_no_falsum := by
      intro S ⟨hS, hc⟩ hf
      exact hc (.assumption hf (hS hf))
    C0_no_contradiction := by
      intro S ⟨hS, hc⟩ φ ⟨hφ, hφn⟩
      exact hc (.neg_elim (.assumption hφ (hS hφ)) (.assumption hφn (hS hφn)))
    C1_imp := by
      intro S ⟨hS, hc⟩ φ ψ himp
      -- Either S ∪ {¬φ} or S ∪ {ψ} is consistent
      by_contra h; push_neg at h
      have h₁ := h.1; have h₂ := h.2
      -- S ∪ {¬φ} ⊆ A.formulas
      have hSA₁ : S ∪ {φ.not} ⊆ B.formulas := by
        intro τ hτ; rcases hτ with hτ_S | hτ_eq
        · exact hS hτ_S
        · rw [Set.mem_singleton_iff.mp hτ_eq]
          exact B.closed_neg φ (B.closed_imp_left φ ψ (hS himp))
      have hSA₂ : S ∪ {ψ} ⊆ B.formulas := by
        intro τ hτ; rcases hτ with hτ_S | hτ_eq
        · exact hS hτ_S
        · rw [Set.mem_singleton_iff.mp hτ_eq]
          exact B.closed_imp_right φ ψ (hS himp)
      have hinc₁ := not_AConsistent_of_not_mem_consistentSets hSA₁ h₁
      have hinc₂ := not_AConsistent_of_not_mem_consistentSets hSA₂ h₂
      -- S ∪ {¬φ} derives ⊥, so S derives ¬¬φ = φ.not.not
      unfold AConsistent at hinc₁ hinc₂; push_neg at hinc₁ hinc₂
      have hφ_deriv := Derivable.not_not_elim
        (.neg_intro (B.closed_neg φ (B.closed_imp_left φ ψ (hS himp))) hinc₁)
      -- S ∪ {ψ} derives ⊥, so S derives ¬ψ
      have hψn := Derivable.neg_intro (B.closed_imp_right φ ψ (hS himp)) hinc₂
      -- φ → ψ ∈ S, so S derives ψ from φ
      have hψ := Derivable.imp_elim (.assumption himp (hS himp)) hφ_deriv
      exact hc (.neg_elim hψ hψn)
    C1_neg_imp := by
      -- ¬(φ → ψ) ∈ S → S ∪ {φ} ∈ sets ∧ S ∪ {¬ψ} ∈ sets
      sorry
    C2_not_not := by
      intro S ⟨hS, hc⟩ φ hnn
      refine ⟨?_, ?_⟩
      · intro τ hτ; rcases hτ with hτ_S | hτ_eq
        · exact hS hτ_S
        · rw [Set.mem_singleton_iff.mp hτ_eq]
          exact B.closed_imp_left _ _ (B.closed_imp_left _ _ (hS hnn))
      · intro hd
        unfold AConsistent at hc; apply hc
        have h_neg := Derivable.neg_intro
          (B.closed_imp_left _ _ (B.closed_imp_left _ _ (hS hnn))) hd
        exact .neg_elim (.not_not_elim (.assumption hnn (hS hnn))) h_neg
    C3_iInf := by
      intro S ⟨hS, hc⟩ φs hinf k
      refine ⟨?_, ?_⟩
      · intro τ hτ; rcases hτ with hτ_S | hτ_eq
        · exact hS hτ_S
        · rw [Set.mem_singleton_iff.mp hτ_eq]
          exact B.closed_iInf_component φs k (hS hinf)
      · intro hd
        apply hc
        have h_neg := Derivable.neg_intro (B.closed_iInf_component φs k (hS hinf)) hd
        exact .neg_elim (.iInf_elim k (.assumption hinf (hS hinf))) h_neg
    C3_neg_iInf := by
      -- ¬(⋀ φs) ∈ S → ∃ k, S ∪ {¬φₖ} consistent
      intro S ⟨hS, hc⟩ φs hninf
      by_contra h; push_neg at h
      have hall : ∀ k, Derivable B.toAdmissibleFragment S (φs k) := by
        intro k
        have hk_mem := B.closed_iInf_component φs k
          (B.closed_imp_left _ _ (hS hninf))
        have hSAk : S ∪ {(φs k).not} ⊆ B.formulas := by
          intro τ hτ; rcases hτ with hτ_S | hτ_eq
          · exact hS hτ_S
          · rw [Set.mem_singleton_iff.mp hτ_eq]; exact B.closed_neg _ hk_mem
        have := not_AConsistent_of_not_mem_consistentSets hSAk (h k)
        unfold AConsistent at this; push_neg at this
        exact .not_not_elim (.neg_intro (B.closed_neg _ hk_mem) this)
      have hinf_deriv := Derivable.iInf_intro hall (B.closed_imp_left _ _ (hS hninf))
      exact hc (.neg_elim hinf_deriv (.assumption hninf (hS hninf)))
    C4_iSup := by
      -- ⋁ φs ∈ S → ∃ k, S ∪ {φₖ} consistent
      intro S ⟨hS, hc⟩ φs hsup
      by_contra h; push_neg at h
      have hnegs : ∀ k, Derivable B.toAdmissibleFragment S (φs k).not := by
        intro k
        have hk_mem := B.closed_iSup_component φs k (hS hsup)
        have hSAk : S ∪ {φs k} ⊆ B.formulas := by
          intro τ hτ; rcases hτ with hτ_S | hτ_eq
          · exact hS hτ_S
          · rw [Set.mem_singleton_iff.mp hτ_eq]; exact hk_mem
        have := not_AConsistent_of_not_mem_consistentSets hSAk (h k)
        unfold AConsistent at this; push_neg at this
        exact .neg_intro hk_mem this
      -- Use iSup_elim: from ⋁φs and ∀k, S∪{φₖ} ⊢ ⊥
      apply hc
      apply Derivable.iSup_elim (.assumption hsup (hS hsup))
      intro k
      -- Need: S ∪ {φₖ} ⊢ ⊥
      exact .neg_elim
        (.assumption (Set.mem_union_right S rfl) (B.closed_iSup_component φs k (hS hsup)))
        (.weaken Set.subset_union_left (hnegs k))
    C4_neg_iSup := by
      intro S ⟨hS, hc⟩ φs hnsup k
      refine ⟨?_, ?_⟩
      · intro τ hτ; rcases hτ with hτ_S | hτ_eq
        · exact hS hτ_S
        · rw [Set.mem_singleton_iff.mp hτ_eq]
          exact B.closed_neg _ (B.closed_iSup_component φs k
            (B.closed_imp_left _ _ (hS hnsup)))
      · intro hd
        apply hc
        have hφk := Derivable.not_not_elim (Derivable.neg_intro
          (B.closed_neg _ (B.closed_iSup_component φs k
            (B.closed_imp_left _ _ (hS hnsup)))) hd)
        have hsup_d := Derivable.iSup_intro (k := k) hφk
          (B.closed_imp_left _ _ (hS hnsup))
        exact .neg_elim hsup_d (.assumption hnsup (hS hnsup))
    extension := by
      -- For any S and φ, either S ∪ {φ} or S ∪ {¬φ} is A-consistent
      sorry
    chain_closure := by
      intro chain hchain hischain hne
      refine ⟨?_, ?_⟩
      · intro τ hτ
        obtain ⟨S, hS_chain, hτ_S⟩ := Set.mem_sUnion.mp hτ
        exact (hchain hS_chain).1 hτ_S
      · exact B.chain_closure_consistent chain hchain hischain hne
  }
  -- Equality and quantifier axioms (C5-C7)
  -- These require detailed proof-theoretic arguments using eq_refl, eq_subst,
  -- all_intro, all_elim rules of Derivable.
  C5_eq_refl := by sorry
  C6_eq_subst := by sorry
  C7_quantifier := by sorry
  C7_all := by sorry
  C7_neg_all := by sorry
  C7_neg_ex := by sorry
  C7_all_bound := by sorry
  C7_neg_all_bound := by sorry

/-- **Barwise Completeness II (syntactic)**: A countable A-consistent theory
in a Barwise fragment of a countable language has a countable model.

This upgrades `barwise_completeness_II` from semantic consistency (membership in
an externally-provided `ConsistencyPropertyEq`) to proof-theoretic consistency
(`AConsistent`). -/
theorem barwise_completeness_II_syntactic
    [Countable (Σ l, L.Functions l)] [Countable (Σ l, L.Relations l)]
    (B : BarwiseFragment L)
    {T : Set L.Sentenceω} (hT : T ⊆ B.formulas) (hT_countable : T.Countable)
    (hcons : AConsistent B.toAdmissibleFragment T) :
    ∃ (M : Type u) (_ : L.Structure M) (_ : Countable M),
      Theoryω.Model T M := by
  let hC := consistencyPropertyOfFragment B
  have hT_in : T ∈ hC.toConsistencyProperty.sets := by
    change T ⊆ B.formulas ∧ AConsistent B.toAdmissibleFragment T
    exact ⟨hT, hcons⟩
  exact consistent_theory_has_model hC T hT_in hT_countable

end Language

end FirstOrder
