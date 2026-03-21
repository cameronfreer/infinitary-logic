/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Admissible.Fragment
import InfinitaryLogic.Lomega1omega.Operations

/-!
# Proof System for Admissible Fragments

This file defines a proof system for admissible fragments of Lω₁ω. The system
is Prop-valued (no proof terms) and operates on sentences.

## Main Definitions

- `Derivable A T φ`: Derivability of sentence `φ` from theory `T` in fragment `A`.
- `AConsistent A T`: Theory `T` is consistent in fragment `A` (cannot derive `⊥`).

## Main Results

- `Derivable.mono`: Derivability is monotone in the theory.
- `AConsistent.mono`: Consistency is antitone in the theory.
- `AConsistent.no_contradiction`: No consistent theory contains both φ and ¬φ.

## Design Notes

The system is sentence-level (not bounded formulas with parameters). The quantifier
rules use the omega-rule: `all_intro` requires derivability of all substitution
instances, and `all_elim` extracts one instance.
-/

universe u v

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

open FirstOrder Structure BoundedFormulaω

/-- Derivability in an admissible fragment. Prop-valued (no proof terms).

The system includes structural rules, propositional rules, infinitary connective
rules, quantifier rules (omega-rule), equality rules, and classical logic (LEM). -/
inductive Derivable (A : AdmissibleFragment L) :
    Set L.Sentenceω → L.Sentenceω → Prop where
  -- Structural
  | assumption : φ ∈ T → φ ∈ A.formulas → Derivable A T φ
  | weaken : T ⊆ T' → Derivable A T φ → Derivable A T' φ
  | falsum_elim : Derivable A T .falsum → φ ∈ A.formulas → Derivable A T φ
  -- Propositional
  | imp_intro : φ ∈ A.formulas → Derivable A (T ∪ {φ}) ψ → Derivable A T (φ.imp ψ)
  | imp_elim : Derivable A T (φ.imp ψ) → Derivable A T φ → Derivable A T ψ
  | not_not_elim : Derivable A T φ.not.not → Derivable A T φ
  -- Infinitary
  | iInf_intro : (∀ k, Derivable A T (φs k)) → .iInf φs ∈ A.formulas →
      Derivable A T (.iInf φs)
  | iInf_elim (k : ℕ) : Derivable A T (.iInf φs) → Derivable A T (φs k)
  | iSup_intro (k : ℕ) : Derivable A T (φs k) → .iSup φs ∈ A.formulas →
      Derivable A T (.iSup φs)
  | iSup_elim : Derivable A T (.iSup φs) →
      (∀ k, Derivable A (T ∪ {φs k}) ψ) → Derivable A T ψ
  -- Quantifiers (omega-rule)
  | all_intro (φ : L.BoundedFormulaω Empty 1) :
      (∀ t : L.Term Empty, Derivable A T (φ.openBounds |>.subst (fun _ => t))) →
      φ.all ∈ A.formulas → Derivable A T φ.all
  | all_elim (φ : L.BoundedFormulaω Empty 1) (t : L.Term Empty) :
      Derivable A T φ.all →
      Derivable A T (φ.openBounds |>.subst (fun _ => t))
  -- Equality
  | eq_refl (t : L.Term (Empty ⊕ Fin 0)) :
      BoundedFormulaω.equal t t ∈ A.formulas →
      Derivable A T (.equal t t)
  | eq_subst (t₁ t₂ : L.Term Empty) (φ : L.Formulaω (Fin 1)) :
      Derivable A T (.equal (t₁.relabel (Sum.inl : Empty → Empty ⊕ Fin 0))
                            (t₂.relabel (Sum.inl : Empty → Empty ⊕ Fin 0))) →
      Derivable A T (φ.subst (fun _ => t₁)) →
      φ.subst (fun _ => t₂) ∈ A.formulas →
      Derivable A T (φ.subst (fun _ => t₂))
  -- Classical
  | em (φ : L.Sentenceω) : φ ∈ A.formulas → Derivable A T (φ.or φ.not)

/-- A theory is A-consistent if ⊥ is not derivable from it. -/
def AConsistent (A : AdmissibleFragment L) (T : Set L.Sentenceω) : Prop :=
  ¬ Derivable A T .falsum

/-! ### Basic lemmas -/

/-- Derivability is monotone in the theory. -/
theorem Derivable.mono {A : AdmissibleFragment L} {T T' : Set L.Sentenceω}
    (h : T ⊆ T') (hd : Derivable A T φ) : Derivable A T' φ :=
  Derivable.weaken h hd

/-- Consistency is antitone: subsets of consistent sets are consistent. -/
theorem AConsistent.mono {A : AdmissibleFragment L} {T T' : Set L.Sentenceω}
    (h : T' ⊆ T) (hc : AConsistent A T) : AConsistent A T' :=
  fun hd => hc (hd.mono h)

/-- A consistent theory does not contain ⊥. -/
theorem AConsistent.no_falsum {A : AdmissibleFragment L} {T : Set L.Sentenceω}
    (hc : AConsistent A T) (hT : T ⊆ A.formulas) : (BoundedFormulaω.falsum : L.Sentenceω) ∉ T :=
  fun h => hc (.assumption h (hT h))

/-- A consistent theory does not contain both φ and ¬φ. -/
theorem AConsistent.no_contradiction {A : AdmissibleFragment L} {T : Set L.Sentenceω}
    (hc : AConsistent A T) (hφ : φ ∈ T) (hφA : φ ∈ A.formulas) :
    φ.not ∉ T := by
  intro hφn
  apply hc
  exact .imp_elim (.assumption hφn (A.closed_neg φ hφA)) (.assumption hφ hφA)

/-- Negation introduction: if T ∪ {φ} ⊢ ⊥, then T ⊢ ¬φ. -/
theorem Derivable.neg_intro {A : AdmissibleFragment L}
    (hφ : φ ∈ A.formulas) (h : Derivable A (T ∪ {φ}) .falsum) :
    Derivable A T φ.not :=
  .imp_intro hφ h

/-- Negation elimination: if T ⊢ φ and T ⊢ ¬φ, then T ⊢ ⊥. -/
theorem Derivable.neg_elim {A : AdmissibleFragment L}
    (h₁ : Derivable A T φ) (h₂ : Derivable A T φ.not) :
    Derivable A T .falsum :=
  .imp_elim h₂ h₁

/-- If `S ⊢ χ` and `S ∪ {χ} ⊢ ⊥`, then `S ⊢ ⊥`. -/
theorem Derivable.derivable_collapses_extension {A : AdmissibleFragment L}
    (hd : Derivable A T χ) (hχ : χ ∈ A.formulas)
    (hbot : Derivable A (T ∪ {χ}) .falsum) :
    Derivable A T .falsum :=
  hd.neg_elim (.neg_intro hχ hbot)

/-- If `S ∪ {φ} ⊢ ⊥` and `S ∪ {¬φ} ⊢ ⊥`, then `S ⊢ ⊥`. -/
theorem Derivable.inconsistent_of_both_extensions {A : AdmissibleFragment L}
    (hφA : φ ∈ A.formulas)
    (h₁ : Derivable A (T ∪ {φ}) .falsum) (h₂ : Derivable A (T ∪ {φ.not}) .falsum) :
    Derivable A T .falsum :=
  -- From h₁: T ⊢ ¬φ. From h₂: T ⊢ ¬¬φ. Then not_not_elim gives T ⊢ φ. neg_elim gives T ⊢ ⊥.
  (Derivable.not_not_elim (.neg_intro (A.closed_neg φ hφA) h₂)).neg_elim (.neg_intro hφA h₁)

/-- If `S ⊢ ¬φ` and `φ, ψ ∈ A.formulas`, then `S ⊢ φ → ψ`. -/
theorem Derivable.imp_intro_from_neg {A : AdmissibleFragment L}
    (hd : Derivable A T φ.not) (hφA : φ ∈ A.formulas) (hψA : ψ ∈ A.formulas) :
    Derivable A T (φ.imp ψ) := by
  apply Derivable.imp_intro hφA
  apply Derivable.falsum_elim _ hψA
  exact Derivable.neg_elim
    (.assumption (Set.mem_union_right T rfl) hφA)
    (.weaken Set.subset_union_left hd)

/-- If `S ⊆ A.formulas`, `AConsistent A S`, and `φ ∈ A.formulas`, then
`AConsistent A (S ∪ {φ}) ∨ AConsistent A (S ∪ {¬φ})`. -/
theorem AConsistent.extension_of_mem_formulas {A : AdmissibleFragment L}
    {S : Set L.Sentenceω} (hSA : S ⊆ A.formulas) (hc : AConsistent A S)
    (hφA : φ ∈ A.formulas) :
    AConsistent A (S ∪ {φ}) ∨ AConsistent A (S ∪ {φ.not}) := by
  by_contra h; push_neg at h
  obtain ⟨h₁, h₂⟩ := h
  unfold AConsistent at h₁ h₂; push_neg at h₁ h₂
  exact hc (.inconsistent_of_both_extensions hφA h₁ h₂)

end Language

end FirstOrder
