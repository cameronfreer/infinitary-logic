/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Lomega1omega.Operations
import Architect

/-!
# Proof System over a Permitted Sentence Set

This file defines a proof system for Lω₁ω over a *permitted sentence set*
`P : Set L.Sentenceω`. The system is Prop-valued (no proof terms) and operates on
sentences.

## Main Definitions

- `Derivable P T φ`: Derivability of sentence `φ` from theory `T`, with conclusions
  permitted by `P`.
- `AConsistent P T`: Theory `T` is `P`-consistent (cannot derive `⊥`).

## Main Results

- `Derivable.mono`: Derivability is monotone in the theory.
- `AConsistent.mono`: Consistency is antitone in the theory.
- `AConsistent.no_contradiction`: No consistent theory contains both φ and ¬φ.

## Design Notes

The system is sentence-level (not bounded formulas with parameters). The quantifier
rules use the omega-rule: `all_intro` requires derivability of all substitution
instances, and `all_elim` extracts one instance.

The permission parameter is a raw `Set L.Sentenceω`, not a fragment structure: the
consumer audit (interface contract §8) established that the proof system consumes
nothing but membership — its membership premises guard *conclusions*, never
hypotheses, so no closure or distinguished-element field is required. Fragment-based
callers pass their sentence set (e.g. `A.formulas`) and supply any needed closure
facts (such as `φ.not ∈ P`) explicitly at the two negation lemmas that use them.
-/

universe u v

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

open FirstOrder Structure BoundedFormulaω

/-- Derivability over a permitted sentence set. Prop-valued (no proof terms).

The system includes structural rules, propositional rules, infinitary connective
rules, quantifier rules (omega-rule), equality rules, and classical logic (LEM). -/
@[blueprint "def:derivable"
  (title := /-- Derivability over a permitted sentence set -/)
  (statement := /-- A sentence $\varphi$ is derivable from theory $T$, with conclusions permitted by the sentence set $P$. The proof system includes structural, propositional, infinitary, quantifier (omega-rule), equality, and classical rules. -/)]
inductive Derivable (P : Set L.Sentenceω) :
    Set L.Sentenceω → L.Sentenceω → Prop where
  -- Structural
  | assumption : φ ∈ T → φ ∈ P → Derivable P T φ
  | weaken : T ⊆ T' → Derivable P T φ → Derivable P T' φ
  | falsum_elim : Derivable P T .falsum → φ ∈ P → Derivable P T φ
  -- Propositional
  | imp_intro : φ ∈ P → Derivable P (T ∪ {φ}) ψ → Derivable P T (φ.imp ψ)
  | imp_elim : Derivable P T (φ.imp ψ) → Derivable P T φ → Derivable P T ψ
  | not_not_elim : Derivable P T φ.not.not → Derivable P T φ
  -- Infinitary
  | iInf_intro : (∀ k, Derivable P T (φs k)) → .iInf φs ∈ P →
      Derivable P T (.iInf φs)
  | iInf_elim (k : ℕ) : Derivable P T (.iInf φs) → Derivable P T (φs k)
  | iSup_intro (k : ℕ) : Derivable P T (φs k) → .iSup φs ∈ P →
      Derivable P T (.iSup φs)
  | iSup_elim : Derivable P T (.iSup φs) →
      (∀ k, Derivable P (T ∪ {φs k}) ψ) → Derivable P T ψ
  -- Quantifiers (omega-rule)
  | all_intro (φ : L.BoundedFormulaω Empty 1) :
      (∀ t : L.Term Empty, Derivable P T (φ.openBounds |>.subst (fun _ => t))) →
      φ.all ∈ P → Derivable P T φ.all
  | all_elim (φ : L.BoundedFormulaω Empty 1) (t : L.Term Empty) :
      Derivable P T φ.all →
      Derivable P T (φ.openBounds |>.subst (fun _ => t))
  -- Equality
  | eq_refl (t : L.Term (Empty ⊕ Fin 0)) :
      BoundedFormulaω.equal t t ∈ P →
      Derivable P T (.equal t t)
  | eq_subst (t₁ t₂ : L.Term Empty) (φ : L.Formulaω (Fin 1)) :
      Derivable P T (.equal (t₁.relabel (Sum.inl : Empty → Empty ⊕ Fin 0))
                            (t₂.relabel (Sum.inl : Empty → Empty ⊕ Fin 0))) →
      Derivable P T (φ.subst (fun _ => t₁)) →
      φ.subst (fun _ => t₂) ∈ P →
      Derivable P T (φ.subst (fun _ => t₂))
  -- Classical
  | em (φ : L.Sentenceω) : φ ∈ P → Derivable P T (φ.or φ.not)

/-- A theory is P-consistent if ⊥ is not derivable from it. -/
@[blueprint "def:a-consistent"
  (title := /-- P-consistency -/)
  (statement := /-- A theory $T$ is $P$-consistent if $\bot$ is not derivable from $T$ with conclusions permitted by $P$. -/)]
def AConsistent (P : Set L.Sentenceω) (T : Set L.Sentenceω) : Prop :=
  ¬ Derivable P T .falsum

/-! ### Basic lemmas -/

/-- Derivability is monotone in the theory. -/
theorem Derivable.mono {P : Set L.Sentenceω} {T T' : Set L.Sentenceω}
    (h : T ⊆ T') (hd : Derivable P T φ) : Derivable P T' φ :=
  Derivable.weaken h hd

/-- Consistency is antitone: subsets of consistent sets are consistent. -/
theorem AConsistent.mono {P : Set L.Sentenceω} {T T' : Set L.Sentenceω}
    (h : T' ⊆ T) (hc : AConsistent P T) : AConsistent P T' :=
  fun hd => hc (hd.mono h)

/-- A consistent theory does not contain ⊥. -/
theorem AConsistent.no_falsum {P : Set L.Sentenceω} {T : Set L.Sentenceω}
    (hc : AConsistent P T) (hT : T ⊆ P) : (BoundedFormulaω.falsum : L.Sentenceω) ∉ T :=
  fun h => hc (.assumption h (hT h))

/-- A consistent theory does not contain both φ and ¬φ. The negation's membership in the
permitted set is an explicit hypothesis (fragment-based callers discharge it by closure). -/
theorem AConsistent.no_contradiction {P : Set L.Sentenceω} {T : Set L.Sentenceω}
    (hc : AConsistent P T) (hφ : φ ∈ T) (hφP : φ ∈ P) (hφnP : φ.not ∈ P) :
    φ.not ∉ T := by
  intro hφn
  apply hc
  exact .imp_elim (.assumption hφn hφnP) (.assumption hφ hφP)

/-- Negation introduction: if T ∪ {φ} ⊢ ⊥, then T ⊢ ¬φ. -/
theorem Derivable.neg_intro {P : Set L.Sentenceω}
    (hφ : φ ∈ P) (h : Derivable P (T ∪ {φ}) .falsum) :
    Derivable P T φ.not :=
  .imp_intro hφ h

/-- Negation elimination: if T ⊢ φ and T ⊢ ¬φ, then T ⊢ ⊥. -/
theorem Derivable.neg_elim {P : Set L.Sentenceω}
    (h₁ : Derivable P T φ) (h₂ : Derivable P T φ.not) :
    Derivable P T .falsum :=
  .imp_elim h₂ h₁

/-- If `S ⊢ χ` and `S ∪ {χ} ⊢ ⊥`, then `S ⊢ ⊥`. -/
theorem Derivable.derivable_collapses_extension {P : Set L.Sentenceω}
    (hd : Derivable P T χ) (hχ : χ ∈ P)
    (hbot : Derivable P (T ∪ {χ}) .falsum) :
    Derivable P T .falsum :=
  hd.neg_elim (.neg_intro hχ hbot)

/-- If `S ∪ {φ} ⊢ ⊥` and `S ∪ {¬φ} ⊢ ⊥`, then `S ⊢ ⊥`. The negation's membership in the
permitted set is an explicit hypothesis. -/
theorem Derivable.inconsistent_of_both_extensions {P : Set L.Sentenceω}
    (hφP : φ ∈ P) (hφnP : φ.not ∈ P)
    (h₁ : Derivable P (T ∪ {φ}) .falsum) (h₂ : Derivable P (T ∪ {φ.not}) .falsum) :
    Derivable P T .falsum :=
  -- From h₁: T ⊢ ¬φ. From h₂: T ⊢ ¬¬φ. Then not_not_elim gives T ⊢ φ. neg_elim gives T ⊢ ⊥.
  (Derivable.not_not_elim (.neg_intro hφnP h₂)).neg_elim (.neg_intro hφP h₁)

/-- If `S ⊢ ¬φ` and `φ, ψ ∈ P`, then `S ⊢ φ → ψ`. -/
theorem Derivable.imp_intro_from_neg {P : Set L.Sentenceω}
    (hd : Derivable P T φ.not) (hφP : φ ∈ P) (hψP : ψ ∈ P) :
    Derivable P T (φ.imp ψ) := by
  apply Derivable.imp_intro hφP
  apply Derivable.falsum_elim _ hψP
  exact Derivable.neg_elim
    (.assumption (Set.mem_union_right T rfl) hφP)
    (.weaken Set.subset_union_left hd)

/-- If `AConsistent P S` and both `φ` and `φ.not` are permitted, then
`AConsistent P (S ∪ {φ}) ∨ AConsistent P (S ∪ {¬φ})`. -/
theorem AConsistent.extension_of_mem_formulas {P : Set L.Sentenceω}
    {S : Set L.Sentenceω} (hc : AConsistent P S)
    (hφP : φ ∈ P) (hφnP : φ.not ∈ P) :
    AConsistent P (S ∪ {φ}) ∨ AConsistent P (S ∪ {φ.not}) := by
  by_contra h; push Not at h
  obtain ⟨h₁, h₂⟩ := h
  unfold AConsistent at h₁ h₂; push Not at h₁ h₂
  exact hc (.inconsistent_of_both_extensions hφP hφnP h₁ h₂)

end Language

end FirstOrder
