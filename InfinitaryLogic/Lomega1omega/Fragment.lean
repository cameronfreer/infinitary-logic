/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Lomega1omega.Semantics

/-!
# Fragments of `L_{ω₁ω}`

The foundational fragment interface of issue #13, per the frozen audit
(`docs/fragments-audit.md`): a fragment is an arity-indexed set of formulas over `Empty` free
variables (parameters enter semantically, through tuples), closed under CONSTRUCTOR COMPONENTS
only — the direction every induction (A-elementarity, Tarski–Vaught, Löwenheim–Skolem, chain
unions) consumes. Deliberately absent, per the audit: atomic-formula membership (would force
countable fragments to have countable languages), formation closure under countable
connectives (destroys countability), syntactic substitution closure (subsumed by semantic
parameters), and formal-negation closure (an NNF concern, #14).
-/

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

/-- **A fragment**: an arity-indexed set of `L_{ω₁ω}`-formulas closed under constructor
components. -/
structure Fragment (L : Language.{u, v}) where
  /-- The member formulas, tagged by arity. -/
  toSet : Set (Σ n, L.BoundedFormulaω Empty n)
  /-- Component closure: the antecedent of a member implication. -/
  imp_left_mem : ∀ {n : ℕ} {φ ψ : L.BoundedFormulaω Empty n},
    (⟨n, φ.imp ψ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ toSet → ⟨n, φ⟩ ∈ toSet
  /-- Component closure: the consequent of a member implication. -/
  imp_right_mem : ∀ {n : ℕ} {φ ψ : L.BoundedFormulaω Empty n},
    (⟨n, φ.imp ψ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ toSet → ⟨n, ψ⟩ ∈ toSet
  /-- Component closure: the body of a member universal. -/
  all_mem : ∀ {n : ℕ} {φ : L.BoundedFormulaω Empty (n + 1)},
    (⟨n, φ.all⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ toSet → ⟨n + 1, φ⟩ ∈ toSet
  /-- Component closure: every component of a member countable conjunction. -/
  iInf_mem : ∀ {n : ℕ} {φs : ℕ → L.BoundedFormulaω Empty n},
    (⟨n, BoundedFormulaω.iInf φs⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ toSet →
      ∀ k, ⟨n, φs k⟩ ∈ toSet
  /-- Component closure: every component of a member countable disjunction. -/
  iSup_mem : ∀ {n : ℕ} {φs : ℕ → L.BoundedFormulaω Empty n},
    (⟨n, BoundedFormulaω.iSup φs⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ toSet →
      ∀ k, ⟨n, φs k⟩ ∈ toSet

namespace Fragment

instance : Membership (Σ n, L.BoundedFormulaω Empty n) (Fragment L) :=
  ⟨fun A p => p ∈ A.toSet⟩

theorem mem_def {A : Fragment L} {p : Σ n, L.BoundedFormulaω Empty n} :
    p ∈ A ↔ p ∈ A.toSet :=
  Iff.rfl

/-- The full fragment: every formula. -/
def top : Fragment L where
  toSet := Set.univ
  imp_left_mem _ := Set.mem_univ _
  imp_right_mem _ := Set.mem_univ _
  all_mem _ := Set.mem_univ _
  iInf_mem _ _ := Set.mem_univ _
  iSup_mem _ _ := Set.mem_univ _

/-- Fragments are closed under intersection. -/
def inter (A B : Fragment L) : Fragment L where
  toSet := A.toSet ∩ B.toSet
  imp_left_mem h := ⟨A.imp_left_mem h.1, B.imp_left_mem h.2⟩
  imp_right_mem h := ⟨A.imp_right_mem h.1, B.imp_right_mem h.2⟩
  all_mem h := ⟨A.all_mem h.1, B.all_mem h.2⟩
  iInf_mem h k := ⟨A.iInf_mem h.1 k, B.iInf_mem h.2 k⟩
  iSup_mem h k := ⟨A.iSup_mem h.1 k, B.iSup_mem h.2 k⟩

end Fragment

end Language

end FirstOrder
