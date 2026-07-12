/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.PermTopology
import Mathlib.Topology.Algebra.Group.Basic

/-!
# `S∞ = Equiv.Perm ℕ` is a Polish topological group (issue #27, commit 2)

Building on the pointwise-convergence topology of `PermTopology.lean`:

- `Equiv.Perm ℕ` is a **Polish space**, as a closed subspace of `(ℕ → ℕ) × (ℕ → ℕ)` via the pair
  embedding (`NatPerm.isClosedEmbedding_embed`).
- Multiplication `(σ, τ) ↦ σ * τ` and inversion `σ ↦ σ⁻¹` are **continuous**, so `Equiv.Perm ℕ` is
  a topological group (`IsTopologicalGroup`).

Continuity of multiplication factors coordinatewise through `NatPerm.continuous_evalComp`:
`(σ * τ) n = σ (τ n)` evaluates `σ` at the continuously varying discrete index `τ n`. Inversion is
immediate: the pair embedding intertwines it with `Prod.swap`.
-/

open Topology

namespace NatPerm

/-- `Equiv.Perm ℕ` is Polish: a closed subspace of `(ℕ → ℕ) × (ℕ → ℕ)`. -/
instance instPolishSpacePermNat : PolishSpace (Equiv.Perm ℕ) :=
  isClosedEmbedding_embed.polishSpace

/-- Multiplication on `Equiv.Perm ℕ` is continuous. -/
theorem continuous_mul : Continuous fun p : Equiv.Perm ℕ × Equiv.Perm ℕ => p.1 * p.2 := by
  rw [isInducing_embed.continuous_iff]
  refine Continuous.prodMk (continuous_pi fun n => ?_) (continuous_pi fun n => ?_)
  · -- (embed (p.1 * p.2)).1 n = p.1 (p.2 n)
    simp only [Function.comp_apply, Equiv.Perm.coe_mul]
    exact continuous_evalComp (continuous_coe.comp continuous_fst)
      ((continuous_apply_perm n).comp continuous_snd)
  · -- (embed (p.1 * p.2)).2 n = p.2⁻¹ (p.1⁻¹ n)
    simp only [Function.comp_apply, mul_inv_rev, Equiv.Perm.coe_mul]
    exact continuous_evalComp (continuous_coe_inv.comp continuous_snd)
      ((continuous_inv_apply n).comp continuous_fst)

/-- Inversion on `Equiv.Perm ℕ` is continuous: `embed` intertwines it with `Prod.swap`. -/
theorem continuous_inv : Continuous fun σ : Equiv.Perm ℕ => σ⁻¹ := by
  rw [isInducing_embed.continuous_iff]
  have h : embed ∘ (fun σ : Equiv.Perm ℕ => σ⁻¹) = Prod.swap ∘ embed := by
    funext σ; simp [embed, Function.comp]
  rw [h]
  exact continuous_swap.comp continuous_embed

instance instContinuousMulPermNat : ContinuousMul (Equiv.Perm ℕ) := ⟨continuous_mul⟩
instance instContinuousInvPermNat : ContinuousInv (Equiv.Perm ℕ) := ⟨continuous_inv⟩

/-- `Equiv.Perm ℕ` with the pointwise topology is a topological group. -/
instance instIsTopologicalGroupPermNat : IsTopologicalGroup (Equiv.Perm ℕ) := ⟨⟩

end NatPerm
