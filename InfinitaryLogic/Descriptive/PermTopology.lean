/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.GroupTheory.Perm.Basic

/-!
# The pointwise-convergence topology on `S∞ = Equiv.Perm ℕ` (issue #27, commit 1)

The infinite symmetric group `Equiv.Perm ℕ` carries a canonical Polish topology — the topology of
pointwise convergence. Mathlib puts no topology on `Equiv.Perm ℕ`, so we install it here via the
**pair embedding**
```
embed : Equiv.Perm ℕ → (ℕ → ℕ) × (ℕ → ℕ),   embed σ = (⇑σ, ⇑σ⁻¹)
```
into a product of two copies of Baire space `ℕ → ℕ`. The image is the closed set of pairs of
mutually inverse functions, so `embed` is a closed embedding — the route to Polishness (commit 2).

## Main results

- `NatPerm.embed`, `instTopologicalSpacePermNat`: the pair embedding and the induced topology.
- `NatPerm.isClosedEmbedding_embed`: `embed` is a closed embedding, cut out by the two inverse
  equations (`NatPerm.range_embed`, `NatPerm.isClosed_range_embed`).
- `NatPerm.continuous_apply_perm`, `NatPerm.continuous_inv_apply`: the evaluations `σ ↦ σ n` and
  `σ ↦ σ⁻¹ n` are continuous.
- `NatPerm.isClopen_stab` and `NatPerm.hasBasis_nhds`: the **acceptance lemma** — the finite
  pointwise stabilizers `{σ | ∀ i ∈ s, σ i = σ₀ i}` are clopen and form a neighborhood basis at
  every `σ₀`. This pins the induced topology to the intended pointwise one (the pair embedding
  could a priori be finer).

## Design

`NatPerm.continuous_evalComp` is the reusable primitive underlying continuity throughout this
tranche: evaluating a continuous function-valued map at a *continuously varying discrete index* is
continuous, because the index can be frozen on a clopen neighborhood. It powers the closed-range
computation here and the continuity of multiplication (commit 2) and of the logic action
(commit 3).
-/

open Topology Filter

namespace NatPerm

/-- **Localized evaluation.** If `f : X → I → Y` is continuous and `e : X → I` is continuous into a
discrete space `I`, then `x ↦ f x (e x)` is continuous: near any `x₀` the index `e x` is frozen at
`e x₀` on the clopen set `e ⁻¹' {e x₀}`, where the map reduces to the continuous `x ↦ f x (e x₀)`. -/
theorem continuous_evalComp {X I Y : Type*} [TopologicalSpace X] [TopologicalSpace I]
    [DiscreteTopology I] [TopologicalSpace Y] {f : X → I → Y} (hf : Continuous f)
    {e : X → I} (he : Continuous e) : Continuous fun x => f x (e x) := by
  rw [continuous_iff_continuousAt]
  intro x
  refine (((continuous_apply (e x)).comp hf).continuousAt).congr ?_
  filter_upwards [he.continuousAt.preimage_mem_nhds ((isOpen_discrete {e x}).mem_nhds rfl)] with y hy
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy
  show f y (e x) = f y (e y)
  rw [hy]

/-! ## The embedding and the induced topology -/

/-- The pair embedding `σ ↦ (σ, σ⁻¹)` of `Equiv.Perm ℕ` into `(ℕ → ℕ) × (ℕ → ℕ)`. -/
def embed (σ : Equiv.Perm ℕ) : (ℕ → ℕ) × (ℕ → ℕ) := (⇑σ, ⇑σ⁻¹)

/-- The topology of pointwise convergence on `Equiv.Perm ℕ`, induced by the pair embedding. -/
instance instTopologicalSpacePermNat : TopologicalSpace (Equiv.Perm ℕ) :=
  TopologicalSpace.induced embed inferInstance

theorem isInducing_embed : IsInducing embed := ⟨rfl⟩

theorem continuous_embed : Continuous embed := isInducing_embed.continuous

theorem embed_injective : Function.Injective embed := fun _ _ h =>
  Equiv.coe_inj.mp (congrArg Prod.fst h)

/-- The coercion `σ ↦ ⇑σ` into `ℕ → ℕ` is continuous. -/
theorem continuous_coe : Continuous fun σ : Equiv.Perm ℕ => (⇑σ : ℕ → ℕ) :=
  continuous_fst.comp continuous_embed

/-- The inverse coercion `σ ↦ ⇑σ⁻¹` into `ℕ → ℕ` is continuous. -/
theorem continuous_coe_inv : Continuous fun σ : Equiv.Perm ℕ => (⇑σ⁻¹ : ℕ → ℕ) :=
  continuous_snd.comp continuous_embed

/-- Evaluation `σ ↦ σ n` is continuous. -/
theorem continuous_apply_perm (n : ℕ) : Continuous fun σ : Equiv.Perm ℕ => σ n :=
  (continuous_apply n).comp continuous_coe

/-- Evaluation `σ ↦ σ⁻¹ n` is continuous. -/
theorem continuous_inv_apply (n : ℕ) : Continuous fun σ : Equiv.Perm ℕ => σ⁻¹ n :=
  (continuous_apply n).comp continuous_coe_inv

/-! ## The image is closed -/

/-- The image of `embed` is the set of pairs of mutually inverse functions. -/
theorem range_embed :
    Set.range embed =
      {p : (ℕ → ℕ) × (ℕ → ℕ) | (∀ n, p.1 (p.2 n) = n) ∧ (∀ n, p.2 (p.1 n) = n)} := by
  ext p
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨fun n => by simp [embed], fun n => by simp [embed]⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Equiv.mk p.1 p.2 h2 h1, by ext <;> simp [embed]⟩

theorem isClosed_range_embed : IsClosed (Set.range embed) := by
  rw [range_embed, Set.setOf_and]
  refine IsClosed.inter ?_ ?_
  · rw [Set.setOf_forall]
    exact isClosed_iInter fun n => isClosed_eq
      (continuous_evalComp continuous_fst ((continuous_apply n).comp continuous_snd)) continuous_const
  · rw [Set.setOf_forall]
    exact isClosed_iInter fun n => isClosed_eq
      (continuous_evalComp continuous_snd ((continuous_apply n).comp continuous_fst)) continuous_const

/-- `embed` is a closed embedding: pointwise-inducing, injective, with closed range. -/
theorem isClosedEmbedding_embed : IsClosedEmbedding embed :=
  ⟨⟨isInducing_embed, embed_injective⟩, isClosed_range_embed⟩

/-! ## Acceptance lemma: finite pointwise stabilizers are a clopen neighborhood basis -/

/-- The finite pointwise stabilizer: permutations agreeing with `σ₀` on the finite set `s`. -/
def stab (s : Finset ℕ) (σ₀ : Equiv.Perm ℕ) : Set (Equiv.Perm ℕ) := {σ | ∀ i ∈ s, σ i = σ₀ i}

/-- Each finite pointwise stabilizer is clopen. -/
theorem isClopen_stab (s : Finset ℕ) (σ₀ : Equiv.Perm ℕ) : IsClopen (stab s σ₀) := by
  have : stab s σ₀ = ⋂ i ∈ s, {σ : Equiv.Perm ℕ | σ i = σ₀ i} := by
    ext σ; simp [stab]
  rw [this]
  exact isClopen_biInter_finset fun i _ =>
    (isClopen_discrete {σ₀ i}).preimage (continuous_apply_perm i)

/-- Cylinder neighborhood basis in `ℕ → ℕ`: sets fixing finitely many coordinates. -/
theorem hasBasis_nhds_fun (a : ℕ → ℕ) :
    (𝓝 a).HasBasis (fun _ : Finset ℕ => True) (fun s => {g : ℕ → ℕ | ∀ i ∈ s, g i = a i}) := by
  rw [nhds_pi]
  simp only [nhds_discrete]
  refine (hasBasis_pi (fun i => hasBasis_pure (a i))).to_hasBasis ?_ ?_
  · rintro ⟨I, _⟩ ⟨hIfin, -⟩
    refine ⟨hIfin.toFinset, trivial, ?_⟩
    intro g hg
    rw [Set.mem_pi]
    intro i hi
    rw [Set.mem_singleton_iff]
    exact hg i (hIfin.mem_toFinset.mpr hi)
  · rintro s -
    refine ⟨⟨(s : Set ℕ), fun _ => ()⟩, ⟨s.finite_toSet, fun i _ => trivial⟩, ?_⟩
    intro g hg i hi
    rw [Set.mem_pi] at hg
    have := hg i (Finset.mem_coe.mpr hi)
    rwa [Set.mem_singleton_iff] at this

/-- **Acceptance lemma.** The finite pointwise stabilizers form a neighborhood basis at every
`σ₀`, so the induced topology is exactly the pointwise-convergence topology — controlling `σ` on a
finite set already controls `σ⁻¹` on the corresponding image, so the inverse coordinates in the
pair embedding contribute no finer neighborhoods. -/
theorem hasBasis_nhds (σ₀ : Equiv.Perm ℕ) :
    (𝓝 σ₀).HasBasis (fun _ : Finset ℕ => True) (fun s => stab s σ₀) := by
  have hprod := (hasBasis_nhds_fun (⇑σ₀)).prod (hasBasis_nhds_fun (⇑σ₀⁻¹))
  rw [isInducing_embed.nhds_eq_comap σ₀]
  have hnb : (𝓝 (embed σ₀)) = 𝓝 (⇑σ₀ : ℕ → ℕ) ×ˢ 𝓝 (⇑σ₀⁻¹ : ℕ → ℕ) := nhds_prod_eq
  rw [hnb]
  refine (hprod.comap embed).to_hasBasis ?_ ?_
  · rintro ⟨s, t⟩ -
    refine ⟨s ∪ t.image (⇑σ₀⁻¹), trivial, ?_⟩
    intro σ hσ
    simp only [stab, Set.mem_setOf_eq] at hσ
    simp only [embed, Set.mem_preimage, Set.mem_prod, Set.mem_setOf_eq]
    refine ⟨fun i hi => hσ i (Finset.mem_union_left _ hi), fun j hj => ?_⟩
    have hk : σ (σ₀⁻¹ j) = σ₀ (σ₀⁻¹ j) :=
      hσ (σ₀⁻¹ j) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj))
    have hj' : σ (σ₀⁻¹ j) = j := by rw [hk]; simp
    show σ⁻¹ j = σ₀⁻¹ j
    have h := congrArg (fun x => σ⁻¹ x) hj'
    simpa using h.symm
  · rintro s -
    refine ⟨(s, ∅), ⟨trivial, trivial⟩, ?_⟩
    intro σ hσ
    simp only [embed, Set.mem_preimage, Set.mem_prod, Set.mem_setOf_eq] at hσ
    simp only [stab, Set.mem_setOf_eq]
    exact fun i hi => hσ.1 i hi

end NatPerm
