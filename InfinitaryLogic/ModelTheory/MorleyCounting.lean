/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.CountingCountable
import InfinitaryLogic.Descriptive.BFEquivBorel
import Architect

/-!
# Morley's Counting Theorem via Scott-Height Stratification

This file proves the full Morley counting theorem: for any Lω₁ω sentence φ,
the number of isomorphism classes of countable models is either ≤ ℵ₁ or exactly
2^ℵ₀, conditional on the Silver-Burgess dichotomy.

The proof stratifies by Scott height. For each α < ω₁, BFEquiv_α is a Borel
equivalence relation on ModelsOf φ, coarser than isomorphism. If any BFEquiv_α
has 2^ℵ₀ classes, iso has ≥ 2^ℵ₀ hence = 2^ℵ₀. If all have ≤ ℵ₀, then for
each α, the iso classes with height ≤ α inject into BFEquiv_α classes, giving
≤ ℵ₀ iso classes per stratum, hence ≤ ℵ₁ total over ω₁ strata.

## Main Result

- `morley_counting`: Conditional Morley counting theorem for all countable models.
-/

universe u v

namespace FirstOrder

namespace Language

open Cardinal Ordinal

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

/-! ### BFEquiv setoid on coded models -/

/-- The BFEquiv α equivalence relation on coded ℕ-models of φ (at the empty tuple). -/
def bfEquivSetoid (φ : L.Sentenceω) (α : Ordinal.{0}) :
    Setoid ↥(ModelsOf φ) where
  r c₁ c₂ := @BFEquiv L ℕ c₁.1.toStructure ℕ c₂.1.toStructure α 0 Fin.elim0 Fin.elim0
  iseqv := sorry

/-- Iso implies BFEquiv α: isoSetoid refines bfEquivSetoid. -/
theorem isoSetoid_refines_bfEquivSetoid (φ : L.Sentenceω) (α : Ordinal.{0})
    {c₁ c₂ : ↥(ModelsOf φ)} :
    (isoSetoid φ).r c₁ c₂ → (bfEquivSetoid φ α).r c₁ c₂ := by
  sorry

/-- The BFEquiv α relation on ModelsOf φ is measurable. -/
theorem bfEquivSetoid_measurableSet (φ : L.Sentenceω) (α : Ordinal.{0})
    (hα : α < Ordinal.omega 1) :
    MeasurableSet {p : ↥(ModelsOf φ) × ↥(ModelsOf φ) |
      (bfEquivSetoid φ α).r p.1 p.2} := by
  sorry

/-- Per-level BFEquiv dichotomy. -/
theorem bfEquiv_classes_dichotomy (silver : SilverBurgessDichotomy.{v})
    (φ : L.Sentenceω) (α : Ordinal.{0}) (hα : α < Ordinal.omega 1) :
    (#(Quotient (bfEquivSetoid φ α)) ≤ ℵ₀) ∨
    (#(Quotient (bfEquivSetoid φ α)) = Cardinal.continuum) :=
  silver (bfEquivSetoid φ α) (bfEquivSetoid_measurableSet φ α hα)

/-- Refinement gives: #(BFEquiv α classes) ≤ #(iso classes). -/
theorem bfEquiv_classes_le_iso_classes (φ : L.Sentenceω) (α : Ordinal.{0}) :
    #(Quotient (bfEquivSetoid φ α)) ≤ #(Quotient (isoSetoid φ)) := by
  sorry

/-! ### Height function on iso classes -/

/-- scottHeight lifted to the ℕ-model quotient. -/
noncomputable def isoClassHeight {φ : L.Sentenceω}
    (q : Quotient (isoSetoid φ)) : Ordinal.{0} :=
  Quotient.lift
    (fun (c : ↥(ModelsOf φ)) =>
      letI : L.Structure ℕ := StructureSpace.toStructure c.1
      scottHeight (L := L) ℕ)
    (fun c₁ c₂ h => by
      obtain ⟨e⟩ := h
      exact @scottHeight_eq_of_equiv L _ _ ℕ (StructureSpace.toStructure c₁.1) _
        ℕ (StructureSpace.toStructure c₂.1) _ e) q

/-- Every ℕ-model iso class has height < ω₁. -/
theorem isoClassHeight_lt_omega1 {φ : L.Sentenceω}
    (q : Quotient (isoSetoid φ)) :
    isoClassHeight q < Ordinal.omega 1 :=
  Quotient.inductionOn q fun c =>
    @scottHeight_lt_omega1 L _ _ ℕ (StructureSpace.toStructure c.1) _

/-! ### Morley counting: ℕ-coded models -/

/-- Morley counting for ℕ-coded models: ≤ ℵ₁ or = 2^ℵ₀. -/
theorem morley_counting_coded (silver : SilverBurgessDichotomy.{v}) (φ : L.Sentenceω) :
    (#(Quotient (isoSetoid φ)) ≤ Cardinal.aleph 1) ∨
    (#(Quotient (isoSetoid φ)) = Cardinal.continuum) := by
  sorry

/-! ### Full Morley counting theorem -/

/-- **Morley's counting theorem** (conditional on Silver-Burgess):
the number of isomorphism classes of countable models of an Lω₁ω sentence
is either ≤ ℵ₁ or exactly 2^ℵ₀.

Combines the ℕ-tier (via Scott-height stratification + BFEquiv Borelness)
with finite-carrier tiers (via permutation orbits). -/
@[blueprint "thm:morley-counting"
  (title := /-- Morley's counting theorem -/)
  (statement := /-- For any $\Lomegaone$ sentence $\varphi$, the number of isomorphism
    classes of countable models is either $\leq \aleph_1$ or exactly $2^{\aleph_0}$. -/)
  (proof := /-- Stratify by Scott height. For each $\alpha < \omegaone$, BF-equivalence at
    level $\alpha$ is Borel with $\leq \aleph_0$ or $2^{\aleph_0}$ classes. Iso classes
    with height $\leq \alpha$ inject into BF classes. Union over $\omegaone$ strata gives
    $\leq \aleph_1$. -/)
  (uses := ["thm:counting-all-countable", "thm:bfequiv-borel"])]
theorem morley_counting (silver : SilverBurgessDichotomy.{v}) (φ : L.Sentenceω) :
    (#(AllCodedIsoClasses φ) ≤ Cardinal.aleph 1) ∨
    (#(AllCodedIsoClasses φ) = Cardinal.continuum) := by
  sorry

end Language

end FirstOrder
