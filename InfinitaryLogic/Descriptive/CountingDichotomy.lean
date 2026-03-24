/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.ModelClassStandardBorel
import InfinitaryLogic.Descriptive.IsomorphismBorel
import Mathlib.SetTheory.Cardinal.Continuum
import Architect

/-!
# Conditional Counting Dichotomy for Models

This file states the Silver–Burgess dichotomy as an explicit hypothesis, defines the
isomorphism equivalence relation on coded ℕ-models, and derives a conditional
counting theorem: for Lω₁ω sentences whose ℕ-models have bounded Scott height,
the number of isomorphism classes is either ≤ ℵ₀ or exactly 2^ℵ₀.

## Main Definitions

- `SilverBurgessDichotomy`: The Silver–Burgess dichotomy for Borel equivalence
  relations on standard Borel spaces.
- `isoSetoid`: The isomorphism equivalence relation on `↥(ModelsOf φ)`.

## Main Results

- `counting_coded_models_dichotomy`: Conditional on `SilverBurgessDichotomy`, for
  any Lω₁ω sentence with bounded Scott height, the number of isomorphism classes
  among coded ℕ-models is either ≤ ℵ₀ or exactly 2^ℵ₀.
-/

universe u v w

namespace FirstOrder

namespace Language

open Cardinal Ordinal

/-- The Silver–Burgess dichotomy for Borel equivalence relations:
on a standard Borel space, a Borel equivalence relation has either
at most countably many classes or exactly continuum-many. -/
@[blueprint "def:silver-burgess-dichotomy"
  (title := /-- Silver–Burgess dichotomy (hypothesis) -/)
  (statement := /-- On any standard Borel space, a Borel equivalence relation has either
    at most countably many equivalence classes or exactly $2^{\aleph_0}$. -/)]
def SilverBurgessDichotomy : Prop :=
  ∀ {X : Type w} [MeasurableSpace X] [StandardBorelSpace X]
    (r : Setoid X),
    MeasurableSet {p : X × X | r.r p.1 p.2} →
    (#(Quotient r) ≤ ℵ₀) ∨ (#(Quotient r) = Cardinal.continuum)

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

/-- The isomorphism equivalence relation on coded ℕ-models of φ.
Two codes are related iff the decoded structures on ℕ are L-isomorphic. -/
@[blueprint "def:iso-setoid"
  (title := /-- Isomorphism setoid on coded models -/)
  (statement := /-- The equivalence relation on coded $\mathbb{N}$-models of $\varphi$
    where two codes are related iff their decoded structures are $L$-isomorphic. -/)]
def isoSetoid (φ : L.Sentenceω) : Setoid ↥(ModelsOf φ) where
  r c₁ c₂ := Nonempty (@Language.Equiv L ℕ ℕ c₁.1.toStructure c₂.1.toStructure)
  iseqv := {
    refl := fun c => ⟨@Language.Equiv.refl L ℕ c.1.toStructure⟩
    symm := fun {c₁ c₂} ⟨e⟩ =>
      ⟨@Language.Equiv.symm L ℕ ℕ c₁.1.toStructure c₂.1.toStructure e⟩
    trans := fun {c₁ c₂ c₃} ⟨e₁⟩ ⟨e₂⟩ =>
      ⟨@Language.Equiv.comp L ℕ ℕ c₁.1.toStructure c₂.1.toStructure ℕ
        c₃.1.toStructure e₂ e₁⟩
  }

omit [Countable (Σ l, L.Relations l)] in
/-- The subtype inclusion `↥(ModelsOf φ) × ↥(ModelsOf φ) → StructureSpace L × StructureSpace L`
is measurable. -/
private theorem measurable_subtypeVal_prod (φ : L.Sentenceω) :
    Measurable (fun p : ↥(ModelsOf φ) × ↥(ModelsOf φ) => (p.1.1, p.2.1)) :=
  (measurable_subtype_coe.comp measurable_fst).prodMk
    (measurable_subtype_coe.comp measurable_snd)

/-- The isomorphism relation on coded ℕ-models is measurable when Scott height is bounded.
This lifts `iso_borel_of_bounded_scottHeight` to the subtype `↥(ModelsOf φ)`. -/
private theorem isoSetoid_measurableSet
    {φ : L.Sentenceω} {α : Ordinal.{0}} (hα : α < Ordinal.omega 1)
    (hbound : ∀ (M : Type) [L.Structure M] [Countable M],
      Sentenceω.Realize φ M → scottHeight (L := L) M ≤ α) :
    MeasurableSet {p : ↥(ModelsOf φ) × ↥(ModelsOf φ) | (isoSetoid φ).r p.1 p.2} := by
  have hborel := iso_borel_of_bounded_scottHeight hα hbound
  have hset : {p : ↥(ModelsOf φ) × ↥(ModelsOf φ) | (isoSetoid φ).r p.1 p.2} =
      (fun p : ↥(ModelsOf φ) × ↥(ModelsOf φ) => (p.1.1, p.2.1)) ⁻¹'
        (IsoSet L ∩ (ModelsOf φ ×ˢ ModelsOf φ)) := by
    ext ⟨⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩⟩
    simp only [Set.mem_setOf_eq, isoSetoid, Set.mem_preimage, Set.mem_inter_iff,
      Set.mem_prod, IsoSet]
    exact ⟨fun h => ⟨h, hc₁, hc₂⟩, fun ⟨h, _, _⟩ => h⟩
  rw [hset]
  exact (measurable_subtypeVal_prod φ) hborel

/-- Conditional counting theorem for ℕ-models with bounded Scott height:
if the Silver–Burgess dichotomy holds, then for any Lω₁ω sentence whose
ℕ-models all have Scott height ≤ α < ω₁, the number of isomorphism classes
among ℕ-models of φ is either ≤ ℵ₀ or exactly 2^ℵ₀. -/
@[blueprint "thm:counting-dichotomy"
  (title := /-- Conditional counting dichotomy -/)
  (statement := /-- If the Silver--Burgess dichotomy holds, then for any $\Lomegaone$ sentence
    whose $\mathbb{N}$-models all have Scott height $\leq \alpha < \omegaone$, the number of
    isomorphism classes among coded $\mathbb{N}$-models is either $\leq \aleph_0$ or exactly
    $2^{\aleph_0}$. -/)
  (proof := /-- The model class is standard Borel and the isomorphism relation is Borel
    (by bounded Scott height), so Silver--Burgess applies directly. -/)
  (uses := ["def:silver-burgess-dichotomy", "def:iso-setoid", "thm:iso-borel", "thm:models-standard-borel"])]
theorem counting_coded_models_dichotomy
    (silver : SilverBurgessDichotomy.{v})
    {φ : L.Sentenceω} {α : Ordinal.{0}} (hα : α < Ordinal.omega 1)
    (hbound : ∀ (M : Type) [L.Structure M] [Countable M],
      Sentenceω.Realize φ M → scottHeight (L := L) M ≤ α) :
    (#(Quotient (isoSetoid φ)) ≤ ℵ₀) ∨
    (#(Quotient (isoSetoid φ)) = Cardinal.continuum) :=
  silver (isoSetoid φ) (isoSetoid_measurableSet hα hbound)

end Language

end FirstOrder
