/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.SatisfactionBorelOn
import InfinitaryLogic.Descriptive.CountingDichotomy
import Mathlib.GroupTheory.Perm.Basic
import Architect

/-!
# Finite-Carrier Counting via Permutation Orbits

This file proves that for structures on `Fin n`, isomorphism is the orbit
equivalence relation of `Equiv.Perm (Fin n)`, which is Borel (finite union of
graphs of continuous maps). Combined with the existing ℕ-tier result, this
gives a counting dichotomy for all countable models.

## Main Definitions

- `isoSetoidOn`: Isomorphism setoid on `ModelsOfOn (α := Fin n) φ`.
- `AllCodedIsoClasses`: Disjoint union of iso classes across all carrier tiers.

## Main Results

- `iso_iff_orbit`: Isomorphism of `Fin n`-structures = orbit of `Sym(Fin n)`.
- `isoSetoidOn_measurableSet`: The isomorphism relation on `Fin n`-models is Borel.
- `counting_fin_models_dichotomy`: Per-tier counting dichotomy.
- `allCodedIsoClasses_dichotomy`: Combined counting dichotomy for all countable models.
-/

universe u v

namespace FirstOrder

namespace Language

open Cardinal Ordinal

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

/-! ### Permutation action on finite-carrier structure space -/

/-- `Equiv.Perm (Fin n)` acts on `StructureSpaceOn L (Fin n)` by relabeling:
`(σ • c) ⟨R, v⟩ = c ⟨R, σ.symm ∘ v⟩`. -/
instance permSmul (n : ℕ) : SMul (Equiv.Perm (Fin n)) (StructureSpaceOn L (Fin n)) where
  smul σ c := fun ⟨R, v⟩ => c ⟨R, σ.symm ∘ v⟩

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
@[simp]
theorem perm_smul_apply (n : ℕ) (σ : Equiv.Perm (Fin n))
    (c : StructureSpaceOn L (Fin n)) (R : Σ l, L.Relations l) (v : Fin R.1 → Fin n) :
    (σ • c) ⟨R, v⟩ = c ⟨R, σ.symm ∘ v⟩ := rfl

instance permMulAction (n : ℕ) :
    MulAction (Equiv.Perm (Fin n)) (StructureSpaceOn L (Fin n)) where
  one_smul c := by ext ⟨R, v⟩; simp [HSMul.hSMul, SMul.smul]
  mul_smul σ τ c := by
    ext ⟨R, v⟩
    show c ⟨R, ⇑(σ * τ).symm ∘ v⟩ = c ⟨R, ⇑τ.symm ∘ ⇑σ.symm ∘ v⟩
    congr 1

/-! ### Isomorphism = orbit equivalence -/

/-- Two `Fin n`-structures are L-isomorphic iff they lie in the same `Sym(Fin n)` orbit. -/
theorem iso_iff_orbit (n : ℕ) (c₁ c₂ : StructureSpaceOn L (Fin n)) :
    Nonempty (@Language.Equiv L (Fin n) (Fin n) c₁.toStructure c₂.toStructure) ↔
    ∃ σ : Equiv.Perm (Fin n), σ • c₁ = c₂ := by
  constructor
  · rintro ⟨e⟩
    set σ := @Language.Equiv.toEquiv L (Fin n) (Fin n) c₁.toStructure c₂.toStructure e
    refine ⟨σ, ?_⟩
    ext ⟨⟨l, R⟩, v⟩
    simp only [perm_smul_apply]
    have hrel := @Language.Equiv.map_rel' L (Fin n) (Fin n) c₁.toStructure c₂.toStructure
      e l R (σ.symm ∘ v)
    rw [StructureSpaceOn.relMap_toStructure c₂,
        StructureSpaceOn.relMap_toStructure c₁] at hrel
    simp only [Equiv.toFun_as_coe] at hrel
    have hsimp : (⇑σ) ∘ ⇑σ.symm ∘ v = v := by
      funext i; simp [Function.comp, Equiv.apply_symm_apply]
    rw [hsimp] at hrel
    cases h₁ : c₁ ⟨⟨l, R⟩, ⇑σ.symm ∘ v⟩ <;>
    cases h₂ : c₂ ⟨⟨l, R⟩, v⟩ <;> simp_all
  · rintro ⟨σ, hσ⟩
    refine ⟨@Language.Equiv.mk L (Fin n) (Fin n) c₁.toStructure c₂.toStructure σ
      (fun f => isEmptyElim f) (fun {l} R v => ?_)⟩
    rw [StructureSpaceOn.relMap_toStructure c₂,
        StructureSpaceOn.relMap_toStructure c₁]
    -- Goal: c₂ ⟨⟨l, R⟩, σ ∘ v⟩ = true ↔ c₁ ⟨⟨l, R⟩, v⟩ = true
    -- From hσ: (σ • c₁) = c₂, i.e. c₁ ⟨_, σ.symm ∘ w⟩ = c₂ ⟨_, w⟩ for all w
    -- Set w = σ ∘ v: c₁ ⟨_, σ.symm ∘ σ ∘ v⟩ = c₂ ⟨_, σ ∘ v⟩, i.e. c₁ ⟨_, v⟩ = c₂ ⟨_, σ ∘ v⟩
    have := congr_fun hσ ⟨⟨l, R⟩, σ ∘ v⟩
    simp only [perm_smul_apply] at this
    have hsimp : σ.symm ∘ (σ : Fin n → Fin n) ∘ v = v := by
      funext i; simp [Function.comp, Equiv.symm_apply_apply]
    rw [show (⇑σ.symm ∘ ⇑σ ∘ v) = v from hsimp] at this
    simp only [Equiv.toFun_as_coe] at *
    exact ⟨fun h => by rwa [this], fun h => by rwa [← this]⟩

/-! ### Isomorphism setoid on finite-carrier models -/

/-- The isomorphism setoid on models of φ with carrier `Fin n`. -/
def isoSetoidOn (φ : L.Sentenceω) (n : ℕ) :
    Setoid ↥(ModelsOfOn (α := Fin n) φ) where
  r c₁ c₂ := Nonempty (@Language.Equiv L (Fin n) (Fin n)
    (StructureSpaceOn.toStructure c₁.1) (StructureSpaceOn.toStructure c₂.1))
  iseqv := {
    refl := fun c => ⟨@Language.Equiv.refl L (Fin n) (StructureSpaceOn.toStructure c.1)⟩
    symm := fun {c₁ c₂} ⟨e⟩ =>
      ⟨@Language.Equiv.symm L (Fin n) (Fin n) c₁.1.toStructure c₂.1.toStructure e⟩
    trans := fun {c₁ c₂ c₃} ⟨e₁⟩ ⟨e₂⟩ =>
      ⟨@Language.Equiv.comp L (Fin n) (Fin n) c₁.1.toStructure c₂.1.toStructure
        (Fin n) c₃.1.toStructure e₂ e₁⟩
  }

/-! ### Isomorphism relation is Borel on finite carriers -/

/-- Each orbit map `c ↦ σ • c` is continuous on `StructureSpaceOn L (Fin n)`. -/
theorem continuous_perm_smul (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Continuous (fun c : StructureSpaceOn L (Fin n) => σ • c) := by
  apply continuous_pi
  intro ⟨R, v⟩
  exact continuous_apply (⟨R, σ.symm ∘ v⟩ : RelQueryOn L (Fin n))

/-- The isomorphism relation on `Fin n`-models is measurable.
It equals `⋃ σ : Perm(Fin n), graph(σ • ·)`, a finite union of closed sets. -/
@[blueprint "thm:finite-carrier-iso-borel"
  (title := /-- Isomorphism is Borel on finite carriers -/)
  (statement := /-- For structures on $\operatorname{Fin} n$, the isomorphism relation
    is the orbit of $\operatorname{Sym}(\operatorname{Fin} n)$, a finite union of graphs
    of continuous maps, hence Borel. -/)]
theorem isoSetoidOn_measurableSet (φ : L.Sentenceω) (n : ℕ) :
    MeasurableSet {p : ↥(ModelsOfOn (α := Fin n) φ) × ↥(ModelsOfOn (α := Fin n) φ) |
      (isoSetoidOn φ n).r p.1 p.2} := by
  -- The relation on the subtype is the preimage of the relation on the full space
  -- under the measurable subtype inclusion.
  -- Step 1: Express the relation as ⋃ σ, {p | σ • p.1.1 = p.2.1}
  have hset : {p : ↥(ModelsOfOn (α := Fin n) φ) × ↥(ModelsOfOn (α := Fin n) φ) |
      (isoSetoidOn φ n).r p.1 p.2} =
    ⋃ σ : Equiv.Perm (Fin n),
      {p | σ • p.1.1 = p.2.1} := by
    ext ⟨⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩⟩
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, isoSetoidOn]
    exact iso_iff_orbit n c₁ c₂
  rw [hset]
  -- Step 2: Finite union of measurable sets is measurable
  apply MeasurableSet.iUnion
  intro σ
  -- Step 3: Each {p | σ • p.1.1 = p.2.1} is preimage of diagonal under
  --         (p ↦ (σ • p.1.1, p.2.1))
  have hgraph : {p : ↥(ModelsOfOn (α := Fin n) φ) × ↥(ModelsOfOn (α := Fin n) φ) |
      σ • p.1.1 = p.2.1} =
    (fun p : ↥(ModelsOfOn (α := Fin n) φ) × ↥(ModelsOfOn (α := Fin n) φ) =>
      (σ • p.1.1, p.2.1)) ⁻¹' {q : StructureSpaceOn L (Fin n) × StructureSpaceOn L (Fin n) |
        q.1 = q.2} := by
    ext p; simp [Set.mem_preimage, Set.mem_setOf_eq, Prod.ext_iff]
  rw [hgraph]
  -- Step 4: The diagonal is closed, hence measurable
  exact isClosed_diagonal.measurableSet.preimage
    (((continuous_perm_smul n σ).comp (continuous_subtype_val.comp continuous_fst)).measurable.prodMk
      (continuous_subtype_val.comp continuous_snd).measurable)

/-! ### Per-tier counting dichotomy -/

/-- Per-tier counting dichotomy: for each n, the iso classes among `Fin n`-models
of φ are either ≤ ℵ₀ or = 2^ℵ₀. Does NOT need bounded Scott height. -/
theorem counting_fin_models_dichotomy
    (silver : SilverBurgessDichotomy.{v})
    (φ : L.Sentenceω) (n : ℕ) :
    (#(Quotient (isoSetoidOn φ n)) ≤ ℵ₀) ∨
    (#(Quotient (isoSetoidOn φ n)) = Cardinal.continuum) := by
  haveI : StandardBorelSpace ↥(ModelsOfOn (α := Fin n) φ) :=
    (modelsOfOn_measurableSet φ).standardBorel
  exact silver (isoSetoidOn φ n) (isoSetoidOn_measurableSet φ n)

/-! ### Combined counting theorem -/

/-- The type of all coded isomorphism classes across all carrier tiers:
ℕ-models plus Fin n-models for each n. -/
def AllCodedIsoClasses (φ : L.Sentenceω) :=
  Quotient (isoSetoid φ) ⊕ Σ n, Quotient (isoSetoidOn φ n)

/-- Counting dichotomy for all countable models with bounded Scott height.
The type `AllCodedIsoClasses φ` faithfully represents all isomorphism classes of
countable models of φ (via the bridge theorems `codeModel`, `iso_of_codeModel_eq`,
`codeModel_surjective`).
This theorem states the dichotomy on its cardinality. -/
@[blueprint "thm:counting-all-countable"
  (title := /-- Counting dichotomy for all countable models -/)
  (statement := /-- If the Silver--Burgess dichotomy holds, then for any $\Lomegaone$ sentence
    whose countable models all have Scott height $\leq \alpha < \omegaone$, the total number of
    isomorphism classes of countable models is either $\leq \aleph_0$ or exactly
    $2^{\aleph_0}$. -/)
  (proof := /-- Combine the $\mathbb{N}$-coded result (via BF-equivalence Borelness)
    with finite-carrier orbit arguments for each $\operatorname{Fin} n$ tier. -/)
  (uses := ["thm:counting-dichotomy", "thm:finite-carrier-iso-borel"])]
theorem allCodedIsoClasses_dichotomy
    (silver : SilverBurgessDichotomy.{v})
    {φ : L.Sentenceω} {α : Ordinal.{0}} (hα : α < Ordinal.omega 1)
    (hbound : ∀ (M : Type) [L.Structure M] [Countable M],
      Sentenceω.Realize φ M → scottHeight (L := L) M ≤ α) :
    (#(AllCodedIsoClasses φ) ≤ ℵ₀) ∨
    (#(AllCodedIsoClasses φ) = Cardinal.continuum) := by
  sorry

end Language

end FirstOrder
