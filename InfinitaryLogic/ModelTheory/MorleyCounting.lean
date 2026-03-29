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
  iseqv := by
    refine ⟨fun c => ?_, fun {c₁ c₂} h => ?_, fun {c₁ c₂ c₃} h₁ h₂ => ?_⟩
    · exact @BFEquiv.refl L ℕ c.1.toStructure 0 α Fin.elim0
    · exact @BFEquiv.symm L ℕ c₁.1.toStructure ℕ c₂.1.toStructure 0 α
        Fin.elim0 Fin.elim0 h
    · exact @BFEquiv.trans L ℕ c₁.1.toStructure ℕ c₂.1.toStructure
        ℕ c₃.1.toStructure (n := 0) (α := α)
        (a := Fin.elim0) (b := Fin.elim0) (c := Fin.elim0) h₁ h₂

omit [Countable (Σ l, L.Relations l)] in
/-- Iso implies BFEquiv α: isoSetoid refines bfEquivSetoid. -/
theorem isoSetoid_refines_bfEquivSetoid (φ : L.Sentenceω) (α : Ordinal.{0})
    {c₁ c₂ : ↥(ModelsOf φ)} :
    (isoSetoid φ).r c₁ c₂ → (bfEquivSetoid φ α).r c₁ c₂ := by
  intro ⟨e⟩
  unfold bfEquivSetoid
  simp only
  conv_rhs => rw [show (Fin.elim0 : Fin 0 → ℕ) = e ∘ Fin.elim0 from
    (comp_fin_elim0 e).symm]
  exact @equiv_implies_BFEquiv L ℕ ℕ c₁.1.toStructure c₂.1.toStructure e α 0 Fin.elim0

/-- The BFEquiv α relation on ModelsOf φ is measurable. -/
theorem bfEquivSetoid_measurableSet (φ : L.Sentenceω) (α : Ordinal.{0})
    (hα : α < Ordinal.omega 1) :
    MeasurableSet {p : ↥(ModelsOf φ) × ↥(ModelsOf φ) |
      (bfEquivSetoid φ α).r p.1 p.2} := by
  -- The set is the preimage of BFEquivSet under the subtype inclusion
  have hset : {p : ↥(ModelsOf φ) × ↥(ModelsOf φ) | (bfEquivSetoid φ α).r p.1 p.2} =
      (fun p : ↥(ModelsOf φ) × ↥(ModelsOf φ) => (p.1.1, p.2.1)) ⁻¹'
        (BFEquivSet (L := L) α 0 Fin.elim0 Fin.elim0) := by
    ext ⟨⟨c₁, _⟩, ⟨c₂, _⟩⟩
    simp only [bfEquivSetoid, Set.mem_setOf_eq, Set.mem_preimage, BFEquivSet]
  rw [hset]
  exact ((measurable_subtype_coe.comp measurable_fst).prodMk
    (measurable_subtype_coe.comp measurable_snd))
    (bfEquivSet_measurableSet α hα 0 Fin.elim0 Fin.elim0)

/-- Per-level BFEquiv dichotomy. -/
theorem bfEquiv_classes_dichotomy (silver : SilverBurgessDichotomy.{v})
    (φ : L.Sentenceω) (α : Ordinal.{0}) (hα : α < Ordinal.omega 1) :
    (#(Quotient (bfEquivSetoid φ α)) ≤ ℵ₀) ∨
    (#(Quotient (bfEquivSetoid φ α)) = Cardinal.continuum) :=
  silver (bfEquivSetoid φ α) (bfEquivSetoid_measurableSet φ α hα)

omit [Countable (Σ l, L.Relations l)] in
/-- Refinement gives: #(BFEquiv α classes) ≤ #(iso classes). -/
theorem bfEquiv_classes_le_iso_classes (φ : L.Sentenceω) (α : Ordinal.{0}) :
    #(Quotient (bfEquivSetoid φ α)) ≤ #(Quotient (isoSetoid φ)) := by
  -- The map Quotient.map id sends iso classes to BFEquiv classes surjectively
  have hsurj : Function.Surjective
      (Quotient.map id (fun a b h => isoSetoid_refines_bfEquivSetoid φ α h) :
        Quotient (isoSetoid φ) → Quotient (bfEquivSetoid φ α)) := by
    intro q
    exact q.inductionOn fun c => ⟨Quotient.mk _ c, rfl⟩
  exact Cardinal.mk_le_of_surjective hsurj

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

/-- For coded models with same Scott height and same BFEquiv class, they are isomorphic. -/
private theorem bfEquiv_at_height_implies_iso {φ : L.Sentenceω} {c₁ c₂ : ↥(ModelsOf φ)}
    {α : Ordinal.{0}} (hα : α < Ordinal.omega 1)
    (hht₁ : isoClassHeight (Quotient.mk (isoSetoid φ) c₁) ≤ α)
    (hBF : (bfEquivSetoid φ α).r c₁ c₂) :
    (isoSetoid φ).r c₁ c₂ := by
  -- isoClassHeight unfolds to scottHeight with c₁.1.toStructure
  have hstab : @StabilizesCompletely L ℕ c₁.1.toStructure α :=
    @scottHeight_le_implies_stabilizesCompletely_of L _ _
      countableRefinementHypothesis ℕ c₁.1.toStructure inferInstance (α := α) hht₁
  exact ⟨(@stabilization_bound_iso_eq_BFEquiv L _
    ℕ ℕ c₁.1.toStructure c₂.1.toStructure
    inferInstance inferInstance (α := α) hα hstab hBF).some⟩

omit [L.IsRelational] in
/-- The cardinality of StructureSpace L is at most continuum. -/
private theorem mk_structureSpace_le_continuum :
    #(StructureSpace L) ≤ Cardinal.continuum := by
  -- StructureSpace L = RelQuery L → Bool, and RelQuery L is countable
  -- #(X → Bool) = 2^(#X) ≤ 2^ℵ₀ = continuum when #X ≤ ℵ₀
  unfold StructureSpace
  -- Now the goal is about StructureSpaceOn L ℕ = RelQueryOn L ℕ → Bool
  show #(RelQuery L → Bool) ≤ _
  calc #(RelQuery L → Bool)
      = Cardinal.lift.{v, 0} #Bool ^ Cardinal.lift.{0, v} #(RelQuery L) := Cardinal.mk_arrow _ _
    _ = (2 : Cardinal) ^ Cardinal.lift.{0, v} #(RelQuery L) := by
        simp
    _ ≤ (2 : Cardinal) ^ ℵ₀ := by
        apply Cardinal.power_le_power_left (by norm_num : (2 : Cardinal) ≠ 0)
        rw [Cardinal.lift_le_aleph0]
        exact Cardinal.mk_le_aleph0
    _ = Cardinal.continuum := Cardinal.two_power_aleph0

/-- Morley counting for ℕ-coded models: ≤ ℵ₁ or = 2^ℵ₀. -/
theorem morley_counting_coded (silver : SilverBurgessDichotomy.{v}) (φ : L.Sentenceω) :
    (#(Quotient (isoSetoid φ)) ≤ Cardinal.aleph 1) ∨
    (#(Quotient (isoSetoid φ)) = Cardinal.continuum) := by
  -- Case split: does some BFEquiv_α level have continuum-many classes?
  by_cases hc : ∃ α, α < Ordinal.omega 1 ∧
    #(Quotient (bfEquivSetoid φ α)) = Cardinal.continuum
  · -- Case 1: Some BFEquiv_α has continuum classes → iso has continuum classes
    right
    obtain ⟨α, hα, hcont⟩ := hc
    apply le_antisymm
    · -- Upper bound: quotient ≤ type ≤ StructureSpace ≤ continuum
      calc #(Quotient (isoSetoid φ))
          ≤ #(↥(ModelsOf φ)) := Cardinal.mk_quotient_le
        _ ≤ #(StructureSpace L) := Cardinal.mk_subtype_le _
        _ ≤ Cardinal.continuum := mk_structureSpace_le_continuum
    · -- Lower bound: BFEquiv_α has continuum classes, and iso refines BFEquiv_α
      calc Cardinal.continuum = #(Quotient (bfEquivSetoid φ α)) := hcont.symm
        _ ≤ #(Quotient (isoSetoid φ)) := bfEquiv_classes_le_iso_classes φ α
  · -- Case 2: All BFEquiv_α have ≤ ℵ₀ classes → iso has ≤ ℵ₁ classes
    left
    push_neg at hc
    -- Every BFEquiv_α with α < ω₁ has ≤ ℵ₀ classes
    have hle : ∀ α, α < Ordinal.omega 1 →
        #(Quotient (bfEquivSetoid φ α)) ≤ ℵ₀ := by
      intro α hα
      rcases bfEquiv_classes_dichotomy silver φ α hα with h | h
      · exact h
      · exact absurd h (hc α hα)
    -- For each α < ω₁, iso classes with height = α inject into BFEquiv_α classes (≤ ℵ₀)
    -- Total over ω₁ strata: ≤ ℵ₁
    set Q := Quotient (isoSetoid φ)
    -- Fiber bound: for each α < ω₁, #{iso classes with height = α} ≤ ℵ₀
    have hfiber_le : ∀ α, α < Ordinal.omega 1 →
        #{ q : Q // isoClassHeight q = α } ≤ ℵ₀ := by
      intro α hα
      have hinj : Function.Injective (fun (q : { q : Q // isoClassHeight q = α }) =>
          Quotient.map id (fun a b h => isoSetoid_refines_bfEquivSetoid φ α h) q.1 :
          { q : Q // isoClassHeight q = α } → Quotient (bfEquivSetoid φ α)) := by
        intro ⟨q₁, hq₁⟩ ⟨q₂, hq₂⟩ heq
        ext
        induction q₁ using Quotient.inductionOn with | _ c₁ =>
        induction q₂ using Quotient.inductionOn with | _ c₂ =>
        apply Quotient.sound
        have hBF : (bfEquivSetoid φ α).r c₁ c₂ := Quotient.exact heq
        exact bfEquiv_at_height_implies_iso hα (hq₁ ▸ le_rfl) hBF
      calc #{ q : Q // isoClassHeight q = α }
          ≤ #(Quotient (bfEquivSetoid φ α)) := Cardinal.mk_le_of_injective hinj
        _ ≤ ℵ₀ := hle α hα
    -- Now bound #Q ≤ ℵ₁ using the fiber bound.
    -- Strategy: use Cardinal.mk_subtype_le_of_countable_eventually_mem
    -- or directly show the lifted inequality.
    -- We use: lift #Q ≤ lift #(Iio ω₁) * ⨆ i, lift #(fiber i)
    -- via mk_iUnion_le_lift for the fibers indexed by Iio ω₁.
    -- Then bound: lift #(Iio ω₁) ≤ aleph 1, sup (lift #(fiber i)) ≤ ℵ₀.
    -- aleph 1 * ℵ₀ = aleph 1. Then use lift_le to get #Q ≤ aleph 1.
    -- Define fibers
    set fibers : Set.Iio (Ordinal.omega 1 : Ordinal.{0}) → Set Q :=
      fun ⟨α, _⟩ => {q | isoClassHeight q = α}
    -- Q = ⋃ fibers
    have hQ_eq : (Set.univ : Set Q) ⊆ ⋃ (α : Set.Iio (Ordinal.omega 1 : Ordinal.{0})),
        fibers α := by
      intro q _
      exact Set.mem_iUnion.mpr ⟨⟨isoClassHeight q, isoClassHeight_lt_omega1 q⟩, rfl⟩
    have hQ_le : #Q ≤ #(⋃ (α : Set.Iio (Ordinal.omega 1 : Ordinal.{0})), fibers α) := by
      rw [← Cardinal.mk_univ]
      exact Cardinal.mk_le_mk_of_subset hQ_eq
    -- Bound the union using lift
    have hbound := Cardinal.mk_iUnion_le_lift (α := Q)
      (ι := Set.Iio (Ordinal.omega 1 : Ordinal.{0})) fibers
    -- hbound : lift #(⋃ ...) ≤ lift #(Iio ω₁) * ⨆ i, lift #(fiber i)
    -- We want: #Q ≤ aleph 1 (in Cardinal.{v})
    -- From hbound, the RHS is in Cardinal.{max 1 v}.
    -- We need: Cardinal.lift.{1,v} (#Q) ≤ Cardinal.aleph 1 (in Cardinal.{max 1 v})
    suffices h : Cardinal.lift.{1, v} #Q ≤ Cardinal.aleph 1 by
      rwa [Cardinal.lift_le_aleph_one] at h
    calc Cardinal.lift.{1, v} #Q
        ≤ Cardinal.lift.{1, v} #(⋃ (α : Set.Iio (Ordinal.omega 1 : Ordinal.{0})), fibers α) :=
          Cardinal.lift_le.mpr hQ_le
      _ ≤ Cardinal.lift.{v, 1} #(Set.Iio (Ordinal.omega 1 : Ordinal.{0})) *
            ⨆ (i : Set.Iio (Ordinal.omega 1 : Ordinal.{0})),
              Cardinal.lift.{1, v} #↑(fibers i) := hbound
      _ ≤ Cardinal.aleph 1 * ℵ₀ := by
          apply mul_le_mul'
          · -- lift.{v,1} #(Iio ω₁) = aleph 1
            rw [Ordinal.mk_Iio_ordinal, Cardinal.lift_lift, Ordinal.card_omega,
              Cardinal.lift_aleph, Ordinal.lift_one]
          · -- ⨆ i, lift #(fiber i) ≤ ℵ₀
            haveI : Nonempty (Set.Iio (Ordinal.omega 1 : Ordinal.{0})) :=
              ⟨⟨0, Ordinal.omega_pos 1⟩⟩
            apply ciSup_le
            intro ⟨α, hα⟩
            rw [Cardinal.lift_le_aleph0]
            exact hfiber_le α hα
      _ = Cardinal.aleph 1 := Cardinal.mul_aleph0_eq (Cardinal.aleph0_le_aleph 1)

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
  -- Per-tier dichotomies
  have hN := morley_counting_coded silver φ
  have hFin := fun n => counting_fin_models_dichotomy silver φ n
  -- Sigma embedding
  have hEmbed : ∀ n₀, #(Quotient (isoSetoidOn φ n₀)) ≤
      #(Σ n, Quotient (isoSetoidOn φ n)) := fun n₀ =>
    ⟨⟨fun x => ⟨n₀, x⟩, fun a b h => eq_of_heq (Sigma.mk.inj h).2⟩⟩
  -- Sigma bound
  have hSigma_bound : ∀ (bound : Cardinal),
      (∀ n, #(Quotient (isoSetoidOn φ n)) ≤ bound) → ℵ₀ ≤ bound →
      #(Σ n, Quotient (isoSetoidOn φ n)) ≤ ℵ₀ * bound := by
    intro bound hle hge
    calc #(Σ n, Quotient (isoSetoidOn φ n))
      = Cardinal.sum (fun n => #(Quotient (isoSetoidOn φ n))) := Cardinal.mk_sigma _
      _ ≤ Cardinal.lift.{v, 0} #ℕ * ⨆ i, Cardinal.lift.{0, v} (#(Quotient (isoSetoidOn φ i))) :=
        Cardinal.sum_le_lift_mk_mul_iSup_lift _
      _ = ℵ₀ * ⨆ i, #(Quotient (isoSetoidOn φ i)) := by
        rw [Cardinal.mk_nat, Cardinal.lift_aleph0]
        congr 1; apply iSup_congr; intro i; exact Cardinal.lift_uzero _
      _ ≤ ℵ₀ * bound := by
        apply mul_le_mul_right
        exact ciSup_le fun n => hle n
  -- Case split: does any tier have continuum-many classes?
  by_cases hc : (#(Quotient (isoSetoid φ)) = Cardinal.continuum) ∨
    ∃ n, #(Quotient (isoSetoidOn φ n)) = Cardinal.continuum
  · -- Some tier = continuum → total = continuum
    right
    have hA_le : #(Quotient (isoSetoid φ)) ≤ Cardinal.continuum :=
      hN.elim (·.trans (Cardinal.aleph_one_le_continuum)) le_of_eq
    have hFin_le : ∀ n, #(Quotient (isoSetoidOn φ n)) ≤ Cardinal.continuum :=
      fun n => (hFin n).elim (·.trans Cardinal.aleph0_le_continuum) le_of_eq
    show #(AllCodedIsoClasses φ) = Cardinal.continuum
    apply le_antisymm
    · -- Upper bound
      show #(Quotient (isoSetoid φ) ⊕ Σ n, Quotient (isoSetoidOn φ n)) ≤ Cardinal.continuum
      rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
      apply Cardinal.add_le_of_le Cardinal.aleph0_le_continuum hA_le
      calc #(Σ n, Quotient (isoSetoidOn φ n))
        ≤ ℵ₀ * Cardinal.continuum := hSigma_bound _ hFin_le Cardinal.aleph0_le_continuum
        _ = Cardinal.continuum := Cardinal.aleph0_mul_eq Cardinal.aleph0_le_continuum
    · -- Lower bound
      rcases hc with hcA | ⟨n₀, hn₀⟩
      · show Cardinal.continuum ≤ #(AllCodedIsoClasses φ)
        show Cardinal.continuum ≤ #(Quotient (isoSetoid φ) ⊕ Σ n, Quotient (isoSetoidOn φ n))
        rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
        calc Cardinal.continuum = #(Quotient (isoSetoid φ)) := hcA.symm
          _ ≤ _ := le_self_add
      · show Cardinal.continuum ≤ #(AllCodedIsoClasses φ)
        show Cardinal.continuum ≤ #(Quotient (isoSetoid φ) ⊕ Σ n, Quotient (isoSetoidOn φ n))
        rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
        calc Cardinal.continuum = #(Quotient (isoSetoidOn φ n₀)) := hn₀.symm
          _ ≤ #(Σ n, Quotient (isoSetoidOn φ n)) := hEmbed n₀
          _ ≤ #(Quotient (isoSetoid φ)) + #(Σ n, Quotient (isoSetoidOn φ n)) :=
            self_le_add_left _ _
  · -- No tier = continuum → ℕ-tier ≤ ℵ₁, Fin-tiers ≤ ℵ₀ → total ≤ ℵ₁
    left
    push_neg at hc
    obtain ⟨hcA, hcFin⟩ := hc
    have hA_le : #(Quotient (isoSetoid φ)) ≤ Cardinal.aleph 1 := hN.resolve_right hcA
    have hFin_le : ∀ n, #(Quotient (isoSetoidOn φ n)) ≤ ℵ₀ :=
      fun n => (hFin n).resolve_right (hcFin n)
    show #(Quotient (isoSetoid φ) ⊕ Σ n, Quotient (isoSetoidOn φ n)) ≤ Cardinal.aleph 1
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    apply Cardinal.add_le_of_le (Cardinal.aleph0_le_aleph 1) hA_le
    calc #(Σ n, Quotient (isoSetoidOn φ n))
      ≤ ℵ₀ * ℵ₀ := hSigma_bound _ hFin_le le_rfl
      _ = ℵ₀ := Cardinal.aleph0_mul_aleph0
      _ ≤ Cardinal.aleph 1 := Cardinal.aleph0_le_aleph 1

end Language

end FirstOrder
