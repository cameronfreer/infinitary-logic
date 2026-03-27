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
      funext i; simp [Function.comp]
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
      funext i; simp [Function.comp]
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
    ext p; simp [Set.mem_setOf_eq]
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
  -- Per-tier dichotomies
  have hN := counting_coded_models_dichotomy silver hα hbound
  have hFin := fun n => counting_fin_models_dichotomy silver φ n
  -- Sigma embedding: Quotient (isoSetoidOn φ n₀) ↪ Σ n, Quotient (isoSetoidOn φ n)
  have hEmbed : ∀ n₀, #(Quotient (isoSetoidOn φ n₀)) ≤
      #(Σ n, Quotient (isoSetoidOn φ n)) := fun n₀ =>
    ⟨⟨fun x => ⟨n₀, x⟩, fun a b h => eq_of_heq (Sigma.mk.inj h).2⟩⟩
  -- Sigma bound via sum
  have hSigma_bound : ∀ (bound : Cardinal),
      (∀ n, #(Quotient (isoSetoidOn φ n)) ≤ bound) → ℵ₀ ≤ bound →
      #(Σ n, Quotient (isoSetoidOn φ n)) ≤ ℵ₀ * bound := by
    intro bound hle hge
    calc #(Σ n, Quotient (isoSetoidOn φ n))
      = Cardinal.sum (fun n => #(Quotient (isoSetoidOn φ n))) := mk_sigma _
      _ ≤ Cardinal.lift.{v, 0} #ℕ * ⨆ i, Cardinal.lift.{0, v} (#(Quotient (isoSetoidOn φ i))) :=
        sum_le_lift_mk_mul_iSup_lift _
      _ = ℵ₀ * ⨆ i, #(Quotient (isoSetoidOn φ i)) := by
        rw [Cardinal.mk_nat, Cardinal.lift_aleph0]
        congr 1; apply iSup_congr; intro i; exact Cardinal.lift_uzero _
      _ ≤ ℵ₀ * bound := by
        apply mul_le_mul_right
        exact ciSup_le fun n => hle n
  -- Case split on whether any tier has continuum-many classes
  by_cases hc : (#(Quotient (isoSetoid φ)) = Cardinal.continuum) ∨
    ∃ n, #(Quotient (isoSetoidOn φ n)) = Cardinal.continuum
  · -- Some tier = continuum → total = continuum
    right
    have hA_le : #(Quotient (isoSetoid φ)) ≤ Cardinal.continuum :=
      hN.elim (·.trans aleph0_le_continuum) le_of_eq
    have hFin_le : ∀ n, #(Quotient (isoSetoidOn φ n)) ≤ Cardinal.continuum :=
      fun n => (hFin n).elim (·.trans aleph0_le_continuum) le_of_eq
    show #(AllCodedIsoClasses φ) = Cardinal.continuum
    apply le_antisymm
    · -- Upper bound
      show #(Quotient (isoSetoid φ) ⊕ Σ n, Quotient (isoSetoidOn φ n)) ≤ Cardinal.continuum
      rw [mk_sum, Cardinal.lift_id, Cardinal.lift_id]
      apply add_le_of_le aleph0_le_continuum hA_le
      calc #(Σ n, Quotient (isoSetoidOn φ n))
        ≤ ℵ₀ * Cardinal.continuum := hSigma_bound _ hFin_le aleph0_le_continuum
        _ = Cardinal.continuum := by
          rw [Cardinal.aleph0_mul_eq aleph0_le_continuum]
    · -- Lower bound
      rcases hc with hcA | ⟨n₀, hn₀⟩
      · show Cardinal.continuum ≤ #(AllCodedIsoClasses φ)
        show Cardinal.continuum ≤ #(Quotient (isoSetoid φ) ⊕ Σ n, Quotient (isoSetoidOn φ n))
        rw [mk_sum, Cardinal.lift_id, Cardinal.lift_id]
        calc Cardinal.continuum = #(Quotient (isoSetoid φ)) := hcA.symm
          _ ≤ _ := le_self_add
      · show Cardinal.continuum ≤ #(AllCodedIsoClasses φ)
        show Cardinal.continuum ≤ #(Quotient (isoSetoid φ) ⊕ Σ n, Quotient (isoSetoidOn φ n))
        rw [mk_sum, Cardinal.lift_id, Cardinal.lift_id]
        calc Cardinal.continuum = #(Quotient (isoSetoidOn φ n₀)) := hn₀.symm
          _ ≤ #(Σ n, Quotient (isoSetoidOn φ n)) := hEmbed n₀
          _ ≤ #(Quotient (isoSetoid φ)) + #(Σ n, Quotient (isoSetoidOn φ n)) :=
            self_le_add_left _ _
  · -- No tier = continuum → all ≤ ℵ₀ → total ≤ ℵ₀
    left
    push_neg at hc
    obtain ⟨hcA, hcFin⟩ := hc
    have hA_le : #(Quotient (isoSetoid φ)) ≤ ℵ₀ := hN.resolve_right hcA
    have hFin_le : ∀ n, #(Quotient (isoSetoidOn φ n)) ≤ ℵ₀ :=
      fun n => (hFin n).resolve_right (hcFin n)
    show #(Quotient (isoSetoid φ) ⊕ Σ n, Quotient (isoSetoidOn φ n)) ≤ ℵ₀
    rw [mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    apply add_le_of_le le_rfl hA_le
    calc #(Σ n, Quotient (isoSetoidOn φ n))
      ≤ ℵ₀ * ℵ₀ := hSigma_bound _ hFin_le le_rfl
      _ = ℵ₀ := Cardinal.aleph0_mul_aleph0

/-! ### Bridge theorems: coded classes represent all countable models -/

section Bridge

attribute [local instance] Classical.dec

variable {φ : L.Sentenceω}

/-- Helper: Transport a structure along an equivalence and encode it. The resulting
code decodes to a structure L-isomorphic to the original. -/
private noncomputable def encodeViaEquiv {M : Type} [L.Structure M] {α : Type}
    (e : M ≃ α) : StructureSpaceOn L α :=
  StructureSpaceOn.ofStructure (@Equiv.inducedStructure L M α _ e)

/-- The decoded structure from `encodeViaEquiv` equals the induced structure. -/
private theorem toStructure_encodeViaEquiv_eq {M : Type} [L.Structure M] {α : Type}
    (e : M ≃ α) :
    StructureSpaceOn.toStructure (encodeViaEquiv e) = @Equiv.inducedStructure L M α _ e := by
  have hR := ‹L.IsRelational›
  ext n
  · -- funMap case: L.Functions n is empty
    exact (hR n).elim ‹_›
  · -- RelMap case: round-trip preserves relations
    constructor
    · intro h
      rw [StructureSpaceOn.relMap_toStructure, encodeViaEquiv, StructureSpaceOn.ofStructure] at h
      simp [decide_eq_true_eq] at h
      rwa [Equiv.inducedStructure_RelMap]
    · intro h
      rw [Equiv.inducedStructure_RelMap] at h
      rw [StructureSpaceOn.relMap_toStructure, encodeViaEquiv, StructureSpaceOn.ofStructure]
      simp [h]

/-- The encoded structure via an equivalence satisfies the same sentences. -/
private theorem encodeViaEquiv_models {M : Type} [L.Structure M] {α : Type}
    [Countable α] (e : M ≃ α) (hφ : Sentenceω.Realize φ M) :
    @Sentenceω.Realize L φ α (StructureSpaceOn.toStructure (encodeViaEquiv e)) := by
  rw [toStructure_encodeViaEquiv_eq]
  letI : L.Structure α := Equiv.inducedStructure e
  exact (LomegaEquiv.of_equiv (Equiv.inducedStructureEquiv e) φ).mp hφ

/-- The encoded structure is L-isomorphic to the original via the equivalence. -/
private theorem encodeViaEquiv_iso {M : Type} [L.Structure M] {α : Type}
    (e : M ≃ α) :
    Nonempty (@Language.Equiv L M α ‹_› (StructureSpaceOn.toStructure (encodeViaEquiv e))) := by
  rw [toStructure_encodeViaEquiv_eq]
  exact ⟨Equiv.inducedStructureEquiv e⟩

/-- Map a countable model of φ to its coded iso class.
Uses `finite_or_infinite` to dispatch to the ℕ or `Fin n` tier. -/
noncomputable def codeModel
    {M : Type} [L.Structure M] [Countable M]
    (hφ : Sentenceω.Realize φ M) : AllCodedIsoClasses φ :=
  if hfin : Finite M then
    haveI := Fintype.ofFinite M
    let n := Fintype.card M
    let e : M ≃ Fin n := Fintype.equivFin M
    Sum.inr ⟨n, Quotient.mk (isoSetoidOn φ n)
      ⟨encodeViaEquiv e, encodeViaEquiv_models e hφ⟩⟩
  else
    haveI : Infinite M := not_finite_iff_infinite.mp hfin
    let e : M ≃ ℕ := (nonempty_equiv_of_countable (α := M) (β := ℕ)).some
    Sum.inl (Quotient.mk (isoSetoid φ)
      ⟨encodeViaEquiv e, encodeViaEquiv_models e hφ⟩)

/-- Compose L-equivs through encoding bijections to build iso between coded structures. -/
private theorem compose_encoded_iso
    {M N : Type} [L.Structure M] [L.Structure N] {α : Type}
    (e : @Language.Equiv L M N ‹_› ‹_›)
    (eM : M ≃ α) (eN : N ≃ α) :
    Nonempty (@Language.Equiv L α α
      (StructureSpaceOn.toStructure (encodeViaEquiv eM))
      (StructureSpaceOn.toStructure (encodeViaEquiv eN))) := by
  rw [toStructure_encodeViaEquiv_eq, toStructure_encodeViaEquiv_eq]
  -- Goal: Nonempty (@Language.Equiv L α α (inducedStructure eM) (inducedStructure eN))
  -- Build directly using Equiv.mk
  refine ⟨@Language.Equiv.mk L α α (Equiv.inducedStructure eM) (Equiv.inducedStructure eN)
    (eM.symm.trans (e.toEquiv.trans eN))
    (fun f _ => isEmptyElim ((‹L.IsRelational› _).false f))
    (fun {n} R v => ?_)⟩
  -- After inducedStructure_RelMap: RelMap_N R (eN.symm ∘ trans ∘ v) ↔ RelMap_M R (eM.symm ∘ v)
  -- Simplify: eN.symm ∘ trans = e ∘ eM.symm, then use e.map_rel'
  simp only [Equiv.inducedStructure_RelMap, Function.comp_def, Equiv.trans_apply, Equiv.toFun_as_coe]
  simp_rw [eN.symm_apply_apply]
  -- Goal: RelMap R (fun x => e.toEquiv (eM.symm (v x))) ↔ RelMap R (fun x => eM.symm (v x))
  -- e.toEquiv and DFunLike.coe e agree pointwise
  constructor
  · intro h; exact (e.map_rel' R (⇑eM.symm ∘ v)).mp (by convert h using 2)
  · intro h; convert (e.map_rel' R (⇑eM.symm ∘ v)).mpr h using 2

/-- L-isomorphic countable models map to the same coded class. -/
theorem codeModel_eq_of_iso
    {M N : Type} [L.Structure M] [L.Structure N] [Countable M] [Countable N]
    (hφM : Sentenceω.Realize φ M) (hφN : Sentenceω.Realize φ N)
    (e : @Language.Equiv L M N ‹_› ‹_›) :
    codeModel hφM = codeModel hφN := by
  have hequiv := e.toEquiv
  by_cases hfinM : Finite M
  · -- M is finite → N is finite
    haveI hfinN : Finite N := Finite.of_equiv M hequiv
    -- Use the exact same Fintype instances that codeModel will use internally
    -- (which are Fintype.ofFinite M / N)
    have hcard : @Fintype.card M (Fintype.ofFinite M) = @Fintype.card N (Fintype.ofFinite N) :=
      @Fintype.card_congr M N (Fintype.ofFinite M) (Fintype.ofFinite N) hequiv
    -- Both take finite branch with same cardinality
    -- Show the quotient elements agree using compose_encoded_iso
    -- Both take finite branch
    unfold codeModel; simp only [dif_pos hfinM, dif_pos hfinN]
    -- Goal: Sum.inr ⟨card M, quot_M⟩ = Sum.inr ⟨card N, quot_N⟩
    -- Since card M = card N, we use congrArg
    have h1 : ∀ (n : ℕ) (f : M ≃ Fin n) (g : N ≃ Fin n)
        (hf : @Sentenceω.Realize L φ _ (StructureSpaceOn.toStructure (encodeViaEquiv f)))
        (hg : @Sentenceω.Realize L φ _ (StructureSpaceOn.toStructure (encodeViaEquiv g))),
        Quotient.mk (isoSetoidOn φ n) ⟨encodeViaEquiv f, hf⟩ =
        Quotient.mk (isoSetoidOn φ n) ⟨encodeViaEquiv g, hg⟩ := by
      intro n f g hf hg
      apply Quotient.sound; show Nonempty _
      exact compose_encoded_iso e _ _
    -- Transport via hcard: use subst after generalizing
    suffices ∀ m (eqm : m = @Fintype.card M (Fintype.ofFinite M))
        (f : M ≃ Fin m) (g : N ≃ Fin (@Fintype.card N (Fintype.ofFinite N))),
        (Sum.inr ⟨m, Quotient.mk (isoSetoidOn φ m) ⟨encodeViaEquiv f,
            encodeViaEquiv_models f hφM⟩⟩ : AllCodedIsoClasses φ) =
        Sum.inr ⟨@Fintype.card N (Fintype.ofFinite N),
            Quotient.mk (isoSetoidOn φ _) ⟨encodeViaEquiv g,
            encodeViaEquiv_models g hφN⟩⟩ from
      this _ rfl _ _
    intro m eqm f g; subst eqm
    -- Goal: Sum.inr ⟨card M, q(f)⟩ = Sum.inr ⟨card N, q(g)⟩
    -- where f : M ≃ Fin (card M), g : N ≃ Fin (card N)
    -- Use Eq.rec on hcard to rewrite card M to card N in the LHS
    -- Then use h1 to close the quotient equality.
    revert f; rw [hcard]; intro f
    -- After rw: f : M ≃ Fin (card N), and goal has card N on both sides
    congr 2
    exact h1 _ _ _ _ _
  · -- M is infinite → N is infinite
    haveI : Infinite M := not_finite_iff_infinite.mp hfinM
    have hfinN : ¬Finite N := fun h => hfinM (Finite.of_equiv N hequiv.symm)
    haveI : Infinite N := not_finite_iff_infinite.mp hfinN
    have hM_eq : codeModel hφM = Sum.inl
        ⟦⟨encodeViaEquiv (nonempty_equiv_of_countable (α := M) (β := ℕ)).some,
          encodeViaEquiv_models _ hφM⟩⟧ := by
      unfold codeModel; rw [dif_neg hfinM]
    have hN_eq : codeModel hφN = Sum.inl
        ⟦⟨encodeViaEquiv (nonempty_equiv_of_countable (α := N) (β := ℕ)).some,
          encodeViaEquiv_models _ hφN⟩⟧ := by
      unfold codeModel; rw [dif_neg hfinN]
    rw [hM_eq, hN_eq]
    congr 1
    apply Quotient.sound
    show Nonempty _
    exact compose_encoded_iso e _ _

/-- Models mapping to the same coded class are L-isomorphic.
The proof composes: `M ≃[L] carrier` (from `encodeViaEquiv_iso`), the carrier-carrier
L-isomorphism (extracted from the quotient equality in `h`), and `carrier ≃[L] N`
(from `encodeViaEquiv_iso`). -/
theorem iso_of_codeModel_eq
    {M N : Type} [L.Structure M] [L.Structure N] [Countable M] [Countable N]
    (hφM : Sentenceω.Realize φ M) (hφN : Sentenceω.Realize φ N)
    (h : codeModel hφM = codeModel hφN) :
    Nonempty (@Language.Equiv L M N ‹_› ‹_›) := by
  -- M and N have L-isos to their respective carriers via encodeViaEquiv_iso.
  -- The hypothesis h says they land in the same quotient class, which means the decoded
  -- carrier structures are L-isomorphic. We compose: M ≃[L] carrier ≃[L] N.
  -- The proof only needs that M and N are in the same quotient class, not which class.
  -- So we just need: encodeViaEquiv_iso gives M ≃[L] carrier, and if the quotient
  -- classes agree, the carrier structures are L-isomorphic.
  -- Since both are countable models of φ, the L-isomorphism exists.
  -- Use codeModel_eq_of_iso in reverse: if codeModel hφM = codeModel hφN, build the iso.
  -- The simplest approach: both M and N are L-isomorphic to their decoded carrier structures.
  -- If the carriers are the same type AND the decoded structures are L-isomorphic, we're done.
  -- This requires being in the same Sum branch and the same quotient class.
  -- Helper: compose M ≃[L] α ≃[L] α ≃[L] N
  have compose {α : Type} {instα₁ instα₂ : L.Structure α}
      (iM : @Language.Equiv L M α ‹L.Structure M› instα₁)
      (q : @Language.Equiv L α α instα₁ instα₂)
      (iN : @Language.Equiv L N α ‹L.Structure N› instα₂) :
      Nonempty (@Language.Equiv L M N ‹_› ‹_›) :=
    -- inner : M ≃[L] α (instα₂)
    let inner := @Language.Equiv.comp L M α ‹L.Structure M› instα₁ α instα₂ q iM
    -- outer : M ≃[L] N
    ⟨@Language.Equiv.comp L M α ‹L.Structure M› instα₂ N ‹L.Structure N›
      (@Language.Equiv.symm L N α ‹L.Structure N› instα₂ iN) inner⟩
  by_cases hfinM : Finite M
  · -- Finite M → finite N
    have hfinN : Finite N := by
      by_contra hinfN
      unfold codeModel at h; rw [dif_pos hfinM, dif_neg hinfN] at h
      exact absurd h (by simp [Sum.inr_ne_inl])
    haveI := Fintype.ofFinite M; haveI := Fintype.ofFinite N
    set eM := Fintype.equivFin M
    set eN := Fintype.equivFin N
    unfold codeModel at h; rw [dif_pos hfinM, dif_pos hfinN] at h
    -- h : Sum.inr ⟨card M, ⟦⟨encodeViaEquiv eM, _⟩⟧⟩ = Sum.inr ⟨card N, ⟦⟨encodeViaEquiv eN, _⟩⟧⟩
    -- Same pattern as infinite branch but with Sigma-dependent Fin n.
    -- Technical: dependent sigma typing makes extraction fiddly.
    sorry
  · -- Infinite M → infinite N
    haveI : Infinite M := not_finite_iff_infinite.mp hfinM
    have hfinN : ¬Finite N := by
      intro hfN
      unfold codeModel at h; rw [dif_neg hfinM, dif_pos hfN] at h
      exact absurd h (by simp [Sum.inl_ne_inr])
    haveI : Infinite N := not_finite_iff_infinite.mp hfinN
    set eM : M ≃ ℕ := (nonempty_equiv_of_countable (α := M) (β := ℕ)).some
    set eN : N ≃ ℕ := (nonempty_equiv_of_countable (α := N) (β := ℕ)).some
    unfold codeModel at h; rw [dif_neg hfinM, dif_neg hfinN] at h
    obtain ⟨qIso⟩ := Quotient.exact (Sum.inl.inj h)
    obtain ⟨iM⟩ := encodeViaEquiv_iso (L := L) (M := M) eM
    obtain ⟨iN⟩ := encodeViaEquiv_iso (L := L) (M := N) eN
    exact compose iM qIso iN

/-- Every coded class is realized by some countable model. -/
theorem codeModel_surjective :
    ∀ q : AllCodedIsoClasses φ,
    ∃ (M : Type) (_ : L.Structure M) (_ : Countable M)
      (hφ : Sentenceω.Realize φ M), codeModel hφ = q := by
  -- Helper: given a code c on carrier α, decode it and show codeModel maps back
  -- to the same quotient class (up to the encoding isomorphism).
  intro q
  rcases q with ⟨qN⟩ | ⟨n, qFin⟩
  · -- ℕ branch: decode representative, ℕ with its toStructure is the model.
    -- The quotient equality follows from compose_encoded_iso with refl.
    -- Technical: let-bindings from `unfold codeModel` block `rw`/`simp`.
    sorry
  · -- Fin n branch: decode representative, Fin n with its toStructure is the model.
    -- Same pattern as ℕ branch but with Fintype.card (Fin n) = n.
    sorry

end Bridge

end Language

end FirstOrder
