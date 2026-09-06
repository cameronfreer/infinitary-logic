/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.FragmentSpectrum

/-!
# The realized-spectrum relation is Borel

For a fragment `F` and an arity `n`, the **realized spectrum** of a coded structure `c` is the
set of `F`-types of its `n`-tuples, `Fragment.realizedSpectrum F n c`.  Two codes are
`F,n`-**spectrum equivalent** (`SameRealizedSpectrum`) when they realize the same spectrum: every
tuple of one has a matching tuple in the other, where matching means agreement on every member of
the slice.  Tuples and the slice are countable, so the relation is a countable combination of
Borel satisfaction conditions (`measurableSet_sameRealizedSpectrum`).  No topology on a powerset
of types is needed.

Isomorphism refines the relation (`sameRealizedSpectrum_of_iso`): the pointed-type transport
sends tuples to tuples of the same type.  The converse is not claimed.

Everything here is below Silver; the dichotomy and the thinness characterization are in
`Conditional/FragmentSpectrumThin.lean`.

Classical background: Marker, *Lectures on Infinitary Model Theory* (Cambridge, 2016),
Corollary 3.3.3, works with the relation of realizing the same fragment types.
-/

namespace FirstOrder.Language

open MeasureTheory Set

variable {L : Language.{0, 0}} [L.IsRelational] [Countable (Σ n, L.Relations n)]

namespace Fragment

omit [L.IsRelational] [Countable (Σ n, L.Relations n)] in
/-- The arity slice of a countable fragment is countable. -/
theorem slice_countable {F : Fragment L} (hF : F.toSet.Countable) (n : ℕ) :
    Countable (F.slice n) := by
  have : Countable F.toSet := hF.to_subtype
  exact (show Function.Injective (fun φ : F.slice n => (⟨⟨n, φ.1⟩, φ.2⟩ : F.toSet)) from by
    rintro ⟨φ, _⟩ ⟨ψ, _⟩ h
    simp only [Subtype.mk.injEq, Sigma.mk.injEq, heq_eq_eq, true_and] at h
    exact Subtype.ext h).countable

/-- **The realized spectrum** of a code at arity `n`: the `F`-types of its `n`-tuples. -/
def realizedSpectrum (F : Fragment L) (n : ℕ) (c : StructureSpace L) : Set (F.slice n → Bool) :=
  Set.range fun a : Fin n → ℕ => F.pointedType c a

omit [Countable (Σ n, L.Relations n)] in
theorem realizedSpectrum_eq_typeSpectrum_singleton (F : Fragment L) (n : ℕ)
    (c : StructureSpace L) : F.realizedSpectrum n c = F.typeSpectrum n {c} := by
  ext t
  rw [mem_typeSpectrum]
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨c, rfl, a, rfl⟩
  · rintro ⟨d, rfl, a, rfl⟩; exact ⟨a, rfl⟩

omit [Countable (Σ n, L.Relations n)] in
theorem realizedSpectrum_countable (F : Fragment L) (n : ℕ) (c : StructureSpace L) :
    (F.realizedSpectrum n c).Countable :=
  Set.countable_range _

/-- **Spectrum equivalence**: the two codes realize the same `F`-types at arity `n`. -/
def SameRealizedSpectrum (F : Fragment L) (n : ℕ) (c d : StructureSpace L) : Prop :=
  F.realizedSpectrum n c = F.realizedSpectrum n d

omit [Countable (Σ n, L.Relations n)] in
/-- Spectrum equivalence, expanded: every tuple of each code has a matching tuple in the other. -/
theorem sameRealizedSpectrum_iff (F : Fragment L) (n : ℕ) (c d : StructureSpace L) :
    F.SameRealizedSpectrum n c d ↔
      (∀ a : Fin n → ℕ, ∃ b : Fin n → ℕ, F.pointedType c a = F.pointedType d b) ∧
      (∀ b : Fin n → ℕ, ∃ a : Fin n → ℕ, F.pointedType d b = F.pointedType c a) := by
  constructor
  · intro h
    refine ⟨fun a => ?_, fun b => ?_⟩
    · have : F.pointedType c a ∈ F.realizedSpectrum n d := h ▸ ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := this
      exact ⟨b, hb.symm⟩
    · have : F.pointedType d b ∈ F.realizedSpectrum n c := h.symm ▸ ⟨b, rfl⟩
      obtain ⟨a, ha⟩ := this
      exact ⟨a, ha.symm⟩
  · rintro ⟨h₁, h₂⟩
    ext t
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := h₁ a
      exact ⟨b, hb.symm⟩
    · rintro ⟨b, rfl⟩
      obtain ⟨a, ha⟩ := h₂ b
      exact ⟨a, ha.symm⟩

omit [Countable (Σ n, L.Relations n)] in
theorem sameRealizedSpectrum_refl (F : Fragment L) (n : ℕ) (c : StructureSpace L) :
    F.SameRealizedSpectrum n c c := rfl

omit [Countable (Σ n, L.Relations n)] in
theorem sameRealizedSpectrum_symm (F : Fragment L) (n : ℕ) {c d : StructureSpace L}
    (h : F.SameRealizedSpectrum n c d) : F.SameRealizedSpectrum n d c := h.symm

omit [Countable (Σ n, L.Relations n)] in
theorem sameRealizedSpectrum_trans (F : Fragment L) (n : ℕ) {c d e : StructureSpace L}
    (h₁ : F.SameRealizedSpectrum n c d) (h₂ : F.SameRealizedSpectrum n d e) :
    F.SameRealizedSpectrum n c e := h₁.trans h₂

/-- The spectrum-equivalence setoid. -/
def sameRealizedSpectrumSetoid (F : Fragment L) (n : ℕ) : Setoid (StructureSpace L) where
  r := F.SameRealizedSpectrum n
  iseqv := ⟨sameRealizedSpectrum_refl F n, sameRealizedSpectrum_symm F n,
    sameRealizedSpectrum_trans F n⟩

omit [Countable (Σ n, L.Relations n)] in
/-- **Isomorphism refines spectrum equivalence.** -/
theorem sameRealizedSpectrum_of_iso (F : Fragment L) (n : ℕ) {c d : StructureSpace L}
    (h : (structureIsoSetoid L).r c d) : F.SameRealizedSpectrum n c d := by
  unfold SameRealizedSpectrum
  rw [realizedSpectrum_eq_typeSpectrum_singleton, realizedSpectrum_eq_typeSpectrum_singleton,
    ← typeSpectrum_isoClass F n c, ← typeSpectrum_isoClass F n d]
  congr 1
  ext e
  exact ⟨fun h' => (structureIsoSetoid L).trans ((structureIsoSetoid L).symm h) h',
    fun h' => (structureIsoSetoid L).trans h h'⟩

/-! ## Borelness -/

omit [Countable (Σ n, L.Relations n)] in
/-- Pointed types agree at `(c, a)` and `(d, b)`: a countable intersection over the slice. -/
private theorem measurableSet_pointedType_eq (F : Fragment L) {n : ℕ} (hF : F.toSet.Countable)
    (a b : Fin n → ℕ) :
    MeasurableSet {p : StructureSpace L × StructureSpace L |
      F.pointedType p.1 a = F.pointedType p.2 b} := by
  have : Countable (F.slice n) := slice_countable hF n
  have heq : {p : StructureSpace L × StructureSpace L | F.pointedType p.1 a = F.pointedType p.2 b}
      = ⋂ φ : F.slice n, {p | p.1 ∈ ModelsOfBounded φ.1 Empty.elim a ↔
          p.2 ∈ ModelsOfBounded φ.1 Empty.elim b} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, funext_iff]
    refine forall_congr' fun φ => ?_
    rw [← pointedType_apply_iff, ← pointedType_apply_iff]
    constructor
    · intro h; rw [h]
    · intro h
      cases h1 : F.pointedType p.1 a φ <;> cases h2 : F.pointedType p.2 b φ <;> simp_all
  rw [heq]
  refine MeasurableSet.iInter fun φ => ?_
  have hA : MeasurableSet (Prod.fst ⁻¹' ModelsOfBounded φ.1 Empty.elim a :
      Set (StructureSpace L × StructureSpace L)) :=
    (modelsOfBounded_measurableSet φ.1 Empty.elim a).preimage measurable_fst
  have hB : MeasurableSet (Prod.snd ⁻¹' ModelsOfBounded φ.1 Empty.elim b :
      Set (StructureSpace L × StructureSpace L)) :=
    (modelsOfBounded_measurableSet φ.1 Empty.elim b).preimage measurable_snd
  have : {p : StructureSpace L × StructureSpace L | p.1 ∈ ModelsOfBounded φ.1 Empty.elim a ↔
      p.2 ∈ ModelsOfBounded φ.1 Empty.elim b}
      = (Prod.fst ⁻¹' ModelsOfBounded φ.1 Empty.elim a ∩
          Prod.snd ⁻¹' ModelsOfBounded φ.1 Empty.elim b)
        ∪ ((Prod.fst ⁻¹' ModelsOfBounded φ.1 Empty.elim a)ᶜ ∩
          (Prod.snd ⁻¹' ModelsOfBounded φ.1 Empty.elim b)ᶜ) := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_compl_iff]
    tauto
  rw [this]
  exact (hA.inter hB).union (hA.compl.inter hB.compl)

omit [Countable (Σ n, L.Relations n)] in
/-- **Spectrum equivalence is Borel** for a countable fragment: countable unions and
intersections over tuples of the agreement conditions. -/
theorem measurableSet_sameRealizedSpectrum (F : Fragment L) (n : ℕ) (hF : F.toSet.Countable) :
    MeasurableSet {p : StructureSpace L × StructureSpace L | F.SameRealizedSpectrum n p.1 p.2} := by
  have heq : {p : StructureSpace L × StructureSpace L | F.SameRealizedSpectrum n p.1 p.2}
      = (⋂ a : Fin n → ℕ, ⋃ b : Fin n → ℕ, {p | F.pointedType p.1 a = F.pointedType p.2 b}) ∩
        (⋂ b : Fin n → ℕ, ⋃ a : Fin n → ℕ, {p | F.pointedType p.2 b = F.pointedType p.1 a}) := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_iUnion]
    exact sameRealizedSpectrum_iff F n p.1 p.2
  rw [heq]
  refine MeasurableSet.inter (MeasurableSet.iInter fun a => MeasurableSet.iUnion fun b => ?_)
    (MeasurableSet.iInter fun b => MeasurableSet.iUnion fun a => ?_)
  · exact measurableSet_pointedType_eq F hF a b
  · have := (measurableSet_pointedType_eq F hF b a).preimage
      (measurable_snd.prodMk measurable_fst :
        Measurable fun p : StructureSpace L × StructureSpace L => (p.2, p.1))
    convert this using 1
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]

end Fragment

end FirstOrder.Language
