/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.FragmentType
import InfinitaryLogic.Descriptive.SentenceRecovery

/-!
# Pointed fragment spectra of coded classes

For a fragment `F`, an arity `n`, and a class `C` of coded structures, the **realized spectrum**
`Fragment.typeSpectrum F n C` is the set of `F`-types of `n`-tuples of naturals in members of
`C`, counted across the whole class: two members realizing the same type contribute one point.

* `Fragment.pointedType F c a` — the realized type at a tuple of a coded structure.
* `pointedType_iso` — pointed isomorphism invariance: an isomorphism of codes transports the
  type of `a` to the type of `e ∘ a`.
* `pointedType_zero_eq_sentenceTheory` — arity zero recovers the sentence interface.
* `typeSpectrum_countable_of_determining_cover` — **the counting theorem**: if a countable
  family of descriptions covers the pointed structures of `C` and any two pointed structures
  of `C` satisfying the same description have the same `F`-type, the spectrum is countable.
  Descriptions may overlap, need not belong to `F`, and carry no measurability.
* `typeSpectrum_singleton_countable`, `typeSpectrum_isoClass` — one code, hence one
  isomorphism class, realizes countably many types at every arity: the countably many tuples
  of one structure.  This is the per-model count that the counting theorem is *not*.
* `measurableSet_pointedRealize`, `measurable_pointedType` — joint measurability in the code
  and the tuple, a countable union over tuples of fixed-tuple measurability.
* `typeSpectrum_countable_iff_encoded` — the Cantor encoding through an enumeration of the
  slice is a comparison theorem, secondary to the intrinsic slice-indexed type.

Empty slices, empty fragments, empty classes, and repeated coordinates are all admitted; the
regression guard `scripts/check_fragment_spectrum_regressions.lean` exercises them.  No
isomorphism-invariance of `C` is assumed anywhere.  The relation between countable spectra at
every arity and thinness (scatteredness) is not established here: the arity-zero direction
follows from the sentence-spectrum characterization, and the pointed-to-unpointed bridge is a
separate theorem with its own descriptive prerequisite.
-/

namespace FirstOrder.Language

open MeasureTheory Set

variable {L : Language.{0, 0}} [L.IsRelational] [Countable (Σ n, L.Relations n)]

namespace Fragment

/-- The realized `F`-type of a tuple of naturals in a coded structure. -/
noncomputable def pointedType (F : Fragment L) (c : StructureSpace L) {n : ℕ}
    (a : Fin n → ℕ) : F.slice n → Bool :=
  @realizedType L F ℕ c.toStructure n a

omit [Countable (Σ n, L.Relations n)] in
theorem pointedType_apply_iff (F : Fragment L) (c : StructureSpace L) {n : ℕ} (a : Fin n → ℕ)
    (φ : F.slice n) :
    F.pointedType c a φ = true ↔ c ∈ ModelsOfBounded φ.1 Empty.elim a :=
  @realizedType_apply_iff L F ℕ c.toStructure n a φ

omit [Countable (Σ n, L.Relations n)] in
/-- **Pointed isomorphism invariance** on codes. -/
theorem pointedType_iso (F : Fragment L) {c d : StructureSpace L}
    (e : @Language.Equiv L ℕ ℕ c.toStructure d.toStructure) {n : ℕ} (a : Fin n → ℕ) :
    F.pointedType d (e ∘ a) = F.pointedType c a :=
  @realizedType_equiv L F ℕ ℕ c.toStructure d.toStructure e n a

omit [Countable (Σ n, L.Relations n)] in
/-- **Arity zero is the sentence interface**: a sentence list inside `F` has the truth sequence
read off the arity-zero pointed type. -/
theorem pointedType_zero_eq_sentenceTheory (F : Fragment L) (θ : ℕ → L.Sentenceω)
    (hθ : ∀ k, (⟨0, θ k⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ F) (c : StructureSpace L) :
    sentenceTheory θ c = fun k => F.pointedType c Fin.elim0 ⟨θ k, hθ k⟩ := by
  funext k
  exact decide_eq_decide.mpr Iff.rfl

/-! ## The spectrum -/

/-- **The realized spectrum** of `F` at arity `n` on a class `C`: the types of all `n`-tuples of
all members, counted across the class. -/
def typeSpectrum (F : Fragment L) (n : ℕ) (C : Set (StructureSpace L)) :
    Set (F.slice n → Bool) :=
  (fun p : StructureSpace L × (Fin n → ℕ) => F.pointedType p.1 p.2) '' (C ×ˢ Set.univ)

omit [Countable (Σ n, L.Relations n)] in
theorem mem_typeSpectrum {F : Fragment L} {n : ℕ} {C : Set (StructureSpace L)}
    {t : F.slice n → Bool} :
    t ∈ F.typeSpectrum n C ↔ ∃ c ∈ C, ∃ a : Fin n → ℕ, F.pointedType c a = t := by
  constructor
  · rintro ⟨⟨c, a⟩, ⟨hc, -⟩, rfl⟩
    exact ⟨c, hc, a, rfl⟩
  · rintro ⟨c, hc, a, rfl⟩
    exact ⟨⟨c, a⟩, ⟨hc, Set.mem_univ _⟩, rfl⟩

omit [Countable (Σ n, L.Relations n)] in
theorem typeSpectrum_empty (F : Fragment L) (n : ℕ) : F.typeSpectrum n ∅ = ∅ := by
  simp [typeSpectrum]

omit [Countable (Σ n, L.Relations n)] in
theorem typeSpectrum_mono (F : Fragment L) (n : ℕ) {C D : Set (StructureSpace L)}
    (h : C ⊆ D) : F.typeSpectrum n C ⊆ F.typeSpectrum n D :=
  Set.image_mono (Set.prod_mono h subset_rfl)

omit [Countable (Σ n, L.Relations n)] in
/-- **One code realizes countably many types**: the countably many tuples of one structure.
This is the per-model count, not the counting theorem. -/
theorem typeSpectrum_singleton_countable (F : Fragment L) (n : ℕ) (c : StructureSpace L) :
    (F.typeSpectrum n {c}).Countable := by
  refine (Set.countable_range fun a : Fin n → ℕ => F.pointedType c a).mono ?_
  rintro t ht
  obtain ⟨d, hd, a, rfl⟩ := mem_typeSpectrum.mp ht
  rw [Set.mem_singleton_iff.mp hd]
  exact ⟨a, rfl⟩

omit [Countable (Σ n, L.Relations n)] in
/-- The spectrum of an isomorphism class is the spectrum of any representative. -/
theorem typeSpectrum_isoClass (F : Fragment L) (n : ℕ) (c : StructureSpace L) :
    F.typeSpectrum n {d | (structureIsoSetoid L).r c d} = F.typeSpectrum n {c} := by
  ext t
  simp only [mem_typeSpectrum, Set.mem_ofPred_eq, Set.mem_singleton_iff, exists_eq_left]
  constructor
  · rintro ⟨d, ⟨e⟩, a, rfl⟩
    let e' := @Language.Equiv.symm L ℕ ℕ c.toStructure d.toStructure e
    refine ⟨⇑e' ∘ a, ?_⟩
    have := F.pointedType_iso e (⇑e' ∘ a)
    rw [show (⇑e ∘ (⇑e' ∘ a)) = a from funext fun i =>
      (@Language.Equiv.toEquiv L ℕ ℕ c.toStructure d.toStructure e).apply_symm_apply (a i)] at this
    exact this.symm
  · rintro ⟨a, rfl⟩
    exact ⟨c, (structureIsoSetoid L).refl c, a, rfl⟩

omit [Countable (Σ n, L.Relations n)] in
theorem typeSpectrum_isoClass_countable (F : Fragment L) (n : ℕ) (c : StructureSpace L) :
    (F.typeSpectrum n {d | (structureIsoSetoid L).r c d}).Countable := by
  rw [typeSpectrum_isoClass]
  exact typeSpectrum_singleton_countable F n c

/-! ## The counting theorem -/

omit [Countable (Σ n, L.Relations n)] in
/-- **Countable spectrum from a determining cover.**  A countable family of descriptions
`χ e` (formulas of arity `n`, not necessarily in `F`) covers the pointed structures of `C`, and
any two pointed structures of `C` satisfying the same description agree on every member of the
slice; then the realized spectrum of `F` at arity `n` on `C` is countable.  Overlapping
descriptions and repeated tuple coordinates are admitted; no measurability of the cover is
used. -/
theorem typeSpectrum_countable_of_determining_cover (F : Fragment L) {n : ℕ}
    (C : Set (StructureSpace L)) {E : Type*} [Countable E] (χ : E → L.BoundedFormulaω Empty n)
    (cover : ∀ c ∈ C, ∀ a : Fin n → ℕ, ∃ e, c ∈ ModelsOfBounded (χ e) Empty.elim a)
    (det : ∀ e, ∀ c ∈ C, ∀ d ∈ C, ∀ (a b : Fin n → ℕ),
      c ∈ ModelsOfBounded (χ e) Empty.elim a → d ∈ ModelsOfBounded (χ e) Empty.elim b →
      ∀ φ : F.slice n,
        c ∈ ModelsOfBounded φ.1 Empty.elim a ↔ d ∈ ModelsOfBounded φ.1 Empty.elim b) :
    (F.typeSpectrum n C).Countable := by
  refine Set.countable_image_of_determining_cover _ (C ×ˢ Set.univ)
    (fun e p => p.1 ∈ ModelsOfBounded (χ e) Empty.elim p.2) ?_ ?_
  · rintro ⟨c, a⟩ ⟨hc, -⟩
    exact cover c hc a
  · rintro e ⟨c, a⟩ ⟨hc, -⟩ ⟨d, b⟩ ⟨hd, -⟩ hca hdb
    funext φ
    exact decide_eq_decide.mpr (det e c hc d hd a b hca hdb φ)

/-! ## Joint measurability in the code and the tuple -/

omit [L.IsRelational] [Countable (Σ n, L.Relations n)] in
theorem measurableSet_pointedRealize [L.IsRelational] {n : ℕ} (φ : L.BoundedFormulaω Empty n) :
    MeasurableSet
      {p : StructureSpace L × (Fin n → ℕ) | p.1 ∈ ModelsOfBounded φ Empty.elim p.2} := by
  have : {p : StructureSpace L × (Fin n → ℕ) | p.1 ∈ ModelsOfBounded φ Empty.elim p.2}
      = ⋃ a : Fin n → ℕ, ModelsOfBounded φ Empty.elim a ×ˢ {a} := by
    ext ⟨c, a⟩
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff]
    exact ⟨fun h => ⟨a, h, rfl⟩, fun ⟨b, hb, hab⟩ => hab ▸ hb⟩
  rw [this]
  exact MeasurableSet.iUnion fun a =>
    (modelsOfBounded_measurableSet φ Empty.elim a).prod (measurableSet_singleton a)

omit [Countable (Σ n, L.Relations n)] in
/-- The pointed type is jointly measurable in the code and the tuple. -/
theorem measurable_pointedType (F : Fragment L) (n : ℕ) :
    Measurable fun p : StructureSpace L × (Fin n → ℕ) => F.pointedType p.1 p.2 := by
  apply measurable_pi_lambda
  intro φ
  apply measurable_to_bool
  convert measurableSet_pointedRealize (L := L) φ.1 using 1
  ext p
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  exact pointedType_apply_iff F p.1 p.2 φ

/-! ## The Cantor encoding, as a comparison -/

omit [Countable (Σ n, L.Relations n)] in
/-- **The Cantor encoding is secondary.**  Through a surjective enumeration of the slice, the
spectrum is countable iff its encoded image in Cantor space is: the encoding is injective on
types. -/
theorem typeSpectrum_countable_iff_encoded (F : Fragment L) (n : ℕ) (C : Set (StructureSpace L))
    (s : ℕ → F.slice n) (hs : Function.Surjective s) :
    (F.typeSpectrum n C).Countable ↔
      ((fun t : F.slice n → Bool => t ∘ s) '' F.typeSpectrum n C).Countable := by
  have hinj : Function.Injective fun t : F.slice n → Bool => t ∘ s := fun t u h => by
    funext φ
    obtain ⟨k, rfl⟩ := hs φ
    exact congrFun h k
  exact ⟨fun h => h.image _,
    fun h => (h.preimage_of_injOn hinj.injOn).mono (Set.subset_preimage_image _ _)⟩

end Fragment

end FirstOrder.Language
