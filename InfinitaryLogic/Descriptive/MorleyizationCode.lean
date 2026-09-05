/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.Morleyization
import InfinitaryLogic.Descriptive.SatisfactionBorel
import InfinitaryLogic.Descriptive.StructureIsoSetoid

/-!
# Morleyization on coded structures

The first coded endpoint: a countable relational base `L` and a countable family `Φ`.

* `morleyCode Φ : StructureSpace L → StructureSpace (L.morleyize Φ)` sends a code to the code
  of the canonical expansion of its structure: base coordinates are copied, and the coordinate
  of a defined symbol at a tuple is the truth of the named formula there.
* `toStructure_morleyCode`: the decoded structure of the expansion code is the canonical
  expansion of the decoded structure.
* `measurable_morleyCode`: the map is Borel (base coordinates are projections, defined
  coordinates are `modelsOfBounded_measurableSet`); `morleyCode_injective`: the reduct
  recovers the code.  Hence `measurableEmbedding_morleyCode` (Lusin–Souslin, through
  `Measurable.measurableEmbedding`) and Borel images of Borel classes
  (`measurableSet_image_morleyCode`).
* `range_morleyCode`: the image is exactly the class of expansion codes satisfying the defining
  theory, by uniqueness of expansions satisfying it.
* `morleyCode_iso_iff`: two expansion codes are isomorphic iff the base codes are — the
  classification boundary, from `nonempty_morleyEquiv_iff`.

Borel, not necessarily continuous: a defined coordinate is the truth of an infinitary formula.
The fragment logic topology is a separate construction.
-/

namespace FirstOrder.Language

open MeasureTheory

variable {L : Language.{0, 0}} [L.IsRelational] [Countable (Σ l, L.Relations l)]
  (Φ : Set (Σ n, L.BoundedFormulaω Empty n))

/-- The defined symbols of a countable family form a countable sigma type. -/
instance morleyize_countable_relations [Countable ↥Φ] :
    Countable (Σ n, (L.morleyize Φ).Relations n) := by
  have : Countable (Σ n, DefinedSym Φ n) :=
    (show Function.Injective (fun p : Σ n, DefinedSym Φ n => (⟨⟨p.1, p.2.1⟩, p.2.2⟩ : ↥Φ)) from by
      rintro ⟨n, φ, hφ⟩ ⟨m, ψ, hψ⟩ h
      simp only [Subtype.mk.injEq, Sigma.mk.injEq] at h
      obtain ⟨rfl, h⟩ := h
      cases eq_of_heq h
      rfl).countable
  exact (Equiv.sigmaSumDistrib (fun n => L.Relations n)
    (fun n => DefinedSym Φ n)).injective.countable

/-- **The expansion code**: base coordinates copied, defined coordinates by truth. -/
noncomputable def morleyCode (c : StructureSpace L) : StructureSpace (L.morleyize Φ) :=
  fun q => match q with
    | ⟨⟨n, Sum.inl R⟩, v⟩ => c ⟨⟨n, R⟩, v⟩
    | ⟨⟨_, Sum.inr φ⟩, v⟩ =>
      @decide (c ∈ ModelsOfBounded φ.1 Empty.elim v) (Classical.propDecidable _)

variable {Φ}

omit [Countable (Σ l, L.Relations l)] in
theorem morleyCode_inl (c : StructureSpace L) {n : ℕ} (R : L.Relations n) (v : Fin n → ℕ) :
    morleyCode Φ c ⟨⟨n, Sum.inl R⟩, v⟩ = c ⟨⟨n, R⟩, v⟩ := rfl

omit [Countable (Σ l, L.Relations l)] in
theorem morleyCode_inr (c : StructureSpace L) {n : ℕ} (φ : DefinedSym Φ n) (v : Fin n → ℕ) :
    morleyCode Φ c ⟨⟨n, Sum.inr φ⟩, v⟩ = true ↔ c ∈ ModelsOfBounded φ.1 Empty.elim v := by
  simp [morleyCode]

omit [Countable (Σ l, L.Relations l)] in
/-- The decoded expansion code is the canonical expansion of the decoded base code. -/
theorem toStructure_morleyCode (c : StructureSpace L) :
    (morleyCode Φ c).toStructure = @morleyExpansion L Φ ℕ c.toStructure := by
  refine @Structure.ext (L.morleyize Φ) ℕ _ _ ?_ ?_
  · funext n f
    exact (morleyize_isRelational Φ n).elim f
  · funext n R v
    rcases R with R | φ
    · rfl
    · show (morleyCode Φ c ⟨⟨n, Sum.inr φ⟩, v⟩ = true) = _
      exact propext (morleyCode_inr c φ v)

/-! ## Borel, injective, and the image -/

omit [Countable (Σ l, L.Relations l)] in
/-- **The expansion code is Borel**: base coordinates are projections, defined coordinates are
formula satisfaction. -/
theorem measurable_morleyCode : Measurable (morleyCode Φ) := by
  apply measurable_pi_lambda
  rintro ⟨⟨n, R | φ⟩, v⟩
  · exact measurable_pi_apply _
  · apply measurable_to_bool
    convert modelsOfBounded_measurableSet φ.1 Empty.elim v using 1
    ext c
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact morleyCode_inr c φ v

omit [Countable (Σ l, L.Relations l)] in
/-- **The expansion code is injective**: the base coordinates recover the code. -/
theorem morleyCode_injective : Function.Injective (morleyCode Φ) := by
  intro c d h
  funext ⟨⟨n, R⟩, v⟩
  have := congrFun h ⟨⟨n, Sum.inl R⟩, v⟩
  exact this

/-- **Lusin–Souslin**: the expansion code is a measurable embedding. -/
theorem measurableEmbedding_morleyCode [Countable ↥Φ] : MeasurableEmbedding (morleyCode Φ) :=
  (measurable_morleyCode (Φ := Φ)).measurableEmbedding morleyCode_injective

/-- **Borel images**: the expansion code sends Borel classes to Borel classes. -/
theorem measurableSet_image_morleyCode [Countable ↥Φ] {C : Set (StructureSpace L)}
    (hC : MeasurableSet C) : MeasurableSet (morleyCode Φ '' C) :=
  (measurableEmbedding_morleyCode (Φ := Φ)).measurableSet_image.mpr hC

/-- The base reduct of an expansion code: drop the defined coordinates. -/
def reductCode (d : StructureSpace (L.morleyize Φ)) : StructureSpace L :=
  fun q => d ⟨⟨q.1.1, Sum.inl q.1.2⟩, q.2⟩

omit [Countable (Σ l, L.Relations l)] in
theorem reductCode_morleyCode (c : StructureSpace L) : reductCode (morleyCode Φ c) = c := rfl

omit [Countable (Σ l, L.Relations l)] in
/-- The decoded expansion code is an expansion of its decoded reduct along the inclusion. -/
theorem isExpansionOn_toStructure_reductCode (d : StructureSpace (L.morleyize Φ)) :
    @LHom.IsExpansionOn L (L.morleyize Φ) (lhomMorleyize Φ) ℕ (reductCode d).toStructure
      d.toStructure :=
  @LHom.IsExpansionOn.mk L (L.morleyize Φ) (lhomMorleyize Φ) ℕ (reductCode d).toStructure
    d.toStructure (fun f => (‹L.IsRelational› _).elim f) (fun _ _ => rfl)

omit [Countable (Σ l, L.Relations l)] in
/-- **The image is the class of expansion codes satisfying the defining theory.** -/
theorem range_morleyCode :
    Set.range (morleyCode Φ) =
      {d : StructureSpace (L.morleyize Φ) |
        @Theoryω.Model (L.morleyize Φ) (definingTheory Φ) ℕ d.toStructure} := by
  ext d
  constructor
  · rintro ⟨c, rfl⟩
    show @Theoryω.Model (L.morleyize Φ) (definingTheory Φ) ℕ (morleyCode Φ c).toStructure
    rw [toStructure_morleyCode]
    exact @morleyExpansion_model_definingTheory L Φ ℕ c.toStructure
  · intro hd
    refine ⟨reductCode d, ?_⟩
    have hS : d.toStructure = @morleyExpansion L Φ ℕ (reductCode d).toStructure :=
      @eq_morleyExpansion_of_model_definingTheory L Φ ℕ (reductCode d).toStructure d.toStructure
        (isExpansionOn_toStructure_reductCode d) hd
    have : (morleyCode Φ (reductCode d)).toStructure = d.toStructure := by
      rw [toStructure_morleyCode, hS]
    have hcode := congrArg StructureSpace.ofStructure this
    rwa [StructureSpace.ofStructure_toStructure, StructureSpace.ofStructure_toStructure] at hcode

omit [Countable (Σ l, L.Relations l)] in
/-- **The classification boundary**: expansion codes are isomorphic iff the base codes are. -/
theorem morleyCode_iso_iff (c d : StructureSpace L) :
    (structureIsoSetoid (L.morleyize Φ)).r (morleyCode Φ c) (morleyCode Φ d) ↔
      (structureIsoSetoid L).r c d := by
  show Nonempty (@Language.Equiv (L.morleyize Φ) ℕ ℕ (morleyCode Φ c).toStructure
      (morleyCode Φ d).toStructure) ↔
    Nonempty (@Language.Equiv L ℕ ℕ c.toStructure d.toStructure)
  rw [toStructure_morleyCode, toStructure_morleyCode]
  exact @nonempty_morleyEquiv_iff L Φ ℕ c.toStructure ℕ d.toStructure

end FirstOrder.Language
