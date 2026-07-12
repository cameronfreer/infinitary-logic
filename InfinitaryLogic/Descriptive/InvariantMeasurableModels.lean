/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.InvariantMeasurableSpace

/-!
# Compatibility of the invariant σ-algebras with the Borel structure (issue #28, commit 2)

The invariant σ-algebras of `InvariantMeasurableSpace.lean` sit *below* the ambient product
(Borel) σ-algebra, and the model classes `ModelsOf φ` are measurable in them.

- `MeasurableSpace.smulInvariant_le` (and the named `actionInvariantMeasurableSpace_le`,
  `isoInvariantMeasurableSpace_le`): the invariant σ-algebra is **coarser** than the base one, so
  the identity `X → X` from the base space to the invariant space is measurable
  (`measurable_id_smulInvariant` and the named forms) — the correct direction.
- `measurableSet_isoInvariant_modelsOf` / `measurableSet_actionInvariant_modelsOf`: `ModelsOf φ` is
  measurable in either named invariant σ-algebra, under exactly the hypotheses of the existing
  satisfaction-measurability theorem `modelsOf_measurableSet` (relational vocabulary only — no
  countability, no Polishness).
- `MeasurableSet.of_actionInvariant` / `MeasurableSet.of_isoInvariant` and
  `measurableSet_actionInvariant_iff_isoInvariant`: convenience lemmas for consuming these
  statements without temporarily installing a global `MeasurableSpace` instance.
-/

open MeasureTheory

namespace MeasurableSpace

/-- The generic invariant σ-algebra is coarser than its base. -/
theorem smulInvariant_le {G X : Type*} [SMul G X] (m : MeasurableSpace X) :
    MeasurableSpace.smulInvariant G m ≤ m := fun _ hB => hB.1

/-- The identity from the base space to the (coarser) invariant σ-algebra is measurable. -/
theorem measurable_id_smulInvariant {G X : Type*} [SMul G X] (m : MeasurableSpace X) :
    Measurable[m, MeasurableSpace.smulInvariant G m] (id : X → X) :=
  fun _ hs => (smulInvariant_le (G := G) m) _ hs

end MeasurableSpace

namespace FirstOrder.Language

variable {L : Language.{0, 0}}

/-! ## Coarseness and the identity map -/

/-- `actionInvariantMeasurableSpace` is coarser than the ambient product σ-algebra. -/
theorem actionInvariantMeasurableSpace_le :
    (actionInvariantMeasurableSpace : MeasurableSpace (StructureSpace L))
      ≤ inferInstanceAs (MeasurableSpace (StructureSpace L)) :=
  fun _ hB => hB.1

/-- `isoInvariantMeasurableSpace` is coarser than the ambient product σ-algebra. -/
theorem isoInvariantMeasurableSpace_le [L.IsRelational] :
    (isoInvariantMeasurableSpace : MeasurableSpace (StructureSpace L))
      ≤ inferInstanceAs (MeasurableSpace (StructureSpace L)) :=
  fun _ hB => hB.1

/-- The identity from the ambient Borel space to `actionInvariantMeasurableSpace` is measurable. -/
theorem measurable_id_actionInvariant :
    Measurable[inferInstanceAs (MeasurableSpace (StructureSpace L)), actionInvariantMeasurableSpace]
      (id : StructureSpace L → StructureSpace L) :=
  fun _ hs => actionInvariantMeasurableSpace_le _ hs

/-- The identity from the ambient Borel space to `isoInvariantMeasurableSpace` is measurable. -/
theorem measurable_id_isoInvariant [L.IsRelational] :
    Measurable[inferInstanceAs (MeasurableSpace (StructureSpace L)), isoInvariantMeasurableSpace]
      (id : StructureSpace L → StructureSpace L) :=
  fun _ hs => isoInvariantMeasurableSpace_le _ hs

/-! ## Consuming invariant-measurability -/

/-- An action-invariant-measurable class is measurable in the ambient Borel space. -/
theorem MeasurableSet.of_actionInvariant {B : Set (StructureSpace L)}
    (h : MeasurableSet[actionInvariantMeasurableSpace] B) : MeasurableSet B := h.1

/-- An isomorphism-invariant-measurable class is measurable in the ambient Borel space. -/
theorem MeasurableSet.of_isoInvariant [L.IsRelational] {B : Set (StructureSpace L)}
    (h : MeasurableSet[isoInvariantMeasurableSpace] B) : MeasurableSet B := h.1

/-- The two invariant σ-algebras have the same measurable sets — a convenient bridge for consuming
either statement without installing a global instance. -/
theorem measurableSet_actionInvariant_iff_isoInvariant [L.IsRelational]
    {B : Set (StructureSpace L)} :
    MeasurableSet[actionInvariantMeasurableSpace] B ↔ MeasurableSet[isoInvariantMeasurableSpace] B :=
  by rw [actionInvariantMeasurableSpace_eq_isoInvariantMeasurableSpace]

/-! ## Model classes are invariant-measurable -/

/-- **`ModelsOf φ` is isomorphism-invariant-measurable** — under exactly the hypothesis of the
satisfaction-measurability theorem (relational vocabulary; no countability, no Polishness). -/
theorem measurableSet_isoInvariant_modelsOf [L.IsRelational] (φ : L.Sentenceω) :
    MeasurableSet[isoInvariantMeasurableSpace] (ModelsOf φ) :=
  measurableSet_isoInvariantMeasurableSpace.mpr (modelsOf_measurable_invariant φ)

/-- **`ModelsOf φ` is action-invariant-measurable** — same hypothesis. -/
theorem measurableSet_actionInvariant_modelsOf [L.IsRelational] (φ : L.Sentenceω) :
    MeasurableSet[actionInvariantMeasurableSpace] (ModelsOf φ) :=
  measurableSet_actionInvariantMeasurableSpace.mpr
    ⟨modelsOf_measurableSet φ,
      (actionInvariant_iff_isomorphismInvariant _).mpr (isomorphismInvariant_modelsOf φ)⟩

end FirstOrder.Language
