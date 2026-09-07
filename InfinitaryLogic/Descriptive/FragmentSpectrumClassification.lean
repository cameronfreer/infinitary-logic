/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.CountableQuotient
import InfinitaryLogic.Descriptive.FragmentSpectrum

/-!
# From countable sentence spectra to countably many isomorphism classes

API integration, not a classification theorem.  `typeSpectrum_countable_of_determining_cover`
counts the realized types of a fragment across a class; it says nothing about isomorphism.
Passing from countably many arity-zero types to countably many isomorphism classes needs a
**third** obligation, kept visible as a hypothesis here:

* **coverage** — countably many descriptions cover the pointed structures of the class;
* **type determination** — two pointed structures satisfying one description agree on the
  fragment's slice;
* **isomorphism classification** — two members of the class with the same arity-zero
  `F`-type (the same `F`-theory) are isomorphic:

  `∀ c ∈ C, ∀ d ∈ C, F.pointedType c Fin.elim0 = F.pointedType d Fin.elim0 → (structureIsoSetoid L).r c d`.

Neither the cover nor the classification hypothesis is constructed here; both are inputs.
Isomorphism transports the type of a tuple to the type of its image (`pointedType_iso`), so
the classification hypothesis is a genuine restriction on the class and the fragment, not a
consequence of isomorphism invariance.

The two declarations:

* `Fragment.countable_isoQuotient_of_countable_sentenceSpectrum` — countable arity-zero
  spectrum + classification ⇒ the isomorphism quotient of `C` is countable;
* `Fragment.countable_isoQuotient_of_determining_cover` — the determining-cover corollary,
  through the existing spectrum-counting theorem.

The isomorphism quotient of `C` is `Quotient (F.structureIsoSetoidRestrict C)`, the isomorphism relation
pulled back to the subtype `C`.  No Borelness or isomorphism-invariance of `C`, no countability
of the fragment or of the signature, and no rank machinery is used.  Empty classes and
overlapping descriptions are admitted; `scripts/check_fragment_spectrum_classification.lean`
exercises them together with the composition.
-/

namespace FirstOrder.Language

open Set

variable {L : Language.{0, 0}} [L.IsRelational]

/-- Isomorphism of coded structures, restricted to the members of a class. -/
abbrev structureIsoSetoidRestrict (L : Language.{0, 0}) [L.IsRelational] (C : Set (StructureSpace L)) :
    Setoid C :=
  Setoid.comap Subtype.val (structureIsoSetoid L)

namespace Fragment

/-- **Countable sentence spectrum + classification ⇒ countably many isomorphism classes.**
If the realized arity-zero `F`-types on `C` are countable and equal arity-zero `F`-types on
`C` force isomorphism, then `C` has countably many isomorphism classes.  The classification
hypothesis is not derived from anything; it is the third obligation. -/
theorem countable_isoQuotient_of_countable_sentenceSpectrum (F : Fragment L)
    (C : Set (StructureSpace L)) (hspec : (F.typeSpectrum 0 C).Countable)
    (hclass : ∀ c ∈ C, ∀ d ∈ C,
      F.pointedType c Fin.elim0 = F.pointedType d Fin.elim0 → (structureIsoSetoid L).r c d) :
    Countable (Quotient (structureIsoSetoidRestrict L C)) :=
  countable_quotient_of_countable_range (structureIsoSetoidRestrict L C)
    (fun c : C => F.pointedType c.1 Fin.elim0)
    (hspec.mono (by
      rintro _ ⟨c, rfl⟩
      exact mem_typeSpectrum.mpr ⟨c.1, c.2, Fin.elim0, rfl⟩))
    (fun c d h => hclass c.1 c.2 d.1 d.2 h)

/-- **Determining cover + classification ⇒ countably many isomorphism classes.**  A countable
family of sentences covering `C` and determining the `F`-theory, together with the
classification hypothesis, gives countably many isomorphism classes in `C`.  The spectrum
count is `typeSpectrum_countable_of_determining_cover` at arity zero; nothing else enters. -/
theorem countable_isoQuotient_of_determining_cover (F : Fragment L)
    (C : Set (StructureSpace L)) {E : Type*} [Countable E] (χ : E → L.BoundedFormulaω Empty 0)
    (cover : ∀ c ∈ C, ∀ a : Fin 0 → ℕ, ∃ e, c ∈ ModelsOfBounded (χ e) Empty.elim a)
    (det : ∀ e, ∀ c ∈ C, ∀ d ∈ C, ∀ (a b : Fin 0 → ℕ),
      c ∈ ModelsOfBounded (χ e) Empty.elim a → d ∈ ModelsOfBounded (χ e) Empty.elim b →
      ∀ φ : F.slice 0,
        c ∈ ModelsOfBounded φ.1 Empty.elim a ↔ d ∈ ModelsOfBounded φ.1 Empty.elim b)
    (hclass : ∀ c ∈ C, ∀ d ∈ C,
      F.pointedType c Fin.elim0 = F.pointedType d Fin.elim0 → (structureIsoSetoid L).r c d) :
    Countable (Quotient (structureIsoSetoidRestrict L C)) :=
  F.countable_isoQuotient_of_countable_sentenceSpectrum C
    (F.typeSpectrum_countable_of_determining_cover C χ cover det) hclass

end Fragment

end FirstOrder.Language
