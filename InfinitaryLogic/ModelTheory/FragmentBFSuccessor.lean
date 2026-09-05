/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.FragmentBFAdapters
import InfinitaryLogic.Descriptive.FragmentSpectrum
import InfinitaryLogic.ModelTheory.BFExtensionSpectrum

/-!
# Adapter C: counting successor-level classes from types and extension spectra

`countable_bfTupleQuotient_succ` counts the `(α+1)`-classes of `n`-tuples of a class of coded
models from **two** inputs: countably many depth-`α` classes of `n`-tuples, and countably many
realized depth-`α` extension *spectra* (each a set of classes of `(n+1)`-tuples).  Countably
many extension classes do not give countably many sets of them, so the two inputs are
supplied separately and never conflated:

* **Input 1 from fragment types, through adapter B.**  If the bounded Scott formula of every
  tuple at level `α` belongs to `F`, then equal `F`-types force depth-`α` equivalence, so a
  countable realized `F`-type spectrum gives countably many depth-`α` classes
  (`countable_bfTupleQuotient_of_types`).  This uses B (fragment types refine `BFEquiv α`), not
  A.
* **Input 2 from a determining cover on the spectrum map.**  A countable family of descriptions
  covering the tuples, any two tuples sharing a description having the *same whole extension
  spectrum*, gives countably many realized spectra (`countable_bfExtensionSpectra_of_cover`),
  by `Set.countable_image_of_determining_cover` applied directly to `bfExtensionSpectrum`.

`countable_bfTupleQuotient_succ_of_types_and_cover` feeds both to the existing successor
theorem; its conclusion is at `Order.succ α`, the successor visible.  The characterization
`bfTupleSetoid_succ_iff` (α-equivalence together with equal depth-`α` spectra) is used as is.
-/

namespace FirstOrder.Language

open Set

variable {L : Language.{0, 0}} [L.IsRelational]

/-- A quotient is countable when a map with countable range refines the relation: fibres of the
map lie inside classes.  Representative-free apart from one choice per value. -/
theorem countable_quotient_of_countable_range {X T : Type*} (s : Setoid X) (t : X → T)
    (hrange : (Set.range t).Countable) (h : ∀ x y, t x = t y → s.r x y) :
    Countable (Quotient s) := by
  classical
  have : Countable (Set.range t) := hrange.to_subtype
  refine Function.Surjective.countable (f := fun v : Set.range t => Quotient.mk s v.2.choose) ?_
  intro q
  induction q using Quotient.inductionOn with | _ x =>
  refine ⟨⟨t x, x, rfl⟩, Quotient.sound (h _ _ ?_)⟩
  exact (⟨x, rfl⟩ : t x ∈ Set.range t).choose_spec

namespace Fragment

variable [Countable (Σ l, L.Relations l)] (F : Fragment L) (φ : L.Sentenceω)
  (C : Set ↥(ModelsOf φ)) (α : Ordinal.{0}) (n : ℕ)

omit [Countable (Σ l, L.Relations l)] in
/-- The realized `F`-types of the `n`-tuples of `C`-models lie in the spectrum of `F` on the
underlying codes. -/
theorem range_pointedType_subset_typeSpectrum :
    Set.range (fun x : CodedModelTuple φ C n => F.pointedType x.1.1.1 x.2) ⊆
      F.typeSpectrum n (Subtype.val '' C) := by
  rintro _ ⟨x, rfl⟩
  exact mem_typeSpectrum.mpr ⟨x.1.1.1, ⟨x.1.1, x.1.2, rfl⟩, x.2, rfl⟩

/-- **Input 1, from fragment types through adapter B.**  If the bounded Scott formula at level
`α < ω₁` of every `n`-tuple of a `C`-model belongs to `F`, and `F` realizes countably many
`n`-types on the codes of `C`, then there are countably many depth-`α` classes of `n`-tuples. -/
theorem countable_bfTupleQuotient_of_types (hα : α < Ordinal.omega 1)
    (hmem : ∀ x : CodedModelTuple φ C n,
      (⟨n, @scottBounded L _ ℕ x.1.1.1.toStructure _ n x.2 α⟩ :
        Σ n, L.BoundedFormulaω Empty n) ∈ F)
    (htypes : (F.typeSpectrum n (Subtype.val '' C)).Countable) :
    Countable (Quotient (bfTupleSetoid φ C α n)) :=
  countable_quotient_of_countable_range _
    (fun x : CodedModelTuple φ C n => F.pointedType x.1.1.1 x.2)
    (htypes.mono (range_pointedType_subset_typeSpectrum F φ C n))
    fun x y h => @bfEquiv_of_realizedType_eq L _ _ F ℕ x.1.1.1.toStructure _ ℕ y.1.1.1.toStructure
      α hα n x.2 y.2 (hmem x) h

omit [Countable (Σ l, L.Relations l)] in
/-- **Input 2, from a determining cover on the spectrum map.**  Countably many descriptions cover
the `n`-tuples of `C`-models, and any two tuples sharing a description have the same depth-`α`
extension spectrum; then countably many spectra are realized.  Determination is equality of
whole spectra, not of extension classes. -/
theorem countable_bfExtensionSpectra_of_cover {E : Type*} [Countable E]
    (P : E → CodedModelTuple φ C n → Prop) (cover : ∀ x, ∃ e, P e x)
    (det : ∀ e x y, P e x → P e y →
      bfExtensionSpectrum φ C α n x = bfExtensionSpectrum φ C α n y) :
    Countable (bfExtensionSpectra φ C α n) := by
  have := Set.countable_image_of_determining_cover (bfExtensionSpectrum φ C α n) Set.univ P
    (fun x _ => cover x) (fun e x _ y _ hx hy => det e x y hx hy)
  rw [Set.image_univ] at this
  exact this.to_subtype

/-- **Adapter C.**  Both counting inputs, then the existing successor theorem: countably many
`(α+1)`-classes of `n`-tuples.  The successor is visible in the conclusion. -/
theorem countable_bfTupleQuotient_succ_of_types_and_cover (hα : α < Ordinal.omega 1)
    (hmem : ∀ x : CodedModelTuple φ C n,
      (⟨n, @scottBounded L _ ℕ x.1.1.1.toStructure _ n x.2 α⟩ :
        Σ n, L.BoundedFormulaω Empty n) ∈ F)
    (htypes : (F.typeSpectrum n (Subtype.val '' C)).Countable)
    {E : Type*} [Countable E] (P : E → CodedModelTuple φ C n → Prop) (cover : ∀ x, ∃ e, P e x)
    (det : ∀ e x y, P e x → P e y →
      bfExtensionSpectrum φ C α n x = bfExtensionSpectrum φ C α n y) :
    Countable (Quotient (bfTupleSetoid φ C (Order.succ α) n)) :=
  countable_bfTupleQuotient_succ φ C α n
    (countable_bfTupleQuotient_of_types F φ C α n hα hmem htypes)
    (countable_bfExtensionSpectra_of_cover φ C α n P cover det)

end Fragment

end FirstOrder.Language
