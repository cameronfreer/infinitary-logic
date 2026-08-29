/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.MorleyCounting

/-!
# Back-and-forth successor levels via extension spectra

For a class `C` of coded models of a sentence `φ` and an ordinal `α`, the depth-`α`
back-and-forth relation on `n`-tuples of `C`-models is an equivalence relation
(`bfTupleSetoid`).  By `BFEquiv.succ`, two tuples are `(α+1)`-equivalent iff they are
`α`-equivalent and have the same set of depth-`α` classes of one-point extensions — their
**depth-`α` extension spectrum** (`bfExtensionSpectrum`).  So the `(α+1)`-classes over
`n`-tuples are counted by the `α`-classes together with the realized extension spectra.

## Main results

* `bfTupleSetoid_succ_iff` — `(α+1)`-equivalence is `α`-equivalence together with equality of
  extension spectra, for every arity and every class of models.
* `bfExtensionSpectra` — the realized extension spectra, the range of `bfExtensionSpectrum`.
* `countable_bfTupleQuotient_succ` — countably many `α`-classes over `n`-tuples and countably
  many realized extension spectra give countably many `(α+1)`-classes over `n`-tuples.
* `mk_bfTupleQuotient_succ_le_aleph_one` — the same transfer with `≤ ℵ₁` on both inputs.
* `bfTupleSetoid_zero_eq_comap` — at arity `0` the setoid is the pullback of `bfEquivSetoid`
  along the forgetful map to the underlying coded model (the tuple is trivial, and the class
  membership is forgotten); `bfTupleSetoid_zero_iff` is the pointwise form.

The hypothesis on the extension spectra is the whole content: a subset of a countable class
space can a priori take continuum many values, so nothing here bounds the spectra themselves.
Nothing is said about limit levels.
-/

universe u v

namespace FirstOrder

namespace Language

open Cardinal

variable {L : Language.{u, v}} [L.IsRelational]

/-- Coded models of `φ` in a class `C`, each with an `n`-tuple. -/
abbrev CodedModelTuple (φ : L.Sentenceω) (C : Set ↥(ModelsOf φ)) (n : ℕ) :=
  C × (Fin n → ℕ)

/-- The depth-`α` back-and-forth setoid on `n`-tuples of `C`-models. -/
def bfTupleSetoid (φ : L.Sentenceω) (C : Set ↥(ModelsOf φ)) (α : Ordinal.{0}) (n : ℕ) :
    Setoid (CodedModelTuple φ C n) where
  r x y := @BFEquiv L ℕ x.1.1.1.toStructure ℕ y.1.1.1.toStructure α n x.2 y.2
  iseqv := by
    refine ⟨fun x => ?_, fun {x y} h => ?_, fun {x y z} h₁ h₂ => ?_⟩
    · exact @BFEquiv.refl L ℕ x.1.1.1.toStructure n α x.2
    · exact @BFEquiv.symm L ℕ x.1.1.1.toStructure ℕ y.1.1.1.toStructure n α x.2 y.2 h
    · exact @BFEquiv.trans L ℕ x.1.1.1.toStructure ℕ y.1.1.1.toStructure
        ℕ z.1.1.1.toStructure (n := n) (α := α) (a := x.2) (b := y.2) (c := z.2) h₁ h₂

/-- At arity `0` the tuple is trivial, and the setoid is the pullback of `bfEquivSetoid` along
the map forgetting the class membership and the empty tuple. -/
theorem bfTupleSetoid_zero_eq_comap (φ : L.Sentenceω) (C : Set ↥(ModelsOf φ))
    (α : Ordinal.{0}) :
    bfTupleSetoid φ C α 0 =
      (bfEquivSetoid φ α).comap (fun x : CodedModelTuple φ C 0 => x.1.1) := by
  ext x y
  change @BFEquiv L ℕ x.1.1.1.toStructure ℕ y.1.1.1.toStructure α 0 x.2 y.2 ↔
    @BFEquiv L ℕ x.1.1.1.toStructure ℕ y.1.1.1.toStructure α 0 Fin.elim0 Fin.elim0
  rw [Fin.eq_elim0 x.2, Fin.eq_elim0 y.2]

/-- The pointwise form of `bfTupleSetoid_zero_eq_comap`. -/
theorem bfTupleSetoid_zero_iff (φ : L.Sentenceω) (C : Set ↥(ModelsOf φ)) (α : Ordinal.{0})
    (x y : CodedModelTuple φ C 0) :
    (bfTupleSetoid φ C α 0).r x y ↔ (bfEquivSetoid φ α).r x.1.1 y.1.1 := by
  rw [bfTupleSetoid_zero_eq_comap]
  exact Iff.rfl

/-- **The depth-`α` extension spectrum** of a tuple: the depth-`α` classes of its one-point
extensions. -/
def bfExtensionSpectrum (φ : L.Sentenceω) (C : Set ↥(ModelsOf φ)) (α : Ordinal.{0}) (n : ℕ)
    (x : CodedModelTuple φ C n) : Set (Quotient (bfTupleSetoid φ C α (n + 1))) :=
  Set.range (fun m : ℕ => Quotient.mk (bfTupleSetoid φ C α (n + 1)) (x.1, Fin.snoc x.2 m))

/-- **The realized extension spectra** of `n`-tuples of `C`-models at depth `α`. -/
def bfExtensionSpectra (φ : L.Sentenceω) (C : Set ↥(ModelsOf φ)) (α : Ordinal.{0}) (n : ℕ) :
    Set (Set (Quotient (bfTupleSetoid φ C α (n + 1)))) :=
  Set.range (bfExtensionSpectrum φ C α n)

/-- **The successor characterization**: `(α+1)`-equivalence is `α`-equivalence with equal
depth-`α` extension spectra. -/
theorem bfTupleSetoid_succ_iff (φ : L.Sentenceω) (C : Set ↥(ModelsOf φ)) (α : Ordinal.{0})
    (n : ℕ) (x y : CodedModelTuple φ C n) :
    (bfTupleSetoid φ C (Order.succ α) n).r x y ↔
      (bfTupleSetoid φ C α n).r x y ∧
        bfExtensionSpectrum φ C α n x = bfExtensionSpectrum φ C α n y := by
  change @BFEquiv L ℕ x.1.1.1.toStructure ℕ y.1.1.1.toStructure (Order.succ α) n x.2 y.2 ↔ _
  rw [@BFEquiv.succ L ℕ x.1.1.1.toStructure ℕ y.1.1.1.toStructure n α x.2 y.2]
  constructor
  · rintro ⟨h0, hforth, hback⟩
    refine ⟨h0, Set.Subset.antisymm ?_ ?_⟩
    · rintro _ ⟨m, rfl⟩
      obtain ⟨m', hm'⟩ := hforth m
      exact ⟨m', (Quotient.sound hm').symm⟩
    · rintro _ ⟨m', rfl⟩
      obtain ⟨m, hm⟩ := hback m'
      exact ⟨m, Quotient.sound hm⟩
  · rintro ⟨h0, hspec⟩
    refine ⟨h0, fun m => ?_, fun m' => ?_⟩
    · have hmem : Quotient.mk (bfTupleSetoid φ C α (n + 1)) (x.1, Fin.snoc x.2 m) ∈
          bfExtensionSpectrum φ C α n x := ⟨m, rfl⟩
      rw [hspec] at hmem
      obtain ⟨m', hm'⟩ := hmem
      exact ⟨m', Quotient.exact hm'.symm⟩
    · have hmem : Quotient.mk (bfTupleSetoid φ C α (n + 1)) (y.1, Fin.snoc y.2 m') ∈
          bfExtensionSpectrum φ C α n y := ⟨m', rfl⟩
      rw [← hspec] at hmem
      obtain ⟨m, hm⟩ := hmem
      exact ⟨m, Quotient.exact hm⟩

/-- The `(α+1)`-classes over `n`-tuples inject into pairs (an `α`-class, a realized extension
spectrum). -/
theorem exists_injective_bfTupleQuotient_succ (φ : L.Sentenceω) (C : Set ↥(ModelsOf φ))
    (α : Ordinal.{0}) (n : ℕ) :
    ∃ f : Quotient (bfTupleSetoid φ C (Order.succ α) n) →
      Quotient (bfTupleSetoid φ C α n) × bfExtensionSpectra φ C α n,
      Function.Injective f := by
  refine ⟨Quotient.lift
    (fun x => (Quotient.mk (bfTupleSetoid φ C α n) x,
      ⟨bfExtensionSpectrum φ C α n x, Set.mem_range_self x⟩))
    (fun x y h => by
      obtain ⟨h0, hs⟩ := (bfTupleSetoid_succ_iff φ C α n x y).mp h
      exact Prod.ext (Quotient.sound h0) (Subtype.ext hs)), ?_⟩
  intro q₁ q₂ h
  induction q₁ using Quotient.inductionOn with | _ x =>
  induction q₂ using Quotient.inductionOn with | _ y =>
  apply Quotient.sound
  exact (bfTupleSetoid_succ_iff φ C α n x y).mpr
    ⟨Quotient.exact (congrArg Prod.fst h), congrArg (fun p => p.2.1) h⟩

/-- **Countability transfer**: countably many `α`-classes over `n`-tuples and countably many
realized extension spectra give countably many `(α+1)`-classes over `n`-tuples. -/
theorem countable_bfTupleQuotient_succ (φ : L.Sentenceω) (C : Set ↥(ModelsOf φ))
    (α : Ordinal.{0}) (n : ℕ)
    (hα : Countable (Quotient (bfTupleSetoid φ C α n)))
    (hspec : Countable (bfExtensionSpectra φ C α n)) :
    Countable (Quotient (bfTupleSetoid φ C (Order.succ α) n)) :=
  let ⟨_, hf⟩ := exists_injective_bfTupleQuotient_succ φ C α n
  hf.countable

/-- **Countability transfer at `≤ ℵ₁`**: if the `α`-classes over `n`-tuples and the realized
extension spectra both number at most `ℵ₁`, so do the `(α+1)`-classes over `n`-tuples. -/
theorem mk_bfTupleQuotient_succ_le_aleph_one (φ : L.Sentenceω) (C : Set ↥(ModelsOf φ))
    (α : Ordinal.{0}) (n : ℕ)
    (hα : #(Quotient (bfTupleSetoid φ C α n)) ≤ Cardinal.aleph 1)
    (hspec : #(bfExtensionSpectra φ C α n) ≤ Cardinal.aleph 1) :
    #(Quotient (bfTupleSetoid φ C (Order.succ α) n)) ≤ Cardinal.aleph 1 := by
  obtain ⟨f, hf⟩ := exists_injective_bfTupleQuotient_succ φ C α n
  calc #(Quotient (bfTupleSetoid φ C (Order.succ α) n))
      ≤ #(Quotient (bfTupleSetoid φ C α n) × bfExtensionSpectra φ C α n) :=
        Cardinal.mk_le_of_injective hf
    _ = Cardinal.lift #(Quotient (bfTupleSetoid φ C α n)) *
          Cardinal.lift #(bfExtensionSpectra φ C α n) := Cardinal.mk_prod _ _
    _ ≤ Cardinal.aleph 1 * Cardinal.aleph 1 := by
        apply mul_le_mul'
        · exact Cardinal.lift_le_aleph_one.mpr hα
        · exact Cardinal.lift_le_aleph_one.mpr hspec
    _ = Cardinal.aleph 1 := by simp only [Cardinal.aleph_mul_aleph, max_self]

end Language

end FirstOrder
