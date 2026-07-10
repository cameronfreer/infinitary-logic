/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.MorleyHanf

/-!
# Bounded-spectrum witnesses: lower bounds for the `L_{ω₁ω}` Hanf number

The sharpness pilot (toward `Hanf(L_{ω₁ω}) = ℶ_{ω₁}`): concrete sentences whose model spectra
are BOUNDED, refuting small global Hanf bounds through the universal-property API.

This file: the countable-spectrum sentence over `constantsOn ℕ` — the constants are pairwise
distinct and every element is a constant. Every model is countably infinite; in particular the
sentence has a model of size `ℵ₀` and none larger, so no `κ ≤ ℵ₀` is a global Hanf bound and
`ℵ₀ < Lomega1omegaHanfNumber` (Marker, *Lectures on Infinitary Model Theory*, Ch. 1). The
continuum-bound (powerset) witness and the full `ℶ_{α+1}` ladder (Marker, Exercise 5.3) are the
next steps of the pilot.
-/

namespace FirstOrder

namespace Language

open Cardinal

/-- The `n`-th constant of `constantsOn ℕ`, as a term over any variable type. -/
def specConst (n : ℕ) {α : Type} : (constantsOn ℕ).Term α :=
  Term.func (show (constantsOn ℕ).Functions 0 from n) Fin.elim0

/-- A `specConst` realizes valuation-independently, to the interpretation of its symbol. -/
theorem specConst_realize {M : Type*} [(constantsOn ℕ).Structure M] {α : Type}
    (v : α → M) (n : ℕ) :
    (specConst n : (constantsOn ℕ).Term α).realize v
      = Structure.funMap (L := constantsOn ℕ) (M := M)
          (show (constantsOn ℕ).Functions 0 from n) Fin.elim0 := by
  show Structure.funMap _ _ = _
  congr 1
  exact funext fun i => i.elim0

/-- Under a `constantsOn.structure σ` interpretation, a `specConst` realizes to its `σ`-value. -/
theorem specConst_realize_structure {M : Type*} (σ : ℕ → M) {α : Type} (v : α → M) (n : ℕ) :
    letI : (constantsOn ℕ).Structure M := constantsOn.structure σ
    (specConst n : (constantsOn ℕ).Term α).realize v = σ n :=
  rfl

/-- The `n`-th conjunct of the countable-spectrum sentence: for `n` coding the pair `(i, j)`
with `i ≠ j`, the disequality `cᵢ ≠ cⱼ`; a tautology on the diagonal. -/
noncomputable def specDistinctAt (n : ℕ) : (constantsOn ℕ).Sentenceω :=
  if (Nat.unpair n).1 = (Nat.unpair n).2 then
    BoundedFormulaω.imp BoundedFormulaω.falsum BoundedFormulaω.falsum
  else
    (BoundedFormulaω.equal (specConst (Nat.unpair n).1) (specConst (Nat.unpair n).2)).not

/-- Surjectivity onto the constants: every element equals some `cₙ`. -/
def specSurj : (constantsOn ℕ).Sentenceω :=
  BoundedFormulaω.all (BoundedFormulaω.iSup fun n =>
    BoundedFormulaω.equal (Term.var (Sum.inr 0)) (specConst n))

/-- **The countable-spectrum sentence**: constants pairwise distinct, every element a constant.
Its models are exactly the sets enumerated bijectively by `ℕ` — countably infinite, never
larger. -/
noncomputable def countableSpectrumSentence : (constantsOn ℕ).Sentenceω :=
  BoundedFormulaω.iInf fun n =>
    match n with
    | 0 => specSurj
    | n + 1 => specDistinctAt n

/-- `ℕ` itself (constants interpreted by `id`) models the countable-spectrum sentence. -/
theorem nat_models_countableSpectrumSentence :
    letI : (constantsOn ℕ).Structure ℕ := constantsOn.structure id
    Sentenceω.Realize countableSpectrumSentence ℕ := by
  letI : (constantsOn ℕ).Structure ℕ := constantsOn.structure id
  show BoundedFormulaω.Realize _ (Empty.elim : Empty → ℕ) Fin.elim0
  rw [countableSpectrumSentence, BoundedFormulaω.realize_iInf]
  intro n
  match n with
  | 0 =>
    show BoundedFormulaω.Realize specSurj Empty.elim Fin.elim0
    rw [specSurj, BoundedFormulaω.realize_all]
    intro x
    rw [BoundedFormulaω.realize_iSup]
    refine ⟨x, ?_⟩
    rw [BoundedFormulaω.realize_equal, specConst_realize_structure (σ := id)]
    show (Fin.snoc (Fin.elim0 : Fin 0 → ℕ) x : Fin 1 → ℕ) (Fin.last 0) = id x
    exact Fin.snoc_last _ _
  | n + 1 =>
    show BoundedFormulaω.Realize (specDistinctAt n) Empty.elim Fin.elim0
    rw [specDistinctAt]
    split_ifs with h
    · rw [BoundedFormulaω.realize_imp]
      exact fun hf => hf
    · rw [BoundedFormulaω.realize_not, BoundedFormulaω.realize_equal,
        specConst_realize_structure (σ := id), specConst_realize_structure (σ := id)]
      exact fun heq => h heq

/-- Every model of the countable-spectrum sentence is countable: the constant interpretation
`ℕ → M` is surjective by the surjectivity clause. -/
theorem countable_of_models_countableSpectrumSentence {M : Type} [(constantsOn ℕ).Structure M]
    (hM : Sentenceω.Realize countableSpectrumSentence M) : Cardinal.mk M ≤ Cardinal.aleph0 := by
  have hreal : BoundedFormulaω.Realize countableSpectrumSentence
      (Empty.elim : Empty → M) Fin.elim0 := hM
  rw [countableSpectrumSentence, BoundedFormulaω.realize_iInf] at hreal
  have hsurj : BoundedFormulaω.Realize specSurj (Empty.elim : Empty → M) Fin.elim0 := hreal 0
  rw [specSurj, BoundedFormulaω.realize_all] at hsurj
  have hS : Function.Surjective (fun n : ℕ =>
      Structure.funMap (L := constantsOn ℕ) (M := M)
        (show (constantsOn ℕ).Functions 0 from n) Fin.elim0) := by
    intro x
    have hx := hsurj x
    rw [BoundedFormulaω.realize_iSup] at hx
    obtain ⟨n, hn⟩ := hx
    rw [BoundedFormulaω.realize_equal, specConst_realize] at hn
    have hx0 : (Sum.elim (Empty.elim : Empty → M) (Fin.snoc Fin.elim0 x) : _ → M) (Sum.inr 0)
        = x := by
      show (Fin.snoc (Fin.elim0 : Fin 0 → M) x : Fin 1 → M) (Fin.last 0) = x
      exact Fin.snoc_last _ _
    exact ⟨n, hn.symm.trans hx0⟩
  haveI : Countable M := hS.countable
  exact Cardinal.mk_le_aleph0

/-- The countable-spectrum sentence has no models of any uncountable size — its spectrum is
bounded, so it does NOT have arbitrarily large models. -/
theorem not_hasArbLargeModels_countableSpectrumSentence :
    ¬HasArbLargeModels countableSpectrumSentence := by
  intro h
  obtain ⟨M, instM, hreal, hsize⟩ := h (Cardinal.aleph 1)
  exact absurd (le_trans hsize (countable_of_models_countableSpectrumSentence hreal))
    (not_le.mpr Cardinal.aleph0_lt_aleph_one)

/-- **No `κ ≤ ℵ₀` is a global `L_{ω₁ω}` Hanf bound**: the countable-spectrum sentence has a
model of size `≥ κ` (namely `ℕ`) but not arbitrarily large models. -/
theorem not_isLomega1omegaHanfBound_of_le_aleph0 {κ : Cardinal}
    (hκ : κ ≤ Cardinal.aleph0) : ¬IsLomega1omegaHanfBound κ := by
  intro h
  letI : (constantsOn ℕ).Structure ℕ := constantsOn.structure id
  exact not_hasArbLargeModels_countableSpectrumSentence
    (h (constantsOn ℕ) countableSpectrumSentence
      ⟨ℕ, inferInstance, nat_models_countableSpectrumSentence,
        by rw [Cardinal.mk_nat]; exact hκ⟩)

/-- **The first sharpness step**: `ℵ₀ < Lomega1omegaHanfNumber`. -/
theorem aleph0_lt_Lomega1omegaHanfNumber :
    Cardinal.aleph0 < Lomega1omegaHanfNumber := by
  by_contra hle
  rw [not_lt] at hle
  exact not_isLomega1omegaHanfBound_of_le_aleph0 le_rfl
    (Lomega1omegaHanfNumber_le_iff_isHanfBound.mp hle)

end Language

end FirstOrder
