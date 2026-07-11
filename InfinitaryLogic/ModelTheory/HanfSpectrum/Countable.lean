/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.MorleyHanf

/-!
# The countable-spectrum witness

The first bounded-spectrum sentence of the sharpness chain: over `constantsOn ℕ`, the constants
are pairwise distinct and every element is a constant. The spectrum is EXACTLY `{ℵ₀}`
(`mk_eq_aleph0_of_models_countableSpectrumSentence` — the constant interpretation is a
bijection `ℕ ≃ M`), so through the generic bounded-spectrum endpoint
`lt_Lomega1omegaHanfNumber_of_maximal_model`:

* `aleph0_lt_Lomega1omegaHanfNumber` — `ℵ₀ < Hanf(L_{ω₁ω})`.

Reference: Marker, *Lectures on Infinitary Model Theory*, Ch. 1. The powerset witness (ladder
stage `α = 0`) and the Marker Exercise 5.3 `ℶ_{α+1}` ladder complete the chain in sibling files
(endpoint: `Lomega1omegaHanfNumber_eq_beth_omega1`, `HanfSpectrum/BethLadder.lean`).
Implementation helpers live in the `CountableSpectrum` namespace; only the sentence and the
headline spectrum theorems are top-level.
-/

namespace FirstOrder

namespace Language

open Cardinal

namespace CountableSpectrum

/-- The `n`-th constant of `constantsOn ℕ`, as a term over any variable type. -/
def const (n : ℕ) {α : Type} : (constantsOn ℕ).Term α :=
  Term.func (show (constantsOn ℕ).Functions 0 from n) Fin.elim0

/-- A constant realizes valuation-independently, to the interpretation of its symbol. -/
theorem const_realize {M : Type*} [(constantsOn ℕ).Structure M] {α : Type}
    (v : α → M) (n : ℕ) :
    (const n : (constantsOn ℕ).Term α).realize v
      = Structure.funMap (L := constantsOn ℕ) (M := M)
          (show (constantsOn ℕ).Functions 0 from n) Fin.elim0 := by
  show Structure.funMap _ _ = _
  congr 1
  exact funext fun i => i.elim0

/-- Under a `constantsOn.structure σ` interpretation, a constant realizes to its `σ`-value. -/
theorem const_realize_structure {M : Type*} (σ : ℕ → M) {α : Type} (v : α → M) (n : ℕ) :
    letI : (constantsOn ℕ).Structure M := constantsOn.structure σ
    (const n : (constantsOn ℕ).Term α).realize v = σ n :=
  rfl

/-- The `n`-th distinctness conjunct: for `n` coding the pair `(i, j)` with `i ≠ j`, the
disequality `cᵢ ≠ cⱼ`; a tautology on the diagonal. -/
noncomputable def distinctAt (n : ℕ) : (constantsOn ℕ).Sentenceω :=
  if (Nat.unpair n).1 = (Nat.unpair n).2 then
    BoundedFormulaω.imp BoundedFormulaω.falsum BoundedFormulaω.falsum
  else
    (BoundedFormulaω.equal (const (Nat.unpair n).1) (const (Nat.unpair n).2)).not

/-- Surjectivity onto the constants: every element equals some `cₙ`. -/
def surj : (constantsOn ℕ).Sentenceω :=
  BoundedFormulaω.all (BoundedFormulaω.iSup fun n =>
    BoundedFormulaω.equal (Term.var (Sum.inr 0)) (const n))

end CountableSpectrum

/-- **The countable-spectrum sentence**: constants pairwise distinct, every element a constant.
Its models are exactly the sets enumerated bijectively by `ℕ` — spectrum `{ℵ₀}`. -/
noncomputable def countableSpectrumSentence : (constantsOn ℕ).Sentenceω :=
  BoundedFormulaω.iInf fun n =>
    match n with
    | 0 => CountableSpectrum.surj
    | n + 1 => CountableSpectrum.distinctAt n

namespace CountableSpectrum

/-- `ℕ` itself (constants interpreted by `id`) models the countable-spectrum sentence. -/
theorem nat_models :
    letI : (constantsOn ℕ).Structure ℕ := constantsOn.structure id
    Sentenceω.Realize countableSpectrumSentence ℕ := by
  letI : (constantsOn ℕ).Structure ℕ := constantsOn.structure id
  show BoundedFormulaω.Realize _ (Empty.elim : Empty → ℕ) Fin.elim0
  rw [countableSpectrumSentence, BoundedFormulaω.realize_iInf]
  intro n
  match n with
  | 0 =>
    show BoundedFormulaω.Realize surj Empty.elim Fin.elim0
    rw [surj, BoundedFormulaω.realize_all]
    intro x
    rw [BoundedFormulaω.realize_iSup]
    refine ⟨x, ?_⟩
    rw [BoundedFormulaω.realize_equal, const_realize_structure (σ := id)]
    show (Fin.snoc (Fin.elim0 : Fin 0 → ℕ) x : Fin 1 → ℕ) (Fin.last 0) = id x
    exact Fin.snoc_last _ _
  | n + 1 =>
    show BoundedFormulaω.Realize (distinctAt n) Empty.elim Fin.elim0
    rw [distinctAt]
    split_ifs with h
    · rw [BoundedFormulaω.realize_imp]
      exact fun hf => hf
    · rw [BoundedFormulaω.realize_not, BoundedFormulaω.realize_equal,
        const_realize_structure (σ := id), const_realize_structure (σ := id)]
      exact fun heq => h heq

/-- The constant interpretation of a model is surjective (the surjectivity clause). -/
theorem constInterp_surjective {M : Type} [(constantsOn ℕ).Structure M]
    (hM : Sentenceω.Realize countableSpectrumSentence M) :
    Function.Surjective (fun n : ℕ =>
      Structure.funMap (L := constantsOn ℕ) (M := M)
        (show (constantsOn ℕ).Functions 0 from n) Fin.elim0) := by
  have hreal : BoundedFormulaω.Realize countableSpectrumSentence
      (Empty.elim : Empty → M) Fin.elim0 := hM
  rw [countableSpectrumSentence, BoundedFormulaω.realize_iInf] at hreal
  have hsurj : BoundedFormulaω.Realize surj (Empty.elim : Empty → M) Fin.elim0 := hreal 0
  rw [surj, BoundedFormulaω.realize_all] at hsurj
  intro x
  have hx := hsurj x
  rw [BoundedFormulaω.realize_iSup] at hx
  obtain ⟨n, hn⟩ := hx
  rw [BoundedFormulaω.realize_equal, const_realize] at hn
  have hx0 : (Sum.elim (Empty.elim : Empty → M) (Fin.snoc Fin.elim0 x) : _ → M) (Sum.inr 0)
      = x := by
    show (Fin.snoc (Fin.elim0 : Fin 0 → M) x : Fin 1 → M) (Fin.last 0) = x
    exact Fin.snoc_last _ _
  exact ⟨n, hn.symm.trans hx0⟩

/-- The constant interpretation of a model is injective (the distinctness clauses, keyed by
`Nat.pair`). -/
theorem constInterp_injective {M : Type} [(constantsOn ℕ).Structure M]
    (hM : Sentenceω.Realize countableSpectrumSentence M) :
    Function.Injective (fun n : ℕ =>
      Structure.funMap (L := constantsOn ℕ) (M := M)
        (show (constantsOn ℕ).Functions 0 from n) Fin.elim0) := by
  intro i j hij
  by_contra hne
  have hreal : BoundedFormulaω.Realize countableSpectrumSentence
      (Empty.elim : Empty → M) Fin.elim0 := hM
  rw [countableSpectrumSentence, BoundedFormulaω.realize_iInf] at hreal
  have hd : BoundedFormulaω.Realize (distinctAt (Nat.pair i j))
      (Empty.elim : Empty → M) Fin.elim0 := hreal (Nat.pair i j + 1)
  rw [distinctAt, Nat.unpair_pair] at hd
  rw [if_neg (show ¬((i, j).1 = (i, j).2) from hne)] at hd
  rw [BoundedFormulaω.realize_not, BoundedFormulaω.realize_equal,
    const_realize, const_realize] at hd
  exact hd hij

end CountableSpectrum

/-- **The exact countable spectrum**: every model of the countable-spectrum sentence has size
exactly `ℵ₀` — the constant interpretation is a bijection `ℕ ≃ M`. -/
theorem mk_eq_aleph0_of_models_countableSpectrumSentence {M : Type}
    [(constantsOn ℕ).Structure M]
    (hM : Sentenceω.Realize countableSpectrumSentence M) :
    Cardinal.mk M = Cardinal.aleph0 := by
  refine le_antisymm ?_ ?_
  · haveI : Countable M := (CountableSpectrum.constInterp_surjective hM).countable
    exact Cardinal.mk_le_aleph0
  · have h := Cardinal.mk_le_of_injective (CountableSpectrum.constInterp_injective hM)
    rwa [Cardinal.mk_nat] at h

/-- The countable-spectrum sentence has no uncountable models — it does NOT have arbitrarily
large models. -/
theorem not_hasArbLargeModels_countableSpectrumSentence :
    ¬HasArbLargeModels countableSpectrumSentence := by
  intro h
  obtain ⟨M, instM, hreal, hsize⟩ := h (Cardinal.aleph 1)
  exact absurd (le_trans hsize (mk_eq_aleph0_of_models_countableSpectrumSentence hreal).le)
    (not_le.mpr Cardinal.aleph0_lt_aleph_one)

/-- **The first sharpness step**: `ℵ₀ < Lomega1omegaHanfNumber` — the countable-spectrum
sentence through the generic bounded-spectrum endpoint. -/
theorem aleph0_lt_Lomega1omegaHanfNumber :
    Cardinal.aleph0 < Lomega1omegaHanfNumber := by
  letI : (constantsOn ℕ).Structure ℕ := constantsOn.structure id
  exact lt_Lomega1omegaHanfNumber_of_maximal_model
    ⟨ℕ, inferInstance, CountableSpectrum.nat_models, by rw [Cardinal.mk_nat]⟩
    (fun M instM hM =>
      (@mk_eq_aleph0_of_models_countableSpectrumSentence M instM hM).le)

/-- No `κ ≤ ℵ₀` is a global `L_{ω₁ω}` Hanf bound. -/
theorem not_isLomega1omegaHanfBound_of_le_aleph0 {κ : Cardinal}
    (hκ : κ ≤ Cardinal.aleph0) : ¬IsLomega1omegaHanfBound κ := fun h =>
  (lt_Lomega1omegaHanfNumber_iff_not_isHanfBound.mp aleph0_lt_Lomega1omegaHanfNumber)
    (h.mono hκ)

end Language

end FirstOrder
