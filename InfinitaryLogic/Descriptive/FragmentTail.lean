/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.SentenceRecovery
import InfinitaryLogic.Descriptive.RankedThinness
import InfinitaryLogic.OrdinalUtil
import Mathlib.SetTheory.Cardinal.Regular

/-!
# Tail smallness bounds ranks on Cantor antichains

A countable-fragment alternative to uniform bounded back-and-forth comparison.  The rank `r` is
arbitrary: it need not be Borel and need not be an isomorphism invariant.

`antichain_rank_bounded_of_fragment_tails`: if for every countable sentence list `θ` there is a
threshold `b < ω₁` such that the spectrum of `θ` on the rank tail `{c ∈ C | b ≤ r c}` is
countable, then `r` is bounded below `ω₁` on every Borel Cantor isomorphism antichain in `C`.
Recover the Cantor parameter by sentences (`sentences_recover_cantor`), so the parameters of
high rank are countably many; the supremum of their successor ranks is a countable bound.  The
separating list is chosen *after* the antichain, so the tail hypothesis must hold for every
list; the threshold may depend on the list.

`fragment_tails_of_eventual_sentence_decision` supplies that hypothesis from a stronger,
sentence-by-sentence input: each sentence eventually has constant truth on the rank tail.
Thresholds may depend on the whole sentence, not merely its quantifier rank.

`ThinRankAnalysis.bounded_refined_of_fragment_tails` discharges the refined
boundedness field of `ThinRankAnalysis` with `e := id`: the bound holds on the whole antichain.
The other fields of a thinness argument — countable ranks and countable fixed-rank antichains —
remain inputs.  Nothing here establishes tail smallness for any particular class.
-/

namespace FirstOrder.Language

open MeasureTheory Set

variable {L : Language.{0, 0}} [L.IsRelational] [Countable (Σ n, L.Relations n)]

/-- Cantor space is Polish; local to this file. -/
private theorem polishSpace_cantor : PolishSpace (ℕ → Bool) :=
  PolishSpace.mk

attribute [local instance] polishSpace_cantor

/-- **Tail smallness bounds the rank on every Borel Cantor antichain**, without a rank-domination
theorem or a measurable rank. -/
theorem antichain_rank_bounded_of_fragment_tails (C : Set (StructureSpace L))
    (r : StructureSpace L → Ordinal.{0}) (hr : ∀ c ∈ C, r c < Ordinal.omega 1)
    (htail : ∀ θ : ℕ → L.Sentenceω, ∃ b < Ordinal.omega 1,
      (sentenceTheory θ '' {c | c ∈ C ∧ b ≤ r c}).Countable)
    (f : (ℕ → Bool) → StructureSpace L) (hf : Measurable f) (hm : ∀ x, f x ∈ C)
    (hanti : ∀ x y, x ≠ y → ¬ (structureIsoSetoid L).r (f x) (f y)) :
    ∃ b < Ordinal.omega 1, ∀ x, r (f x) < b := by
  obtain ⟨θ, hθ⟩ := sentences_recover_cantor f hf hanti
  obtain ⟨b, hb, hsmall⟩ := htail θ
  let H : Set (ℕ → Bool) := {x | b ≤ r (f x)}
  have hsub : H ⊆ sentenceTheory θ '' {c | c ∈ C ∧ b ≤ r c} := fun x hx =>
    ⟨f x, ⟨hm x, hx⟩, sentenceTheory_eq_parameter f θ hθ x⟩
  have hH : H.Countable := hsmall.mono hsub
  have : Countable H := hH.to_subtype
  let s : Ordinal.{0} := ⨆ x : H, Order.succ (r (f x.1))
  have hs : s < Ordinal.omega 1 := Ordinal.iSup_lt_omega_one fun x =>
    Order.IsSuccLimit.succ_lt (Cardinal.isSuccLimit_omega 1) (hr _ (hm x.1))
  refine ⟨max b s, max_lt hb hs, fun x => ?_⟩
  by_cases hx : x ∈ H
  · exact (lt_of_lt_of_le (Order.lt_succ (r (f x)))
      (Ordinal.le_iSup (fun y : H => Order.succ (r (f y.1))) ⟨x, hx⟩)).trans_le
        (le_max_right b s)
  · exact (lt_of_not_ge hx).trans_le (le_max_left b s)

omit [Countable (Σ n, L.Relations n)] in
/-- **Eventual sentence decision gives tail smallness**: if each sentence eventually has constant
truth on the rank tail, every countable list has a countable tail spectrum.  Countable suprema
handle a whole list. -/
theorem fragment_tails_of_eventual_sentence_decision (C : Set (StructureSpace L))
    (r : StructureSpace L → Ordinal.{0})
    (hdecide : ∀ θ : L.Sentenceω, ∃ b < Ordinal.omega 1, ∃ p : Bool,
      ∀ c ∈ C, b ≤ r c → (c ∈ ModelsOf θ ↔ p = true)) :
    ∀ θ : ℕ → L.Sentenceω, ∃ b < Ordinal.omega 1,
      (sentenceTheory θ '' {c | c ∈ C ∧ b ≤ r c}).Countable := by
  classical
  intro θ
  choose b hb p hp using fun n => hdecide (θ n)
  refine ⟨⨆ n, b n, Ordinal.iSup_lt_omega_one hb, ?_⟩
  apply (Set.countable_singleton p).mono
  rintro y ⟨c, ⟨hc, hr⟩, rfl⟩
  apply Set.mem_singleton_iff.mpr
  funext n
  have hh := hp n c hc ((Ordinal.le_iSup b n).trans hr)
  simp only [sentenceTheory, hh]
  cases p n <;> rfl

/-- **The refined boundedness field from tail smallness**, with `e := id`: the bound holds on the
whole antichain, so no subcopy is needed.  The remaining fields of `ThinRankAnalysis` are not
supplied here. -/
theorem ThinRankAnalysis.bounded_refined_of_fragment_tails
    (C : Set (StructureSpace L)) (r : StructureSpace L → Ordinal.{0})
    (hr : ∀ c ∈ C, r c < Ordinal.omega 1)
    (htail : ∀ θ : ℕ → L.Sentenceω, ∃ b < Ordinal.omega 1,
      (sentenceTheory θ '' {c | c ∈ C ∧ b ≤ r c}).Countable) :
    ∀ f : (ℕ → Bool) → StructureSpace L, Continuous f → (∀ x, f x ∈ C) →
      (∀ x y, x ≠ y → ¬ (structureIsoSetoid L).r (f x) (f y)) →
      ∃ e : (ℕ → Bool) → (ℕ → Bool), Continuous e ∧ Function.Injective e ∧
        ∃ β < Ordinal.omega 1, ∀ x, r (f (e x)) < β := by
  intro f hf hm hanti
  exact ⟨id, continuous_id, Function.injective_id,
    antichain_rank_bounded_of_fragment_tails C r hr htail f hf.measurable hm hanti⟩

end FirstOrder.Language
