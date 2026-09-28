/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.FiniteCarrier

/-!
# The perfect-set dichotomy across carrier tiers

Two formulations of the perfect-set dichotomy for a sentence `φ`, and their refutations from
`ℕ`-tier thinness with uncountably many `ℕ`-classes:

* `Sentenceω.PerfectSetDichotomyNat`: countably many `ℕ`-classes, or a perfect set of pairwise
  non-isomorphic `ℕ`-models.  Refuted by `not_perfectSetDichotomyNat_of_thin`.
* `Sentenceω.PerfectSetDichotomyAllCountable`: countably many classes across **all** carrier
  tiers (`AllCodedIsoClasses`), or a perfect set in the `ℕ` tier, or a perfect set in some
  finite tier `Fin n`.  Thinness on the `ℕ` tier says nothing about the finite tiers (a sentence
  with no infinite models can still have continuum many pairwise non-isomorphic one-element
  models), so the refutation needs an explicit finite-tier premise: either no perfect antichain
  in any finite tier (`not_perfectSetDichotomyAllCountable_of_thin_of_finThin`), or the stronger
  and more convenient emptiness of every finite-tier model class, `Fin 0` included
  (`not_perfectSetDichotomyAllCountable_of_thin`).  No new public predicate is introduced.

The cardinal step is the left injection of the `ℕ`-tier quotient into the sum
`AllCodedIsoClasses φ` (`mk_quotient_isoSetoid_le_allCodedIsoClasses`); no equality of
cardinals is needed.  Everything sits below `Conditional/`: no Silver.
-/

universe u v

namespace FirstOrder.Language

open Cardinal

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

/-- The `ℕ`-tier perfect-set dichotomy: countably many classes of `ℕ`-models, or a perfect set of
pairwise non-isomorphic `ℕ`-models. -/
def Sentenceω.PerfectSetDichotomyNat (φ : L.Sentenceω) : Prop :=
  #(Quotient (isoSetoid φ)) ≤ ℵ₀ ∨ φ.HasPerfectSetOfPairwiseNonisomorphicNatModels

/-- The all-countable perfect-set dichotomy: countably many classes across all carrier tiers, or
a perfect set of pairwise non-isomorphic models in the `ℕ` tier or in some finite tier. -/
def Sentenceω.PerfectSetDichotomyAllCountable (φ : L.Sentenceω) : Prop :=
  #(AllCodedIsoClasses φ) ≤ ℵ₀ ∨ φ.HasPerfectSetOfPairwiseNonisomorphicNatModels ∨
    ∃ n, φ.HasPerfectSetOfPairwiseNonisomorphicFinModels n

omit [Countable (Σ l, L.Relations l)] in
/-- The `ℕ`-tier classes inject into the classes of all tiers (the left summand). -/
theorem mk_quotient_isoSetoid_le_allCodedIsoClasses (φ : L.Sentenceω) :
    #(Quotient (isoSetoid φ)) ≤ #(AllCodedIsoClasses φ) :=
  Cardinal.mk_le_of_injective (Sum.inl_injective (β := Σ n, Quotient (isoSetoidOn φ n)))

omit [Countable (Σ l, L.Relations l)] in
/-- An empty finite-tier model class carries no perfect set. -/
theorem Sentenceω.not_hasPerfectSetFin_of_modelsOfOn_eq_empty {φ : L.Sentenceω} {n : ℕ}
    (h : ModelsOfOn (α := Fin n) φ = ∅) : ¬ φ.HasPerfectSetOfPairwiseNonisomorphicFinModels n := by
  rintro ⟨P, _, ⟨x, hx⟩, hsub, _⟩
  have := hsub hx
  rw [h] at this
  exact this

omit [Countable (Σ l, L.Relations l)] in
/-- **`ℕ`-tier thinness with uncountably many classes refutes the `ℕ`-tier dichotomy.** -/
theorem Sentenceω.not_perfectSetDichotomyNat_of_thin {φ : L.Sentenceω}
    (hthin : φ.IsThinOnNatModels) (hbig : ℵ₀ < #(Quotient (isoSetoid φ))) :
    ¬ φ.PerfectSetDichotomyNat := by
  rintro (h | h)
  · exact absurd h (not_le.mpr hbig)
  · exact hthin h

omit [Countable (Σ l, L.Relations l)] in
/-- **The all-countable dichotomy is refuted** from `ℕ`-tier thinness, uncountably many `ℕ`-classes,
and no perfect antichain in any finite tier. -/
theorem Sentenceω.not_perfectSetDichotomyAllCountable_of_thin_of_finThin {φ : L.Sentenceω}
    (hthin : φ.IsThinOnNatModels) (hbig : ℵ₀ < #(Quotient (isoSetoid φ)))
    (hfinthin : ∀ n, ¬ φ.HasPerfectSetOfPairwiseNonisomorphicFinModels n) :
    ¬ φ.PerfectSetDichotomyAllCountable := by
  rintro (h | h | ⟨n, h⟩)
  · exact absurd (hbig.trans_le (mk_quotient_isoSetoid_le_allCodedIsoClasses φ)) (not_lt.mpr h)
  · exact hthin h
  · exact hfinthin n h

omit [Countable (Σ l, L.Relations l)] in
/-- **The all-countable dichotomy is refuted** from `ℕ`-tier thinness, uncountably many `ℕ`-classes,
and explicit emptiness of every finite-tier model class (`Fin 0` included). -/
theorem Sentenceω.not_perfectSetDichotomyAllCountable_of_thin {φ : L.Sentenceω}
    (hthin : φ.IsThinOnNatModels) (hbig : ℵ₀ < #(Quotient (isoSetoid φ)))
    (hfin : ∀ n, ModelsOfOn (α := Fin n) φ = ∅) : ¬ φ.PerfectSetDichotomyAllCountable :=
  φ.not_perfectSetDichotomyAllCountable_of_thin_of_finThin hthin hbig fun n =>
    Sentenceω.not_hasPerfectSetFin_of_modelsOfOn_eq_empty (hfin n)

end FirstOrder.Language
