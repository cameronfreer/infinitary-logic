/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.BFExtensionSpectrum
import InfinitaryLogic.ModelTheory.BFLimitIsolation

/-!
# Few models from level-by-level smallness of the back-and-forth hierarchy

`mk_isoSetoid_quotient_le_aleph_one` bounds the isomorphism classes of coded models of a
sentence by `ℵ₁` once every back-and-forth level below `ω₁` has countably many classes.  This
module assembles the level-by-level analysis that produces such bounds from *local* data, for
an arbitrary class `C` of coded models and every tuple arity at once:

* at level `0`, countably many depth-`0` classes of `n`-tuples — an assumption, not a
  consequence of a countable language, since the atomic type of a tuple is a subset of a
  countable set of atomic formulas and may a priori take continuum many values;
* at a successor, countably many realized extension spectra (`bfExtensionSpectra`), which by
  `countable_bfTupleQuotient_succ` carry countability up one level;
* at a limit, pointwise isolation from the lower levels (`Setoid.IsolatedBy`), which by
  `Setoid.countable_quotient_of_isolatedBy` carries countability through the limit.

## Main results

* `BFSmall φ C` — the three local smallness conditions.
* `countable_bfTupleQuotient_of_bfSmall` — the transfinite induction: every level `α < ω₁` has
  countably many classes at every arity.
* `countable_bfProjRange_representedIn` — the arity-`0` classes of `C`-models cover the
  depth-`α` projection of the isomorphism classes represented in `C` (`RepresentedIn`).
* `mk_representedIn_le_aleph_one_of_bfSmall` — hence, by the relativized stratification bound
  `mk_isoSetoid_subtype_le_aleph_one_of_countable_levels`, the isomorphism classes represented
  in `C` number at most `ℵ₁`; `mk_isoSetoid_quotient_le_aleph_one_of_bfSmall` is the case
  `C := Set.univ`.
-/

universe u v

namespace FirstOrder

namespace Language

open Cardinal

variable {L : Language.{u, v}} [L.IsRelational]

/-- **Level-by-level smallness** of a class `C` of coded models: countably many depth-`0`
classes at every arity; countably many realized extension spectra at every depth `α < ω₁` and
arity; pointwise isolation from the lower levels at every limit `λ < ω₁` and arity. -/
structure BFSmall (φ : L.Sentenceω) (C : Set ↥(ModelsOf φ)) : Prop where
  /-- Countably many depth-`0` classes of `n`-tuples. -/
  zero : ∀ n : ℕ, Countable (Quotient (bfTupleSetoid φ C 0 n))
  /-- Countably many realized depth-`α` extension spectra of `n`-tuples. -/
  succ : ∀ α : Ordinal.{0}, α < Ordinal.omega 1 → ∀ n : ℕ, Countable (bfExtensionSpectra φ C α n)
  /-- Pointwise isolation from the lower levels at every limit. -/
  limit : ∀ lam : Ordinal.{0}, lam < Ordinal.omega 1 → Order.IsSuccLimit lam → ∀ n : ℕ,
    Setoid.IsolatedBy (fun β : Set.Iio lam => bfTupleSetoid φ C β.1 n) (bfTupleSetoid φ C lam n)

/-- **The transfinite induction**: under `BFSmall`, every level below `ω₁` has countably many
classes at every arity. -/
theorem countable_bfTupleQuotient_of_bfSmall {φ : L.Sentenceω} {C : Set ↥(ModelsOf φ)}
    (h : BFSmall φ C) {α : Ordinal.{0}} (hα : α < Ordinal.omega 1) (n : ℕ) :
    Countable (Quotient (bfTupleSetoid φ C α n)) := by
  induction α using Ordinal.limitRecOn generalizing n with
  | zero => exact h.zero n
  | add_one β ih =>
    rw [← Order.succ_eq_add_one] at hα ⊢
    have hβ : β < Ordinal.omega 1 := (Order.lt_succ β).trans hα
    exact countable_bfTupleQuotient_succ φ C β n (ih hβ n) (h.succ β hβ n)
  | limit β hβ ih =>
    have := InfinitaryLogic.countable_Iio_of_lt_omega1 β hα
    have : ∀ i : Set.Iio β, Countable (Quotient (bfTupleSetoid φ C i.1 n)) :=
      fun i => ih i.1 i.2 (i.2.trans hα) n
    exact Setoid.countable_quotient_of_isolatedBy (h.limit β hα hβ n)

/-- The isomorphism classes represented in `C`. -/
def RepresentedIn (φ : L.Sentenceω) (C : Set ↥(ModelsOf φ)) (q : Quotient (isoSetoid φ)) :
    Prop :=
  ∃ c ∈ C, Quotient.mk (isoSetoid φ) c = q

/-- **The arity-`0` bridge**: the depth-`α` classes of `C`-models (with the empty tuple) map onto
the depth-`α` projection of the isomorphism classes represented in `C`. -/
theorem countable_bfProjRange_representedIn (φ : L.Sentenceω) (C : Set ↥(ModelsOf φ))
    (α : Ordinal.{0}) (hcount : Countable (Quotient (bfTupleSetoid φ C α 0))) :
    Countable (bfProjRange φ (RepresentedIn φ C) α) := by
  let g : Quotient (bfTupleSetoid φ C α 0) → bfProjRange φ (RepresentedIn φ C) α :=
    Quotient.lift
      (fun x => ⟨Quotient.mk (bfEquivSetoid φ α) x.1.1,
        mem_bfProjRange.mpr ⟨⟨Quotient.mk (isoSetoid φ) x.1.1, x.1.1, x.1.2, rfl⟩, rfl⟩⟩)
      (fun x y hxy => Subtype.ext (Quotient.sound ((bfTupleSetoid_zero_iff φ C α x y).mp hxy)))
  have hg : Function.Surjective g := by
    rintro ⟨p, hp⟩
    obtain ⟨⟨q, c, hc, rfl⟩, rfl⟩ := mem_bfProjRange.mp hp
    exact ⟨Quotient.mk _ (⟨c, hc⟩, Fin.elim0), rfl⟩
  exact hg.countable

variable [Countable (Σ l, L.Relations l)]

/-- **Few models from smallness**: under `BFSmall φ C`, the isomorphism classes represented in
`C` number at most `ℵ₁`. -/
theorem mk_representedIn_le_aleph_one_of_bfSmall {φ : L.Sentenceω} {C : Set ↥(ModelsOf φ)}
    (h : BFSmall φ C) :
    #{q : Quotient (isoSetoid φ) // RepresentedIn φ C q} ≤ Cardinal.aleph 1 :=
  mk_isoSetoid_subtype_le_aleph_one_of_countable_levels φ (RepresentedIn φ C) fun α hα =>
    Cardinal.mk_le_aleph0_iff.mpr
      (countable_bfProjRange_representedIn φ C α (countable_bfTupleQuotient_of_bfSmall h hα 0))

/-- The case `C := Set.univ`: level-by-level smallness of all coded models of `φ` gives at most
`ℵ₁` isomorphism classes — the hypothesis of `mk_isoSetoid_quotient_le_aleph_one` obtained from
local data. -/
theorem mk_isoSetoid_quotient_le_aleph_one_of_bfSmall {φ : L.Sentenceω}
    (h : BFSmall φ Set.univ) : #(Quotient (isoSetoid φ)) ≤ Cardinal.aleph 1 := by
  have hall : ∀ q : Quotient (isoSetoid φ), RepresentedIn φ Set.univ q := fun q =>
    let ⟨c, hc⟩ := Quotient.exists_rep q
    ⟨c, Set.mem_univ c, hc⟩
  have := mk_representedIn_le_aleph_one_of_bfSmall h
  rwa [Cardinal.mk_congr (Equiv.subtypeUnivEquiv hall)] at this

end Language

end FirstOrder
