/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.MorleyCounting
import InfinitaryLogic.ModelTheory.HanfSpectrum.CardinalBounds
import InfinitaryLogic.OrdinalUtil

/-!
# Back-and-forth levels via pointwise isolation from lower levels

The motivating application is a limit ordinal `λ`: there `BFEquiv λ` is the conjunction of the
`BFEquiv β` for `β < λ` (`BFEquiv.limit`), so a depth-`λ` class is a coherent family of classes
at the lower levels, and countably many classes at every lower level do **not** by themselves
bound the number of depth-`λ` classes — a countable product of countable sets can have the size
of the continuum.

A sufficient condition is *pointwise isolation*: every model is determined, up to depth-`λ`
equivalence, by its class at some lower level `β < λ`, where `β` may depend on the model.  Then
each depth-`λ` class is pinned by one node of a countable collection of lower-level quotients,
so level `λ` inherits the cardinal bound of the lower levels.  The results below assume only
this isolation hypothesis and `λ < ω₁`; they do not assume `λ` is a limit and never use
`BFEquiv.limit` (at a successor the hypothesis holds trivially with `β := λ - 1`).

The generic statement is about an arbitrary family of setoids `E : I → Setoid X` with `I`
countable and a target setoid `L` (`Setoid.IsolatedBy`); no uniformity in the isolating index
is required, and nothing about a product of the lower levels is used.

## Main results

* `Setoid.exists_injective_sigma_of_isolatedBy` — the `L`-classes inject into the dependent
  sum of the `E i`-classes.
* `Setoid.countable_quotient_of_isolatedBy`, `Setoid.lift_mk_quotient_le_of_isolatedBy` —
  the countable and general cardinal transfers.
* `countable_bfEquivSetoid_quotient_of_isolated`, `mk_bfEquivSetoid_quotient_le_aleph_one_of_isolated`
  — the instances for `bfEquivSetoid φ λ`, `λ < ω₁`, from the levels `β < λ`.
-/

universe u v w

namespace Setoid

variable {X : Type u} {I : Type w}

/-- **Pointwise isolation**: every point has an index `i` such that its `E i`-class determines
its `L`-class.  The index may depend on the point. -/
def IsolatedBy (E : I → Setoid X) (L : Setoid X) : Prop :=
  ∀ x : X, ∃ i : I, ∀ y : X, (E i).r x y → L.r x y

/-- Under pointwise isolation, the `L`-classes inject into the dependent sum of the
`E i`-classes: send a class to (an isolating index of a representative, the representative's
class there). -/
theorem exists_injective_sigma_of_isolatedBy {E : I → Setoid X} {L : Setoid X}
    (h : IsolatedBy E L) :
    ∃ f : Quotient L → Σ i : I, Quotient (E i), Function.Injective f := by
  classical
  let rep : Quotient L → X := Quotient.out
  let idx : Quotient L → I := fun q => (h (rep q)).choose
  have hidx (q : Quotient L) : ∀ y : X, (E (idx q)).r (rep q) y → L.r (rep q) y :=
    (h (rep q)).choose_spec
  refine ⟨fun q => ⟨idx q, Quotient.mk (E (idx q)) (rep q)⟩, ?_⟩
  intro q₁ q₂ hq
  obtain ⟨hi, hcls⟩ := Sigma.mk.inj_iff.mp hq
  rw [hi] at hcls
  have he : (E (idx q₂)).r (rep q₁) (rep q₂) := Quotient.exact (eq_of_heq hcls)
  have hL : L.r (rep q₁) (rep q₂) := L.symm (hidx q₂ (rep q₁) ((E (idx q₂)).symm he))
  exact (Quotient.out_eq q₁).symm.trans ((Quotient.sound hL).trans (Quotient.out_eq q₂))

/-- Countable lower levels and pointwise isolation give a countable limit level. -/
theorem countable_quotient_of_isolatedBy [Countable I] {E : I → Setoid X} {L : Setoid X}
    [∀ i, Countable (Quotient (E i))] (h : IsolatedBy E L) : Countable (Quotient L) :=
  let ⟨_, hf⟩ := exists_injective_sigma_of_isolatedBy h
  hf.countable

/-- The general cardinal transfer: lower levels of size `≤ κ` (for infinite `κ`, countably
many of them) and pointwise isolation give a limit level of size `≤ κ`.  Stated with the
lifts needed when the index type and the carrier live in different universes. -/
theorem lift_mk_quotient_le_of_isolatedBy [Countable I] {E : I → Setoid X} {L : Setoid X}
    {κ : Cardinal.{max u w}} (hκ : Cardinal.aleph0 ≤ κ)
    (hE : ∀ i, Cardinal.lift.{w} (Cardinal.mk (Quotient (E i))) ≤ κ)
    (h : IsolatedBy E L) : Cardinal.lift.{w} (Cardinal.mk (Quotient L)) ≤ κ := by
  obtain ⟨f, hf⟩ := exists_injective_sigma_of_isolatedBy h
  have hf' : Function.Injective (f ∘ ULift.down.{w} (α := Quotient L)) :=
    hf.comp ULift.down_injective
  calc Cardinal.lift.{w} (Cardinal.mk (Quotient L))
      = Cardinal.mk (ULift.{w} (Quotient L)) := (Cardinal.mk_uLift _).symm
    _ ≤ Cardinal.mk (Σ i : I, Quotient (E i)) := Cardinal.mk_le_of_injective hf'
    _ = Cardinal.sum (fun i => Cardinal.mk (Quotient (E i))) := Cardinal.mk_sigma _
    _ ≤ κ := FirstOrder.HanfLadder.sum_le_of_countable_lift hκ hE

end Setoid

namespace FirstOrder

namespace Language

open Cardinal

variable {L : Language.{u, v}} [L.IsRelational]

/-- **Pointwise isolation from lower levels** for coded models: every model is determined, up
to depth-`λ` back-and-forth equivalence, by its depth-`β` class for some `β < λ` depending on
the model.  The intended `λ` is a limit ordinal, but nothing below requires it. -/
def BFIsolatedBelow (φ : L.Sentenceω) (lam : Ordinal.{0}) : Prop :=
  Setoid.IsolatedBy (fun β : Set.Iio lam => bfEquivSetoid φ β.1) (bfEquivSetoid φ lam)

/-- Countable levels below a countable `λ`, with pointwise isolation, give a countable level
`λ`. -/
theorem countable_bfEquivSetoid_quotient_of_isolated (φ : L.Sentenceω) {lam : Ordinal.{0}}
    (hlam : lam < Ordinal.omega 1)
    (hlevel : ∀ β : Set.Iio lam, Countable (Quotient (bfEquivSetoid φ β.1)))
    (hiso : BFIsolatedBelow φ lam) : Countable (Quotient (bfEquivSetoid φ lam)) :=
  haveI := InfinitaryLogic.countable_Iio_of_lt_omega1 lam hlam
  Setoid.countable_quotient_of_isolatedBy hiso

/-- Levels of size `≤ ℵ₁` below a countable `λ`, with pointwise isolation, give a level `λ` of
size `≤ ℵ₁`. -/
theorem mk_bfEquivSetoid_quotient_le_aleph_one_of_isolated (φ : L.Sentenceω)
    {lam : Ordinal.{0}} (hlam : lam < Ordinal.omega 1)
    (hlevel : ∀ β : Set.Iio lam, #(Quotient (bfEquivSetoid φ β.1)) ≤ Cardinal.aleph 1)
    (hiso : BFIsolatedBelow φ lam) :
    #(Quotient (bfEquivSetoid φ lam)) ≤ Cardinal.aleph 1 := by
  have := InfinitaryLogic.countable_Iio_of_lt_omega1 lam hlam
  have h := Setoid.lift_mk_quotient_le_of_isolatedBy (κ := Cardinal.aleph 1)
    (Cardinal.aleph0_le_aleph 1) (fun β => Cardinal.lift_le_aleph_one.mpr (hlevel β)) hiso
  exact Cardinal.lift_le_aleph_one.mp h

end Language

end FirstOrder
