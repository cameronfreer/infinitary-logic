/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Rank
import Mathlib.SetTheory.Ordinal.Family

/-!
# Small ordinal facts

Neutral helpers about countable ordinals, used by the Scott refinement count, the Borel
`BFEquiv` analysis, and the ranked-thinness package, together with the comparison of
`WellFounded.rank` along a relation homomorphism (`rank_le_rank_of_relHom`, not necessarily
injective) used for tree heights. Nothing here is specific to infinitary logic, descriptive set
theory, or any one of those consumers.  It also records the greatest attainable stage
(`exists_forall_iff_le_of_bounded_of_isSuccLimit_closed`): a downward-closed property of ordinals
holding at `0`, closed at successor limits and bounded, holds exactly up to a last, attained
stage, with a convenience form below `ω₁`.

Both shapes of the countability statement are provided: `Set.Countable (Set.Iio β)` and the
`Countable` *instance* on the coercion, since consumers need one or the other and converting
at each site is noise.

The greatest-attainable-stage lemma was offered for upstreaming by a consumer of this library.
-/

universe u

namespace InfinitaryLogic

/-- For `β < ω₁`, the ordinals below `β` form a countable **type**. -/
theorem countable_Iio_of_lt_omega1 (β : Ordinal.{0}) (hβ : β < Ordinal.omega 1) :
    Countable (Set.Iio β) := by
  have hle : β.card ≤ Cardinal.aleph0 := by
    have hlt : β.card < Cardinal.aleph 1 := Cardinal.lt_omega_iff_card_lt.mp hβ
    rw [← Cardinal.succ_aleph0] at hlt
    exact Order.lt_succ_iff.mp hlt
  rw [← Cardinal.mk_le_aleph0_iff]
  calc Cardinal.mk (Set.Iio β)
      = Cardinal.lift.{1, 0} β.card := Cardinal.mk_Iio_ordinal β
    _ ≤ Cardinal.lift.{1, 0} Cardinal.aleph0 := Cardinal.lift_le.mpr hle
    _ = Cardinal.aleph0 := by simp

/-- The same fact as a `Set.Countable`. -/
theorem setCountable_Iio_of_lt_omega1 (β : Ordinal.{0}) (hβ : β < Ordinal.omega 1) :
    Set.Countable (Set.Iio β) :=
  Set.countable_coe_iff.mp (countable_Iio_of_lt_omega1 β hβ)

/-- `ω₁` absorbs `+ ω`: a countable ordinal stays countable after appending `ω`.

The standard way to exceed a bound `α < ω₁` while staying countable — `α + ω` is at least `α`,
infinite, and still countable — which is what order-type diagonalizations against a boundedness
theorem need. -/
theorem add_omega0_lt_omega1 {α : Ordinal.{0}} (hα : α < (Cardinal.aleph 1).ord) :
    α + Ordinal.omega0 < (Cardinal.aleph 1).ord := by
  rw [Cardinal.ord_aleph, Cardinal.lt_omega_iff_card_lt] at hα ⊢
  rw [← Cardinal.succ_aleph0] at hα
  rw [Ordinal.card_add, Ordinal.card_omega0, ← Cardinal.succ_aleph0]
  calc α.card + Cardinal.aleph0 ≤ Cardinal.aleph0 + Cardinal.aleph0 :=
        add_le_add (Order.lt_succ_iff.mp hα) le_rfl
    _ = Cardinal.aleph0 := Cardinal.aleph0_add_aleph0
    _ < Order.succ Cardinal.aleph0 := Order.lt_succ _

/-! ## The greatest attainable stage -/

/-- **The greatest attainable stage.**  Let `P` be a property of ordinals ("`ξ` is a stage")
that holds at `0`, is closed downward, and is closed at successor limits.  If every stage is
at most `A`, then there is a last stage `ρ ≤ A`, it is attained (`P ρ`), and the stages are
exactly the ordinals `ξ ≤ ρ`.

This turns "the stages are bounded" into "there is a last stage and it is attained".
Boundedness alone gives neither: `P α ↔ α < ω` is bounded by `ω`, downward closed and holds
at `0`, but has no greatest stage, and `ω` itself is not a stage; closure at successor limits is
what fails there.  The supplied bound `A` need not itself be attainable: only `ρ ≤ A` is
returned.

No countability is used; this general form is the primary statement.
`exists_isGreatest_setOf_of_bounded_of_isSuccLimit_closed` restates it with `IsGreatest`, and
`exists_greatest_stage_lt_omega1` is the convenience form below `ω₁`. -/
theorem exists_forall_iff_le_of_bounded_of_isSuccLimit_closed (P : Ordinal.{u} → Prop)
    (hzero : P 0) (hdown : ∀ {α β}, α ≤ β → P β → P α)
    (hlim : ∀ l, Order.IsSuccLimit l → (∀ ξ, ξ < l → P ξ) → P l)
    {A : Ordinal.{u}} (hbound : ∀ ξ, P ξ → ξ ≤ A) :
    ∃ ρ, ρ ≤ A ∧ P ρ ∧ ∀ ξ, P ξ ↔ ξ ≤ ρ := by
  -- The supremum of the stages is a stage: at a successor limit by limit closure, and
  -- otherwise because a supremum that is not a successor limit is attained.
  have hne : {ξ | P ξ}.Nonempty := ⟨0, hzero⟩
  have hbdd : BddAbove {ξ | P ξ} := ⟨A, hbound⟩
  have hρ : P (sSup {ξ | P ξ}) := by
    by_cases h : Order.IsSuccLimit (sSup {ξ | P ξ})
    · refine hlim _ h fun ξ hξ ↦ ?_
      obtain ⟨b, hb, hξb⟩ := (lt_csSup_iff hbdd hne).mp hξ
      exact hdown hξb.le hb
    · exact csSup_mem_of_not_isSuccLimit hne hbdd h
  exact ⟨_, csSup_le hne hbound, hρ, fun ξ ↦ ⟨(le_csSup hbdd ·), (hdown · hρ)⟩⟩

/-- **The greatest attainable stage**, as `IsGreatest`: under the hypotheses of
`exists_forall_iff_le_of_bounded_of_isSuccLimit_closed`, the set of stages has a greatest
element, and it lies at or below the supplied bound `A` (which need not be a stage). -/
theorem exists_isGreatest_setOf_of_bounded_of_isSuccLimit_closed (P : Ordinal.{u} → Prop)
    (hzero : P 0) (hdown : ∀ {α β}, α ≤ β → P β → P α)
    (hlim : ∀ l, Order.IsSuccLimit l → (∀ ξ, ξ < l → P ξ) → P l)
    {A : Ordinal.{u}} (hbound : ∀ ξ, P ξ → ξ ≤ A) :
    ∃ ρ, ρ ≤ A ∧ IsGreatest {ξ | P ξ} ρ := by
  obtain ⟨ρ, hρA, hρ, hiff⟩ :=
    exists_forall_iff_le_of_bounded_of_isSuccLimit_closed P hzero hdown hlim hbound
  exact ⟨ρ, hρA, hρ, fun ξ hξ ↦ (hiff ξ).mp hξ⟩

/-- **The greatest attainable stage, from hypotheses below `ω₁`.**  Limit closure is asked only
at limits `l < ω₁`, and the bound `A < ω₁` is asked to dominate only the countable stages.  The
conclusion is the full one of `exists_forall_iff_le_of_bounded_of_isSuccLimit_closed`: there is
a last stage `ρ ≤ A`, it is attained, and the stages are exactly the ordinals `ξ ≤ ρ`; as there,
`A` need not be a stage.

Restricting the conclusion to `ξ < ω₁` is unnecessary, because downward closure is global: a
stage at or above `ω₁` would make `succ A < ω₁` a stage.  The restricted shape
`∀ ξ, ξ < Ordinal.omega 1 → (P ξ ↔ ξ ≤ ρ)` follows by specialisation.

`ω₁` is inessential (it is used only to know that `succ A < ω₁`); the general form is primary,
and this one is a convenience in the project's `Ordinal.omega 1` convention for countable
ordinals.  It is the general form applied to `ξ ↦ ξ < ω₁ ∧ P ξ`. -/
theorem exists_greatest_stage_lt_omega1 (P : Ordinal.{0} → Prop) (hzero : P 0)
    (hdown : ∀ {α β}, α ≤ β → P β → P α)
    (hlim : ∀ l, Order.IsSuccLimit l → l < Ordinal.omega 1 → (∀ ξ, ξ < l → P ξ) → P l)
    {A : Ordinal.{0}} (hA : A < Ordinal.omega 1)
    (hbound : ∀ ξ, ξ < Ordinal.omega 1 → P ξ → ξ ≤ A) :
    ∃ ρ, ρ ≤ A ∧ P ρ ∧ ∀ ξ, P ξ ↔ ξ ≤ ρ := by
  have homega : Order.IsSuccLimit (Ordinal.omega 1) := Cardinal.isSuccLimit_omega 1
  have hs : Order.succ A < Ordinal.omega 1 := homega.succ_lt hA
  obtain ⟨ρ, hρA, ⟨_, hρ⟩, hiff⟩ := exists_forall_iff_le_of_bounded_of_isSuccLimit_closed
    (fun ξ ↦ ξ < Ordinal.omega 1 ∧ P ξ) ⟨Ordinal.omega_pos 1, hzero⟩
    (fun hle ⟨hlt, hP⟩ ↦ ⟨hle.trans_lt hlt, hdown hle hP⟩)
    (fun l hl hall ↦ by
      have hl1 : l ≤ Ordinal.omega 1 := by
        by_contra h
        exact (hall _ (lt_of_not_ge h)).1.false
      rcases hl1.lt_or_eq with hlt | heq
      · exact ⟨hlt, hlim l hl hlt fun ξ hξ ↦ (hall ξ hξ).2⟩
      · exfalso
        subst heq
        exact (Order.lt_succ A).not_ge ((hall _ hs).2 |> hbound _ hs))
    (A := A) (fun ξ ⟨hlt, hP⟩ ↦ hbound ξ hlt hP)
  refine ⟨ρ, hρA, hρ, fun ξ ↦ ⟨fun hξ ↦ ?_, fun hle ↦ hdown hle hρ⟩⟩
  by_cases hξ1 : ξ < Ordinal.omega 1
  · exact (hiff ξ).mp ⟨hξ1, hξ⟩
  · exact absurd (hbound _ hs (hdown ((not_lt.mp hξ1).trans' hs.le) hξ))
      (Order.lt_succ A).not_ge

/-! ## Rank is monotone along relation homomorphisms -/

/-- **Rank under a relation homomorphism.**  If `f : r →r s` sends every `r`-step to an `s`-step,
then the `r`-rank of `a` is at most the `s`-rank of `f a`.  No injectivity is assumed: distinct
points may share an image, since only the steps below `a` are transported. -/
theorem rank_le_rank_of_relHom {α β : Type u} {r : α → α → Prop} {s : β → β → Prop}
    [WellFounded r] [WellFounded s] (f : r →r s) (a : α) :
    WellFounded.rank r a ≤ WellFounded.rank s (f a) := by
  induction a using WellFounded.induction' r with
  | ind a ih =>
    rw [WellFounded.rank_eq r]
    refine Ordinal.iSup_le fun b ↦ Order.succ_le_of_lt ?_
    exact (ih b b.2).trans_lt (WellFounded.rank_lt_of_rel (f.map_rel b.2))

/-- If `r ⊆ s` are both well-founded, ranks under `r` are bounded by ranks under `s`: the
identity case of `rank_le_rank_of_relHom`. -/
theorem rank_le_rank_of_imp {α : Type*} {r s : α → α → Prop} [WellFounded r]
    [WellFounded s] (h : ∀ a b, r a b → s a b) (a : α) :
    WellFounded.rank r a ≤ WellFounded.rank s a :=
  rank_le_rank_of_relHom ⟨id, h _ _⟩ a

end InfinitaryLogic
