/-
Regression guard for the greatest attainable stage (`InfinitaryLogic/OrdinalUtil.lean`):
`exists_forall_iff_le_of_bounded_of_isSuccLimit_closed`,
`exists_isGreatest_setOf_of_bounded_of_isSuccLimit_closed` and
`exists_greatest_stage_lt_omega1`.

Checked: all three exports **applied** generically (the general forms at an arbitrary universe
`u`, the `ω₁` form on `Ordinal.{0}`), and the **restricted shape** `∀ ξ < ω₁, P ξ ↔ ξ ≤ ρ`
recovered from the `ω₁` form by specialisation; the **finite-stage counterexample**
`P α ↔ α < ω`, which holds at `0`, is downward closed and is bounded by `ω` but has no greatest
member (stated with `IsGreatest`), with closure at successor limits shown to be exactly the
hypothesis that fails (at `ω`); an **unattained bound** (`P α ↔ α ≤ 3`, `A = 5`: the returned
stage is `3`, and `5` is not a stage); **greatest stage zero** (`P α ↔ α = 0`, `A = 0`); a
**limit bound** (`P α ↔ α ≤ ω`, `A = ω`: the returned stage `ω` is itself a limit; this pins
the statement, not a proof route, see `limit_bound_regression`); a **`Type 1` instance** of the
general form on `Ordinal.{1}`; the **`ω₁` form** at a bound `A = ω` with `A + 1` not a stage,
its conclusion holding for all `ξ`, not only below `ω₁`; an **`IsGreatest` application**
returning `3`; the **consumer's contract shape** (`exists_greatest_countable_stage`, guard-only,
in the `(Cardinal.aleph 1).ord` notation with the conclusion restricted to countable `ξ`)
derived from the `ω₁` form by `Cardinal.ord_aleph`; an **existential presentation predicate**
(`ToyStage`), destructured with the consumer's own call pattern
`⟨ρ, hρ, ⟨W, hW, hbase⟩, hstages⟩`, recovering an actual presentation at the greatest stage `ω`
on the literal base, with none at its successor; through the contract
shape, `P α ↔ α ≤ κ` returning `κ` for every countable `κ ≤ A`, and a **limit with a loose
bound** (`κ = ω`, `A = ω + 1`); **negative controls**, each proving which hypotheses hold and
refuting the conclusion: without `P 0` (the empty predicate), without downward closure (the
stages `0, 2, 3, …`), and without a countable bound (`ξ < ω₁`: no countable bound and no
attained greatest countable stage; with `hA` dropped and `A = ω₁`, every remaining contract
hypothesis and the bound hold, `ρ = ω₁` satisfies the restricted characterization, and
attainment fails since `ω₁` is not a stage); the **derivation**: the constant cones of the
`ω₁` form and of the `IsGreatest` form contain the general lemma, the cone of the guard's
contract shape contains the `ω₁` form (it is not a second proof), and the cone of the
migration-shape regression contains the contract shape; the **exact
import closure** of `OrdinalUtil` (itself only: no other `InfinitaryLogic` module, Mathlib
only); **standard axioms** for the three exports and every guard declaration.  The OK line is
printed only after the cone, closure and axiom checks.

Run with: lake env lean scripts/check_greatest_stage_regressions.lean
-/
import InfinitaryLogic.OrdinalUtil
import Mathlib.Tactic.NormNum

open Lean InfinitaryLogic

universe u

namespace GreatestStageRegressions

/-! ### Generic applications -/

/-- The general form, applied at an arbitrary universe. -/
theorem generic_exists_regression (P : Ordinal.{u} → Prop) (hzero : P 0)
    (hdown : ∀ {α β}, α ≤ β → P β → P α)
    (hlim : ∀ l, Order.IsSuccLimit l → (∀ ξ, ξ < l → P ξ) → P l)
    {A : Ordinal.{u}} (hbound : ∀ ξ, P ξ → ξ ≤ A) :
    ∃ ρ, ρ ≤ A ∧ P ρ ∧ ∀ ξ, P ξ ↔ ξ ≤ ρ :=
  exists_forall_iff_le_of_bounded_of_isSuccLimit_closed P hzero hdown hlim hbound

/-- The `IsGreatest` form, applied at an arbitrary universe. -/
theorem generic_isGreatest_regression (P : Ordinal.{u} → Prop) (hzero : P 0)
    (hdown : ∀ {α β}, α ≤ β → P β → P α)
    (hlim : ∀ l, Order.IsSuccLimit l → (∀ ξ, ξ < l → P ξ) → P l)
    {A : Ordinal.{u}} (hbound : ∀ ξ, P ξ → ξ ≤ A) :
    ∃ ρ, ρ ≤ A ∧ IsGreatest {ξ | P ξ} ρ :=
  exists_isGreatest_setOf_of_bounded_of_isSuccLimit_closed P hzero hdown hlim hbound

/-- The `ω₁` form, applied on `Ordinal.{0}` in the `Ordinal.omega 1` convention. -/
theorem generic_omega1_regression (P : Ordinal.{0} → Prop) (hzero : P 0)
    (hdown : ∀ {α β}, α ≤ β → P β → P α)
    (hlim : ∀ l, Order.IsSuccLimit l → l < Ordinal.omega 1 → (∀ ξ, ξ < l → P ξ) → P l)
    {A : Ordinal.{0}} (hA : A < Ordinal.omega 1)
    (hbound : ∀ ξ, ξ < Ordinal.omega 1 → P ξ → ξ ≤ A) :
    ∃ ρ, ρ ≤ A ∧ P ρ ∧ ∀ ξ, P ξ ↔ ξ ≤ ρ :=
  exists_greatest_stage_lt_omega1 P hzero hdown hlim hA hbound

/-- **The restricted shape by specialisation**: the conclusion restricted to `ξ < ω₁`, as
originally offered, follows from the `ω₁` form.  This is the consumer's contract shape in the
library's `Ordinal.omega 1` notation; `exists_greatest_countable_stage` below is the same shape in
the consumer's `(Cardinal.aleph 1).ord` notation. -/
theorem omega1_restricted_shape_regression (P : Ordinal.{0} → Prop) (hzero : P 0)
    (hdown : ∀ {α β}, α ≤ β → P β → P α)
    (hlim : ∀ l, Order.IsSuccLimit l → l < Ordinal.omega 1 → (∀ ξ, ξ < l → P ξ) → P l)
    {A : Ordinal.{0}} (hA : A < Ordinal.omega 1)
    (hbound : ∀ ξ, ξ < Ordinal.omega 1 → P ξ → ξ ≤ A) :
    ∃ ρ, ρ ≤ A ∧ P ρ ∧ ∀ ξ, ξ < Ordinal.omega 1 → (P ξ ↔ ξ ≤ ρ) := by
  obtain ⟨ρ, hρA, hρ, hiff⟩ := exists_greatest_stage_lt_omega1 P hzero hdown hlim hA hbound
  exact ⟨ρ, hρA, hρ, fun ξ _ ↦ hiff ξ⟩

/-! ### Concrete stage predicates -/

/-- An initial segment `Iic c` is closed at successor limits (in any universe). -/
theorem le_isSuccLimit_closed (c : Ordinal.{u}) :
    ∀ l, Order.IsSuccLimit l → (∀ ξ, ξ < l → ξ ≤ c) → l ≤ c := fun l hl hall ↦ by
  by_contra h
  exact (Order.lt_succ c).not_ge (hall _ (hl.succ_lt (lt_of_not_ge h)))

/-- **Finite-stage counterexample.**  `P α ↔ α < ω` has no greatest member. -/
theorem finite_stages_no_greatest :
    ¬ ∃ ρ : Ordinal.{0}, IsGreatest {ξ : Ordinal.{0} | ξ < Ordinal.omega0} ρ := by
  rintro ⟨ρ, hρ, hmax⟩
  have h1 : Order.succ ρ < Ordinal.omega0 := Ordinal.isSuccLimit_omega0.succ_lt hρ
  exact (Order.lt_succ ρ).not_ge (hmax h1)

/-- **Limit closure is the hypothesis that fails** for `P α ↔ α < ω`: it holds at `0`, is
downward closed and is bounded by `ω`, but every ordinal below the limit `ω` is a stage while `ω`
is not. -/
theorem finite_stages_only_limit_closure_fails :
    (0 : Ordinal.{0}) < Ordinal.omega0 ∧
      (∀ {α β : Ordinal.{0}}, α ≤ β → β < Ordinal.omega0 → α < Ordinal.omega0) ∧
      (∀ ξ : Ordinal.{0}, ξ < Ordinal.omega0 → ξ ≤ Ordinal.omega0) ∧
      (Order.IsSuccLimit (Ordinal.omega0 : Ordinal.{0}) ∧
        (∀ ξ : Ordinal.{0}, ξ < Ordinal.omega0 → ξ < Ordinal.omega0) ∧
        ¬ (Ordinal.omega0 : Ordinal.{0}) < Ordinal.omega0) :=
  ⟨Ordinal.omega0_pos, fun hle h ↦ hle.trans_lt h, fun _ h ↦ h.le,
    Ordinal.isSuccLimit_omega0, fun _ h ↦ h, lt_irrefl _⟩

/-- **Unattained bound.**  `P α ↔ α ≤ 3` with the supplied bound `A = 5`: the returned stage is
`3`, and the bound `5` is not itself a stage. -/
theorem unattained_bound_regression :
    (∃ ρ : Ordinal.{0}, ρ ≤ 5 ∧ ρ = 3 ∧ ∀ ξ, ξ ≤ 3 ↔ ξ ≤ ρ) ∧ ¬ (5 : Ordinal.{0}) ≤ 3 := by
  have h35 : (3 : Ordinal.{0}) < 5 := by exact_mod_cast (show (3 : ℕ) < 5 by norm_num)
  obtain ⟨ρ, hρ5, hρ3, hiff⟩ := exists_forall_iff_le_of_bounded_of_isSuccLimit_closed
    (fun ξ : Ordinal.{0} ↦ ξ ≤ 3) (zero_le) (fun hle h ↦ hle.trans h)
    (le_isSuccLimit_closed 3) (A := 5) (fun _ h ↦ h.trans h35.le)
  exact ⟨⟨ρ, hρ5, le_antisymm hρ3 ((hiff 3).mp le_rfl), hiff⟩, h35.not_ge⟩

/-- **Greatest stage zero.**  `P α ↔ α = 0` with the bound `A = 0`. -/
theorem greatest_stage_zero_regression :
    ∃ ρ : Ordinal.{0}, ρ ≤ 0 ∧ ρ = 0 ∧ ∀ ξ, ξ = 0 ↔ ξ ≤ ρ :=
  exists_forall_iff_le_of_bounded_of_isSuccLimit_closed (fun ξ : Ordinal.{0} ↦ ξ = 0)
    rfl (fun hle h ↦ le_antisymm (h ▸ hle) zero_le)
    (fun l hl hall ↦ by
      have h0 : (0 : Ordinal.{0}) < l := hl.bot_lt
      exact absurd (hall _ (hl.succ_lt h0)) (Order.lt_succ (0 : Ordinal.{0})).ne')
    (A := 0) (fun _ h ↦ h.le)

/-- **Limit bound.**  `P α ↔ α ≤ ω` with the bound `A = ω`, a limit: the returned stage `ω` is
itself a limit, so the result is not confined to successor or finite stages.  This pins the
statement, not a proof route.  The current `sSup` proof meets this instance in its limit case
(the supremum `ω` is a successor limit, and limit closure makes it a stage); a least-non-stage
proof would meet it in its successor case instead (the least non-stage is `ω + 1`), with its
limit case not reached. -/
theorem limit_bound_regression :
    Order.IsSuccLimit (Ordinal.omega0 : Ordinal.{0}) ∧
      ∃ ρ : Ordinal.{0}, ρ = Ordinal.omega0 ∧ ∀ ξ, ξ ≤ Ordinal.omega0 ↔ ξ ≤ ρ := by
  obtain ⟨ρ, hρA, hρ, hiff⟩ := exists_forall_iff_le_of_bounded_of_isSuccLimit_closed
    (fun ξ : Ordinal.{0} ↦ ξ ≤ Ordinal.omega0) zero_le (fun hle h ↦ hle.trans h)
    (le_isSuccLimit_closed _) (A := Ordinal.omega0) (fun _ h ↦ h)
  exact ⟨Ordinal.isSuccLimit_omega0, ρ, le_antisymm hρA ((hiff _).mp le_rfl), hiff⟩

/-- **`Type 1` instance** of the general form, on `Ordinal.{1}` (pinned by ascription). -/
theorem universe_one_regression :
    ∃ ρ : Ordinal.{1}, ρ = Ordinal.omega0 ∧ ∀ ξ : Ordinal.{1}, ξ ≤ Ordinal.omega0 ↔ ξ ≤ ρ := by
  obtain ⟨ρ, hρA, _, hiff⟩ := (exists_forall_iff_le_of_bounded_of_isSuccLimit_closed
    (fun ξ : Ordinal.{1} ↦ ξ ≤ Ordinal.omega0) zero_le (fun hle h ↦ hle.trans h)
    (le_isSuccLimit_closed _) (A := Ordinal.omega0) (fun _ h ↦ h) :
    ∃ ρ : Ordinal.{1}, ρ ≤ Ordinal.omega0 ∧ ρ ≤ Ordinal.omega0 ∧
      ∀ ξ : Ordinal.{1}, ξ ≤ Ordinal.omega0 ↔ ξ ≤ ρ)
  exact ⟨ρ, le_antisymm hρA ((hiff _).mp le_rfl), hiff⟩

/-- **The `ω₁` form** at the countable bound `A = ω`, which is a stage while `A + 1` is not:
`P ξ ↔ ξ ≤ ω`, and the returned stage is `ω`; the characterization holds for all `ξ`, not
only below `ω₁`. -/
theorem omega1_bound_regression :
    ¬ (Ordinal.omega0 + 1 : Ordinal.{0}) ≤ Ordinal.omega0 ∧
      ∃ ρ : Ordinal.{0}, ρ = Ordinal.omega0 ∧ ∀ ξ, ξ ≤ Ordinal.omega0 ↔ ξ ≤ ρ := by
  obtain ⟨ρ, hρA, _, hiff⟩ := exists_greatest_stage_lt_omega1
    (fun ξ : Ordinal.{0} ↦ ξ ≤ Ordinal.omega0) zero_le (fun hle h ↦ hle.trans h)
    (fun l hl _ hall ↦ le_isSuccLimit_closed _ l hl hall) Ordinal.omega0_lt_omega_one
    (fun _ _ h ↦ h)
  exact ⟨(lt_add_one _).not_ge, ρ, le_antisymm hρA ((hiff _).mp le_rfl), hiff⟩

/-- **`IsGreatest` application.**  For `P α ↔ α ≤ 3` with the bound `A = 5`, the greatest stage
is `3`. -/
theorem isGreatest_regression :
    ∃ ρ : Ordinal.{0}, ρ ≤ 5 ∧ IsGreatest {ξ : Ordinal.{0} | ξ ≤ 3} ρ ∧ ρ = 3 := by
  have h35 : (3 : Ordinal.{0}) ≤ 5 := by exact_mod_cast (show (3 : ℕ) ≤ 5 by norm_num)
  obtain ⟨ρ, hρ5, hρ⟩ := exists_isGreatest_setOf_of_bounded_of_isSuccLimit_closed
    (fun ξ : Ordinal.{0} ↦ ξ ≤ 3) zero_le (fun hle h ↦ hle.trans h)
    (le_isSuccLimit_closed 3) (A := 5) (fun _ h ↦ h.trans h35)
  exact ⟨ρ, hρ5, hρ, hρ.unique isGreatest_Iic⟩

/-! ### The consumer's contract shape -/

/-- **The consumer's contract shape**, verbatim from the handoff: the binders and conclusion in
the `(Cardinal.aleph 1).ord` notation, with the conclusion restricted to countable `ξ`.  It is
derived from the library's `exists_greatest_stage_lt_omega1` by `Cardinal.ord_aleph` and
specialisation, with no second proof.  The library form is stronger: its conclusion
`∀ ξ, P ξ ↔ ξ ≤ ρ` is unrestricted.  This name is guard-only; it is not exported. -/
theorem exists_greatest_countable_stage
    (P : Ordinal.{0} → Prop)
    (hzero : P 0)
    (hdown : ∀ {α β}, α ≤ β → P β → P α)
    (hlim : ∀ l, Order.IsSuccLimit l →
      l < (Cardinal.aleph 1).ord →
      (∀ ξ, ξ < l → P ξ) → P l)
    {A : Ordinal.{0}}
    (hA : A < (Cardinal.aleph 1).ord)
    (hbound : ∀ ξ, ξ < (Cardinal.aleph 1).ord → P ξ → ξ ≤ A) :
    ∃ ρ, ρ ≤ A ∧ P ρ ∧
      ∀ ξ, ξ < (Cardinal.aleph 1).ord → (P ξ ↔ ξ ≤ ρ) := by
  rw [Cardinal.ord_aleph] at hlim hA hbound ⊢
  obtain ⟨ρ, hρA, hρ, hiff⟩ := exists_greatest_stage_lt_omega1 P hzero hdown hlim hA hbound
  exact ⟨ρ, hρA, hρ, fun ξ _ ↦ hiff ξ⟩

/-- `succ ρ` is countable when `ρ` is, in the contract's `(Cardinal.aleph 1).ord` notation. -/
theorem succ_lt_aleph_one_ord {ρ : Ordinal.{0}} (hρ : ρ < (Cardinal.aleph 1).ord) :
    Order.succ ρ < (Cardinal.aleph 1).ord := by
  rw [Cardinal.ord_aleph] at hρ ⊢
  exact (Cardinal.isSuccLimit_omega 1).succ_lt hρ

/-- `ω` is countable, in the contract's `(Cardinal.aleph 1).ord` notation. -/
theorem omega0_lt_aleph_one_ord : Ordinal.omega0 < (Cardinal.aleph 1).ord := by
  rw [Cardinal.ord_aleph]
  exact Ordinal.omega0_lt_omega_one

/-! ### Consumer migration shape: an existential presentation predicate -/

/-- A toy presentation at stage `ξ`: a literal base object together with the evidence that the
stage is admissible for it (here: `ξ ≤ ω`).  Presentations exist exactly at the stages `ξ ≤ ω`,
so the greatest stage is the limit `ω`. -/
structure ToyPresentation (ξ : Ordinal.{0}) where
  /-- The literal base object the presentation is on. -/
  base : ℕ
  /-- The stage is admissible. -/
  fits : ξ ≤ Ordinal.omega0

/-- Validity of a toy presentation: its base is nonzero. -/
def ToyValid (ξ : Ordinal.{0}) (w : ToyPresentation ξ) : Prop := 0 < w.base

/-- The fixed base object. -/
def toyBase : ℕ := 7

/-- A presentation on the literal base `toyBase` is valid, at every admissible stage. -/
theorem toyValid_toyBase {ξ : Ordinal.{0}} (h : ξ ≤ Ordinal.omega0) :
    ToyValid ξ ⟨toyBase, h⟩ :=
  -- `ToyValid` and `toyBase` unfold definitionally, so the goal is `0 < 7`.
  show 0 < 7 by norm_num

/-- The consumer's predicate shape: a valid presentation at stage `ξ` on the literal base. -/
def ToyStage (ξ : Ordinal.{0}) : Prop :=
  ∃ w : ToyPresentation ξ, ToyValid ξ w ∧ w.base = toyBase

/-- **Consumer migration shape.**  The four hypotheses are supplied for `ToyStage` (the
presentation at zero; reduction to lower stages preserving the literal base; existence at a
countable nonzero limit from all lower stages; a countable bound on every presentation), the
contract theorem is destructured with the consumer's own call pattern
`⟨ρ, hρ, ⟨W, hW, hbase⟩, hstages⟩` (with `P := ToyStage`), and the destructured witness `W` is
used: it is an actual presentation at the greatest stage `ρ = ω`, on the literal
base `toyBase`, and there is no presentation at `succ ρ`. -/
theorem existential_presentation_regression :
    ∃ ρ : Ordinal.{0}, ρ = Ordinal.omega0 ∧
      (∃ w : ToyPresentation ρ, ToyValid ρ w ∧ w.base = toyBase) ∧
      ¬ ToyStage (Order.succ ρ) := by
  have hzero : ToyStage 0 := ⟨_, toyValid_toyBase zero_le, rfl⟩
  have hdown : ∀ {α β : Ordinal.{0}}, α ≤ β → ToyStage β → ToyStage α :=
    -- `hw : ToyValid β w` is reused at `α` by unfolding: `ToyValid` reads only the base,
    -- which the lower presentation keeps literally.
    fun hle ⟨w, hw, hb⟩ ↦ ⟨⟨w.base, hle.trans w.fits⟩, hw, hb⟩
  have hlimit : ∀ l, Order.IsSuccLimit l → l < (Cardinal.aleph 1).ord →
      (∀ ξ, ξ < l → ToyStage ξ) → ToyStage l := fun l hl _ hall ↦
    ⟨_, toyValid_toyBase (le_isSuccLimit_closed _ l hl fun ξ hξ ↦
      let ⟨w, _⟩ := hall ξ hξ; w.fits), rfl⟩
  have hA : Ordinal.omega0 < (Cardinal.aleph 1).ord := omega0_lt_aleph_one_ord
  have hbound : ∀ ξ, ξ < (Cardinal.aleph 1).ord → ToyStage ξ → ξ ≤ Ordinal.omega0 :=
    fun _ _ ⟨w, _, _⟩ ↦ w.fits
  obtain ⟨ρ, hρ, ⟨W, hW, hbase⟩, hstages⟩ :=
    exists_greatest_countable_stage ToyStage hzero hdown hlimit hA hbound
  have hρω : ρ = Ordinal.omega0 :=
    le_antisymm hρ ((hstages _ hA).mp ⟨_, toyValid_toyBase le_rfl, rfl⟩)
  refine ⟨ρ, hρω, ⟨W, hW, hbase⟩, fun hs ↦ ?_⟩
  exact (Order.lt_succ ρ).not_ge
    ((hstages _ (succ_lt_aleph_one_ord (hρ.trans_lt hA))).mp hs)

/-! ### Positive cases through the contract shape -/

/-- `P ξ ↔ ξ ≤ κ` through the contract shape, for any countable `κ ≤ A`: the returned stage is
`κ`, whatever the (possibly loose) bound `A`.  The successor case with a loose bound
(`unattained_bound_regression`, `κ = 3`, `A = 5`) and the zero case
(`greatest_stage_zero_regression`) are already pinned above; the limit case with a loose bound is
new, below. -/
theorem Iic_contract_regression (κ A : Ordinal.{0}) (hκA : κ ≤ A)
    (hA : A < (Cardinal.aleph 1).ord) :
    ∃ ρ, ρ = κ ∧ ρ ≤ A ∧ ∀ ξ, ξ < (Cardinal.aleph 1).ord → (ξ ≤ κ ↔ ξ ≤ ρ) := by
  obtain ⟨ρ, hρA, hρ, hiff⟩ := exists_greatest_countable_stage (fun ξ ↦ ξ ≤ κ) zero_le
    (fun hle h ↦ hle.trans h) (fun l hl _ hall ↦ le_isSuccLimit_closed κ l hl hall) hA
    (fun _ _ h ↦ h.trans hκA)
  exact ⟨ρ, le_antisymm hρ ((hiff κ (hκA.trans_lt hA)).mp le_rfl), hρA, hiff⟩

/-- **Limit stage, loose bound.**  `P ξ ↔ ξ ≤ ω` with `A = ω + 1`: the returned stage is the
limit `ω`, not `ω + 1`, and `ω + 1` is not a stage. -/
theorem limit_stage_contract_regression :
    Order.IsSuccLimit (Ordinal.omega0 : Ordinal.{0}) ∧
      (∃ ρ : Ordinal.{0}, ρ = Ordinal.omega0 ∧ ρ ≤ Ordinal.omega0 + 1 ∧
        ∀ ξ, ξ < (Cardinal.aleph 1).ord → (ξ ≤ Ordinal.omega0 ↔ ξ ≤ ρ)) ∧
      ¬ (Ordinal.omega0 + 1 : Ordinal.{0}) ≤ Ordinal.omega0 := by
  refine ⟨Ordinal.isSuccLimit_omega0, Iic_contract_regression _ _ (le_add_right le_rfl) ?_,
    (lt_add_one _).not_ge⟩
  rw [← Order.succ_eq_add_one]
  exact succ_lt_aleph_one_ord omega0_lt_aleph_one_ord

/-! ### Negative controls: each isolates one hypothesis -/

/-- The empty stage predicate, for the control without `hzero`. -/
def EmptyStage (_ : Ordinal.{0}) : Prop := False

/-- **Control: `hzero` is needed.**  The empty predicate is downward closed, closed at countable
nonzero limits (vacuously, since the premise fails at `0 < l`) and bounded by `A = 0 < ω₁`, but
fails at `0` and has no attained stage at all. -/
theorem empty_stages_only_zero_fails :
    (∀ {α β : Ordinal.{0}}, α ≤ β → EmptyStage β → EmptyStage α) ∧
      (∀ l : Ordinal.{0}, Order.IsSuccLimit l → l < Ordinal.omega 1 →
        (∀ ξ, ξ < l → EmptyStage ξ) → EmptyStage l) ∧
      (0 : Ordinal.{0}) < Ordinal.omega 1 ∧
      (∀ ξ : Ordinal.{0}, ξ < Ordinal.omega 1 → EmptyStage ξ → ξ ≤ 0) ∧
      ¬ EmptyStage 0 ∧ ¬ ∃ ρ, EmptyStage ρ :=
  ⟨fun _ h ↦ h, fun _ hl _ hall ↦ hall 0 hl.bot_lt, Ordinal.omega_pos 1, fun _ _ h ↦ h.elim,
    id, fun ⟨_, h⟩ ↦ h⟩

/-- The gapped stage predicate `{0} ∪ [2, ω)`, for the control without downward closure. -/
def GapStage (ξ : Ordinal.{0}) : Prop := ξ = 0 ∨ (2 ≤ ξ ∧ ξ < Ordinal.omega0)

/-- `1` is not a stage of `GapStage`. -/
theorem not_gapStage_one : ¬ GapStage 1 := by
  rintro (h | ⟨h, -⟩)
  · exact one_ne_zero h
  · exact absurd (by exact_mod_cast h : (2 : ℕ) ≤ 1) (by norm_num)

/-- **Control: downward closure is needed.**  `GapStage` (the stages `0, 2, 3, …`) holds at `0`,
is closed at countable nonzero limits (vacuously: every nonzero limit exceeds the missing stage
`1`) and is bounded by `A = ω < ω₁`, but is not downward closed (`2` is a stage, `1` is not)
and has no greatest stage. -/
theorem gap_stages_only_downward_closure_fails :
    GapStage 0 ∧
      (∀ l : Ordinal.{0}, Order.IsSuccLimit l → l < Ordinal.omega 1 →
        (∀ ξ, ξ < l → GapStage ξ) → GapStage l) ∧
      Ordinal.omega0 < Ordinal.omega 1 ∧
      (∀ ξ : Ordinal.{0}, ξ < Ordinal.omega 1 → GapStage ξ → ξ ≤ Ordinal.omega0) ∧
      ((1 : Ordinal.{0}) ≤ 2 ∧ GapStage 2 ∧ ¬ GapStage 1) ∧
      ¬ ∃ ρ, IsGreatest {ξ | GapStage ξ} ρ := by
  have h2ω : (2 : Ordinal.{0}) < Ordinal.omega0 := Ordinal.natCast_lt_omega0 2
  refine ⟨Or.inl rfl, fun l hl _ hall ↦ ?_, Ordinal.omega0_lt_omega_one,
    fun ξ _ h ↦ ?_, ⟨by exact_mod_cast (show (1 : ℕ) ≤ 2 by norm_num),
      Or.inr ⟨le_rfl, h2ω⟩, not_gapStage_one⟩, ?_⟩
  · have h1 : (1 : Ordinal.{0}) < l := by
      simpa using hl.succ_lt hl.bot_lt
    exact (not_gapStage_one (hall 1 h1)).elim
  · rcases h with rfl | ⟨-, h⟩
    · exact zero_le
    · exact h.le
  · rintro ⟨ρ, hρ, hmax⟩
    rcases hρ with rfl | ⟨h2, hω⟩
    · have h20 : (2 : Ordinal.{0}) ≤ 0 := hmax (Or.inr ⟨le_rfl, h2ω⟩)
      simp at h20
    · exact (Order.lt_succ ρ).not_ge (hmax (Or.inr ⟨h2.trans (Order.le_succ ρ),
        Ordinal.isSuccLimit_omega0.succ_lt hω⟩))

/-- The countable stage predicate `ξ < ω₁`, for the control without a countable bound. -/
def CountableStage (ξ : Ordinal.{0}) : Prop := ξ < Ordinal.omega 1

/-- **Control: the countable bound is needed.**  Stated in the contract's
`(Cardinal.aleph 1).ord` notation.  `CountableStage` (`ξ < ω₁`) satisfies the contract's `hzero`,
`hdown` and `hlim`, but no countable `A` bounds its countable stages, and the contract's
conclusion fails for every `A`: no attained `ρ` has `∀ ξ < ω₁, (P ξ ↔ ξ ≤ ρ)`. -/
theorem countable_stages_only_bound_fails :
    CountableStage 0 ∧
      (∀ {α β : Ordinal.{0}}, α ≤ β → CountableStage β → CountableStage α) ∧
      (∀ l : Ordinal.{0}, Order.IsSuccLimit l → l < (Cardinal.aleph 1).ord →
        (∀ ξ, ξ < l → CountableStage ξ) → CountableStage l) ∧
      (¬ ∃ A < (Cardinal.aleph 1).ord,
        ∀ ξ, ξ < (Cardinal.aleph 1).ord → CountableStage ξ → ξ ≤ A) ∧
      ¬ ∃ ρ, CountableStage ρ ∧
        ∀ ξ, ξ < (Cardinal.aleph 1).ord → (CountableStage ξ ↔ ξ ≤ ρ) := by
  rw [Cardinal.ord_aleph]
  have hs : ∀ {A : Ordinal.{0}}, A < Ordinal.omega 1 → Order.succ A < Ordinal.omega 1 :=
    (Cardinal.isSuccLimit_omega 1).succ_lt
  refine ⟨Ordinal.omega_pos 1, fun hle h ↦ hle.trans_lt h, fun _ _ h _ ↦ h, ?_, ?_⟩
  · rintro ⟨A, hA, hbound⟩
    exact (Order.lt_succ A).not_ge (hbound _ (hs hA) (hs hA))
  · rintro ⟨ρ, hρ, hiff⟩
    exact (Order.lt_succ ρ).not_ge ((hiff _ (hs hρ)).mp (hs hρ))

/-- **Control: an uncountable bound does not repair it.**  The contract with `hA` dropped, at
the uncountable bound `A = (Cardinal.aleph 1).ord`: the remaining hypotheses `hzero`, `hdown` and
`hlim` hold (`countable_stages_only_bound_fails`; `hlim` asks closure only at limits `l < ω₁`),
and `A` bounds the countable stages.  What fails is **attainment**: `ρ = A` satisfies the
restricted characterization `∀ ξ < ω₁, (P ξ ↔ ξ ≤ ρ)`, but `A` is not a stage, so the contract's
conclusion (which includes `P ρ`) fails.

The last conjunct concerns the **general form**
`exists_forall_iff_le_of_bounded_of_isSuccLimit_closed` only: there closure is asked at every
successor limit, and with the previous conjuncts it fails at the limit `ω₁` (all smaller
ordinals are stages, `ω₁` is not), so that form does not apply either. -/
theorem countable_stages_uncountable_bound :
    (∀ ξ, ξ < (Cardinal.aleph 1).ord → CountableStage ξ → ξ ≤ (Cardinal.aleph 1).ord) ∧
      (∀ ξ, ξ < (Cardinal.aleph 1).ord →
        (CountableStage ξ ↔ ξ ≤ (Cardinal.aleph 1).ord)) ∧
      ¬ CountableStage (Cardinal.aleph 1).ord ∧
      (¬ ∃ ρ, ρ ≤ (Cardinal.aleph 1).ord ∧ CountableStage ρ ∧
        ∀ ξ, ξ < (Cardinal.aleph 1).ord → (CountableStage ξ ↔ ξ ≤ ρ)) ∧
      (Order.IsSuccLimit (Cardinal.aleph 1).ord ∧
        ∀ ξ, ξ < (Cardinal.aleph 1).ord → CountableStage ξ) := by
  obtain ⟨-, -, -, -, hno⟩ := countable_stages_only_bound_fails
  simp only [Cardinal.ord_aleph] at hno ⊢
  exact ⟨fun _ h _ ↦ h.le, fun _ h ↦ ⟨fun _ ↦ h.le, fun _ ↦ h⟩, lt_irrefl _,
    fun ⟨ρ, _, hρ, hiff⟩ ↦ hno ⟨ρ, hρ, hiff⟩, Cardinal.isSuccLimit_omega 1, fun _ h ↦ h⟩

end GreatestStageRegressions

/-! ### Axiom hygiene and exact import closure -/

/-- The three exports and every guard declaration. -/
def headline : List Name :=
  [`InfinitaryLogic.exists_forall_iff_le_of_bounded_of_isSuccLimit_closed,
   `InfinitaryLogic.exists_isGreatest_setOf_of_bounded_of_isSuccLimit_closed,
   `InfinitaryLogic.exists_greatest_stage_lt_omega1,
   `GreatestStageRegressions.generic_exists_regression,
   `GreatestStageRegressions.generic_isGreatest_regression,
   `GreatestStageRegressions.generic_omega1_regression,
   `GreatestStageRegressions.omega1_restricted_shape_regression,
   `GreatestStageRegressions.le_isSuccLimit_closed,
   `GreatestStageRegressions.finite_stages_no_greatest,
   `GreatestStageRegressions.finite_stages_only_limit_closure_fails,
   `GreatestStageRegressions.unattained_bound_regression,
   `GreatestStageRegressions.greatest_stage_zero_regression,
   `GreatestStageRegressions.limit_bound_regression,
   `GreatestStageRegressions.universe_one_regression,
   `GreatestStageRegressions.omega1_bound_regression,
   `GreatestStageRegressions.isGreatest_regression,
   `GreatestStageRegressions.exists_greatest_countable_stage,
   `GreatestStageRegressions.succ_lt_aleph_one_ord,
   `GreatestStageRegressions.omega0_lt_aleph_one_ord,
   `GreatestStageRegressions.ToyPresentation,
   `GreatestStageRegressions.ToyValid,
   `GreatestStageRegressions.toyBase,
   `GreatestStageRegressions.toyValid_toyBase,
   `GreatestStageRegressions.ToyStage,
   `GreatestStageRegressions.existential_presentation_regression,
   `GreatestStageRegressions.Iic_contract_regression,
   `GreatestStageRegressions.limit_stage_contract_regression,
   `GreatestStageRegressions.EmptyStage,
   `GreatestStageRegressions.empty_stages_only_zero_fails,
   `GreatestStageRegressions.GapStage,
   `GreatestStageRegressions.not_gapStage_one,
   `GreatestStageRegressions.gap_stages_only_downward_closure_fails,
   `GreatestStageRegressions.CountableStage,
   `GreatestStageRegressions.countable_stages_only_bound_fails,
   `GreatestStageRegressions.countable_stages_uncountable_bound]

/-- The standard axioms. -/
def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

/-- The modules transitively imported by `m` (including `m`), read from the environment
header. -/
partial def importClosure (env : Environment) (m : Name) : NameSet :=
  go [m] {}
where
  go : List Name → NameSet → NameSet
    | [], seen => seen
    | m :: rest, seen =>
      if seen.contains m then go rest seen
      else
        let deps := match env.getModuleIdx? m with
          | some idx => (env.header.moduleData[idx.toNat]!).imports.toList.map (·.module)
          | none => []
        go (deps ++ rest) (seen.insert m)

/-- The constants a declaration refers to: its type, its value (theorem, definition and opaque
bodies alike), and the constructors, recursor rules and mutual families of inductive data. -/
def refs (ci : ConstantInfo) : NameSet := Id.run do
  let mut s := ci.type.getUsedConstantsAsSet
  match ci with
  | .defnInfo v => s := s ++ v.value.getUsedConstantsAsSet
  | .thmInfo v => s := s ++ v.value.getUsedConstantsAsSet
  | .opaqueInfo v => s := s ++ v.value.getUsedConstantsAsSet
  | .inductInfo v => s := s ++ .ofList v.ctors ++ .ofList v.all
  | .ctorInfo v => s := s.insert v.induct
  | .recInfo v =>
    s := s ++ .ofList v.all
    for r in v.rules do s := s ++ r.rhs.getUsedConstantsAsSet
  | .axiomInfo _ | .quotInfo _ => pure ()
  return s

/-- The transitive constant cone of `root`, failing closed on any constant that is not in the
environment. -/
def cone (env : Environment) (root : Name) : Except String NameSet := do
  let mut visited : NameSet := {}
  let mut stack : Array Name := #[root]
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if visited.contains n then
      continue
    visited := visited.insert n
    let some ci := env.find? n
      | throw s!"[UNKNOWN CONSTANT] {n} (reached from {root}) is not in the environment"
    for m in refs ci do
      unless visited.contains m do
        stack := stack.push m
  return visited

/-- The general lemma, which the other two exports must be derived from. -/
def generalLemma : Name := `InfinitaryLogic.exists_forall_iff_le_of_bounded_of_isSuccLimit_closed

/-- The exports whose constant cones must contain `generalLemma`. -/
def derivedExports : List Name :=
  [`InfinitaryLogic.exists_isGreatest_setOf_of_bounded_of_isSuccLimit_closed,
   `InfinitaryLogic.exists_greatest_stage_lt_omega1]

/-- The library's `ω₁` form, which the guard's contract shape must quote. -/
def omega1Form : Name := `InfinitaryLogic.exists_greatest_stage_lt_omega1

/-- The guard's copy of the consumer's contract shape. -/
def contractShape : Name := `GreatestStageRegressions.exists_greatest_countable_stage

/-- The migration-shape regression, which must go through the contract shape: its statement is
provable without it, so only the cone pins that the consumer's call is exercised. -/
def migrationShape : Name := `GreatestStageRegressions.existential_presentation_regression

/-- The exact `InfinitaryLogic` import closure of `OrdinalUtil`: the module itself, so that it
stays Mathlib-only.  Extending it is a deliberate decision.  The forbidden-prefix rule (no
`InfinitaryLogic` module other than `OrdinalUtil` itself) coincides with the `extra` half of this
pin, so the single `[CLOSURE DRIFT]` check reports both. -/
def allowedClosure : List Name := [`InfinitaryLogic.OrdinalUtil]

-- All checks run in one command, so the OK line cannot follow a failure of any of them.
run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a ↦ !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  for n in derivedExports do
    let c ← match cone env n with
      | .ok c => pure c
      | .error e => throwError e
    unless c.contains generalLemma do
      throwError "[NOT DERIVED] the cone of {n} does not contain {generalLemma}"
  -- the guard's contract shape quotes the library's omega 1 form, not a second proof
  let cc ← match cone env contractShape with
    | .ok c => pure c
    | .error e => throwError e
  unless cc.contains omega1Form do
    throwError "[NOT DERIVED] the cone of {contractShape} does not contain {omega1Form}"
  -- the migration-shape regression goes through the contract shape
  let cm ← match cone env migrationShape with
    | .ok c => pure c
    | .error e => throwError e
  unless cm.contains contractShape do
    throwError "[NOT DERIVED] the cone of {migrationShape} does not contain {contractShape}"
  -- control: the general lemma's own cone contains neither derived export
  let cg ← match cone env generalLemma with
    | .ok c => pure c
    | .error e => throwError e
  for n in derivedExports do
    if cg.contains n then
      throwError "[CONE CONTROL] the cone of {generalLemma} contains {n}"
  let target := `InfinitaryLogic.OrdinalUtil
  unless (env.getModuleIdx? target).isSome do
    throwError "module {target} is not in the environment"
  let cl := importClosure env target
  let ilModules := cl.toList.filter fun m ↦ (`InfinitaryLogic).isPrefixOf m
  let extra := ilModules.filter fun m ↦ !allowedClosure.contains m
  let missing := allowedClosure.filter fun m ↦ !ilModules.contains m
  unless extra.isEmpty && missing.isEmpty do
    throwError "[CLOSURE DRIFT] the InfinitaryLogic closure of {target} is {ilModules}; it must \
      stay Mathlib-only, and every other InfinitaryLogic module is forbidden; update \
      allowedClosure deliberately (extra {extra}, missing {missing})"
  logInfo m!"greatest stage regression guard: OK (applied: the general form and the IsGreatest \
    form at an arbitrary universe, the omega 1 form on Ordinal.\{0} with its conclusion for all \
    ξ, and the restricted shape below omega 1 by specialisation; the finite-stage \
    counterexample P α ↔ α < ω has no greatest member, and closure at successor limits is the \
    hypothesis that fails (at ω), the others holding; unattained bound P α ↔ α ≤ 3 with A = 5 \
    returns 3, and 5 is not a stage; greatest stage zero with A = 0; limit bound A = ω with \
    P α ↔ α ≤ ω returns ω, itself a limit; a Type 1 instance on Ordinal.\{1}; the omega 1 form \
    at A = ω with A + 1 not a stage returns ω; the IsGreatest form returns 3; the consumer's \
    contract shape in the (Cardinal.aleph 1).ord notation derived from the omega 1 form by \
    Cardinal.ord_aleph; the existential presentation predicate destructured with the \
    consumer's call pattern, recovering a presentation at the greatest stage ω on the literal \
    base, with none at its successor; through the contract shape, P α ↔ α ≤ κ returns κ for \
    every countable κ ≤ A, and the limit ω with the loose bound A = ω + 1 returns ω; controls: \
    the empty predicate has every hypothesis but P 0 and no stage, the gapped stages 0, 2, \
    3, … have every hypothesis but downward closure and no greatest member, and ξ < ω₁ has \
    every hypothesis but a countable bound and no attained greatest countable stage for any \
    A; with hA dropped and A = ω₁ the bound holds and ρ = ω₁ satisfies the restricted \
    characterization, but attainment fails (ω₁ is not a stage); the cones of the IsGreatest \
    and omega 1 forms contain the general lemma, and not conversely, the cone of the \
    contract shape contains the omega 1 form, and the cone of the migration-shape \
    regression contains the contract shape; import closure of {ilModules.length} \
    InfinitaryLogic module, OrdinalUtil itself (Mathlib-only); \
    standard axioms for the three exports and all {headline.length - 3} guard declarations)"
