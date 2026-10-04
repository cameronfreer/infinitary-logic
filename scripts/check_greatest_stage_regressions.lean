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
returning `3`; the **derivation**: the constant cones of the `ω₁` form and of the `IsGreatest`
form contain the general lemma; the **exact import closure** of `OrdinalUtil` (itself only: no
other `InfinitaryLogic` module, Mathlib only); **standard axioms** for the three exports and
every guard declaration.  The OK line is printed only after the cone, closure and axiom
checks.

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
originally offered, follows from the `ω₁` form. -/
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
   `GreatestStageRegressions.isGreatest_regression]

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
    at A = ω with A + 1 not a stage returns ω; the IsGreatest form returns 3; the cones of the \
    IsGreatest and omega 1 forms contain the general lemma, and not conversely; import \
    closure of {ilModules.length} InfinitaryLogic module, OrdinalUtil itself (Mathlib-only); \
    standard axioms for the three exports and all {headline.length - 3} guard declarations)"
