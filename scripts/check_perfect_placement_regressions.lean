/-
Regression guard for the placement of `Perfect.mk_eq_continuum`.

The lemma lives in `Topology/Perfect.lean`, a module with Mathlib imports only: its hypotheses
are purely topological (`MetricSpace`, `CompleteSpace`, `SecondCountableTopology`), so a user of
it should not have to import descriptive set theory or any logic.  It used to live in
`Descriptive/PerfectAntichain.lean`, which now imports it.  This file imports only
`InfinitaryLogic.Topology.Perfect` and checks:

* **Statement**: argument order, binder types and the universe shape, by
  `example : T := @Perfect.mk_eq_continuum`.
* **Positional universe order**: a single universe parameter (the carrier's), pinned by explicit
  instantiation `Perfect.mk_eq_continuum.{3}` and by the level-parameter count.
* **Applied**: `ℝ` has no isolated points, so it is a nonempty perfect subset of itself and has
  cardinality continuum.
* **Home module**: the lemma is declared in `InfinitaryLogic.Topology.Perfect`.
* **Import closure**: the `InfinitaryLogic` closure of `Topology/Perfect` is exactly the module
  itself; no Scott, descriptive, model-theory, Karp, Lω₁ω, methods, admissible or conditional
  module.

The declarations use only the standard axioms.

Run with: lake env lean scripts/check_perfect_placement_regressions.lean
-/
import InfinitaryLogic.Topology.Perfect

open Lean Cardinal Set

universe u

namespace PerfectPlacementGuard

/-! ### Statement and positional universe order -/

/-- The statement: carrier first, then the three instances, then the set and the two
hypotheses. -/
example : ∀ {α : Type u} [MetricSpace α] [CompleteSpace α] [SecondCountableTopology α]
    {C : Set α}, Perfect C → C.Nonempty → #C = Cardinal.continuum :=
  @Perfect.mk_eq_continuum

/-- One universe parameter, the carrier's, pinned by explicit instantiation. -/
example {α : Type 3} [MetricSpace α] [CompleteSpace α] [SecondCountableTopology α]
    {C : Set α} (hperf : Perfect C) (hne : C.Nonempty) : #C = Cardinal.continuum.{3} :=
  Perfect.mk_eq_continuum.{3} hperf hne

/-! ### Applied -/

/-- **Applied**: the real line has no isolated points, so it is a nonempty perfect subset of
itself and has size continuum. -/
theorem mk_univ_real : #(univ : Set ℝ) = Cardinal.continuum :=
  haveI : PerfectSpace ℝ := perfectSpace_iff_forall_not_isolated.mpr fun _ ↦ inferInstance
  Perfect.mk_eq_continuum (PerfectSpace.univ_perfect ℝ) univ_nonempty

end PerfectPlacementGuard

/-! ### Home module, import closure and axiom audit -/

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

/-- Module-name prefixes no module of the closure may have. -/
def forbiddenPrefixes : List Name :=
  [`InfinitaryLogic.Scott, `InfinitaryLogic.Descriptive, `InfinitaryLogic.ModelTheory,
   `InfinitaryLogic.Karp, `InfinitaryLogic.Lomega1omega, `InfinitaryLogic.Methods,
   `InfinitaryLogic.Admissible, `InfinitaryLogic.Conditional]

/-- The exact `InfinitaryLogic` import closure of `Topology/Perfect`.  Extending it is a
deliberate decision: update this list together with the module docstring. -/
def allowedClosure : List Name :=
  [`InfinitaryLogic.Topology.Perfect]

run_cmd do
  let env ← getEnv
  let d := `Perfect.mk_eq_continuum
  let home := `InfinitaryLogic.Topology.Perfect
  let some idx := env.getModuleIdxFor? d | throwError "declaration {d} not found"
  let m := env.header.moduleNames[idx.toNat]!
  unless m == home do throwError "[MOVED] {d} is declared in {m}, expected {home}"
  let some ci := env.find? d | throwError "declaration {d} not found"
  unless ci.levelParams.length == 1 do
    throwError "[UNIVERSES] {d} has universe parameters {ci.levelParams}, expected exactly one"
  let cl := importClosure env home
  let hits := cl.toList.filter fun m ↦ forbiddenPrefixes.any (·.isPrefixOf m)
  unless hits.isEmpty do
    throwError "[BROAD CONE] the closure of {home} reaches {hits}"
  let ilModules := cl.toList.filter fun m ↦ (`InfinitaryLogic).isPrefixOf m
  let extra := ilModules.filter fun m ↦ !allowedClosure.contains m
  let missing := allowedClosure.filter fun m ↦ !ilModules.contains m
  unless extra.isEmpty && missing.isEmpty do
    throwError "[CLOSURE DRIFT] the InfinitaryLogic closure of {home} is {ilModules}; \
      update allowedClosure deliberately (extra {extra}, missing {missing})"

/-- The audited declarations. -/
def auditedDecls : List Name :=
  [`Perfect.mk_eq_continuum, `PerfectPlacementGuard.mk_univ_real]

/-- The standard axioms. -/
def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in auditedDecls do
    unless (env.find? n).isSome do throwError "declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a ↦ !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "Perfect placement regression guard: OK (Perfect.mk_eq_continuum in \
    Topology/Perfect, statement and argument order pinned, one universe parameter pinned by \
    explicit instantiation; applied: the real line has size continuum; InfinitaryLogic import \
    closure of Topology/Perfect exactly the module itself, without Scott, descriptive, \
    model-theory, Karp, Lomega1omega, methods, admissible or conditional modules; standard \
    axioms)"
