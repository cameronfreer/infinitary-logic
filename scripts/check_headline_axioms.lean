/-
Structural headline-axiom check, run by `scripts/check_headline_axioms.sh` (the guard runner
`scripts/check_all_guards.sh` runs a `check_*.lean` that has a same-named `.sh` wrapper only
through the wrapper, so this file is not run twice).

For every listed headline name it

* resolves the name in the environment (`[MISSING]` otherwise);
* for the default-surface list, checks that the declaring module lies in the import closure
  of `InfinitaryLogic.All`, which is what `import InfinitaryLogic` loads (the root file imports
  exactly `InfinitaryLogic.All`) (`[NOT ON DEFAULT SURFACE]` otherwise);
* runs `Lean.collectAxioms` and fails unless the result is contained in
  `[propext, Classical.choice, Quot.sound]` (`[NONSTANDARD AXIOMS]`);
* requires complete coverage: the number of examined names equals the length of the lists.

This replaces the previous mechanism, which parsed the printed `#print axioms` output line by
line and silently skipped every axiom list that Lean wrapped across lines.

Negative controls run first and must be flagged: a guard-local declaration proved by `sorry`
(so depending on `sorryAx`) and one using a guard-local `axiom`. They live only in this file;
`scripts/check_sorry_boundary.py` scans `InfinitaryLogic.lean` and `InfinitaryLogic/` only, so
this deliberate control does not trip it (the `declaration uses 'sorry'` warning below is
expected).

Run with: lake env lean scripts/check_headline_axioms.lean
-/
import InfinitaryLogic.Everything

open Lean

namespace HeadlineAxiomsControl

/-- Negative control: a custom axiom. -/
axiom customAxiom : False

/-- Negative control: depends on the custom axiom. -/
theorem usesCustomAxiom : False := customAxiom

/-- Negative control: depends on `sorryAx`. -/
theorem usesSorry : False := sorry

end HeadlineAxiomsControl

/-- Headline declarations that `import InfinitaryLogic` must expose. -/
def defaultHeadlines : List Name :=
  [`FirstOrder.Language.morley_hanf,
   `FirstOrder.Language.morleySeedTailTemplateRealizable_holds,
   `FirstOrder.Language.hanfNumber_le_beth_omega1,
   `FirstOrder.Language.Lomega1omegaHanfNumber_le_beth_omega1,
   `FirstOrder.Language.Lomega1omegaHanfNumber_eq_beth_omega1,
   `FirstOrder.Language.exists_small_model_of_hasArbLargeModels,
   `FirstOrder.Language.exists_complete_sentence_of_lomega1omegaSmall,
   `FirstOrder.Language.exists_complete_kCategorical_of_hasArbLargeModels,
   `FirstOrder.Language.morley_hanf_theory,
   `FirstOrder.Language.karp_theorem_w,
   `FirstOrder.Language.model_existence,
   `FirstOrder.Language.craig_interpolation,
   `FirstOrder.Language.lyndon_interpolation,
   `FirstOrder.Language.malitz_interpolation,
   `FirstOrder.Language.exists_model_relPreserving,
   `FirstOrder.Language.wellOrder_type_boundedness,
   `FirstOrder.Language.wellOrdering_undefinable,
   `FirstOrder.Language.lopez_escobar,
   `FirstOrder.Language.lopezEscobar_iff,
   `FirstOrder.Language.lopezEscobar_action_iff,
   `FirstOrder.Language.wellOrderClass_not_measurableSet]

/-- Headline declarations that live in the `Everything` closure. -/
def everythingHeadlines : List Name :=
  [`gandy_harrington_for_relation,
   `FirstOrder.Language.silverBurgessDichotomy]

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

/-- The non-standard axioms a declaration depends on. -/
def nonstandardAxioms (n : Name) : Elab.Command.CommandElabM (List Name) := do
  let axs ← Elab.Command.liftCoreM (collectAxioms n)
  return axs.toList.filter fun a ↦ !standardAxioms.contains a

run_cmd do
  -- Negative controls: the checker must flag both.
  let sorryBad ← nonstandardAxioms ``HeadlineAxiomsControl.usesSorry
  unless sorryBad.contains ``sorryAx do
    throwError "[CONTROL] the sorry control was not flagged (got {sorryBad})"
  let customBad ← nonstandardAxioms ``HeadlineAxiomsControl.usesCustomAxiom
  unless customBad.contains ``HeadlineAxiomsControl.customAxiom do
    throwError "[CONTROL] the custom-axiom control was not flagged (got {customBad})"
  let env ← getEnv
  unless (env.getModuleIdx? `InfinitaryLogic.All).isSome do
    throwError "[MISSING] InfinitaryLogic.All is not in the environment"
  let surface := importClosure env `InfinitaryLogic.All
  let mut examined : Nat := 0
  for (n, onDefault) in defaultHeadlines.map (·, true) ++ everythingHeadlines.map (·, false) do
    unless (env.find? n).isSome do throwError "[MISSING] {n} does not resolve"
    if onDefault then
      let some idx := env.getModuleIdxFor? n | throwError "[MISSING] {n} has no home module"
      let m := env.header.moduleNames[idx.toNat]!
      unless surface.contains m do
        throwError "[NOT ON DEFAULT SURFACE] {n} is declared in {m}, outside \
          InfinitaryLogic.All"
    let bad ← nonstandardAxioms n
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
    examined := examined + 1
  let expected := defaultHeadlines.length + everythingHeadlines.length
  unless examined == expected do
    throwError "[INCOMPLETE] examined {examined} of {expected} headline names"
  logInfo m!"Headline axioms: OK (both negative controls flagged: sorryAx and a custom axiom; \
    {examined} of {expected} names resolved and examined by collectAxioms: \
    {defaultHeadlines.length} on the default surface, {everythingHeadlines.length} in the \
    Everything closure; all within propext, Classical.choice, Quot.sound)"
