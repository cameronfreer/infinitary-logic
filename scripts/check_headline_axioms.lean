/-
Headline-axiom guard: the default import surface (`import InfinitaryLogic`) must expose the
default headline declarations, and every headline declaration must depend only on the standard
axioms `[propext, Classical.choice, Quot.sound]` (subsets allowed): in particular no `sorryAx`
and no custom axiom.

The check is STRUCTURAL: it works on the environment, not on printed output. (The previous
mechanism parsed `#print axioms` output line by line and silently skipped every axiom list
that Lean wrapped across lines.) The trust base is the same as `#print axioms`: both call
`Lean.collectAxioms`.

* **Controls first.** Negative: a guard-local declaration proved by `sorry` and one using a
  guard-local `axiom` must both be flagged. Positive, on IMPORTED declarations (whose axioms
  `collectAxioms` reads from the imported-module table, the path every headline takes, rather
  than walking a local body): `Classical.em` must report exactly
  `[propext, Classical.choice, Quot.sound]`, `funext` exactly `[Quot.sound]`, and
  `FirstOrder.Language.scottSentence_characterizes` exactly the standard three. All controls
  go through the same helper as the headline loop. Any failure is `[CONTROL]`.
* **Lists.** No name may occur twice, within or across the two lists (`[DUPLICATE]`).
* **Each headline name** must resolve (`[MISSING]`); a default-surface name must be declared in
  the import closure of the module `InfinitaryLogic` itself (`[NOT ON DEFAULT SURFACE]`); and
  its axioms must be standard (`[NONSTANDARD AXIOMS]`).
* **Coverage is structural**: the loop examines every listed name or throws; the printed count
  is the number of listed names.

The `sorry` control prints a `declaration uses 'sorry'` warning in this guard's output. That
cannot trip the proof or warning gates: `scripts/check_sorry_boundary.py` scans only
`InfinitaryLogic.lean` and `InfinitaryLogic/`, and `scripts/check_warning_regression.py` counts
warnings of the `lake build` targets, which do not include `scripts/`.

Run with: lake env lean scripts/check_headline_axioms.lean
-/
import InfinitaryLogic
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

/-- Positive controls: imported declarations and their exact axiom sets. -/
def importedControls : List (Name × List Name) :=
  [(`Classical.em, [`propext, `Classical.choice, `Quot.sound]),
   (`funext, [`Quot.sound]),
   (`FirstOrder.Language.scottSentence_characterizes,
    [`propext, `Classical.choice, `Quot.sound])]

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

/-- The axioms a declaration depends on (the one helper every control and headline uses). -/
def axiomsOf (n : Name) : Elab.Command.CommandElabM (List Name) := do
  return (← Elab.Command.liftCoreM (collectAxioms n)).toList

/-- The non-standard axioms a declaration depends on. -/
def nonstandardAxioms (n : Name) : Elab.Command.CommandElabM (List Name) := do
  return (← axiomsOf n).filter fun a ↦ !standardAxioms.contains a

run_cmd do
  let env ← getEnv
  -- Negative controls: the checker must flag both.
  let sorryBad ← nonstandardAxioms ``HeadlineAxiomsControl.usesSorry
  unless sorryBad.contains ``sorryAx do
    throwError "[CONTROL] the sorry control was not flagged (got {sorryBad})"
  let customBad ← nonstandardAxioms ``HeadlineAxiomsControl.usesCustomAxiom
  unless customBad.contains ``HeadlineAxiomsControl.customAxiom do
    throwError "[CONTROL] the custom-axiom control was not flagged (got {customBad})"
  -- Positive controls on imported declarations: exact axiom sets.
  for (n, expected) in importedControls do
    unless (env.getModuleIdxFor? n).isSome do
      throwError "[CONTROL] {n} is not an imported declaration"
    let axs ← axiomsOf n
    unless axs.all expected.contains && expected.all axs.contains do
      throwError "[CONTROL] collectAxioms reports {axs} for the imported declaration {n}, \
        expected exactly {expected}"
  -- The lists: no duplicates within or across them.
  let all := defaultHeadlines ++ everythingHeadlines
  for n in all do
    unless (all.filter (· == n)).length == 1 do
      throwError "[DUPLICATE] {n} is listed more than once"
  -- The headlines.
  unless (env.getModuleIdx? `InfinitaryLogic).isSome do
    throwError "[MISSING] the module InfinitaryLogic is not in the environment"
  let surface := importClosure env `InfinitaryLogic
  for (n, onDefault) in defaultHeadlines.map (·, true) ++ everythingHeadlines.map (·, false) do
    unless (env.find? n).isSome do throwError "[MISSING] {n} does not resolve"
    if onDefault then
      let some idx := env.getModuleIdxFor? n | throwError "[MISSING] {n} has no home module"
      let m := env.header.moduleNames[idx.toNat]!
      unless surface.contains m do
        throwError "[NOT ON DEFAULT SURFACE] {n} is declared in {m}, outside the import \
          closure of InfinitaryLogic"
    let bad ← nonstandardAxioms n
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo m!"Headline axioms: OK (negative controls flagged: sorryAx and a custom axiom; \
    positive controls on {importedControls.length} imported declarations report their exact \
    axiom sets; {all.length} distinct headline names examined by collectAxioms: \
    {defaultHeadlines.length} on the default surface (import closure of InfinitaryLogic), \
    {everythingHeadlines.length} in the Everything closure; all within propext, \
    Classical.choice, Quot.sound)"
