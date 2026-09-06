/-
Authoritative absence guard for the retired `Admissible/Barwise/ConsistencyBridge.lean`
(see `docs/migration-consistency-bridge.md`).

Environment: the whole `InfinitaryLogic.Admissible` bundle, imported explicitly, with an
import-presence assertion so that an accidental narrowing of the import cannot make the absence
assertions vacuous.  Mechanism: one environment-lookup helper is used both for the positive
control and for the absence assertions.  The control is a synthetic declaration declared in this
file; it must resolve through the helper, so deleting it fails the guard.  The five retired public
names must then fail to resolve through the same helper; reintroducing any of them fails the
guard.

The cone and assembly checks of the successor endpoints stay in their own guards
(`check_henkin_closed_cone.lean`, `check_proof_system_boundary.lean`, ...).

Run with: lake env lean scripts/check_consistency_bridge_retired.lean
-/
import InfinitaryLogic.Admissible

open Lean

/-- The synthetic positive control: a declaration that MUST resolve. -/
def retiredNamesControl : Nat := 0

/-- The one lookup helper shared by the control and the absence assertions. -/
def present (env : Environment) (n : Name) : Bool := (env.find? n).isSome

/-- The retired public declarations. -/
def retiredNames : List Name :=
  [`FirstOrder.Language.BarwiseFragment,
   `FirstOrder.Language.FullBarwiseFragment,
   `FirstOrder.Language.consistentSets,
   `FirstOrder.Language.consistencyPropertyOfFullFragment,
   `FirstOrder.Language.barwise_completeness_II_syntactic_full]

/-- Modules whose presence certifies that the production environment is the intended one. -/
def requiredModules : List Name :=
  [`InfinitaryLogic.Admissible,
   `InfinitaryLogic.Admissible.Barwise.HenkinClosed,
   `InfinitaryLogic.Admissible.Barwise.SourceFragment,
   `InfinitaryLogic.Admissible.Barwise.GraphUniverse,
   `InfinitaryLogic.Admissible.Fragment]

run_cmd do
  let env ← getEnv
  -- import presence
  for m in requiredModules do
    unless (env.getModuleIdx? m).isSome do
      throwError "[ENVIRONMENT] {m} is not imported; the absence assertions would be vacuous"
  -- positive control: the lookup helper must see a declaration that exists
  unless present env `retiredNamesControl do
    throwError "positive control FAILED: the lookup helper does not resolve retiredNamesControl"
  -- the retired names must not resolve through the same helper
  for n in retiredNames do
    if present env n then
      throwError "[RETIRED NAME PRESENT] {n} has reappeared in the production environment"
  logInfo "consistency-bridge retirement guard: OK (Admissible bundle imported; lookup control \
    resolves; the five retired names are absent)"
