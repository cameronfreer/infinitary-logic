/-
Import-closure guard for the graph-universe endpoint (issue #19).

`Admissible/Barwise/GraphUniverse.lean` consumes the Craig Layer-3 relationalization
(`GraphLanguage`, `TermGraph`, `Relationalize`, `GraphAxioms`, `GraphReconstruction`).  Those
modules sit below the broad interpolation cone; the Barwise adapter must stay there too.  This
guard fails if the module's import closure reaches the inseparability machinery, the budgeted
pair, the Lyndon material, or the Craig endpoints themselves.

Run with: lake env lean scripts/check_graph_universe_imports.lean
-/
import InfinitaryLogic.Admissible.Barwise.GraphUniverse

open Lean

/-- Modules the graph-universe closure must not reach.  Existence is not required, and the rule
is a substring match: it catches a module only while its name retains one of these substrings,
so a rename that drops the substring escapes it.  The guard enforces the present boundary; it
does not track renames. -/
def forbiddenModuleSub : List String :=
  ["Inseparability", "BudgetedPair", "Lyndon", "CraigArbitrary", "CraigInterpolation",
   "Interpolation.Craig"]

run_cmd do
  let env ← getEnv
  let target := `InfinitaryLogic.Admissible.Barwise.GraphUniverse
  unless (env.getModuleIdx? target).isSome do
    throwError "module {target} is not in the environment"
  -- the relationalization chain must actually be present
  for m in [`InfinitaryLogic.Methods.Interpolation.GraphReconstruction,
            `InfinitaryLogic.Methods.Interpolation.Relationalize,
            `InfinitaryLogic.Methods.Interpolation.GraphAxioms] do
    unless (env.getModuleIdx? m).isSome do
      throwError "[MISSING CHAIN] {m} is not in the import closure"
  let hits := env.header.moduleNames.toList.filter fun m =>
    forbiddenModuleSub.any fun s => (m.toString.splitOn s).length ≠ 1
  unless hits.isEmpty do
    throwError "[BROAD CONE] the graph-universe closure reaches {hits}"
  logInfo "graph-universe import guard: OK (relationalization chain present; no inseparability, \
    budgeted pair, Lyndon, or Craig endpoint in the closure)"
