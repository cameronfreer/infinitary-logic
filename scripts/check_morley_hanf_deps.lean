/-
Dependency-cone guard for the definitive Morley–Hanf theorem.

Verifies, at the DECLARATION level (module-import checks cannot distinguish this,
since the historical theorems sharing files with the endpoint legitimately import
the Ramsey modules):

1. `morley_hanf`'s transitive proof-term cone uses NO declaration from
   - `InfinitaryLogic.Combinatorics.InfiniteRamsey`
   - `InfinitaryLogic.Combinatorics.InfiniteRamseyFamily`  (ordinary infinite Ramsey —
     unnecessary for the seed route: injective sequences are already seed-indiscernible)
   - `InfinitaryLogic.Combinatorics.ErdosRado`              (the frozen legacy ladder);

2. the cone DOES use the bounded finite-arity Erdős–Rado Marker supply
   (`finiteArityHomogeneousUpTo_beth_stage`) — the load-bearing combinatorial engine.

Run with: lake env lean scripts/check_morley_hanf_deps.lean
-/
import InfinitaryLogic

open Lean

def forbiddenModules : List Name :=
  [`InfinitaryLogic.Combinatorics.InfiniteRamsey,
   `InfinitaryLogic.Combinatorics.InfiniteRamseyFamily,
   `InfinitaryLogic.Combinatorics.ErdosRado]

def rootDecl : Name := `FirstOrder.Language.morley_hanf

def requiredWitness : Name := `finiteArityHomogeneousUpTo_beth_stage

open Elab Command in
run_cmd do
  let env ← getEnv
  -- sanity: the root and witness exist
  unless (env.find? rootDecl).isSome do
    throwError "root declaration {rootDecl} not found"
  unless (env.find? requiredWitness).isSome do
    throwError "witness declaration {requiredWitness} not found"
  -- transitive constant cone of the root
  let mut visited : NameSet := {}
  let mut stack : Array Name := #[rootDecl]
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if visited.contains n then
      continue
    visited := visited.insert n
    if let some ci := env.find? n then
      for m in ci.getUsedConstantsAsSet do
        unless visited.contains m do
          stack := stack.push m
  -- forbidden-module scan
  let mut offenders : Array (Name × Name) := #[]
  for n in visited.toList do
    if let some idx := env.getModuleIdxFor? n then
      let modName := env.header.moduleNames[idx.toNat]!
      if forbiddenModules.contains modName then
        offenders := offenders.push (n, modName)
  unless offenders.isEmpty do
    throwError "morley_hanf depends on forbidden modules: {offenders.toList}"
  -- positive witness
  unless visited.contains requiredWitness do
    throwError "morley_hanf no longer uses the bounded Marker supply {requiredWitness}"
  logInfo m!"OK: morley_hanf cone ({visited.size} constants) avoids infinite Ramsey and the legacy Erdős–Rado ladder, and uses the bounded Marker supply."
