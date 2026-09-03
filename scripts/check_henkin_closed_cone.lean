/-
Dependency-cone guard for the relational kernel adapter (issue #19B).

`HenkinClosed.exists_countable_model_of_aconsistent` must earn its model from the fair
enumeration and the forward quotient truth lemma, never from a maximal-consistent construction,
and must not touch the legacy fragment structures.

1. FORBIDDEN — no declaration in the cone may be a maximal-consistency lemma
   (`…MaximalConsistent…`), the maximal-consistency biconditional `truthLemma`, the
   maximal→HenkinComplete bridge, or any of `FullBarwiseFragment`, `BarwiseFragment`,
   `FiniteCompactFragment`, `AdmissibleFragmentCore`.
2. REQUIRED — the endpoint's cone MUST contain `HenkinComplete`, `AConsistent`, `Derivable`,
   `exists_henkinComplete` and `truth_both`; the family constructor's cone MUST contain
   `ConsistencyPropertyEqOn`, `AConsistent` and `Derivable`. A root cannot pass by depending
   on nothing.
3. STALENESS — every exactly-named forbidden declaration must still exist.

Theorem bodies are traversed (`.thmInfo` matched explicitly), as in the other cone guards.

Run with: lake env lean scripts/check_henkin_closed_cone.lean
-/
import InfinitaryLogic.Admissible.Barwise.HenkinClosed
import InfinitaryLogic.Admissible.Barwise.ConsistencyBridge
import InfinitaryLogic.Methods.Henkin.Construction

open Lean

def declValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value
  | .thmInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

partial def transitiveDeps (env : Environment) (start : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack : List Name := [start]
  while !stack.isEmpty do
    let n := stack.head!
    stack := stack.tail!
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | none => pure ()
    | some ci =>
      let mut cs := ci.type.getUsedConstantsAsSet
      match declValue? ci with
      | some v => cs := cs.union v.getUsedConstantsAsSet
      | none => pure ()
      for c in cs do
        if !seen.contains c then stack := c :: stack
  return seen

/-- Forbidden by exact name (existence-checked). -/
def forbiddenExact : List Name :=
  [`FirstOrder.Language.truthLemma,
   `FirstOrder.Language.ConsistencyProperty.MaximalConsistent,
   `FirstOrder.Language.ConsistencyProperty.exists_maximal,
   `FirstOrder.Language.FullBarwiseFragment,
   `FirstOrder.Language.BarwiseFragment,
   `FirstOrder.Language.FiniteCompactFragment,
   `FirstOrder.Language.AdmissibleFragmentCore]

/-- Forbidden by substring (catches the whole maximal-consistency namespace). -/
def forbiddenSub : List String :=
  ["MaximalConsistent", "FullBarwiseFragment", "BarwiseFragment", "FiniteCompactFragment",
   "AdmissibleFragmentCore", "henkinComplete_univ_of_maximal"]

/-- Per-root required witnesses: the endpoint must run the fair enumeration and the forward
truth lemma; the family constructor must consume the kernel's structure and the proof system. -/
def guardedRoots : List (Name × List Name) :=
  [(`FirstOrder.Language.HenkinClosed.exists_countable_model_of_aconsistent,
    [`FirstOrder.Language.HenkinComplete, `FirstOrder.Language.AConsistent,
     `FirstOrder.Language.Derivable, `FirstOrder.Language.exists_henkinComplete,
     `FirstOrder.Language.truth_both]),
   (`FirstOrder.Language.HenkinClosed.consistencyPropertyEqOn,
    [`FirstOrder.Language.ConsistencyPropertyEqOn, `FirstOrder.Language.AConsistent,
     `FirstOrder.Language.Derivable])]

def requiredWitness : List Name := (guardedRoots.map Prod.snd).flatten

run_cmd do
  let env ← getEnv
  for f in forbiddenExact do
    unless (env.find? f).isSome do
      throwError "[STALE GUARD] forbidden declaration {f} no longer exists — update this list"
  for w in requiredWitness do
    unless (env.find? w).isSome do throwError "required witness {w} not found"
  for (root, witnesses) in guardedRoots do
    unless (env.find? root).isSome do throwError "root declaration {root} not found"
    let deps := transitiveDeps env root
    let hits := deps.toList.filter fun d =>
      forbiddenExact.contains d || forbiddenSub.any fun s => (d.toString.splitOn s).length ≠ 1
    unless hits.isEmpty do
      throwError "[FORBIDDEN] {root} reaches maximality or legacy fragment machinery: {hits}"
    let missing := witnesses.filter fun r => !deps.contains r
    unless missing.isEmpty do
      throwError "[MISSING WITNESS] {root} does not consume the kernel: {missing}"
  logInfo "HenkinClosed cone guard: OK (fair-enumeration kernel consumed; no maximality, no legacy \
    fragment structures)"
