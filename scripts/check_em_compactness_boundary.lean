/-
Guard: the EM compactness-oracle layer takes its compactness as an explicit hypothesis and
never reaches legacy admissible machinery.

The EM endpoints once routed a genuine oracle through `admissibleFragmentOfUniv` into a
`FiniteCompactFragment`, which made a plain assumption look like a structural fact about
admissible fragments. Nothing in the pipeline used any fragment-specific property: an EM
template theory is built from an arbitrary `s : ℕ → Σ n, L.BoundedFormulaω Empty n`, so its
sentences lie in an arbitrary fragment. This file is the regression test for that not coming
back.

Two directions are checked, because either alone can pass vacuously:

* FORBIDDEN — no root reaches the legacy admissible structures;
* REQUIRED — each direct root really exposes `Theoryω.OrdinaryCompactness` in its TYPE (so the
  oracle is a hypothesis, not something manufactured internally), and each assembly root's cone
  really contains the ordinary finite-satisfiability corollary (so the oracle is applied to the
  honest premise rather than to something stronger smuggled in).

Plus absence checks for the two deleted `_model_of_fragment` spine declarations.

Run *after* `lake build`, so the oleans it resolves against are current.
-/
import InfinitaryLogic
import InfinitaryLogic.Conditional.MorleyHanfTransfer

open Lean

/-- `value?` returns `none` for THEOREMS (it only exposes `def` bodies); match `.thmInfo`
explicitly, otherwise theorem proof bodies are silently skipped and a forbidden structure
hidden in a proof would be MISSED. Same trap as documented in
`check_proof_system_boundary.lean`. -/
def declValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value
  | .thmInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

/-- Transitive constants, following TYPE, VALUE (via `declValue?`) and inductive constructors. -/
partial def deps (env : Environment) (n : Name) : NameSet := go n {} where
  go (n : Name) (acc : NameSet) : NameSet :=
    if acc.contains n then acc else
      let acc := acc.insert n
      match env.find? n with
      | some ci =>
        let cs := ci.type.getUsedConstants ++
          ((declValue? ci).map (·.getUsedConstants)).getD #[]
        let cs := match ci with
          | .inductInfo ii => cs ++ ii.ctors.toArray
          | _ => cs
        cs.foldl (fun a d => go d a) acc
      | none => acc

/-- The public compactness-oracle endpoints. Each must expose the oracle in its own type. -/
def directRoots : List Name :=
  [`FirstOrder.Language.IsLomega1omegaIndiscernibleOn.templateTheoryOfSeq_model_of_compact,
   `FirstOrder.Language.IsLomega1omegaIndiscernibleOn.stretch_restricted_of_compact,
   `FirstOrder.Language.IsLomega1omegaIndiscernibleOn.stretch_restricted_sequence_of_compact,
   `FirstOrder.Language.IsLomega1omegaIndiscernibleOnTail.templateTheoryOfSeq_model_of_compact]

/-- Downstream assemblies. These need not mention the oracle in their own type (they may
receive it under a `∀ J`), but their cones must reach the finite-satisfiability corollary. -/
def assemblyRoots : List (Name × Name) :=
  [(`FirstOrder.Language.hasArbLargeModels_of_restricted_extraction,
    `FirstOrder.Language.IsLomega1omegaIndiscernibleOn.templateTheoryOfSeq_isFinitelySatisfiable),
   (`FirstOrder.Language.tailTemplateRealizable_of_compact,
    `FirstOrder.Language.IsLomega1omegaIndiscernibleOnTail.templateTheoryOfSeq_isFinitelySatisfiable)]

def forbiddenSub : List String :=
  ["FiniteCompactFragment", "FullBarwiseFragment", "AdmissibleFragmentCore",
   "admissibleFragmentOfUniv", "barwise_compactness"]

/-- Declarations deleted in the #18 EM tranche; their reappearance means the legacy spine
was recreated rather than replaced. -/
def deletedNames : List Name :=
  [`FirstOrder.Language.Lomega1omegaTemplate.templateTheoryOn_model_of_fragment,
   `FirstOrder.Language.Lomega1omegaTemplate.templateTheoryOfSeq_model_of_fragment]

run_cmd do
  let env ← Lean.getEnv
  let oracle := `FirstOrder.Language.Theoryω.OrdinaryCompactness

  -- NEGATIVE CONTROL for the `.thmInfo` path.
  --
  -- The witness must be **proof-only**: a constant that appears in the root's VALUE but not in
  -- its TYPE. `OrdinaryCompactness` would be useless here, since it occurs in the type and the
  -- check would still pass with theorem-body traversal completely broken — which is exactly the
  -- silent-vacuity failure this control exists to prevent.
  let probe := `FirstOrder.Language.IsLomega1omegaIndiscernibleOn.templateTheoryOfSeq_model_of_compact
  let witness :=
    `FirstOrder.Language.IsLomega1omegaIndiscernibleOn.templateTheoryOfSeq_isFinitelySatisfiable
  let some pci := env.find? probe | throwError "negative control: {probe} not found"
  if pci.type.getUsedConstants.contains witness then
    throwError "negative control is no longer proof-only: {witness} now occurs in {probe}'s type"
  let some pval := declValue? pci
    | throwError "negative control: no value for {probe}; declValue? is not matching .thmInfo"
  unless pval.getUsedConstants.contains witness do
    throwError "negative control: {witness} absent from {probe}'s value"
  unless (deps env probe).contains witness do
    throwError "negative control FAILED: theorem-body traversal is broken \
      ({witness} is in {probe}'s value but not in its cone)"

  for root in directRoots do
    unless (env.find? root).isSome do throwError "root {root} not found"
    -- REQUIRED: the oracle is a HYPOTHESIS, visible in the type.
    let some ci := env.find? root | throwError "unreachable"
    unless ci.type.getUsedConstants.contains oracle do
      throwError "[REQUIRED] {root} does not expose Theoryω.OrdinaryCompactness in its type"
    -- FORBIDDEN
    let d := deps env root
    let hits := forbiddenSub.filter fun s =>
      d.toList.any fun n => (n.toString.splitOn s).length > 1
    unless hits.isEmpty do
      throwError "[FORBIDDEN] {root} reaches legacy admissible machinery: {hits}"

  for (root, witness) in assemblyRoots do
    unless (env.find? root).isSome do throwError "assembly root {root} not found"
    let d := deps env root
    unless d.contains witness do
      throwError "[REQUIRED] {root} does not reach the finite-satisfiability corollary {witness}"
    let hits := forbiddenSub.filter fun s =>
      d.toList.any fun n => (n.toString.splitOn s).length > 1
    unless hits.isEmpty do
      throwError "[FORBIDDEN] {root} reaches legacy admissible machinery: {hits}"

  for n in deletedNames do
    if (env.find? n).isSome then
      throwError "[DELETED] {n} is back in the environment"

  Lean.logInfo "EM compactness boundary: OK (oracle is a hypothesis; no legacy admissible machinery)"
