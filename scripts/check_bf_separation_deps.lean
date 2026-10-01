/-
Proof-dependency guard for uniform back-and-forth separation
(`InfinitaryLogic/Descriptive/BFSeparation.lean`).

The import guard `check_bf_separation_regressions.lean` shows that the module does not *import*
the López–Escobar, PC-class or model-theoretic well-order boundedness machinery.  This guard
checks the same boundary at the level of **proof terms**, against the full library, so that it
cannot pass vacuously.

* **The forbidden declarations exist.**  The file imports all of `InfinitaryLogic`, and every
  forbidden name is asserted to be in the environment before any cone is inspected: a rename or
  deletion of one of them fails this guard instead of silently weakening it.
* **The cones avoid them.**  For each root (`exists_uniform_bfSeparation`,
  `exists_uniform_bfSeparation_forall_ge`, `exists_uniform_bfSeparation_of_analyticSets`), the
  transitive constant cone, following types and values through `getUsedConstantsAsSet` (as in
  `check_morley_hanf_deps.lean`), contains no forbidden name and no constant declared in an
  `InfinitaryLogic` module whose name contains a forbidden substring or a component starting
  with `PC`.  Mathlib modules are exempt (`Mathlib.ModelTheory` is the first-order structure
  library every coded structure uses).
* **The cones use the descriptive route.**  Each cone contains
  `KleeneBrouwer.analytic_tree_rank_bounded`, `hasInfiniteBranch_bfTree_iff` and
  `lt_treeHeight_bfTree_of_codeBFEquiv`, and the two corollaries' cones contain
  `exists_uniform_bfSeparation`.
* **Negative control.**  `negativeControl` below has a clean statement and a proof that uses
  `wellOrder_type_boundedness`.  The guard checks that this constant is absent from its type and
  present in its value (matched through `.thmInfo`, as in `check_em_compactness_boundary.lean`),
  and that the *same* violation check used for the roots flags it.  If the walk stopped reaching
  theorem bodies, this control would fail rather than every root passing vacuously.
* **Standard axioms** for the roots (`propext`, `Classical.choice`, `Quot.sound`).

The forbidden names are the present implementation of the López–Escobar route and of
model-theoretic well-order boundedness.  A later migration that gives one of the public
boundedness endpoints a descriptive proof moves that name out of this list; the list tracks the
legacy implementation, not the public statements.

Run *after* `lake build`, so the oleans it resolves against are current:
lake env lean scripts/check_bf_separation_deps.lean
-/
import InfinitaryLogic

open Lean

namespace BFSeparationDeps

/-- The roots whose cones are inspected. -/
def roots : List Name :=
  [`FirstOrder.Language.exists_uniform_bfSeparation,
   `FirstOrder.Language.exists_uniform_bfSeparation_forall_ge,
   `FirstOrder.Language.exists_uniform_bfSeparation_of_analyticSets]

/-- Declarations every root cone must contain: the descriptive route. -/
def requiredWitnesses : List Name :=
  [`KleeneBrouwer.analytic_tree_rank_bounded,
   `FirstOrder.Language.hasInfiniteBranch_bfTree_iff,
   `FirstOrder.Language.lt_treeHeight_bfTree_of_codeBFEquiv]

/-- The corollaries must go through the main theorem. -/
def corollaryRoots : List Name :=
  [`FirstOrder.Language.exists_uniform_bfSeparation_forall_ge,
   `FirstOrder.Language.exists_uniform_bfSeparation_of_analyticSets]

/-- Forbidden declarations: the López–Escobar theorem and its descriptive forms, the PC-sentence
coding, invariant analytic separation, and model-theoretic well-order and well-founded-tree
boundedness.  Each must exist in the full library. -/
def forbiddenNames : List Name :=
  [`FirstOrder.Language.lopez_escobar,
   `FirstOrder.Language.lopezEscobar_iff,
   `FirstOrder.Language.SmallVocabulary.lopezEscobar_iff,
   `FirstOrder.Language.invariant_analytic_separation,
   `FirstOrder.Language.sentence_separates_analytic_classes,
   `FirstOrder.Language.pcSentence,
   `FirstOrder.Language.pcClass_subset_of_invariant_superset,
   `FirstOrder.Language.subset_pcClass,
   `FirstOrder.Language.wellOrder_type_boundedness,
   `FirstOrder.Language.wellFounded_boundedness,
   `FirstOrder.Language.isWellOrder_of_realize_of_modelsOf_subset,
   `FirstOrder.Language.analytic_wellOrder_type_boundedness,
   `FirstOrder.Language.analytic_wellFoundedTree_rank_boundedness]

/-- Substrings no `InfinitaryLogic` module declaring a cone constant may contain (the list of
the import guard `check_bf_separation_regressions.lean`). -/
def forbiddenModuleSub : List String :=
  ["LopezEscobar", "InvariantSeparation", "PCSentence", "PCClass", "PCMem", "WellOrdering",
   "WellOrderBridge", "AnalyticWellOrderBoundedness", "TreeCodes", "SmallVocabulary",
   "Interpolation", "Henkin", "Karp", "Methods", "ModelTheory", "WellOrder", "Code"]

/-- Whether an `InfinitaryLogic` module name is forbidden. -/
def forbiddenModule (m : Name) : Bool :=
  (`InfinitaryLogic).isPrefixOf m &&
    (m.components.any (fun c ↦ c.toString.startsWith "PC") ||
      forbiddenModuleSub.any fun s ↦ (m.toString.splitOn s).length ≠ 1)

/-- The transitive constant cone of `root`, following `ConstantInfo.getUsedConstantsAsSet`
(types and values), as in `check_morley_hanf_deps.lean`. -/
def cone (env : Environment) (root : Name) : NameSet := Id.run do
  let mut visited : NameSet := {}
  let mut stack : Array Name := #[root]
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
  return visited

/-- The violations in a cone: forbidden names, and constants from forbidden modules with their
module. -/
def violations (env : Environment) (c : NameSet) : List Name × List (Name × Name) :=
  let names := forbiddenNames.filter c.contains
  let mods := c.toList.filterMap fun n ↦ do
    let idx ← env.getModuleIdxFor? n
    let m := env.header.moduleNames[idx.toNat]!
    if forbiddenModule m then some (n, m) else none
  (names, mods)

/-- `value?` misses theorems; match `.thmInfo` explicitly, as in
`check_em_compactness_boundary.lean`. -/
def declValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value
  | .thmInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

end BFSeparationDeps

/-- **Negative control**: a clean statement whose proof uses a forbidden constant. -/
theorem BFSeparationDeps.negativeControl : ∃ α : Ordinal.{0}, α < Ordinal.omega 1 := by
  have _h := @FirstOrder.Language.wellOrder_type_boundedness
  exact ⟨0, Ordinal.omega_pos 1⟩

open BFSeparationDeps

run_cmd do
  let env ← getEnv
  -- the forbidden declarations exist, so the check below is not vacuous
  for n in forbiddenNames do
    unless (env.find? n).isSome do
      throwError "[MISSING FORBIDDEN] {n} is not in the full library; update forbiddenNames"
  -- at least one forbidden module exists in the full library
  let forbiddenMods := env.header.moduleNames.toList.filter forbiddenModule
  if forbiddenMods.isEmpty then
    throwError "[VACUOUS] no forbidden InfinitaryLogic module is in the environment"
  -- NEGATIVE CONTROL: the witness is proof-only, and the root check flags it
  let probe := `BFSeparationDeps.negativeControl
  let witness := `FirstOrder.Language.wellOrder_type_boundedness
  let some pci := env.find? probe | throwError "negative control: {probe} not found"
  unless pci matches .thmInfo _ do
    throwError "negative control: {probe} is not a theorem"
  if pci.type.getUsedConstants.contains witness then
    throwError "negative control is no longer proof-only: {witness} occurs in {probe}'s type"
  let some pval := declValue? pci
    | throwError "negative control: no value for {probe}; declValue? is not matching .thmInfo"
  unless pval.getUsedConstants.contains witness do
    throwError "negative control: {witness} is absent from {probe}'s value"
  let (cnames, cmods) := violations env (cone env probe)
  unless cnames.contains witness do
    throwError "negative control FAILED: the cone walk does not reach theorem bodies \
      ({witness} is in {probe}'s value but not flagged)"
  unless cmods.any (fun (n, _) ↦ n == witness) do
    throwError "negative control FAILED: the module check does not flag {witness}"
  -- the roots
  let mut sizes : Array Nat := #[]
  for root in roots do
    unless (env.find? root).isSome do throwError "root {root} not found"
    let c := cone env root
    sizes := sizes.push c.size
    let (names, mods) := violations env c
    unless names.isEmpty do
      throwError "[FORBIDDEN] the cone of {root} contains {names}"
    unless mods.isEmpty do
      throwError "[FORBIDDEN MODULE] the cone of {root} contains {mods.take 10}"
    for w in requiredWitnesses do
      unless (env.find? w).isSome do throwError "witness {w} not found"
      unless c.contains w do
        throwError "[REQUIRED] the cone of {root} does not contain {w}"
    if corollaryRoots.contains root then
      unless c.contains `FirstOrder.Language.exists_uniform_bfSeparation do
        throwError "[REQUIRED] {root} does not go through exists_uniform_bfSeparation"
    let axs ← Elab.Command.liftCoreM (collectAxioms root)
    let bad := axs.toList.filter fun a ↦
      !([`propext, `Classical.choice, `Quot.sound] : List Name).contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {root} uses {bad}"
  logInfo m!"bf separation dependency guard: OK ({forbiddenNames.length} forbidden declarations \
    and {forbiddenMods.length} forbidden modules present in the full library; root cones of \
    {sizes.toList} constants avoid them and contain the tree-boundedness, branch and height \
    witnesses; the proof-only negative control through wellOrder_type_boundedness is flagged; \
    standard axioms)"
