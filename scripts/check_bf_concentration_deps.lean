/-
Proof-dependency guard for concentration at back-and-forth levels
(`InfinitaryLogic/Descriptive/BFConcentration.lean`).

The regression guard `check_bf_concentration_regressions.lean` applies every theorem and checks
the **import** closure of `Descriptive.BFConcentration`, which adds exactly
`Scott.BFEquivRelabel` to the closure of `Descriptive.BFScattered`.  This guard checks, at the
level of **proof terms** and against the full library, where that dependency is used and that
the module goes through the landed descriptive route.

* **Fail-closed cone walk.**  For each root, the transitive constant cone follows types, values
  (theorem, definition and opaque bodies), constructors, recursor rules and inductive families.
  An unknown root, a root that is not a theorem (the definition `ConcentratedAtBFLevels` is
  checked separately), or a constant reached in the walk that is not in the environment stops
  the guard (`[UNKNOWN ROOT]`, `[NOT A THEOREM]`, `[UNKNOWN CONSTANT]`).
* **Where `BFEquiv.map_equiv` is used.**  It is in the cones of `CodeBFEquiv.of_iso`, the bridge
  `ConcentratedAtBFLevels.bfScattered`, its two endpoints, and the necessity lemma
  `invariant_of_bfLevel_saturated` (which is stated through isomorphism and needs
  `CodeBFEquiv.of_iso`).  It is **not** in the cones of the saturation theorems
  `exists_bfLevel_saturated_of_analyticSets` and `exists_bfLevel_saturated`, of the core
  `ConcentratedAtBFLevels.countable_isoClasses_of_saturatedAt`, or of the counting forms
  `ConcentratedAtBFLevels.countable_isoClasses_or_of_analyticSets` and
  `ConcentratedAtBFLevels.countable_isoClasses_or`; nor is `CodeBFEquiv.of_iso`.
* **The descriptive route.**  `exists_uniform_bfSeparation_of_analyticSets` is in the cones of
  both saturation theorems and both counting forms, which also contain the core.  The core is
  purely combinatorial: its cone contains neither `exists_uniform_bfSeparation_of_analyticSets`
  nor `exists_uniform_bfSeparation`.  The two endpoints of the bridge contain
  `not_hasCantorAntichainOn_of_bfScattered` (the thinness endpoint also
  `isThinOn_of_bfScattered`), and the bridge contains `countable_quotient_of_countable_range`.
* **Transitive positive controls.**  `BFEquiv.map_equiv` does not occur in the type or value of
  the bridge, but is in its cone (through `CodeBFEquiv.of_iso`); and
  `exists_uniform_bfSeparation_of_analyticSets` does not occur in the type or value of
  `ConcentratedAtBFLevels.countable_isoClasses_or`, but is in its cone (through
  `exists_bfLevel_saturated`).  The `map_equiv` exclusion check is shown to flag a root
  (`invariant_of_bfLevel_saturated`), so it cannot pass vacuously.
* **Forbidden lists of `check_bf_separation_deps.lean`.**  No cone contains the López–Escobar,
  PC-class, invariant-separation or model-theoretic well-order and well-founded-tree
  boundedness declarations, or a constant declared in an `InfinitaryLogic` module with a
  forbidden name; all forbidden declarations are asserted to exist.
* **Standard axioms**, read off each cone (every `axiom` reached through a type or a body,
  opaque bodies included) and cross-checked against `collectAxioms`: only `propext`,
  `Classical.choice` and `Quot.sound`, for every root and the definition.
* **Negative controls.**  A custom `axiom` used in a theorem body, in an `opaque` body and in a
  theorem type must each be flagged by the same audit, with `collectAxioms` agreeing; and a
  theorem with a clean statement whose proof uses `wellOrder_type_boundedness` must be flagged
  by the same forbidden-name and forbidden-module checks.

Run *after* `lake build`, so the oleans it resolves against are current:
lake env lean scripts/check_bf_concentration_deps.lean
-/
import InfinitaryLogic

open Lean

namespace BFConcentrationDeps

/-- Prefix a list of names with `FirstOrder.Language`. -/
def fol (l : List Name) : List Name := l.map (`FirstOrder.Language ++ ·)

/-- `BFEquiv.map_equiv`, from `Scott.BFEquivRelabel`. -/
def mapEquiv : Name := `FirstOrder.Language.BFEquiv.map_equiv

/-- `CodeBFEquiv.of_iso`, the only consumer of `mapEquiv` in the module. -/
def ofIso : Name := `FirstOrder.Language.CodeBFEquiv.of_iso

/-- Uniform separation of two analytic sets. -/
def sepAnalytic : Name := `FirstOrder.Language.exists_uniform_bfSeparation_of_analyticSets

/-- The core. -/
def core : Name := `FirstOrder.Language.ConcentratedAtBFLevels.countable_isoClasses_of_saturatedAt

/-- Roots whose cones must contain `BFEquiv.map_equiv`. -/
def mapEquivRoots : List Name :=
  [ofIso] ++ fol [`ConcentratedAtBFLevels.bfScattered,
    `ConcentratedAtBFLevels.not_hasCantorAntichainOn, `ConcentratedAtBFLevels.isThinOn,
    `invariant_of_bfLevel_saturated]

/-- Roots whose cones must avoid `BFEquiv.map_equiv` and `CodeBFEquiv.of_iso`. -/
def mapEquivFreeRoots : List Name :=
  fol [`exists_bfLevel_saturated_of_analyticSets, `exists_bfLevel_saturated] ++ [core] ++
    fol [`ConcentratedAtBFLevels.countable_isoClasses_or_of_analyticSets,
      `ConcentratedAtBFLevels.countable_isoClasses_or]

/-- Every theorem root. -/
def roots : List Name :=
  mapEquivRoots ++ fol [`ConcentratedAtBFLevels.mono, `concentratedAtBFLevels_of_countable] ++
    mapEquivFreeRoots

/-- The definition, audited for axioms and forbidden dependencies only. -/
def defRoot : Name := `FirstOrder.Language.ConcentratedAtBFLevels

/-- The dependencies each root's cone must contain. -/
def required : List (Name × List Name) :=
  [(ofIso, [mapEquiv]),
   (`FirstOrder.Language.ConcentratedAtBFLevels.bfScattered,
      [mapEquiv, ofIso] ++ fol [`countable_quotient_of_countable_range]),
   (`FirstOrder.Language.ConcentratedAtBFLevels.not_hasCantorAntichainOn,
      [mapEquiv] ++ fol [`ConcentratedAtBFLevels.bfScattered,
        `not_hasCantorAntichainOn_of_bfScattered]),
   (`FirstOrder.Language.ConcentratedAtBFLevels.isThinOn,
      [mapEquiv] ++ fol [`ConcentratedAtBFLevels.bfScattered, `isThinOn_of_bfScattered,
        `not_hasCantorAntichainOn_of_bfScattered]),
   (`FirstOrder.Language.invariant_of_bfLevel_saturated, [mapEquiv, ofIso]),
   (`FirstOrder.Language.ConcentratedAtBFLevels.mono, []),
   (`FirstOrder.Language.concentratedAtBFLevels_of_countable, []),
   (`FirstOrder.Language.exists_bfLevel_saturated_of_analyticSets, [sepAnalytic]),
   (`FirstOrder.Language.exists_bfLevel_saturated,
      [sepAnalytic] ++ fol [`exists_bfLevel_saturated_of_analyticSets]),
   (core, []),
   (`FirstOrder.Language.ConcentratedAtBFLevels.countable_isoClasses_or_of_analyticSets,
      [sepAnalytic, core] ++ fol [`exists_bfLevel_saturated_of_analyticSets]),
   (`FirstOrder.Language.ConcentratedAtBFLevels.countable_isoClasses_or,
      [sepAnalytic, core] ++ fol [`exists_bfLevel_saturated])]

/-- Constants the core's cone must avoid: it is purely combinatorial. -/
def coreForbidden : List Name :=
  [sepAnalytic, `FirstOrder.Language.exists_uniform_bfSeparation, mapEquiv, ofIso]

/-- Forbidden declarations, as in `check_bf_separation_deps.lean`: the López–Escobar theorem and
its descriptive forms, the PC-sentence coding, invariant analytic separation, and
model-theoretic well-order and well-founded-tree boundedness.  Each must exist. -/
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

/-- Substrings no `InfinitaryLogic` module declaring a cone constant may contain, as in
`check_bf_separation_deps.lean`. -/
def forbiddenModuleSub : List String :=
  ["LopezEscobar", "InvariantSeparation", "PCSentence", "PCClass", "PCMem", "WellOrdering",
   "WellOrderBridge", "AnalyticWellOrderBoundedness", "TreeCodes", "SmallVocabulary",
   "Interpolation", "Henkin", "Karp", "Methods", "ModelTheory", "WellOrder", "Code"]

/-- Whether an `InfinitaryLogic` module name is forbidden. -/
def forbiddenModule (m : Name) : Bool :=
  (`InfinitaryLogic).isPrefixOf m &&
    (m.components.any (fun c ↦ c.toString.startsWith "PC") ||
      forbiddenModuleSub.any fun s ↦ (m.toString.splitOn s).length ≠ 1)

/-- The standard axioms. -/
def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

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

/-- The axioms in a cone. -/
def coneAxioms (env : Environment) (c : NameSet) : List Name :=
  c.toList.filter fun n ↦ match env.find? n with
    | some (.axiomInfo _) => true
    | _ => false

/-- The violations in a cone: forbidden names, and constants from forbidden modules with their
module. -/
def violations (env : Environment) (c : NameSet) : List Name × List (Name × Name) :=
  let names := forbiddenNames.filter c.contains
  let mods := c.toList.filterMap fun n ↦ do
    let idx ← env.getModuleIdxFor? n
    let m := env.header.moduleNames[idx.toNat]!
    if forbiddenModule m then some (n, m) else none
  (names, mods)

/-- The audit of one declaration: its cone and its nonstandard axioms, read off the cone and
cross-checked against `collectAxioms`. -/
def audit (n : Name) : Elab.Command.CommandElabM (NameSet × List Name) := do
  let env ← getEnv
  let c ← match cone env n with
    | .ok c => pure c
    | .error e => throwError e
  let fromCone := coneAxioms env c
  let fromCollect := (← Elab.Command.liftCoreM (collectAxioms n)).toList
  unless fromCone.all fromCollect.contains && fromCollect.all fromCone.contains do
    throwError "[AXIOM MISMATCH] {n}: the cone gives {fromCone}, collectAxioms gives \
      {fromCollect}"
  return (c, fromCone.filter fun a ↦ !standardAxioms.contains a)

/-- The constants occurring directly in a declaration's type or value. -/
def direct (ci : ConstantInfo) : NameSet :=
  ci.type.getUsedConstantsAsSet ++ match ci with
    | .defnInfo v => v.value.getUsedConstantsAsSet
    | .thmInfo v => v.value.getUsedConstantsAsSet
    | .opaqueInfo v => v.value.getUsedConstantsAsSet
    | _ => {}

/-- **The nonstandard axiom of the negative controls.** -/
axiom nonstandardAxiom : (2 : ℕ) + 2 = 4

end BFConcentrationDeps

/-- **Axiom control 1**: a clean statement whose *proof* uses the custom axiom. -/
theorem BFConcentrationDeps.controlBody : (2 : ℕ) + 2 = 4 := BFConcentrationDeps.nonstandardAxiom

/-- **Axiom control 2**: an `opaque` constant whose *body* uses the custom axiom. -/
noncomputable opaque BFConcentrationDeps.controlOpaque : ℕ :=
  (fun _ : (2 : ℕ) + 2 = 4 ↦ 0) BFConcentrationDeps.nonstandardAxiom

/-- **Axiom control 3**: the custom axiom in a *type*. -/
theorem BFConcentrationDeps.controlType :
    BFConcentrationDeps.nonstandardAxiom = BFConcentrationDeps.nonstandardAxiom := rfl

/-- **Forbidden-dependency control**: a clean statement whose proof uses a forbidden constant. -/
theorem BFConcentrationDeps.controlForbidden : ∃ α : Ordinal.{0}, α < Ordinal.omega 1 := by
  have _h := @FirstOrder.Language.wellOrder_type_boundedness
  exact ⟨0, Ordinal.omega_pos 1⟩

open BFConcentrationDeps

run_cmd do
  let env ← getEnv
  let ax := `BFConcentrationDeps.nonstandardAxiom
  -- AXIOM CONTROLS: the custom axiom sits where intended, and the audit flags it
  let some (.thmInfo body) := env.find? `BFConcentrationDeps.controlBody
    | throwError "negative control: controlBody is missing or not a theorem"
  if body.type.getUsedConstants.contains ax then
    throwError "negative control: controlBody is no longer proof-only"
  unless body.value.getUsedConstants.contains ax do
    throwError "negative control: the axiom is absent from controlBody's proof"
  let some (.opaqueInfo op) := env.find? `BFConcentrationDeps.controlOpaque
    | throwError "negative control: controlOpaque is missing or not opaque"
  if op.type.getUsedConstants.contains ax then
    throwError "negative control: controlOpaque's type mentions the axiom"
  unless op.value.getUsedConstants.contains ax do
    throwError "negative control: the axiom is absent from controlOpaque's body"
  let some (.thmInfo ty) := env.find? `BFConcentrationDeps.controlType
    | throwError "negative control: controlType is missing or not a theorem"
  unless ty.type.getUsedConstants.contains ax do
    throwError "negative control: the axiom is absent from controlType's type"
  for ctl in [`BFConcentrationDeps.controlBody, `BFConcentrationDeps.controlOpaque,
      `BFConcentrationDeps.controlType] do
    let (_, bad) ← audit ctl
    unless bad == [ax] do
      throwError "negative control FAILED: the audit of {ctl} reports {bad}, not [{ax}]"
  -- FORBIDDEN-DEPENDENCY CONTROL: proof-only, and flagged by both checks
  let witness := `FirstOrder.Language.wellOrder_type_boundedness
  let some (.thmInfo fc) := env.find? `BFConcentrationDeps.controlForbidden
    | throwError "negative control: controlForbidden is missing or not a theorem"
  if fc.type.getUsedConstants.contains witness then
    throwError "negative control: controlForbidden is no longer proof-only"
  unless fc.value.getUsedConstants.contains witness do
    throwError "negative control: {witness} is absent from controlForbidden's proof"
  let (fcCone, _) ← audit `BFConcentrationDeps.controlForbidden
  let (fnames, fmods) := violations env fcCone
  unless fnames.contains witness && fmods.any (fun (n, _) ↦ n == witness) do
    throwError "negative control FAILED: the forbidden checks do not flag {witness}"
  -- the forbidden declarations and at least one forbidden module exist
  for n in forbiddenNames do
    unless (env.find? n).isSome do
      throwError "[MISSING FORBIDDEN] {n} is not in the full library; update forbiddenNames"
  let forbiddenMods := env.header.moduleNames.toList.filter forbiddenModule
  if forbiddenMods.isEmpty then
    throwError "[VACUOUS] no forbidden InfinitaryLogic module is in the environment"
  -- the definition
  let some (.defnInfo _) := env.find? defRoot | throwError "[UNKNOWN ROOT] {defRoot}"
  let (dc, dbad) ← audit defRoot
  unless dbad.isEmpty do throwError "[NONSTANDARD AXIOMS] {defRoot} uses {dbad}"
  let (dn, dm) := violations env dc
  unless dn.isEmpty && dm.isEmpty do
    throwError "[FORBIDDEN] the cone of {defRoot} reaches {dn} {dm.take 10}"
  -- the roots
  let mut sizes : Array (Name × Nat) := #[]
  let mut cones : Array (Name × NameSet) := #[]
  for root in roots do
    let some ci := env.find? root | throwError "[UNKNOWN ROOT] {root}"
    unless ci matches .thmInfo _ do throwError "[NOT A THEOREM] {root}"
    let (c, bad) ← audit root
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {root} uses {bad}"
    sizes := sizes.push (root.componentsRev.head!, c.size)
    cones := cones.push (root, c)
    let some (_, reqs) := required.find? (·.1 == root)
      | throwError "no required dependencies recorded for {root}"
    for w in reqs do
      unless (env.find? w).isSome do throwError "[UNKNOWN REQUIRED] {w}"
      unless c.contains w do throwError "[REQUIRED] the cone of {root} does not contain {w}"
    let (names, mods) := violations env c
    unless names.isEmpty do throwError "[FORBIDDEN] the cone of {root} contains {names}"
    unless mods.isEmpty do
      throwError "[FORBIDDEN MODULE] the cone of {root} contains {mods.take 10}"
    if mapEquivRoots.contains root then
      unless c.contains mapEquiv do
        throwError "[REQUIRED] the cone of {root} does not contain {mapEquiv}"
    if mapEquivFreeRoots.contains root then
      for w in [mapEquiv, ofIso] do
        if c.contains w then
          throwError "[MAP_EQUIV DRIFT] the cone of {root} contains {w}; only the bridge, its \
            endpoints and the necessity lemma may use Scott.BFEquivRelabel"
    if root == core then
      for w in coreForbidden do
        unless (env.find? w).isSome do throwError "[UNKNOWN] {w}"
        if c.contains w then
          throwError "[CORE DRIFT] the cone of the core contains {w}; the core must stay \
            combinatorial"
  -- TRANSITIVE POSITIVE CONTROLS: reached only through intermediate declarations
  let checkTransitive (root w : Name) : Elab.Command.CommandElabM Unit := do
    let some ci := env.find? root | throwError "[UNKNOWN ROOT] {root}"
    if (direct ci).contains w then
      throwError "transitive control: {w} occurs directly in {root}; pick another witness"
    let some (_, c) := cones.find? (·.1 == root) | throwError "no cone for {root}"
    unless c.contains w do
      throwError "transitive control FAILED: {w} is not reached from {root}"
  checkTransitive `FirstOrder.Language.ConcentratedAtBFLevels.bfScattered mapEquiv
  checkTransitive `FirstOrder.Language.ConcentratedAtBFLevels.countable_isoClasses_or sepAnalytic
  -- the map_equiv exclusion check is not vacuous: the same test flags a root
  let some (_, necCone) :=
      cones.find? (·.1 == `FirstOrder.Language.invariant_of_bfLevel_saturated)
    | throwError "no cone for the necessity lemma"
  unless necCone.contains mapEquiv do
    throwError "[VACUOUS] the map_equiv check flags no root"
  logInfo m!"bf concentration dependency guard: OK (cones {sizes.toList}; BFEquiv.map_equiv in \
    the cones of of_iso, the bridge, its two endpoints and the necessity lemma, and not in the \
    saturation theorems, the core or the counting forms; \
    exists_uniform_bfSeparation_of_analyticSets in both saturation theorems and both counting \
    forms; the core free of separation and of map_equiv; \
    not_hasCantorAntichainOn_of_bfScattered in both endpoints; transitive controls through \
    of_iso and exists_bfLevel_saturated; {forbiddenNames.length} forbidden declarations and \
    {forbiddenMods.length} forbidden modules present and avoided; standard axioms from the cones, \
    agreeing with collectAxioms; the custom-axiom controls in a proof, an opaque body and a \
    type and the forbidden-dependency control are flagged)"
