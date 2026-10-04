/-
Proof-dependency guard for counting isomorphism classes through an isolating rank
(`InfinitaryLogic/Descriptive/ScatteredCounting.lean`).

The regression guard `check_scattered_counting_regressions.lean` applies every declaration and
checks the **import** closure of `Descriptive.ScatteredCounting`.  This guard checks, at the
level of **proof terms** and against the full library including `Conditional`, which parts of
that closure each declaration actually uses.

* **Fail-closed cone walk.**  For each root, the transitive constant cone follows types, values
  (theorem, definition and opaque bodies), constructors, recursor rules and inductive families.
  An unknown root, a theorem root that is not a theorem, or a constant reached in the walk that
  is not in the environment stops the guard (`[UNKNOWN ROOT]`, `[NOT A THEOREM]`,
  `[UNKNOWN CONSTANT]`).
* **Every public declaration is audited.**  The theorem roots and the structural roots (the
  structure `IsIsolatingRank` with its constructor, recursors and fields, `IsIsolatingRank.lift`
  and `codeStabilizationOrdinal`) are exactly the public declarations of the module
  (`[ROOT DRIFT]`).
* **The contract layer uses no stabilization ordinal.**  The cones of the contract API, the code
  form `IsIsolatingRank.exists_isolating_codeLevel` with its contrapositive, and the counting
  statements (`countable_fibers`, `mk_isoClasses_le_aleph_one`, `mk_isoClasses_eq_aleph_one`,
  `countable_isoClasses_iff_bounded`) contain neither `stabilizationOrdinal_spec` nor
  `stabilizationOrdinal`, and no constant declared in `Scott.Sentence`, `Scott.RefinementCount`,
  `Scott.IsolatingLevel`, `Scott.BFEquivRelabel`, `Descriptive.BFConcentration` or any `Karp`
  module (`[CONTRACT DRIFT]`).  `stabilizationOrdinal_spec` and `stabilizationOrdinal_lt_omega1'`
  are in the cone of the instance `isIsolatingRank_codeStabilizationOrdinal`;
  `codeStabilizationOrdinal_congr` reaches `stabilizesAt_of_equiv` but no constant of
  `Scott.RefinementCount` (it needs no countability).
* **`OrdinalCountability` exactly in the cardinal and boundedness forms.**
  `mk_le_aleph_one_of_countable_fibers`, `mk_eq_aleph_one_of_countable_fibers` and
  `countable_iff_rank_bounded` are in the cones of `mk_isoClasses_le_aleph_one`,
  `mk_isoClasses_eq_aleph_one` and `countable_isoClasses_iff_bounded` respectively, and constants
  declared in `OrdinalCountability` occur in exactly those three cones.
* **The family form only in the bridge.**  `exists_isolating_level` (and any constant declared
  in `Scott.IsolatingLevel`), `CodeBFEquiv.of_iso` and `BFEquiv.map_equiv` are in the cone of
  `exists_isolating_codeLevel_of_family` and of no other root (`[FAMILY DRIFT]`).
* **No `Conditional` constant.**  No cone contains a constant declared in a `Conditional` module,
  nor the Silver declarations `silver_countable_or_cantorAntichain`, `silver_core_polish`,
  `silverBurgessDichotomy`, `gandy_harrington_for_relation` or the Silver-half theorems of
  `Conditional/BFScatteredSilver.lean`; all are asserted to exist.
* **Forbidden lists of `check_bf_concentration_deps.lean`.**  No cone contains the López–Escobar,
  PC-class, invariant-separation or model-theoretic well-order and well-founded-tree
  boundedness declarations, or a constant declared in a module with a forbidden name.  `Karp`
  is not a forbidden substring here: `Karp.PotentialIso` is imported by `Scott.Sentence` and is
  reached by the instance and the bridge; instead, `Karp` constants are confined to those two
  cones and to the module `Karp.PotentialIso` (`[KARP DRIFT]`).
* **Transitive positive controls.**  `stabilizesAt_of_equiv` is reached from the instance only
  through `codeStabilizationOrdinal_congr`; `stabilizationOrdinal_spec` is reached from the
  bridge only through `exists_isolating_level`; `mk_le_aleph_one_of_countable_fibers` is reached
  from `mk_isoClasses_eq_aleph_one` only through `mk_eq_aleph_one_of_countable_fibers`.  The
  exclusion checks are shown to flag a root (the instance for the stabilization checks, the
  bridge for the family checks), so they cannot pass vacuously.
* **Standard axioms**, read off each cone and cross-checked against `collectAxioms`.
* **Negative controls.**  A custom `axiom` used in a theorem body, in an `opaque` body and in a
  theorem type must each be flagged by the same audit; and a theorem with a clean statement
  whose proof uses `silver_countable_or_cantorAntichain` must be flagged by the Silver-name and
  `Conditional`-module checks.

Run *after* `lake build InfinitaryLogic InfinitaryLogic.Everything`:
lake env lean scripts/check_scattered_counting_deps.lean
-/
import InfinitaryLogic
import InfinitaryLogic.Conditional

open Lean

namespace ScatteredCountingDeps

/-- Prefix a list of names with `FirstOrder.Language`. -/
def fol (l : List Name) : List Name := l.map (`FirstOrder.Language ++ ·)

/-- Prefix a list of names with `FirstOrder.Language.IsIsolatingRank`. -/
def iir (l : List Name) : List Name := l.map (`FirstOrder.Language.IsIsolatingRank ++ ·)

/-- Prefix a list of names with `InfinitaryLogic`. -/
def ilm (l : List Name) : List Name := l.map (`InfinitaryLogic ++ ·)

/-- `stabilizationOrdinal_spec`. -/
def spec : Name := `FirstOrder.Language.stabilizationOrdinal_spec

/-- `exists_isolating_level`. -/
def familyLevel : Name := `FirstOrder.Language.exists_isolating_level

/-- The instance. -/
def inst : Name := `FirstOrder.Language.isIsolatingRank_codeStabilizationOrdinal

/-- The family bridge. -/
def bridge : Name := `FirstOrder.Language.exists_isolating_codeLevel_of_family

/-- The congruence lemma. -/
def congrRoot : Name := `FirstOrder.Language.codeStabilizationOrdinal_congr

/-- The contract-layer theorems: the API, the code form and the counting statements. -/
def contractTheorems : List Name :=
  iir [`isolates_of_le, `lift_mk, `lift_lt_omega1, `of_le, `exists_isolating_codeLevel,
    `not_countable_isoClasses_of_forall_unisolated, `countable_fibers,
    `mk_isoClasses_le_aleph_one, `mk_isoClasses_eq_aleph_one,
    `countable_isoClasses_iff_bounded]

/-- The structural declarations of the contract: the structure, its constructor, recursors and
fields, and the lifted rank. -/
def contractStructural : List Name :=
  fol [`IsIsolatingRank] ++
    iir [`mk, `rec, `casesOn, `recOn, `iso_invariant, `lt_omega1, `isolates, `lift]

/-- The roots audited as theorems. -/
def theoremRoots : List Name := contractTheorems ++ [congrRoot, inst, bridge]

/-- The roots audited for axioms and forbidden dependencies only. -/
def structuralRoots : List Name :=
  contractStructural ++ fol [`codeStabilizationOrdinal]

/-- All roots. -/
def roots : List Name := theoremRoots ++ structuralRoots

/-- The contract-layer roots: no stabilization ordinal. -/
def contractRoots : List Name := contractTheorems ++ contractStructural

/-- The cardinal and boundedness forms, the only roots reaching `OrdinalCountability`. -/
def ordinalCountabilityRoots : List Name :=
  iir [`mk_isoClasses_le_aleph_one, `mk_isoClasses_eq_aleph_one,
    `countable_isoClasses_iff_bounded]

/-- The roots that may reach `Karp` constants (through `Scott.Sentence`). -/
def karpRoots : List Name := [inst, bridge]

/-- The dependencies each theorem root's cone must contain. -/
def required : List (Name × List Name) :=
  [(`FirstOrder.Language.IsIsolatingRank.isolates_of_le, fol [`CodeBFEquiv.monotone]),
   (`FirstOrder.Language.IsIsolatingRank.lift_mk, iir [`lift]),
   (`FirstOrder.Language.IsIsolatingRank.lift_lt_omega1, iir [`lift, `lt_omega1]),
   (`FirstOrder.Language.IsIsolatingRank.of_le, iir [`isolates_of_le]),
   (`FirstOrder.Language.IsIsolatingRank.exists_isolating_codeLevel,
      iir [`isolates_of_le, `lift_lt_omega1] ++ [`Ordinal.iSup_lt_omega_one]),
   (`FirstOrder.Language.IsIsolatingRank.not_countable_isoClasses_of_forall_unisolated,
      iir [`exists_isolating_codeLevel]),
   (`FirstOrder.Language.IsIsolatingRank.countable_fibers,
      iir [`isolates] ++ fol [`BFScattered, `codeBFEquivSetoid]),
   (`FirstOrder.Language.IsIsolatingRank.mk_isoClasses_le_aleph_one,
      iir [`countable_fibers] ++ [`InfinitaryLogic.mk_le_aleph_one_of_countable_fibers]),
   (`FirstOrder.Language.IsIsolatingRank.mk_isoClasses_eq_aleph_one,
      iir [`countable_fibers] ++ [`InfinitaryLogic.mk_eq_aleph_one_of_countable_fibers,
        `InfinitaryLogic.mk_le_aleph_one_of_countable_fibers]),
   (`FirstOrder.Language.IsIsolatingRank.countable_isoClasses_iff_bounded,
      iir [`countable_fibers] ++ [`InfinitaryLogic.countable_iff_rank_bounded]),
   (congrRoot, fol [`stabilizesAt_of_equiv, `stabilizationOrdinal, `equiv_implies_BFEquiv]),
   (inst, [spec, congrRoot] ++ fol [`stabilizationOrdinal_lt_omega1', `stabilizesAt_of_equiv,
      `codeStabilizationOrdinal]),
   (bridge, [familyLevel, spec] ++ fol [`CodeBFEquiv.of_iso, `BFEquiv.map_equiv])]

/-- Constants no contract-layer cone may contain. -/
def stabilizationNames : List Name :=
  [spec] ++ fol [`stabilizationOrdinal, `stabilizationOrdinal_lt_omega1', `StabilizesAt,
    `codeStabilizationOrdinal]

/-- Modules no contract-layer cone may reach. -/
def contractForbiddenModules : List Name :=
  ilm [`Scott.Sentence, `Scott.RefinementCount, `Scott.IsolatingLevel, `Scott.BFEquivRelabel,
    `Descriptive.BFConcentration]

/-- Constants confined to the cone of the family bridge. -/
def familyNames : List Name :=
  [familyLevel] ++ fol [`CodeBFEquiv.of_iso, `BFEquiv.map_equiv]

/-- The Silver declarations, which no cone may contain; each must exist. -/
def silverNames : List Name :=
  [`silver_countable_or_cantorAntichain, `silver_core_polish,
   `gandy_harrington_for_relation] ++
  fol [`silverBurgessDichotomy, `Sentenceω.bfScattered_of_isThinOnNatModels,
    `Sentenceω.bfScattered_iff_isThinOnNatModels, `Sentenceω.bfScattered_modelsOf_of_lt_continuum]

/-- Forbidden declarations, as in `check_bf_concentration_deps.lean`.  Each must exist. -/
def forbiddenNames : List Name :=
  fol [`lopez_escobar, `lopezEscobar_iff, `SmallVocabulary.lopezEscobar_iff,
    `invariant_analytic_separation, `sentence_separates_analytic_classes, `pcSentence,
    `pcClass_subset_of_invariant_superset, `subset_pcClass, `wellOrder_type_boundedness,
    `wellFounded_boundedness, `isWellOrder_of_realize_of_modelsOf_subset,
    `analytic_wellOrder_type_boundedness, `analytic_wellFoundedTree_rank_boundedness]

/-- Substrings no `InfinitaryLogic` module declaring a cone constant may contain, as in
`check_bf_concentration_deps.lean` but without `Karp` (checked separately) and with
`Conditional`. -/
def forbiddenModuleSub : List String :=
  ["LopezEscobar", "InvariantSeparation", "PCSentence", "PCClass", "PCMem", "WellOrdering",
   "WellOrderBridge", "AnalyticWellOrderBoundedness", "TreeCodes", "SmallVocabulary",
   "Interpolation", "Henkin", "Methods", "ModelTheory", "WellOrder", "Code", "Conditional",
   "ScottProcess", "Admissible", "BFScatteredSentence"]

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

/-- The module declaring a constant. -/
def moduleOf (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  return env.header.moduleNames[idx.toNat]!

/-- The constants of a cone declared in one of the modules `ms`. -/
def moduleHits (env : Environment) (c : NameSet) (ms : List Name) : List Name :=
  c.toList.filter fun n ↦ match moduleOf env n with
    | some m => ms.contains m
    | none => false

/-- The constants of a cone declared in a module with prefix `p`. -/
def prefixHits (env : Environment) (c : NameSet) (p : Name) : List (Name × Name) :=
  c.toList.filterMap fun n ↦ do
    let m ← moduleOf env n
    if p.isPrefixOf m then some (n, m) else none

/-- The axioms in a cone. -/
def coneAxioms (env : Environment) (c : NameSet) : List Name :=
  c.toList.filter fun n ↦ match env.find? n with
    | some (.axiomInfo _) => true
    | _ => false

/-- The violations in a cone: forbidden and Silver names, and constants from forbidden modules
with their module. -/
def violations (env : Environment) (c : NameSet) : List Name × List (Name × Name) :=
  let names := (forbiddenNames ++ silverNames).filter c.contains
  let mods := c.toList.filterMap fun n ↦ do
    let m ← moduleOf env n
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

end ScatteredCountingDeps

/-- **Axiom control 1**: a clean statement whose *proof* uses the custom axiom. -/
theorem ScatteredCountingDeps.controlBody : (2 : ℕ) + 2 = 4 :=
  ScatteredCountingDeps.nonstandardAxiom

/-- **Axiom control 2**: an `opaque` constant whose *body* uses the custom axiom. -/
noncomputable opaque ScatteredCountingDeps.controlOpaque : ℕ :=
  (fun _ : (2 : ℕ) + 2 = 4 ↦ 0) ScatteredCountingDeps.nonstandardAxiom

/-- **Axiom control 3**: the custom axiom in a *type*. -/
theorem ScatteredCountingDeps.controlType :
    ScatteredCountingDeps.nonstandardAxiom = ScatteredCountingDeps.nonstandardAxiom := rfl

/-- **Forbidden-dependency control**: a clean statement whose proof uses Silver's theorem. -/
theorem ScatteredCountingDeps.controlSilver : ∃ α : Ordinal.{0}, α < Ordinal.omega 1 := by
  have _h := @silver_countable_or_cantorAntichain.{0}
  exact ⟨0, Ordinal.omega_pos 1⟩

open ScatteredCountingDeps

run_cmd do
  let env ← getEnv
  let ax := `ScatteredCountingDeps.nonstandardAxiom
  -- AXIOM CONTROLS: the custom axiom sits where intended, and the audit flags it
  let some (.thmInfo body) := env.find? `ScatteredCountingDeps.controlBody
    | throwError "negative control: controlBody is missing or not a theorem"
  if body.type.getUsedConstants.contains ax then
    throwError "negative control: controlBody is no longer proof-only"
  unless body.value.getUsedConstants.contains ax do
    throwError "negative control: the axiom is absent from controlBody's proof"
  let some (.opaqueInfo op) := env.find? `ScatteredCountingDeps.controlOpaque
    | throwError "negative control: controlOpaque is missing or not opaque"
  if op.type.getUsedConstants.contains ax then
    throwError "negative control: controlOpaque's type mentions the axiom"
  unless op.value.getUsedConstants.contains ax do
    throwError "negative control: the axiom is absent from controlOpaque's body"
  let some (.thmInfo ty) := env.find? `ScatteredCountingDeps.controlType
    | throwError "negative control: controlType is missing or not a theorem"
  unless ty.type.getUsedConstants.contains ax do
    throwError "negative control: the axiom is absent from controlType's type"
  for ctl in [`ScatteredCountingDeps.controlBody, `ScatteredCountingDeps.controlOpaque,
      `ScatteredCountingDeps.controlType] do
    let (_, bad) ← audit ctl
    unless bad == [ax] do
      throwError "negative control FAILED: the audit of {ctl} reports {bad}, not [{ax}]"
  -- FORBIDDEN-DEPENDENCY CONTROL: proof-only, flagged by the Silver-name and module checks
  let witness := `silver_countable_or_cantorAntichain
  let some (.thmInfo fc) := env.find? `ScatteredCountingDeps.controlSilver
    | throwError "negative control: controlSilver is missing or not a theorem"
  if fc.type.getUsedConstants.contains witness then
    throwError "negative control: controlSilver is no longer proof-only"
  unless fc.value.getUsedConstants.contains witness do
    throwError "negative control: {witness} is absent from controlSilver's proof"
  let (fcCone, _) ← audit `ScatteredCountingDeps.controlSilver
  let (fnames, fmods) := violations env fcCone
  unless fnames.contains witness && fmods.any (fun (n, _) ↦ n == witness) &&
      !(prefixHits env fcCone `InfinitaryLogic.Conditional).isEmpty do
    throwError "negative control FAILED: the forbidden checks do not flag {witness}"
  -- the forbidden and Silver declarations exist, and so does a forbidden module
  for n in forbiddenNames ++ silverNames do
    unless (env.find? n).isSome do
      throwError "[MISSING FORBIDDEN] {n} is not in the full library; update the guard"
  let forbiddenMods := env.header.moduleNames.toList.filter forbiddenModule
  if forbiddenMods.isEmpty then
    throwError "[VACUOUS] no forbidden InfinitaryLogic module is in the environment"
  for m in contractForbiddenModules ++ [`InfinitaryLogic.OrdinalCountability] do
    unless (env.getModuleIdx? m).isSome do throwError "[VACUOUS] module {m} not found"
  -- the roots are exactly the public declarations of the module
  let targetModule := `InfinitaryLogic.Descriptive.ScatteredCounting
  let some midx := env.getModuleIdx? targetModule | throwError "module {targetModule} not found"
  let pub := (env.header.moduleData[midx.toNat]!).constNames.toList.filter fun n ↦
    !n.isInternalDetail && !(n.getString!.endsWith "congr_simp")
  let unaudited := pub.filter fun n ↦ !roots.contains n
  let foreign := roots.filter fun n ↦ !pub.contains n
  unless unaudited.isEmpty && foreign.isEmpty do
    throwError "[ROOT DRIFT] the public declarations of {targetModule} are not the audited \
      roots (unaudited {unaudited}, not declared there {foreign})"
  -- every root
  let mut sizes : Array (Name × Nat) := #[]
  let mut cones : Array (Name × NameSet) := #[]
  for root in roots do
    let some ci := env.find? root | throwError "[UNKNOWN ROOT] {root}"
    if theoremRoots.contains root then
      unless ci matches .thmInfo _ do throwError "[NOT A THEOREM] {root}"
    let (c, bad) ← audit root
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {root} uses {bad}"
    sizes := sizes.push (root.componentsRev.head!, c.size)
    cones := cones.push (root, c)
    if let some (_, reqs) := required.find? (·.1 == root) then
      for w in reqs do
        unless (env.find? w).isSome do throwError "[UNKNOWN REQUIRED] {w}"
        unless c.contains w do throwError "[REQUIRED] the cone of {root} does not contain {w}"
    else if theoremRoots.contains root then
      throwError "no required dependencies recorded for {root}"
    let (names, mods) := violations env c
    unless names.isEmpty do throwError "[FORBIDDEN] the cone of {root} contains {names}"
    unless mods.isEmpty do
      throwError "[FORBIDDEN MODULE] the cone of {root} contains {mods.take 10}"
    let cond := prefixHits env c `InfinitaryLogic.Conditional
    unless cond.isEmpty do
      throwError "[CONDITIONAL] the cone of {root} contains {cond.take 10}"
    -- the contract layer: no stabilization ordinal, none of the Scott-sentence modules
    if contractRoots.contains root then
      for w in stabilizationNames do
        if c.contains w then
          throwError "[CONTRACT DRIFT] the cone of {root} contains {w}"
      let hitsM := moduleHits env c contractForbiddenModules
      unless hitsM.isEmpty do
        throwError "[CONTRACT DRIFT] the cone of {root} reaches {hitsM.take 10}"
      let karp := prefixHits env c `InfinitaryLogic.Karp
      unless karp.isEmpty do
        throwError "[CONTRACT DRIFT] the cone of {root} reaches Karp: {karp.take 10}"
    -- the congruence lemma needs no countability: nothing from RefinementCount
    if root == congrRoot then
      let hitsR := moduleHits env c (ilm [`Scott.RefinementCount, `Scott.IsolatingLevel])
      unless hitsR.isEmpty && !c.contains spec do
        throwError "[CONGR DRIFT] the cone of {root} reaches {hitsR.take 10}"
    -- OrdinalCountability exactly in the cardinal and boundedness forms
    let oc := moduleHits env c [`InfinitaryLogic.OrdinalCountability]
    if ordinalCountabilityRoots.contains root then
      if oc.isEmpty then throwError "[REQUIRED] the cone of {root} misses OrdinalCountability"
    else unless oc.isEmpty do
      throwError "[ORDINAL COUNTABILITY DRIFT] the cone of {root} reaches {oc.take 10}"
    -- the family form only in the bridge
    if root != bridge then
      for w in familyNames do
        if c.contains w then
          throwError "[FAMILY DRIFT] the cone of {root} contains {w}"
      let fam := moduleHits env c (ilm [`Scott.IsolatingLevel, `Scott.BFEquivRelabel])
      unless fam.isEmpty do
        throwError "[FAMILY DRIFT] the cone of {root} reaches {fam.take 10}"
    -- Karp only through Scott.Sentence, in the instance and the bridge
    let karp := prefixHits env c `InfinitaryLogic.Karp
    unless karp.all (·.2 == `InfinitaryLogic.Karp.PotentialIso) do
      throwError "[KARP DRIFT] the cone of {root} reaches {karp.take 10}"
    if !karpRoots.contains root && !karp.isEmpty then
      throwError "[KARP DRIFT] the cone of {root} reaches {karp.take 10}"
  -- TRANSITIVE POSITIVE CONTROLS: reached only through intermediate declarations
  let checkTransitive (root w : Name) : Elab.Command.CommandElabM Unit := do
    let some ci := env.find? root | throwError "[UNKNOWN ROOT] {root}"
    if (direct ci).contains w then
      throwError "transitive control: {w} occurs directly in {root}; pick another witness"
    let some (_, c) := cones.find? (·.1 == root) | throwError "no cone for {root}"
    unless c.contains w do
      throwError "transitive control FAILED: {w} is not reached from {root}"
  checkTransitive inst `FirstOrder.Language.stabilizesAt_of_equiv
  checkTransitive bridge spec
  checkTransitive `FirstOrder.Language.IsIsolatingRank.mk_isoClasses_eq_aleph_one
    `InfinitaryLogic.mk_le_aleph_one_of_countable_fibers
  -- the exclusion checks are not vacuous: the same tests flag a root
  let some (_, instCone) := cones.find? (·.1 == inst) | throwError "no cone for the instance"
  unless stabilizationNames.any instCone.contains &&
      !(moduleHits env instCone contractForbiddenModules).isEmpty do
    throwError "[VACUOUS] the contract-layer checks flag no root"
  let some (_, bridgeCone) := cones.find? (·.1 == bridge) | throwError "no cone for the bridge"
  unless familyNames.all bridgeCone.contains &&
      !(moduleHits env bridgeCone (ilm [`Scott.IsolatingLevel])).isEmpty &&
      !(prefixHits env bridgeCone `InfinitaryLogic.Karp).isEmpty do
    throwError "[VACUOUS] the family and Karp checks flag no root"
  logInfo m!"scattered counting dependency guard: OK (cones {sizes.toList}; roots exactly the \
    {pub.length} public declarations of the module; the contract API, the code form and the \
    counting statements free of the stabilization ordinal and of Scott.Sentence, \
    RefinementCount, IsolatingLevel, BFEquivRelabel, BFConcentration and Karp constants; \
    stabilizationOrdinal_spec and stabilizationOrdinal_lt_omega1' in the instance; the \
    congruence lemma through stabilizesAt_of_equiv without RefinementCount; \
    OrdinalCountability exactly in mk_isoClasses_le_aleph_one, mk_isoClasses_eq_aleph_one and \
    countable_isoClasses_iff_bounded; exists_isolating_level, CodeBFEquiv.of_iso and \
    BFEquiv.map_equiv only in the family bridge; Karp.PotentialIso only in the instance and the \
    bridge; no Conditional constant and none of {silverNames.length} Silver declarations; \
    {forbiddenNames.length} forbidden declarations and {forbiddenMods.length} forbidden modules \
    present and avoided; transitive controls; exclusion checks shown to flag a root; standard \
    axioms from the cones, agreeing with collectAxioms; the custom-axiom controls and the Silver \
    control are flagged)"
