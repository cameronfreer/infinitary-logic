/-
Proof-dependency guard for minimally unbounded classes for a rank on codes
(`InfinitaryLogic/Descriptive/MinimallyUnbounded.lean`).

The regression guard `check_minimally_unbounded_regressions.lean` applies every declaration and
pins the **import** closure of `Descriptive.MinimallyUnbounded`, which contains
`Karp.PotentialIso` through `Descriptive.ScatteredCounting` and `Scott.Sentence`.  This guard
checks, at the level of **proof terms** and against the full library including `Conditional`,
that the module's declarations use none of it.

* **Fail-closed cone walk.**  For each root, the transitive constant cone follows types, values
  (theorem, definition and opaque bodies), constructors, recursor rules and inductive families.
  An unknown root, a theorem root that is not a theorem, or a constant reached in the walk that
  is not in the environment stops the guard (`[UNKNOWN ROOT]`, `[NOT A THEOREM]`,
  `[UNKNOWN CONSTANT]`).
* **Every public declaration is audited.**  The roots are exactly the public declarations of the
  module (`[ROOT DRIFT]`).
* **Karp-free, with no stabilization ordinal.**  No cone contains a constant declared in a
  `Karp` module or in `Scott.Sentence`, `Scott.RefinementCount` or `Scott.IsolatingLevel`, nor
  `stabilizationOrdinal`, `stabilizationOrdinal_spec`, `stabilizationOrdinal_lt_omega1'`,
  `StabilizesAt`, `codeStabilizationOrdinal` (with `_def` and `_congr`), the instance
  `isIsolatingRank_codeStabilizationOrdinal` or the family bridge
  `exists_isolating_codeLevel_of_family` (`[KARP DRIFT]`, `[STABILIZATION DRIFT]`).
* **Only the abstract contract.**  The constants declared in `Descriptive.ScatteredCounting`
  that a cone contains are among the contract API (`IsIsolatingRank`, its constructor,
  recursors and fields, `lift`, `lift_mk`, `lift_lt_omega1`, `isolates_of_le`, `countable_fiber`,
  `countable_fibers`, `countable_isoClasses_iff_bounded`, and the compiler-generated auxiliary
  declarations of these, such as `countable_fiber.match_1_1`) (`[CONTRACT DRIFT]`).  They occur in
  the four rank-independence cones, each of which contains
  `IsIsolatingRank.countable_isoClasses_iff_bounded` (positive), and in no other cone.  Likewise
  `OrdinalCountability` constants occur exactly in the four rank-independence cones (through the
  counting statement).
* **Required dependencies** per root: the definitions through `BoundedRankOn`,
  `UnboundedRankOn` and `ModelsOf`; the literal form through `modelsOf_inf` and `modelsOf_not`;
  the back-and-forth statements through `modelsOf_scottSentenceAt`, `scottFormula` and (for the
  first half of Lemma XII.8) the engine `exists_bfClass_compl_of_sentence_cuts`; the
  rank-independence statements through the counting statement, and the minimality iff through
  `BFScattered.mono`.
* **No `Conditional` constant**, none of the Silver declarations, and none of the forbidden
  declarations and module names of `check_scattered_counting_deps.lean` (with `Karp` added); all
  are asserted to exist.
* **Transitive positive controls.**  `IsIsolatingRank.countable_fibers` is reached from
  `boundedRankOn_iff_of_isIsolatingRank` only through intermediate declarations, and
  `scottFormula` from `MinimallyUnboundedOn.exists_bfClass_compl_bounded`.  The exclusion
  checks are shown to flag the instance `isIsolatingRank_codeStabilizationOrdinal` (Karp,
  stabilization ordinal, `Scott.Sentence`), so they cannot pass vacuously.
* **Standard axioms**, read off each cone and cross-checked against `collectAxioms`.
* **Negative controls.**  A custom `axiom` used in a theorem body, in an `opaque` body and in a
  theorem type must each be flagged by the same audit; a theorem with a clean statement whose
  proof uses the instance `isIsolatingRank_codeStabilizationOrdinal` must be flagged by the Karp
  and stabilization checks; one whose proof uses `silver_countable_or_cantorAntichain` must be
  flagged by the Silver-name and `Conditional`-module checks.

Run *after* `lake build InfinitaryLogic InfinitaryLogic.Everything`:
lake env lean scripts/check_minimally_unbounded_deps.lean
-/
import InfinitaryLogic
import InfinitaryLogic.Conditional

open Lean

namespace MinimallyUnboundedDeps

/-- Prefix a list of names with `FirstOrder.Language`. -/
def fol (l : List Name) : List Name := l.map (`FirstOrder.Language ++ ·)

/-- Prefix a list of names with `FirstOrder.Language.IsIsolatingRank`. -/
def iir (l : List Name) : List Name := l.map (`FirstOrder.Language.IsIsolatingRank ++ ·)

/-- Prefix a list of names with `InfinitaryLogic`. -/
def ilm (l : List Name) : List Name := l.map (`InfinitaryLogic ++ ·)

/-- The module under test. -/
def targetModule : Name := `InfinitaryLogic.Descriptive.MinimallyUnbounded

/-- The four rank-independence statements. -/
def rankRoots : List Name :=
  iir [`boundedRankOn_iff_countable] ++
    fol [`boundedRankOn_iff_of_isIsolatingRank, `minimallyUnboundedOn_iff_minimallyUncountableOn,
      `minimallyUnboundedOn_iff_of_isIsolatingRank]

/-- The theorems that use no isolating rank. -/
def plainTheorems : List Name :=
  fol [`Sentenceω.minimallyUnbounded_iff_inf, `MinimallyUnboundedOn.bounded_bfClass_or_compl,
    `MinimallyUnboundedOn.exists_bfClass_compl_bounded]

/-- The theorem roots. -/
def theoremRoots : List Name := plainTheorems ++ rankRoots

/-- The definitions. -/
def defRoots : List Name := fol [`MinimallyUnboundedOn, `Sentenceω.MinimallyUnbounded]

/-- All roots. -/
def roots : List Name := theoremRoots ++ defRoots

/-- The counting statement every rank-independence cone must contain. -/
def counting : Name := `FirstOrder.Language.IsIsolatingRank.countable_isoClasses_iff_bounded

/-- The dependencies each root's cone must contain. -/
def required : List (Name × List Name) :=
  [(`FirstOrder.Language.MinimallyUnboundedOn, fol [`BoundedRankOn, `UnboundedRankOn, `ModelsOf]),
   (`FirstOrder.Language.Sentenceω.MinimallyUnbounded, fol [`MinimallyUnboundedOn]),
   (`FirstOrder.Language.Sentenceω.minimallyUnbounded_iff_inf,
      fol [`modelsOf_inf, `modelsOf_not]),
   (`FirstOrder.Language.MinimallyUnboundedOn.bounded_bfClass_or_compl,
      fol [`modelsOf_scottSentenceAt, `scottSentenceAt, `scottFormula,
        `realize_scottFormula_iff_BFEquiv]),
   (`FirstOrder.Language.MinimallyUnboundedOn.exists_bfClass_compl_bounded,
      fol [`exists_bfClass_compl_of_sentence_cuts, `boundedRankOn_sUnion,
        `modelsOf_scottSentenceAt, `scottFormula]),
   (`FirstOrder.Language.IsIsolatingRank.boundedRankOn_iff_countable, [counting]),
   (`FirstOrder.Language.boundedRankOn_iff_of_isIsolatingRank,
      [counting] ++ iir [`boundedRankOn_iff_countable]),
   (`FirstOrder.Language.minimallyUnboundedOn_iff_minimallyUncountableOn,
      [counting] ++ iir [`boundedRankOn_iff_countable] ++
        fol [`BFScattered.mono, `MinimallyUncountableOn]),
   (`FirstOrder.Language.minimallyUnboundedOn_iff_of_isIsolatingRank,
      [counting] ++ fol [`minimallyUnboundedOn_iff_minimallyUncountableOn])]

/-- The contract API: the only `Descriptive.ScatteredCounting` constants a cone may contain. -/
def contractAPI : List Name :=
  fol [`IsIsolatingRank] ++
    iir [`mk, `rec, `casesOn, `recOn, `iso_invariant, `lt_omega1, `isolates, `lift, `lift_mk,
      `lift_lt_omega1, `isolates_of_le, `countable_fiber, `countable_fibers,
      `countable_isoClasses_iff_bounded]

/-- The stabilization-ordinal constants no cone may contain; each must exist. -/
def stabilizationNames : List Name :=
  fol [`stabilizationOrdinal, `stabilizationOrdinal_spec, `stabilizationOrdinal_lt_omega1',
    `StabilizesAt, `codeStabilizationOrdinal, `codeStabilizationOrdinal_def,
    `codeStabilizationOrdinal_congr, `isIsolatingRank_codeStabilizationOrdinal,
    `exists_isolating_codeLevel_of_family, `stabilizationOrdinal_eq_of_equiv,
    `stabilizesAt_of_equiv]

/-- Modules no cone may reach. -/
def scottForbiddenModules : List Name :=
  ilm [`Scott.Sentence, `Scott.RefinementCount, `Scott.IsolatingLevel]

/-- The Silver declarations, which no cone may contain; each must exist. -/
def silverNames : List Name :=
  [`silver_countable_or_cantorAntichain, `silver_core_polish,
   `gandy_harrington_for_relation] ++
  fol [`silverBurgessDichotomy, `Sentenceω.bfScattered_of_isThinOnNatModels,
    `Sentenceω.bfScattered_iff_isThinOnNatModels, `Sentenceω.bfScattered_modelsOf_of_lt_continuum]

/-- Forbidden declarations, as in `check_scattered_counting_deps.lean`.  Each must exist. -/
def forbiddenNames : List Name :=
  fol [`lopez_escobar, `lopezEscobar_iff, `SmallVocabulary.lopezEscobar_iff,
    `invariant_analytic_separation, `sentence_separates_analytic_classes, `pcSentence,
    `pcClass_subset_of_invariant_superset, `subset_pcClass, `wellOrder_type_boundedness,
    `wellFounded_boundedness, `isWellOrder_of_realize_of_modelsOf_subset,
    `analytic_wellOrder_type_boundedness, `analytic_wellFoundedTree_rank_boundedness]

/-- Substrings no `InfinitaryLogic` module declaring a cone constant may contain: the list of
`check_scattered_counting_deps.lean`, with `Karp` added. -/
def forbiddenModuleSub : List String :=
  ["LopezEscobar", "InvariantSeparation", "PCSentence", "PCClass", "PCMem", "WellOrdering",
   "WellOrderBridge", "AnalyticWellOrderBoundedness", "TreeCodes", "SmallVocabulary",
   "Interpolation", "Henkin", "Methods", "ModelTheory", "WellOrder", "Code", "Conditional",
   "ScottProcess", "Admissible", "BFScatteredSentence", "Karp"]

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

/-- The Karp and stabilization violations in a cone: `Karp` constants, stabilization names, and
constants of `Scott.Sentence`, `Scott.RefinementCount` or `Scott.IsolatingLevel`. -/
def karpViolations (env : Environment) (c : NameSet) :
    List (Name × Name) × List Name × List Name :=
  (prefixHits env c `InfinitaryLogic.Karp, stabilizationNames.filter c.contains,
    moduleHits env c scottForbiddenModules)

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

end MinimallyUnboundedDeps

/-- **Axiom control 1**: a clean statement whose *proof* uses the custom axiom. -/
theorem MinimallyUnboundedDeps.controlBody : (2 : ℕ) + 2 = 4 :=
  MinimallyUnboundedDeps.nonstandardAxiom

/-- **Axiom control 2**: an `opaque` constant whose *body* uses the custom axiom. -/
noncomputable opaque MinimallyUnboundedDeps.controlOpaque : ℕ :=
  (fun _ : (2 : ℕ) + 2 = 4 ↦ 0) MinimallyUnboundedDeps.nonstandardAxiom

/-- **Axiom control 3**: the custom axiom in a *type*. -/
theorem MinimallyUnboundedDeps.controlType :
    MinimallyUnboundedDeps.nonstandardAxiom = MinimallyUnboundedDeps.nonstandardAxiom := rfl

/-- **Karp control**: a clean statement whose proof uses the stabilization-ordinal instance. -/
theorem MinimallyUnboundedDeps.controlKarp : ∃ α : Ordinal.{0}, α < Ordinal.omega 1 := by
  have _h := @FirstOrder.Language.isIsolatingRank_codeStabilizationOrdinal.{0, 0}
  exact ⟨0, Ordinal.omega_pos 1⟩

/-- **Forbidden-dependency control**: a clean statement whose proof uses Silver's theorem. -/
theorem MinimallyUnboundedDeps.controlSilver : ∃ α : Ordinal.{0}, α < Ordinal.omega 1 := by
  have _h := @silver_countable_or_cantorAntichain.{0}
  exact ⟨0, Ordinal.omega_pos 1⟩

open MinimallyUnboundedDeps

run_cmd do
  let env ← getEnv
  let ax := `MinimallyUnboundedDeps.nonstandardAxiom
  -- AXIOM CONTROLS: the custom axiom sits where intended, and the audit flags it
  let some (.thmInfo body) := env.find? `MinimallyUnboundedDeps.controlBody
    | throwError "negative control: controlBody is missing or not a theorem"
  if body.type.getUsedConstants.contains ax then
    throwError "negative control: controlBody is no longer proof-only"
  unless body.value.getUsedConstants.contains ax do
    throwError "negative control: the axiom is absent from controlBody's proof"
  let some (.opaqueInfo op) := env.find? `MinimallyUnboundedDeps.controlOpaque
    | throwError "negative control: controlOpaque is missing or not opaque"
  if op.type.getUsedConstants.contains ax then
    throwError "negative control: controlOpaque's type mentions the axiom"
  unless op.value.getUsedConstants.contains ax do
    throwError "negative control: the axiom is absent from controlOpaque's body"
  let some (.thmInfo ty) := env.find? `MinimallyUnboundedDeps.controlType
    | throwError "negative control: controlType is missing or not a theorem"
  unless ty.type.getUsedConstants.contains ax do
    throwError "negative control: the axiom is absent from controlType's type"
  for ctl in [`MinimallyUnboundedDeps.controlBody, `MinimallyUnboundedDeps.controlOpaque,
      `MinimallyUnboundedDeps.controlType] do
    let (_, bad) ← audit ctl
    unless bad == [ax] do
      throwError "negative control FAILED: the audit of {ctl} reports {bad}, not [{ax}]"
  -- KARP CONTROL: proof-only, flagged by the Karp, stabilization and Scott-module checks
  let inst := `FirstOrder.Language.isIsolatingRank_codeStabilizationOrdinal
  let some (.thmInfo kc) := env.find? `MinimallyUnboundedDeps.controlKarp
    | throwError "negative control: controlKarp is missing or not a theorem"
  if kc.type.getUsedConstants.contains inst then
    throwError "negative control: controlKarp is no longer proof-only"
  unless kc.value.getUsedConstants.contains inst do
    throwError "negative control: {inst} is absent from controlKarp's proof"
  let (kcCone, kcBad) ← audit `MinimallyUnboundedDeps.controlKarp
  unless kcBad.isEmpty do throwError "negative control: controlKarp uses {kcBad}"
  let (kk, ks, km) := karpViolations env kcCone
  unless !kk.isEmpty && ks.contains inst && !km.isEmpty &&
      (violations env kcCone).2.any (fun (_, m) ↦ (`InfinitaryLogic.Karp).isPrefixOf m) do
    throwError "negative control FAILED: the Karp checks do not flag {inst}"
  -- FORBIDDEN-DEPENDENCY CONTROL: proof-only, flagged by the Silver-name and module checks
  let witness := `silver_countable_or_cantorAntichain
  let some (.thmInfo fc) := env.find? `MinimallyUnboundedDeps.controlSilver
    | throwError "negative control: controlSilver is missing or not a theorem"
  if fc.type.getUsedConstants.contains witness then
    throwError "negative control: controlSilver is no longer proof-only"
  unless fc.value.getUsedConstants.contains witness do
    throwError "negative control: {witness} is absent from controlSilver's proof"
  let (fcCone, _) ← audit `MinimallyUnboundedDeps.controlSilver
  let (fnames, fmods) := violations env fcCone
  unless fnames.contains witness && fmods.any (fun (n, _) ↦ n == witness) &&
      !(prefixHits env fcCone `InfinitaryLogic.Conditional).isEmpty do
    throwError "negative control FAILED: the forbidden checks do not flag {witness}"
  -- the forbidden, Silver and stabilization declarations exist, and so do the modules
  for n in forbiddenNames ++ silverNames ++ stabilizationNames ++ contractAPI do
    unless (env.find? n).isSome do
      throwError "[MISSING FORBIDDEN] {n} is not in the full library; update the guard"
  let forbiddenMods := env.header.moduleNames.toList.filter forbiddenModule
  if forbiddenMods.isEmpty then
    throwError "[VACUOUS] no forbidden InfinitaryLogic module is in the environment"
  for m in scottForbiddenModules ++ ilm [`Karp.PotentialIso, `Descriptive.ScatteredCounting,
      `OrdinalCountability] do
    unless (env.getModuleIdx? m).isSome do throwError "[VACUOUS] module {m} not found"
  -- the roots are exactly the public declarations of the module
  let some midx := env.getModuleIdx? targetModule | throwError "module {targetModule} not found"
  let pub := (env.header.moduleData[midx.toNat]!).constNames.toList.filter fun n ↦
    !n.isInternalDetail && !(n.getString!.endsWith "congr_simp") && !isPrivateName n
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
    let some (_, reqs) := required.find? (·.1 == root)
      | throwError "no required dependencies recorded for {root}"
    for w in reqs do
      unless (env.find? w).isSome do throwError "[UNKNOWN REQUIRED] {w}"
      unless c.contains w do throwError "[REQUIRED] the cone of {root} does not contain {w}"
    let (names, mods) := violations env c
    unless names.isEmpty do throwError "[FORBIDDEN] the cone of {root} contains {names}"
    unless mods.isEmpty do
      throwError "[FORBIDDEN MODULE] the cone of {root} contains {mods.take 10}"
    let cond := prefixHits env c `InfinitaryLogic.Conditional
    unless cond.isEmpty do
      throwError "[CONDITIONAL] the cone of {root} contains {cond.take 10}"
    -- Karp-free, with no stabilization ordinal and none of the Scott-sentence modules
    let (kk, ks, km) := karpViolations env c
    unless kk.isEmpty do throwError "[KARP DRIFT] the cone of {root} reaches {kk.take 10}"
    unless ks.isEmpty do throwError "[STABILIZATION DRIFT] the cone of {root} contains {ks}"
    unless km.isEmpty do throwError "[KARP DRIFT] the cone of {root} reaches {km.take 10}"
    -- only the abstract contract, and exactly in the rank-independence cones
    let sc := moduleHits env c [`InfinitaryLogic.Descriptive.ScatteredCounting]
    let foreignSC := sc.filter fun n ↦ !contractAPI.contains n &&
      !(n.isInternalDetail && (contractAPI.erase `FirstOrder.Language.IsIsolatingRank).any
        (·.isPrefixOf n))
    unless foreignSC.isEmpty do
      throwError "[CONTRACT DRIFT] the cone of {root} contains {foreignSC}"
    let oc := moduleHits env c [`InfinitaryLogic.OrdinalCountability]
    if rankRoots.contains root then
      unless c.contains counting && !oc.isEmpty do
        throwError "[CONTRACT DRIFT] the cone of {root} misses the counting statement"
    else
      unless sc.isEmpty && oc.isEmpty do
        throwError "[CONTRACT DRIFT] the cone of {root} reaches the contract or \
          OrdinalCountability: {sc ++ oc}"
  -- TRANSITIVE POSITIVE CONTROLS: reached only through intermediate declarations
  let checkTransitive (root w : Name) : Elab.Command.CommandElabM Unit := do
    let some ci := env.find? root | throwError "[UNKNOWN ROOT] {root}"
    if (direct ci).contains w then
      throwError "transitive control: {w} occurs directly in {root}; pick another witness"
    let some (_, c) := cones.find? (·.1 == root) | throwError "no cone for {root}"
    unless c.contains w do
      throwError "transitive control FAILED: {w} is not reached from {root}"
  checkTransitive `FirstOrder.Language.boundedRankOn_iff_of_isIsolatingRank
    `FirstOrder.Language.IsIsolatingRank.countable_fibers
  checkTransitive `FirstOrder.Language.MinimallyUnboundedOn.exists_bfClass_compl_bounded
    `FirstOrder.Language.scottFormula
  -- the exclusion checks are not vacuous: they flag the instance
  let instCone ← match cone env inst with
    | .ok c => pure c
    | .error e => throwError e
  let (ik, is, im) := karpViolations env instCone
  unless !ik.isEmpty && !is.isEmpty && !im.isEmpty do
    throwError "[VACUOUS] the Karp and stabilization checks do not flag {inst}"
  logInfo m!"minimally unbounded dependency guard: OK (cones {sizes.toList}; roots exactly the \
    {pub.length} public declarations of the module; no Karp constant, no stabilization ordinal \
    ({stabilizationNames.length} names) and no Scott.Sentence, RefinementCount or \
    IsolatingLevel constant in any cone, although Karp.PotentialIso is in the import closure; \
    ScatteredCounting constants only from the {contractAPI.length}-name contract API and only \
    in the four rank-independence cones, each containing \
    IsIsolatingRank.countable_isoClasses_iff_bounded; OrdinalCountability exactly there; \
    required dependencies per root; no Conditional constant and none of \
    {silverNames.length} Silver declarations; {forbiddenNames.length} forbidden declarations \
    and {forbiddenMods.length} forbidden modules present and avoided; transitive controls; \
    the exclusion checks flag the instance; standard axioms from the cones, agreeing with \
    collectAxioms; the custom-axiom, Karp and Silver controls are flagged)"
