/-
Proof-dependency guard for the `+ ω` bounds of `InfinitaryLogic/Scott/RankConventions.lean`.

The regression guard `check_rank_conventions_regressions.lean` applies every theorem, derives the
Scott-height bound a second time through the pointed sentence, and checks the **import** closure
of `Scott.RankConventions`.  This guard checks, at the level of **proof terms** and against the
full library, which route the library bounds take.

* **Fail-closed cone walk.**  For each root, the transitive constant cone follows types, values
  (theorem, definition and opaque bodies), constructors, recursor rules and inductive families.
  An unknown root, a root that is not a theorem, or a constant reached in the walk that is not in
  the environment stops the guard (`[UNKNOWN ROOT]`, `[NOT A THEOREM]`, `[UNKNOWN CONSTANT]`).
* **Recognition through the sentence-rank adapter.**  The cones of
  `lift_stabilizationOrdinal_le_iSup_orbitRank_add_omega0` and
  `lift_stabilizationOrdinal_le_internalScottRank_add_omega0` contain
  `stabilizationOrdinal_le_of_formula_rank` (`Scott/SentenceRecognition.lean`),
  `montalbanSentence_characterizes`, `qrank_montalbanSentence_le`,
  `isOrbitFormulaFamily_scottFormula`, `orbitRank_le_lift_scottHeight` and
  `countableRefinementHypothesis`.
* **The Scott-height bounds go through the identity.**  The cones of
  `lift_scottHeight_le_iSup_orbitRank_add_omega0` and
  `lift_scottHeight_le_internalScottRank_add_omega0` contain `lift_scottHeight_eq_max`,
  `scottHeight_le_max_of_orbitRank_le` and the stabilization bound, and do **not** contain
  `montalbanSentencePointed_characterizes` or `isOrbitFormulaFamilyPointed_scottFormula`.  The
  pointed recognition link `scottHeight_le_of_pointed_characterizes_of_qrank_le` and the pointed
  derivation are declared only in the regression guard: no library constant of either name
  exists, under `FirstOrder.Language` or at the root.
* **The absence check is not vacuous.**  The forbidden pointed constants exist; the same check
  flags the library theorem `exists_isPiIn_pointed_of_sigmaIn_orbits`, whose proof uses
  `montalbanSentencePointed_characterizes` directly; and it flags the **transitive** positive
  control `controlTransitive`, declared here, which refers to that theorem but to no forbidden
  constant directly.
* **Standard axioms**, read off the cone itself (every `axiom` reached through a type or a body,
  opaque bodies included) and cross-checked against `collectAxioms`, for every public
  declaration of the module and the two promoted comparisons: only `propext`,
  `Classical.choice` and `Quot.sound`.
* **Nonstandard-axiom negative controls.**  The guard declares a custom `axiom` and three
  declarations using it: in a theorem body, in an `opaque` body, and in a theorem type.  The same
  audit must flag each of them, and `collectAxioms` must agree; otherwise the guard fails.

Run *after* `lake build`, so the oleans it resolves against are current:
lake env lean scripts/check_rank_conventions_deps.lean
-/
import InfinitaryLogic

open Lean

namespace RankConventionsDeps

/-- Prefix a list of names with `FirstOrder.Language`. -/
def fol (l : List Name) : List Name := l.map (`FirstOrder.Language ++ ·)

/-- Every public declaration of `Scott.RankConventions`, with the two comparisons promoted
into `Scott.OrbitRankStabilization`. -/
def roots : List Name :=
  fol [`iSup_orbitRank_le_internalScottRank, `internalScottRank_le_iSup_orbitRank_add_one,
    `internalScottRank_add_omega0_eq, `orbitRank_le_lift_scottHeight,
    `exists_lift_eq_iSup_orbitRank, `isOrbitFormulaFamily_scottFormula,
    `isOrbitFormulaFamilyPointed_scottFormula, `stabilizationOrdinal_le_scottHeight,
    `scottHeight_le_max_of_orbitRank_le, `lift_scottHeight_eq_max,
    `internalScottRank_le_lift_scottHeight_add_one, `sr_le_scottHeight,
    `scottRank_le_scottHeight_add_one, `lift_stabilizationOrdinal_le_iSup_orbitRank_add_omega0,
    `lift_stabilizationOrdinal_le_internalScottRank_add_omega0,
    `lift_scottHeight_le_iSup_orbitRank_add_omega0,
    `lift_scottHeight_le_internalScottRank_add_omega0]

/-- The recognition step every `+ ω` bound goes through. -/
def recognition : List Name :=
  fol [`stabilizationOrdinal_le_of_formula_rank, `montalbanSentence_characterizes,
    `qrank_montalbanSentence_le, `isOrbitFormulaFamily_scottFormula,
    `orbitRank_le_lift_scottHeight, `countableRefinementHypothesis]

/-- The dependencies each audited bound's cone must contain. -/
def required : List (Name × List Name) :=
  [(`FirstOrder.Language.lift_stabilizationOrdinal_le_iSup_orbitRank_add_omega0, recognition),
   (`FirstOrder.Language.lift_stabilizationOrdinal_le_internalScottRank_add_omega0,
      recognition ++ fol [`internalScottRank_add_omega0_eq]),
   (`FirstOrder.Language.lift_scottHeight_le_iSup_orbitRank_add_omega0,
      recognition ++ fol [`lift_scottHeight_eq_max, `scottHeight_le_max_of_orbitRank_le,
        `lift_stabilizationOrdinal_le_iSup_orbitRank_add_omega0]),
   (`FirstOrder.Language.lift_scottHeight_le_internalScottRank_add_omega0,
      recognition ++ fol [`lift_scottHeight_eq_max, `scottHeight_le_max_of_orbitRank_le,
        `internalScottRank_add_omega0_eq])]

/-- The library Scott-height bounds, which must avoid the pointed route. -/
def heightRoots : List Name :=
  fol [`lift_scottHeight_le_iSup_orbitRank_add_omega0,
    `lift_scottHeight_le_internalScottRank_add_omega0]

/-- The pointed constants the library Scott-height bounds must not reach. -/
def forbidden : List Name :=
  fol [`montalbanSentencePointed_characterizes, `isOrbitFormulaFamilyPointed_scottFormula]

/-- The guard-local pointed declarations, which must not exist in the library. -/
def guardOnly : List Name :=
  [`scottHeight_le_of_pointed_characterizes_of_qrank_le,
    `lift_scottHeight_le_iSup_orbitRank_add_omega0_pointed]

/-- The positive control of the absence check: a library theorem whose proof uses
`montalbanSentencePointed_characterizes`. -/
def pointedControl : Name := `FirstOrder.Language.exists_isPiIn_pointed_of_sigmaIn_orbits

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

/-- The forbidden pointed constants in a set of constants. -/
def pointedHits (c : NameSet) : List Name := forbidden.filter c.contains

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

/-- **The nonstandard axiom of the negative controls.** -/
axiom nonstandardAxiom : (2 : ℕ) + 2 = 4

end RankConventionsDeps

/-- **Negative control 1**: a clean statement whose *proof* uses the custom axiom. -/
theorem RankConventionsDeps.controlBody : (2 : ℕ) + 2 = 4 := RankConventionsDeps.nonstandardAxiom

/-- **Negative control 2**: an `opaque` constant whose *body* uses the custom axiom. -/
noncomputable opaque RankConventionsDeps.controlOpaque : ℕ :=
  (fun _ : (2 : ℕ) + 2 = 4 ↦ 0) RankConventionsDeps.nonstandardAxiom

/-- **Negative control 3**: the custom axiom in a *type*. -/
theorem RankConventionsDeps.controlType :
    RankConventionsDeps.nonstandardAxiom = RankConventionsDeps.nonstandardAxiom := rfl

/-- **Transitive positive control**: declared here, referring to a library theorem whose proof
uses `montalbanSentencePointed_characterizes`, but to no pointed constant directly. -/
theorem RankConventionsDeps.controlTransitive : True :=
  (fun _ ↦ trivial) @FirstOrder.Language.exists_isPiIn_pointed_of_sigmaIn_orbits.{0, 0, 0}

open RankConventionsDeps

run_cmd do
  let env ← getEnv
  let ax := `RankConventionsDeps.nonstandardAxiom
  -- NEGATIVE CONTROLS: the custom axiom sits where intended, and the audit flags it
  let some (.thmInfo body) := env.find? `RankConventionsDeps.controlBody
    | throwError "negative control: controlBody is missing or not a theorem"
  if body.type.getUsedConstants.contains ax then
    throwError "negative control: controlBody is no longer proof-only"
  unless body.value.getUsedConstants.contains ax do
    throwError "negative control: the axiom is absent from controlBody's proof"
  let some (.opaqueInfo op) := env.find? `RankConventionsDeps.controlOpaque
    | throwError "negative control: controlOpaque is missing or not opaque"
  if op.type.getUsedConstants.contains ax then
    throwError "negative control: controlOpaque's type mentions the axiom"
  unless op.value.getUsedConstants.contains ax do
    throwError "negative control: the axiom is absent from controlOpaque's body"
  let some (.thmInfo ty) := env.find? `RankConventionsDeps.controlType
    | throwError "negative control: controlType is missing or not a theorem"
  unless ty.type.getUsedConstants.contains ax do
    throwError "negative control: the axiom is absent from controlType's type"
  for ctl in [`RankConventionsDeps.controlBody, `RankConventionsDeps.controlOpaque,
      `RankConventionsDeps.controlType] do
    let (_, bad) ← audit ctl
    unless bad == [ax] do
      throwError "negative control FAILED: the audit of {ctl} reports {bad}, not [{ax}]"
  -- POSITIVE CONTROLS of the absence check: the forbidden constants exist, a library theorem
  -- using one of them directly is flagged, and so is a cone reaching it only transitively
  for f in forbidden do
    unless (env.find? f).isSome do throwError "[VACUOUS] forbidden constant {f} is missing"
  let (cP, _) ← audit pointedControl
  if (pointedHits cP).isEmpty then
    throwError "[VACUOUS] the absence check does not flag the cone of {pointedControl}"
  let tc := `RankConventionsDeps.controlTransitive
  let some tci := env.find? tc | throwError "positive control: {tc} is missing"
  let direct := refs tci
  unless direct.contains pointedControl do
    throwError "positive control: {tc} no longer refers to {pointedControl}"
  unless (pointedHits direct).isEmpty do
    throwError "positive control: {tc} refers to a pointed constant directly"
  let (cT, _) ← audit tc
  if (pointedHits cT).isEmpty then
    throwError "[VACUOUS] the absence check does not flag the transitive cone of {tc}"
  -- the pointed link and the pointed derivation are not library declarations
  for g in guardOnly do
    for n in [g, `FirstOrder.Language ++ g] do
      if (env.find? n).isSome then
        throwError "[GUARD-ONLY] {n} is declared in the library"
  -- the roots
  let mut sizes : Array (Name × Nat) := #[]
  for root in roots do
    let some ci := env.find? root | throwError "[UNKNOWN ROOT] {root}"
    unless ci matches .thmInfo _ do throwError "[NOT A THEOREM] {root}"
    let (c, bad) ← audit root
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {root} uses {bad}"
    if let some (_, reqs) := required.find? (·.1 == root) then
      sizes := sizes.push (root.componentsRev.head!, c.size)
      for w in reqs do
        unless (env.find? w).isSome do throwError "[UNKNOWN REQUIRED] {w}"
        unless c.contains w do throwError "[REQUIRED] the cone of {root} does not contain {w}"
    if heightRoots.contains root then
      let hits := pointedHits c
      unless hits.isEmpty do
        throwError "[POINTED] the cone of {root} reaches {hits}"
  unless required.all (fun (r, _) ↦ roots.contains r) && heightRoots.all roots.contains do
    throwError "an audited bound is not among the roots"
  logInfo m!"rank conventions dependency guard: OK (cones {sizes.toList}; the stabilization \
    bounds through stabilizationOrdinal_le_of_formula_rank, montalbanSentence_characterizes \
    and qrank_montalbanSentence_le; the Scott-height bounds through lift_scottHeight_eq_max, \
    with no montalbanSentencePointed_characterizes or isOrbitFormulaFamilyPointed_scottFormula \
    in their cones and the pointed link absent from the library; the absence check flags a \
    direct and a transitive positive control; standard axioms for all {roots.length} \
    declarations from the cones, agreeing with collectAxioms; the custom-axiom controls in a \
    proof, an opaque body and a type are flagged)"
