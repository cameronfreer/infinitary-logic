/-
Proof-dependency guard for eliminating orbit parameters
(`InfinitaryLogic/Scott/OrbitParameters.lean`).

The module imports `Scott/QuantifierRank`, whose import closure contains `Karp/CarrierTheorem`,
so its import closure alone says nothing about which route the semantic theorems take.  This
guard checks the route on the **proof terms**, against the full library, so that it cannot pass
vacuously; import names are not taken as evidence of proof independence, nor the converse.

* **Fail-closed cone walk.**  For each root, the transitive constant cone follows types, values
  (theorem, definition and opaque bodies), constructors, recursor rules and inductive families.
  An unknown root, a root that is not a theorem, or a constant reached in the walk that is not in
  the environment stops the guard (`[UNKNOWN ROOT]`, `[NOT A THEOREM]`, `[UNKNOWN CONSTANT]`).
* **Satisfaction invariance is the route.**  The cones of
  `realize_existsOrbitParams_iff_orbit`, `realize_existsOrbitParams_iff_orbit'` and
  `realize_existsOrbitParams_iff_orbit_of_isOrbitFormulaFamilyPointed` contain
  `BoundedFormulaω.realize_equiv`, its formula-level form `Formulaω.realize_comp_equiv`, and the
  realization lemma `realize_existsOrbitParams`.
* **No Karp, no rank.**  No constant in those cones is declared in a module under
  `InfinitaryLogic.Karp`, and no constant in them has a name with a component containing
  `qrank`.  Both checks have positive controls: the Karp modules are asserted to be in the
  environment, and the module check must flag the cone of the forward Karp lemma
  `BFEquiv_implies_agreeQR`; the name check must flag the cone of `qrank_existsOrbitParams`.
  A third control, `controlTransitive`, is declared in this file and reaches Karp only
  **transitively**: it refers to `BFEquiv_implies_agree_formulas_omega`
  (`Scott/QuantifierRank`), none of its direct references is declared in a Karp module, and the
  module check must still flag its cone, so the check tests the walk and not only the module
  of the root or of its direct references.
* **Standard axioms**, read off the cone itself (every `axiom` reached through a type or a body,
  opaque bodies included) and cross-checked against `collectAxioms`: only `propext`,
  `Classical.choice` and `Quot.sound`.
* **Nonstandard-axiom negative controls.**  The guard declares a custom `axiom` and three
  declarations using it: in a theorem body, in an `opaque` body, and in a theorem type.  The same
  audit must flag each of them, and `collectAxioms` must agree; otherwise the guard fails.

Run *after* `lake build`, so the oleans it resolves against are current:
lake env lean scripts/check_orbit_parameters_deps.lean
-/
import InfinitaryLogic

open Lean

namespace OrbitParametersDeps

/-- Prefix a list of names with `FirstOrder.Language`. -/
def fol (l : List Name) : List Name := l.map (`FirstOrder.Language ++ ·)

/-- The semantic roots. -/
def roots : List Name :=
  fol [`realize_existsOrbitParams_iff_orbit, `realize_existsOrbitParams_iff_orbit',
    `realize_existsOrbitParams_iff_orbit_of_isOrbitFormulaFamilyPointed]

/-- The dependencies every root's cone must contain. -/
def required : List Name :=
  fol [`BoundedFormulaω.realize_equiv, `Formulaω.realize_comp_equiv, `realize_existsOrbitParams]

/-- The module prefix no constant of a root's cone may be declared under. -/
def karpPrefix : Name := `InfinitaryLogic.Karp

/-- The Karp modules, asserted to be in the environment. -/
def karpModules : List Name :=
  [`InfinitaryLogic.Karp.PotentialIso, `InfinitaryLogic.Karp.CarrierTheorem,
   `InfinitaryLogic.Karp.CountableCorollary]

/-- The positive control of the module check: the forward Karp lemma. -/
def karpControl : Name := `FirstOrder.Language.BFEquiv_implies_agreeQR

/-- The positive control of the name check: the rank identity of the same syntax. -/
def qrankControl : Name := `FirstOrder.Language.qrank_existsOrbitParams

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

/-- The constants of a cone declared in a `Karp` module, with their module. -/
def karpHits (env : Environment) (c : NameSet) : List (Name × Name) :=
  c.toList.filterMap fun n ↦ do
    let idx ← env.getModuleIdxFor? n
    let m := env.header.moduleNames[idx.toNat]!
    if karpPrefix.isPrefixOf m then some (n, m) else none

/-- Whether a name has a string component containing `qrank`. -/
def mentionsQrank (n : Name) : Bool :=
  n.components.any fun c ↦ match c with
    | .str _ s => (s.splitOn "qrank").length > 1
    | _ => false

/-- The constants of a cone with `qrank` in their name. -/
def qrankHits (c : NameSet) : List Name := c.toList.filter mentionsQrank

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

end OrbitParametersDeps

/-- **Negative control 1**: a clean statement whose *proof* uses the custom axiom. -/
theorem OrbitParametersDeps.controlBody : (2 : ℕ) + 2 = 4 := OrbitParametersDeps.nonstandardAxiom

/-- **Negative control 2**: an `opaque` constant whose *body* uses the custom axiom. -/
noncomputable opaque OrbitParametersDeps.controlOpaque : ℕ :=
  (fun _ : (2 : ℕ) + 2 = 4 ↦ 0) OrbitParametersDeps.nonstandardAxiom

/-- **Negative control 3**: the custom axiom in a *type*. -/
theorem OrbitParametersDeps.controlType :
    OrbitParametersDeps.nonstandardAxiom = OrbitParametersDeps.nonstandardAxiom := rfl

/-- **Transitive positive control**: declared outside the Karp modules, referring to a
`Scott/QuantifierRank` theorem whose proof uses the forward Karp lemma. -/
theorem OrbitParametersDeps.controlTransitive : True :=
  (fun _ ↦ trivial) @FirstOrder.Language.BFEquiv_implies_agree_formulas_omega.{0, 0, 0}

open OrbitParametersDeps

run_cmd do
  let env ← getEnv
  let ax := `OrbitParametersDeps.nonstandardAxiom
  -- NEGATIVE CONTROLS: the custom axiom sits where intended, and the audit flags it
  let some (.thmInfo body) := env.find? `OrbitParametersDeps.controlBody
    | throwError "negative control: controlBody is missing or not a theorem"
  if body.type.getUsedConstants.contains ax then
    throwError "negative control: controlBody is no longer proof-only"
  unless body.value.getUsedConstants.contains ax do
    throwError "negative control: the axiom is absent from controlBody's proof"
  let some (.opaqueInfo op) := env.find? `OrbitParametersDeps.controlOpaque
    | throwError "negative control: controlOpaque is missing or not opaque"
  if op.type.getUsedConstants.contains ax then
    throwError "negative control: controlOpaque's type mentions the axiom"
  unless op.value.getUsedConstants.contains ax do
    throwError "negative control: the axiom is absent from controlOpaque's body"
  let some (.thmInfo ty) := env.find? `OrbitParametersDeps.controlType
    | throwError "negative control: controlType is missing or not a theorem"
  unless ty.type.getUsedConstants.contains ax do
    throwError "negative control: the axiom is absent from controlType's type"
  for ctl in [`OrbitParametersDeps.controlBody, `OrbitParametersDeps.controlOpaque,
      `OrbitParametersDeps.controlType] do
    let (_, bad) ← audit ctl
    unless bad == [ax] do
      throwError "negative control FAILED: the audit of {ctl} reports {bad}, not [{ax}]"
  -- POSITIVE CONTROLS: the Karp modules exist, and both checks flag a cone that should be flagged
  for m in karpModules do
    unless (env.getModuleIdx? m).isSome do
      throwError "[VACUOUS] Karp module {m} is not in the full library"
  let (cK, _) ← audit karpControl
  if (karpHits env cK).isEmpty then
    throwError "[VACUOUS] the module check does not flag the cone of {karpControl}"
  let tc := `OrbitParametersDeps.controlTransitive
  let some tci := env.find? tc | throwError "positive control: {tc} is missing"
  let direct := (refs tci).toList
  unless direct.contains `FirstOrder.Language.BFEquiv_implies_agree_formulas_omega do
    throwError "positive control: {tc} no longer refers to BFEquiv_implies_agree_formulas_omega"
  let directKarp := karpHits env (.ofList direct)
  unless directKarp.isEmpty do
    throwError "positive control: {tc} refers to a Karp constant directly: {directKarp}"
  let (cT, _) ← audit tc
  unless cT.contains karpControl do
    throwError "[VACUOUS] the cone of {tc} does not reach {karpControl}"
  if (karpHits env cT).isEmpty then
    throwError "[VACUOUS] the module check does not flag the transitive cone of {tc}"
  let (cQ, _) ← audit qrankControl
  if (qrankHits cQ).isEmpty then
    throwError "[VACUOUS] the name check does not flag the cone of {qrankControl}"
  -- the roots
  let mut sizes : Array (Name × Nat) := #[]
  for root in roots do
    let some ci := env.find? root | throwError "[UNKNOWN ROOT] {root}"
    unless ci matches .thmInfo _ do throwError "[NOT A THEOREM] {root}"
    let (c, bad) ← audit root
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {root} uses {bad}"
    sizes := sizes.push (root.componentsRev.head!, c.size)
    for w in required do
      unless (env.find? w).isSome do throwError "[UNKNOWN REQUIRED] {w}"
      unless c.contains w do throwError "[REQUIRED] the cone of {root} does not contain {w}"
    let kh := karpHits env c
    unless kh.isEmpty do
      throwError "[KARP] the cone of {root} reaches {kh.take 10}"
    let qh := qrankHits c
    unless qh.isEmpty do
      throwError "[QRANK] the cone of {root} reaches {qh.take 10}"
  logInfo m!"orbit-parameters dependency guard: OK (cones {sizes.toList}; each through \
    BoundedFormulaω.realize_equiv, Formulaω.realize_comp_equiv and realize_existsOrbitParams, \
    with no constant from a Karp module and no qrank declaration; both checks flag their \
    positive controls, the Karp check also through a guard-local control reaching Karp only \
    transitively; standard axioms \
    from the cones, agreeing with collectAxioms; the custom-axiom controls in a proof, an opaque \
    body and a type are flagged)"
