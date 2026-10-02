/-
Proof-dependency guard for the rank adapters: infinitary orbit formulas
(`InfinitaryLogic/Scott/OrbitFormulaThreshold.lean`) and whole-model recognition from an absolute
Scott sentence (`InfinitaryLogic/Scott/SentenceRecognition.lean`).

The regression guard `check_rank_adapters_regressions.lean` applies every theorem and checks the
**import** closure of `Scott.SentenceRecognition`.  This guard checks the same boundary at the
level of **proof terms**, against the full library, so that it cannot pass vacuously; import
names are not taken as evidence of proof independence, nor the converse.

* **Fail-closed cone walk.**  For each root, the transitive constant cone follows types, values
  (theorem, definition and opaque bodies), constructors, recursor rules and inductive families.
  An unknown root, a root that is not a theorem, or a constant reached in the walk that is not in
  the environment stops the guard (`[UNKNOWN ROOT]`, `[NOT A THEOREM]`, `[UNKNOWN CONSTANT]`).
* **Required dependencies.**  The part-A cones contain the forward Karp lemma
  `BFEquiv_implies_agreeQR` and `BFEquiv.toOrdinalLift`, and, as each root needs,
  `orbitRank_le_of_mem`, `mem_orbitStable_of_orbit_determined` and
  `internalScottRank_le_of_orbits_determined`.  The part-B cones contain
  `BFEquiv_implies_agreeQR`, `qrank_openBounds`, `realize_openBounds` and
  `equiv_implies_BFEquiv`; the least-ordinal bound goes through `recognition_of_sentence_rank`
  and `csInf_le'`.  The first-order adapters `orbit_determined_of_orbitFormula`,
  `orbitRank_le_lift_qrank_of_orbitFormula` and `internalScottRank_le_omega0_of_orbitFormulas`
  go through the infinitary ones.
* **Part B avoids orbit ranks and heights.**  No constant in a part-B cone is declared in
  `Scott/OrbitRank`, `Scott/OrbitRankStabilization`, `Scott/OrbitFormulaThreshold`,
  `Scott/Height*` or `Scott/Rank`.  The forbidden modules are asserted to be in the environment,
  and the *same* module check is asserted to flag every part-A and first-order cone, through
  `Scott/OrbitRank` itself wherever the orbit-rank API is required, so it cannot pass
  vacuously.
* **Standard axioms**, read off the cone itself (every `axiom` reached through a type or a body,
  opaque bodies included) and cross-checked against `collectAxioms`: only `propext`,
  `Classical.choice` and `Quot.sound`.
* **Nonstandard-axiom negative controls.**  The guard declares a custom `axiom` and three
  declarations using it: in a theorem body, in an `opaque` body, and in a theorem type.  The same
  audit must flag each of them, and `collectAxioms` must agree; otherwise the guard fails.

Run *after* `lake build`, so the oleans it resolves against are current:
lake env lean scripts/check_rank_adapters_deps.lean
-/
import InfinitaryLogic

open Lean

namespace RankAdaptersDeps

/-- Prefix a list of names with `FirstOrder.Language`. -/
def fol (l : List Name) : List Name := l.map (`FirstOrder.Language ++ ·)

/-- The part-A roots: infinitary orbit formulas. -/
def partARoots : List Name :=
  fol [`orbit_determined_of_infinitaryOrbitFormula,
    `orbitRank_le_lift_qrank_of_infinitaryOrbitFormula,
    `internalScottRank_le_of_infinitaryOrbitFormulas]

/-- The part-B roots: recognition from an absolute Scott sentence. -/
def partBRoots : List Name :=
  fol [`recognition_of_sentence_rank, `stabilizationOrdinal_le_of_sentence_rank,
    `stabilizationOrdinal_le_qrank_of_sentence]

/-- The first-order adapters, now corollaries of part A. -/
def firstOrderRoots : List Name :=
  fol [`orbit_determined_of_orbitFormula, `orbitRank_le_lift_qrank_of_orbitFormula,
    `internalScottRank_le_omega0_of_orbitFormulas]

/-- The forward Karp lemma. -/
def karp : Name := `FirstOrder.Language.BFEquiv_implies_agreeQR

/-- The dependencies each root's cone must contain. -/
def required : List (Name × List Name) :=
  [(`FirstOrder.Language.orbit_determined_of_infinitaryOrbitFormula,
      [karp] ++ fol [`BFEquiv.toOrdinalLift]),
   (`FirstOrder.Language.orbitRank_le_lift_qrank_of_infinitaryOrbitFormula,
      [karp] ++ fol [`BFEquiv.toOrdinalLift, `orbitRank_le_of_mem,
        `mem_orbitStable_of_orbit_determined, `orbit_determined_of_infinitaryOrbitFormula]),
   (`FirstOrder.Language.internalScottRank_le_of_infinitaryOrbitFormulas,
      [karp] ++ fol [`BFEquiv.toOrdinalLift, `internalScottRank_le_of_orbits_determined,
        `orbit_determined_of_infinitaryOrbitFormula]),
   (`FirstOrder.Language.recognition_of_sentence_rank,
      [karp] ++ fol [`qrank_openBounds, `realize_openBounds, `equiv_implies_BFEquiv]),
   (`FirstOrder.Language.stabilizationOrdinal_le_of_sentence_rank,
      [karp, `csInf_le'] ++ fol [`qrank_openBounds, `realize_openBounds,
        `recognition_of_sentence_rank]),
   (`FirstOrder.Language.stabilizationOrdinal_le_qrank_of_sentence,
      [karp] ++ fol [`qrank_openBounds, `realize_openBounds,
        `stabilizationOrdinal_le_of_sentence_rank]),
   (`FirstOrder.Language.orbit_determined_of_orbitFormula,
      [karp] ++ fol [`orbit_determined_of_infinitaryOrbitFormula]),
   (`FirstOrder.Language.orbitRank_le_lift_qrank_of_orbitFormula,
      [karp] ++ fol [`orbitRank_le_lift_qrank_of_infinitaryOrbitFormula]),
   (`FirstOrder.Language.internalScottRank_le_omega0_of_orbitFormulas,
      [karp] ++ fol [`orbit_determined_of_infinitaryOrbitFormula,
        `internalScottRank_le_of_orbits_determined])]

/-- Modules no constant of a part-B cone may be declared in (by name prefix). -/
def forbiddenPrefixes : List Name :=
  [`InfinitaryLogic.Scott.OrbitRank, `InfinitaryLogic.Scott.OrbitRankStabilization,
   `InfinitaryLogic.Scott.OrbitFormulaThreshold, `InfinitaryLogic.Scott.Height,
   `InfinitaryLogic.Scott.Rank]

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

/-- The constants of a cone declared in a forbidden module, with their module. -/
def forbiddenHits (env : Environment) (c : NameSet) : List (Name × Name) :=
  c.toList.filterMap fun n ↦ do
    let idx ← env.getModuleIdxFor? n
    let m := env.header.moduleNames[idx.toNat]!
    if forbiddenPrefixes.any (·.isPrefixOf m) then some (n, m) else none

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

end RankAdaptersDeps

/-- **Negative control 1**: a clean statement whose *proof* uses the custom axiom. -/
theorem RankAdaptersDeps.controlBody : (2 : ℕ) + 2 = 4 := RankAdaptersDeps.nonstandardAxiom

/-- **Negative control 2**: an `opaque` constant whose *body* uses the custom axiom. -/
noncomputable opaque RankAdaptersDeps.controlOpaque : ℕ :=
  (fun _ : (2 : ℕ) + 2 = 4 ↦ 0) RankAdaptersDeps.nonstandardAxiom

/-- **Negative control 3**: the custom axiom in a *type*. -/
theorem RankAdaptersDeps.controlType :
    RankAdaptersDeps.nonstandardAxiom = RankAdaptersDeps.nonstandardAxiom := rfl

open RankAdaptersDeps

run_cmd do
  let env ← getEnv
  let ax := `RankAdaptersDeps.nonstandardAxiom
  -- NEGATIVE CONTROLS: the custom axiom sits where intended, and the audit flags it
  let some (.thmInfo body) := env.find? `RankAdaptersDeps.controlBody
    | throwError "negative control: controlBody is missing or not a theorem"
  if body.type.getUsedConstants.contains ax then
    throwError "negative control: controlBody is no longer proof-only"
  unless body.value.getUsedConstants.contains ax do
    throwError "negative control: the axiom is absent from controlBody's proof"
  let some (.opaqueInfo op) := env.find? `RankAdaptersDeps.controlOpaque
    | throwError "negative control: controlOpaque is missing or not opaque"
  if op.type.getUsedConstants.contains ax then
    throwError "negative control: controlOpaque's type mentions the axiom"
  unless op.value.getUsedConstants.contains ax do
    throwError "negative control: the axiom is absent from controlOpaque's body"
  let some (.thmInfo ty) := env.find? `RankAdaptersDeps.controlType
    | throwError "negative control: controlType is missing or not a theorem"
  unless ty.type.getUsedConstants.contains ax do
    throwError "negative control: the axiom is absent from controlType's type"
  for ctl in [`RankAdaptersDeps.controlBody, `RankAdaptersDeps.controlOpaque,
      `RankAdaptersDeps.controlType] do
    let (_, bad) ← audit ctl
    unless bad == [ax] do
      throwError "negative control FAILED: the audit of {ctl} reports {bad}, not [{ax}]"
  -- the forbidden modules exist, so the module check is not vacuous
  for m in forbiddenPrefixes do
    unless (env.getModuleIdx? m).isSome do
      throwError "[VACUOUS] forbidden module {m} is not in the full library"
  -- the roots
  let mut sizes : Array (Name × Nat) := #[]
  for root in partARoots ++ partBRoots ++ firstOrderRoots do
    let some ci := env.find? root | throwError "[UNKNOWN ROOT] {root}"
    unless ci matches .thmInfo _ do throwError "[NOT A THEOREM] {root}"
    let (c, bad) ← audit root
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {root} uses {bad}"
    sizes := sizes.push (root.componentsRev.head!, c.size)
    let some (_, reqs) := required.find? (·.1 == root)
      | throwError "no required dependencies recorded for {root}"
    for w in reqs do
      unless (env.find? w).isSome do throwError "[UNKNOWN REQUIRED] {w}"
      unless c.contains w do throwError "[REQUIRED] the cone of {root} does not contain {w}"
    let hits := forbiddenHits env c
    if partBRoots.contains root then
      unless hits.isEmpty do
        throwError "[FORBIDDEN] the cone of {root} reaches {hits.take 10}"
    else
      -- positive control of the module check: every part-A cone is flagged (it contains its
      -- own root, from `Scott/OrbitFormulaThreshold`), and the orbit-rank cones are flagged
      -- through `Scott/OrbitRank` itself
      if hits.isEmpty then
        throwError "[VACUOUS] the module check does not flag the cone of {root}"
      if reqs.contains `FirstOrder.Language.orbitRank_le_of_mem ||
          reqs.contains `FirstOrder.Language.internalScottRank_le_of_orbits_determined then
        unless hits.any (fun (_, m) ↦ m == `InfinitaryLogic.Scott.OrbitRank) do
          throwError "[VACUOUS] the module check does not flag Scott.OrbitRank in {root}"
  logInfo m!"rank adapters dependency guard: OK (cones {sizes.toList}; part A through the \
    forward Karp lemma and the orbit-rank API; part B through the forward Karp lemma and \
    openBounds, with no constant from the orbit-rank, threshold, height or rank modules; the \
    first-order adapters through the infinitary ones; standard axioms from the cones, agreeing \
    with collectAxioms; the custom-axiom controls in a proof, an opaque body and a type are \
    flagged)"
