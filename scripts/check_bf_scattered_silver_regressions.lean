/-
Regression guard for the Silver half: a thin sentence has back-and-forth scattered models
(`InfinitaryLogic/Conditional/BFScatteredSilver.lean`).

All three public theorems are *applied*, not only listed for their axioms.

* **Generic applications.**  `Sentenceω.bfScattered_of_isThinOnNatModels`,
  `Sentenceω.bfScattered_iff_isThinOnNatModels` (both directions) and
  `Sentenceω.bfScattered_modelsOf_of_lt_continuum` for an arbitrary relational
  `Language.{u, v}` with countably many relation symbols.
* **Concrete.**  In the pure-set language (one code, universes `{1, 2}`) every sentence has at
  most one isomorphism class of coded models, fewer than continuum many, so
  `Sentenceω.bfScattered_modelsOf_of_lt_continuum` makes its models back-and-forth scattered,
  and the iff turns that into thinness.
* **Rank-free proof cones (checked), with the Scott modules present only in the import
  closure.**  A fail-closed walk of the proof cones of the three theorems (types, values,
  constructors, recursor rules; an unknown constant stops the guard) finds no constant whose
  name contains `stabilizationOrdinal`, `StabilizesAt`, `scottRank`, `scottHeight`,
  `IsIsolatingRank` or `codeStabilizationOrdinal`, and no constant declared in `Scott.Rank`,
  `Scott.Height*`, `Scott.RefinementCount`, `Scott.IsolatingLevel` or
  `Descriptive.ScatteredCounting` (`[RANK IN CONE]`).  Positive control: a theorem with a clean
  statement whose proof uses `stabilizationOrdinal_spec` is flagged by both the name and the
  module checks, so the check cannot pass vacuously.  Those Scott modules are nevertheless in the
  import closure, through `ModelTheory.MorleyCounting`.
* **One Silver step, quoted (checked positively).**  The per-level Silver step is
  `Sentenceω.countable_bfClasses_of_isThinOnNatModels` (`Conditional/MorleyPerfect.lean`): it is
  in the proof cone of each of the three theorems, and so are `silver_countable_or_cantorAntichain`
  and `silver_core_polish` (`[DEPENDENCY DRIFT]` otherwise).
* **Statement pins, and no second copy of the step.**  The three statements are restated as
  `pin_*` theorems proved by the originals.  What is compared: each original's type must equal
  its copy's as an expression up to binder names and normalization of universe levels, with the
  same universe parameters (`[STATEMENT DRIFT]` otherwise), and the binder kinds (explicit,
  implicit, instance-implicit, strict-implicit) along the `∀`-telescope must agree
  (`[BINDER DRIFT]` otherwise; expression equality alone ignores them).  Negative control
  (`[BINDER CONTROL]`): `binderControl_bfScattered_iff_isThinOnNatModels` restates
  `Sentenceω.bfScattered_iff_isThinOnNatModels` with `(Θ)` in place of `{Θ}`; expression
  equality accepts it, and the binder-kind comparison must reject it.  No declaration of the
  module, together with its auxiliary declarations in the module, mentions a form of Silver's
  theorem (`silver_countable_or_cantorAntichain`, `silver_countable_or_cantorAntichain_of_isClosed`
  or `silver_core_polish`) directly (`[DUPLICATED STEP]`): Silver enters only through the step.
  Positive control: the same check sees the step itself apply Silver.
* **Separate from the counting layer.**  The `InfinitaryLogic` import closure of
  `Conditional.BFScatteredSilver` is exactly the pinned list `allowedClosure` (58 modules,
  `[CLOSURE DRIFT]` otherwise; 57 before the per-level step moved to `Conditional.MorleyPerfect`,
  which is the one module added); it does **not** contain
  `Descriptive.ScatteredCounting` or `Scott.IsolatingLevel` (`[LAYERING]`).  The converse import
  boundary, that `Descriptive.ScatteredCounting` reaches no `Conditional` module, is asserted by
  `check_scattered_counting_regressions.lean`.
* **Axioms.**  The three theorems go through Silver's theorem
  (`silver_countable_or_cantorAntichain`, through the Gandy–Harrington machinery); the axioms
  reported by `collectAxioms` for them, for the per-level step and for every declaration of this
  guard are printed and must be among `propext`, `Classical.choice` and `Quot.sound`.  The OK
  line is printed only after the cone, closure and axiom checks.

Run with: lake env lean scripts/check_bf_scattered_silver_regressions.lean
-/
import InfinitaryLogic.Conditional.BFScatteredSilver

open Lean FirstOrder FirstOrder.Language

universe u v

noncomputable section

namespace BFScatteredSilverRegressions

/-- **The three statements for an arbitrary countable relational language.** -/
theorem generic_regression {L : Language.{u, v}} [L.IsRelational]
    [Countable (Σ l, L.Relations l)] (Θ : L.Sentenceω) :
    (Θ.IsThinOnNatModels → BFScattered (ModelsOf Θ)) ∧
      (BFScattered (ModelsOf Θ) → Θ.IsThinOnNatModels) ∧
      (Cardinal.mk (Quotient (isoSetoid Θ)) < Cardinal.continuum → BFScattered (ModelsOf Θ)) :=
  ⟨Sentenceω.bfScattered_of_isThinOnNatModels, Sentenceω.bfScattered_iff_isThinOnNatModels.mp,
    Sentenceω.bfScattered_modelsOf_of_lt_continuum⟩

/-! ### Statement pins: copies compared below by expression and by binder kinds -/

theorem pin_bfScattered_of_isThinOnNatModels {L : Language.{u, v}} [L.IsRelational]
    [Countable (Σ l, L.Relations l)] {Θ : L.Sentenceω}
    (h : Θ.IsThinOnNatModels) : BFScattered (ModelsOf Θ) :=
  Sentenceω.bfScattered_of_isThinOnNatModels h

theorem pin_bfScattered_iff_isThinOnNatModels {L : Language.{u, v}} [L.IsRelational]
    [Countable (Σ l, L.Relations l)] {Θ : L.Sentenceω} :
    BFScattered (ModelsOf Θ) ↔ Θ.IsThinOnNatModels :=
  Sentenceω.bfScattered_iff_isThinOnNatModels

theorem pin_bfScattered_modelsOf_of_lt_continuum {L : Language.{u, v}} [L.IsRelational]
    [Countable (Σ l, L.Relations l)] {Θ : L.Sentenceω}
    (h : Cardinal.mk (Quotient (isoSetoid Θ)) < Cardinal.continuum) :
    BFScattered (ModelsOf Θ) :=
  Sentenceω.bfScattered_modelsOf_of_lt_continuum h

/-- **Binder-kind control**: `Sentenceω.bfScattered_iff_isThinOnNatModels` with its implicit `{Θ}`
flipped to `(Θ)`.  Its type is the original's up to binder kinds only; the comparison below must
flag it. -/
theorem binderControl_bfScattered_iff_isThinOnNatModels {L : Language.{u, v}} [L.IsRelational]
    [Countable (Σ l, L.Relations l)] (Θ : L.Sentenceω) :
    BFScattered (ModelsOf Θ) ↔ Θ.IsThinOnNatModels :=
  Sentenceω.bfScattered_iff_isThinOnNatModels

/-- The pure-set language: no function or relation symbols, in universes `{1, 2}`. -/
def pureLang : Language.{1, 2} where
  Functions _ := PEmpty
  Relations _ := PEmpty

instance : pureLang.IsRelational := fun _ ↦ inferInstanceAs (IsEmpty PEmpty)

instance : Countable (Σ l, pureLang.Relations l) :=
  inferInstanceAs (Countable (Σ _ : ℕ, PEmpty.{3}))

/-- There is only one code in the pure-set language. -/
instance : Subsingleton (StructureSpace pureLang) :=
  ⟨fun _ _ ↦ funext fun q ↦ PEmpty.elim q.1.2⟩

/-- **Concrete**: every pure-set sentence has fewer than continuum many classes of coded models,
so its models are back-and-forth scattered, and it is thin by the iff. -/
theorem pureSet_regression (Θ : pureLang.Sentenceω) :
    Cardinal.mk (Quotient (isoSetoid Θ)) < Cardinal.continuum ∧ BFScattered (ModelsOf Θ) ∧
      Θ.IsThinOnNatModels := by
  have hlt : Cardinal.mk (Quotient (isoSetoid Θ)) < Cardinal.continuum :=
    (Cardinal.le_one_iff_subsingleton.mpr inferInstance).trans_lt
      (by simpa using Cardinal.nat_lt_continuum 1)
  have hK := Sentenceω.bfScattered_modelsOf_of_lt_continuum hlt
  exact ⟨hlt, hK, Sentenceω.bfScattered_iff_isThinOnNatModels.mp hK⟩

/-- **Positive control for the rank-free cone check**: a clean statement whose proof uses
`stabilizationOrdinal_spec`. -/
theorem controlRank : True := by
  have _h := @stabilizationOrdinal_spec.{0, 0, 0}
  trivial

end BFScatteredSilverRegressions

end

/-! ### Exact import closure and axiom audit -/

/-- The modules transitively imported by `m` (including `m`), read from the environment
header. -/
partial def importClosure (env : Environment) (m : Name) : NameSet :=
  go [m] {}
where
  go : List Name → NameSet → NameSet
    | [], seen => seen
    | m :: rest, seen =>
      if seen.contains m then go rest seen
      else
        let deps := match env.getModuleIdx? m with
          | some idx => (env.header.moduleData[idx.toNat]!).imports.toList.map (·.module)
          | none => []
        go (deps ++ rest) (seen.insert m)

/-- The module under test. -/
def targetModule : Name := `InfinitaryLogic.Conditional.BFScatteredSilver

/-- The three theorems of the module. -/
def silverTheorems : List Name :=
  [`Sentenceω.bfScattered_of_isThinOnNatModels, `Sentenceω.bfScattered_iff_isThinOnNatModels,
   `Sentenceω.bfScattered_modelsOf_of_lt_continuum].map (`FirstOrder.Language ++ ·)

/-- The per-level Silver step, which every one of the three proof cones must contain, together
with the Silver chain it applies. -/
def requiredDeps : List Name :=
  [`FirstOrder.Language.Sentenceω.countable_bfClasses_of_isThinOnNatModels,
   `silver_countable_or_cantorAntichain, `silver_core_polish]

/-- Silver's theorem in each of its three forms: for a Borel subset, for a closed subset, and the
Polish core.  A declaration mentioning any of them applies Silver directly. -/
def silverFamily : List Name :=
  [`silver_countable_or_cantorAntichain, `silver_countable_or_cantorAntichain_of_isClosed,
   `silver_core_polish]

/-- Each of the three theorems with its copy. -/
def pins : List (Name × Name) :=
  silverTheorems.zip
    ([`pin_bfScattered_of_isThinOnNatModels, `pin_bfScattered_iff_isThinOnNatModels,
      `pin_bfScattered_modelsOf_of_lt_continuum].map (`BFScatteredSilverRegressions ++ ·))

/-- Binder-kind controls: a pinned declaration with a copy differing in one binder kind only. -/
def binderControls : List (Name × Name) :=
  [(`FirstOrder.Language.Sentenceω.bfScattered_iff_isThinOnNatModels,
      `BFScatteredSilverRegressions.binderControl_bfScattered_iff_isThinOnNatModels)]

/-- Name substrings no constant in a rank-free cone may contain. -/
def rankSubstrings : List String :=
  ["stabilizationOrdinal", "StabilizesAt", "scottRank", "scottHeight", "IsIsolatingRank",
   "codeStabilizationOrdinal"]

/-- Module prefixes no constant in a rank-free cone may be declared in. -/
def rankModules : List Name :=
  [`InfinitaryLogic.Scott.Rank, `InfinitaryLogic.Scott.Height,
   `InfinitaryLogic.Scott.RefinementCount, `InfinitaryLogic.Scott.IsolatingLevel,
   `InfinitaryLogic.Descriptive.ScatteredCounting]

/-- The binder kinds (explicit, implicit, instance-implicit, strict-implicit) of the leading
`∀`-telescope of a type, looking through metadata.  `Expr` equality ignores them, so they are
compared separately. -/
partial def binderKinds : Expr → List BinderInfo
  | .forallE _ _ b bi => bi :: binderKinds b
  | .mdata _ e => binderKinds e
  | _ => []

/-- An expression with every universe level normalized: elaboration may leave `max (v+1) 1`
where a restatement has `v+1`, and the two are the same level. -/
def normLevels (e : Expr) : Expr := e.replaceLevel fun l ↦ some l.normalize

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

/-- The constants mentioned by `root` and by the auxiliary (internal) declarations of its own
module that it reaches through such declarations: expansion stops at every public declaration
and at the module boundary. -/
def localRefs (env : Environment) (root : Name) : NameSet := Id.run do
  let home := env.getModuleIdxFor? root
  let mut visited : NameSet := {}
  let mut out : NameSet := {}
  let mut stack : Array Name := #[root]
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if visited.contains n then
      continue
    visited := visited.insert n
    let some ci := env.find? n | continue
    for m in refs ci do
      out := out.insert m
      if m.isInternalDetail && env.getModuleIdxFor? m == home then
        stack := stack.push m
  return out

/-- The rank constants of a cone: by name, and by declaring module. -/
def rankHits (env : Environment) (c : NameSet) : List Name × List (Name × Name) :=
  let names := c.toList.filter fun n ↦
    rankSubstrings.any fun sub ↦ (n.toString.splitOn sub).length ≠ 1
  let mods := c.toList.filterMap fun n ↦ do
    let idx ← env.getModuleIdxFor? n
    let m := env.header.moduleNames[idx.toNat]!
    if rankModules.any (·.isPrefixOf m) then some (n, m) else none
  (names, mods)

/-- Modules the closure must not contain: the counting layer and the family isolating level. -/
def layeringForbidden : List Name :=
  [`InfinitaryLogic.Descriptive.ScatteredCounting, `InfinitaryLogic.Scott.IsolatingLevel]

/-- The exact `InfinitaryLogic` import closure of the module: the Silver chain
(`Conditional.SilverAntichain` and what it imports), `Conditional.MorleyPerfect` (home of the
per-level Silver step), the sentence form of `BFScattered` with the counting theory it brings in,
and the module itself. -/
def allowedClosure : List Name :=
  [`InfinitaryLogic.Conditional.BFScatteredSilver, `InfinitaryLogic.Conditional.GandyHarrington,
   `InfinitaryLogic.Conditional.MorleyPerfect,
   `InfinitaryLogic.Conditional.SilverAntichain, `InfinitaryLogic.Conditional.SilverBurgess,
   `InfinitaryLogic.Conditional.SilverCategoryRoute,
   `InfinitaryLogic.Descriptive.AnalyticClosure,
   `InfinitaryLogic.Descriptive.AnalyticTreeBoundedness,
   `InfinitaryLogic.Descriptive.BFEquivBorel, `InfinitaryLogic.Descriptive.BFScattered,
   `InfinitaryLogic.Descriptive.BFScatteredSentence, `InfinitaryLogic.Descriptive.BFSeparation,
   `InfinitaryLogic.Descriptive.BFTree, `InfinitaryLogic.Descriptive.CantorAntichain,
   `InfinitaryLogic.Descriptive.CodeTransport, `InfinitaryLogic.Descriptive.CountingDichotomy,
   `InfinitaryLogic.Descriptive.FiniteCarrier, `InfinitaryLogic.Descriptive.G0Dichotomy,
   `InfinitaryLogic.Descriptive.G0Fusion, `InfinitaryLogic.Descriptive.GSGraph,
   `InfinitaryLogic.Descriptive.IsomorphismBorel, `InfinitaryLogic.Descriptive.KleeneBrouwer,
   `InfinitaryLogic.Descriptive.KuratowskiUlam, `InfinitaryLogic.Descriptive.Measurable,
   `InfinitaryLogic.Descriptive.ModelClassStandardBorel, `InfinitaryLogic.Descriptive.Mycielski,
   `InfinitaryLogic.Descriptive.PerfectAntichain, `InfinitaryLogic.Descriptive.Polish,
   `InfinitaryLogic.Descriptive.SatisfactionBorel,
   `InfinitaryLogic.Descriptive.SatisfactionBorelOn,
   `InfinitaryLogic.Descriptive.StructureIsoSetoid, `InfinitaryLogic.Descriptive.StructureSpace,
   `InfinitaryLogic.Descriptive.Topology, `InfinitaryLogic.Karp.CarrierTheorem,
   `InfinitaryLogic.Karp.PotentialIso, `InfinitaryLogic.Lomega1omega.OpenBoundsSemantics,
   `InfinitaryLogic.Lomega1omega.Operations, `InfinitaryLogic.Lomega1omega.QuantifierRank,
   `InfinitaryLogic.Lomega1omega.Semantics, `InfinitaryLogic.Lomega1omega.Syntax,
   `InfinitaryLogic.Lomega1omega.Theory, `InfinitaryLogic.ModelTheory.CountingCountable,
   `InfinitaryLogic.ModelTheory.CountingModels, `InfinitaryLogic.ModelTheory.MorleyCounting,
   `InfinitaryLogic.OrdinalUtil, `InfinitaryLogic.Scott.AtomicDiagram,
   `InfinitaryLogic.Scott.BackAndForth, `InfinitaryLogic.Scott.Formula,
   `InfinitaryLogic.Scott.Height, `InfinitaryLogic.Scott.Height.CanonicalSentence,
   `InfinitaryLogic.Scott.Height.Defs, `InfinitaryLogic.Scott.Height.RankBounds,
   `InfinitaryLogic.Scott.QuantifierRank, `InfinitaryLogic.Scott.Rank,
   `InfinitaryLogic.Scott.RefinementCount, `InfinitaryLogic.Scott.Sentence,
   `InfinitaryLogic.Topology.Perfect, `InfinitaryLogic.Util]

/-- The declarations whose axioms are audited: the three theorems, the per-level step and the
guard's own. -/
def audited : List Name :=
  [`Sentenceω.bfScattered_of_isThinOnNatModels, `Sentenceω.bfScattered_iff_isThinOnNatModels,
   `Sentenceω.bfScattered_modelsOf_of_lt_continuum,
   `Sentenceω.countable_bfClasses_of_isThinOnNatModels].map (`FirstOrder.Language ++ ·) ++
  [`generic_regression, `pureLang, `pureSet_regression, `controlRank,
   `pin_bfScattered_of_isThinOnNatModels, `pin_bfScattered_iff_isThinOnNatModels,
   `pin_bfScattered_modelsOf_of_lt_continuum,
   `binderControl_bfScattered_iff_isThinOnNatModels].map (`BFScatteredSilverRegressions ++ ·)

/-- The standard axioms. -/
def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? targetModule
    | throwError "module {targetModule} is not in the environment"
  let ilModules := (importClosure env targetModule).toList.filter fun m ↦
    (`InfinitaryLogic).isPrefixOf m
  let hits := ilModules.filter layeringForbidden.contains
  unless hits.isEmpty do
    throwError "[LAYERING] the closure of {targetModule} reaches {hits}"
  let extra := ilModules.filter fun m ↦ !allowedClosure.contains m
  let missing := allowedClosure.filter fun m ↦ !ilModules.contains m
  unless extra.isEmpty && missing.isEmpty do
    throwError "[CLOSURE DRIFT] the InfinitaryLogic closure of {targetModule} is {ilModules}; \
      update allowedClosure deliberately (extra {extra}, missing {missing})"
  unless ilModules.length == 58 do
    throwError "[CLOSURE DRIFT] expected 58 InfinitaryLogic modules, found {ilModules.length}"
  -- the three theorems are exactly the public declarations of the module
  let pub := (env.header.moduleData[idx.toNat]!).constNames.toList.filter fun n ↦
    !n.isInternalDetail
  let mainDecls := silverTheorems
  unless pub.all mainDecls.contains && mainDecls.all pub.contains do
    throwError "[ROOT DRIFT] the public declarations of {targetModule} are {pub}"
  -- STATEMENT PINS: each original's type is its copy's (up to binder names and level
  -- normalization), with the same universes and the same binder kinds
  for (orig, copy) in pins do
    let some o := env.find? orig | throwError "{orig} not found"
    let some c := env.find? copy | throwError "{copy} not found"
    unless normLevels o.type == normLevels c.type && o.levelParams == c.levelParams do
      throwError "[STATEMENT DRIFT] the statement of {orig} is no longer its pinned copy \
        {copy}: {o.type}"
    unless binderKinds o.type == binderKinds c.type do
      throwError "[BINDER DRIFT] {orig} has binder kinds {repr (binderKinds o.type)}, its \
        pinned copy {copy} has {repr (binderKinds c.type)}"
  -- BINDER CONTROL (negative): each control copy flips one binder kind of a pinned statement;
  -- expression equality alone must accept it and the binder-kind comparison must reject it
  for (orig, ctl) in binderControls do
    let some o := env.find? orig | throwError "{orig} not found"
    let some c := env.find? ctl | throwError "{ctl} not found"
    unless normLevels o.type == normLevels c.type && o.levelParams == c.levelParams do
      throwError "[BINDER CONTROL] {ctl} differs from {orig} in more than a binder kind"
    if binderKinds o.type == binderKinds c.type then
      throwError "[BINDER CONTROL] the binder-kind comparison does not flag {ctl}, whose binder \
        kinds differ from those of {orig}"
  -- NO SECOND COPY OF THE STEP: no declaration of the module applies Silver directly; positive
  -- control: the same check does see the step itself apply Silver
  for d in silverFamily do
    unless (env.find? d).isSome do throwError "[VACUOUS] {d} is not in the environment"
  unless (localRefs env requiredDeps[0]!).contains `silver_countable_or_cantorAntichain do
    throwError "positive control FAILED: the direct-application check does not see \
      {requiredDeps[0]!} apply silver_countable_or_cantorAntichain"
  for n in pub do
    let direct := silverFamily.filter (localRefs env n).contains
    unless direct.isEmpty do
      throwError "[DUPLICATED STEP] {n} applies {direct} directly; quote \
        Sentenceω.countable_bfClasses_of_isThinOnNatModels instead"
  -- DEPENDENCY CHECK (positive): the per-level Silver step and the Silver chain are in all three
  -- proof cones
  for d in requiredDeps do
    unless (env.find? d).isSome do throwError "[VACUOUS] {d} is not in the environment"
  for root in silverTheorems do
    let c ← match cone env root with
      | .ok c => pure c
      | .error e => throwError e
    for d in requiredDeps do
      unless c.contains d do
        throwError "[DEPENDENCY DRIFT] {d} is not in the cone of {root}; the module docstring \
          states the per-level step is quoted there, update both"
  -- rank-free proof cones, with a positive control
  let control := `BFScatteredSilverRegressions.controlRank
  let some (.thmInfo ctl) := env.find? control | throwError "positive control missing"
  if ctl.type.getUsedConstants.contains `FirstOrder.Language.stabilizationOrdinal_spec then
    throwError "positive control: controlRank is no longer proof-only"
  for root in silverTheorems ++ [control] do
    let c ← match cone env root with
      | .ok c => pure c
      | .error e => throwError e
    let (names, mods) := rankHits env c
    if root == control then
      if names.isEmpty || mods.isEmpty then
        throwError "positive control FAILED: the rank-free check does not flag {control} \
          (names {names.take 5}, modules {mods.take 5})"
    else unless names.isEmpty && mods.isEmpty do
      throwError "[RANK IN CONE] the cone of {root} contains {names.take 10} {mods.take 10}"
  for m in [`InfinitaryLogic.Scott.Rank, `InfinitaryLogic.Scott.Height.Defs,
      `InfinitaryLogic.Scott.RefinementCount] do
    unless ilModules.contains m do
      throwError "[CLOSURE DRIFT] {m} is no longer in the import closure; update the docstrings"
  let mut seen : NameSet := {}
  for n in audited do
    unless (env.find? n).isSome do throwError "declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a ↦ !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
    seen := seen ++ .ofList axs.toList
  logInfo m!"bf scattered silver regression guard: OK (applied: thin implies back-and-forth \
    scattered, the iff in both directions and the below-continuum form for an arbitrary \
    countable relational Language.\{u, v}; the per-level step \
    Sentenceω.countable_bfClasses_of_isThinOnNatModels, silver_countable_or_cantorAntichain and \
    silver_core_polish in all three proof cones, and no form of Silver's theorem applied \
    directly by any declaration of the module; the three \
    statements' types equal to their copies up to binder names and level normalization, \
    with the same universe parameters and binder kinds, the binder-kind comparison flagging \
    a \{Θ}-to-(Θ) control that expression equality accepts; rank-free proof cones (no \
    stabilization ordinal, \
    StabilizesAt, Scott rank or height, isolating rank, nor any constant of Scott.Rank, \
    Scott.Height, RefinementCount, IsolatingLevel or ScatteredCounting), the check flagging \
    a proof-only control, with those Scott modules present in the import closure; \
    concretely, every pure-set sentence has fewer than \
    continuum many classes, hence back-and-forth scattered models, hence is thin; exact \
    import closure ({ilModules.length} InfinitaryLogic modules) without \
    Descriptive.ScatteredCounting or Scott.IsolatingLevel; axioms reported for the \
    {audited.length} audited declarations: {seen.toList}, all standard)"
