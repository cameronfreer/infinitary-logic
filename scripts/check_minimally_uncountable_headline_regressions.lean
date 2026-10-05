/-
Regression guard for the sentence headline on minimally uncountable classes
(`InfinitaryLogic/Conditional/MinimallyUncountableHeadline.lean`).

Both theorems are *applied*, not only listed for their axioms.

* **Generic applications.**  `Sentenceω.minimallyUncountable_iff` and
  `Sentenceω.minimallyUncountable_iff_concentrated`, both directions, for an arbitrary
  relational `Language.{u, v}` with countably many relation symbols, an arbitrary sentence and
  an arbitrary isolating rank; and, from the first theorem for two isolating ranks, the
  rank independence of `Sentenceω.MinimallyUnbounded` on back-and-forth scattered models.
* **The landed instance.**  The first theorem at `codeStabilizationOrdinal`, through
  `isIsolatingRank_codeStabilizationOrdinal`.
* **Concrete.**  In the pure-set language (one code, universes `{1, 2}`) every sentence has at
  most one isomorphism class of coded models, so it is **not** minimally uncountable; its models
  are back-and-forth scattered (`concentratedAtBFLevels_of_countable`), so by the headline it is
  not minimally unbounded for `codeStabilizationOrdinal` (nor for any isolating rank), and the
  concentrated form fails on its uncountability conjunct.
* **Dependencies, stated positively.**  The proof cones of both theorems contain `lopez_escobar`
  (through `MinimallyUncountableOn.isThinOn`) and the Silver chain,
  `silver_countable_or_cantorAntichain` and `silver_core_polish` (through
  `Sentenceω.bfScattered_of_isThinOnNatModels`); these are required
  dependencies (`[DEPENDENCY DRIFT]` otherwise), checked separately from the axiom audit.  The
  concentrated form's type mentions no `IsIsolatingRank`; the two theorems are exactly the
  public declarations of the module (`[ROOT DRIFT]`).
* **Statement shape.**  Both left sides are the sentence wrapper `Θ.MinimallyUncountable`
  (`[SHAPE DRIFT]` otherwise), and the headline rewrites a goal stated with it (`rw`) and a
  hypothesis stated with it (`simp only … at`).
* **Exact import closure.**  The `InfinitaryLogic` closure of
  `Conditional.MinimallyUncountableHeadline` is exactly `allowedClosure` (161 modules),
  checked to be the union of the closures of `Conditional.BFScatteredSilver` (57),
  `Descriptive.MinimallyUnbounded` (40) and `Descriptive.MinimallyUncountableThin` (129) plus
  the module; it contains no `Admissible`, `ScottProcess` or `WIP` module and no `Conditional`
  module outside the Silver chain (`[BROAD CONE]`).
* **Standard axioms** (`propext`, `Classical.choice`, `Quot.sound`) for both theorems and every
  declaration of this guard, checked with `collectAxioms` after the dependency and closure
  checks.  The OK line is printed only after all checks.

Run with: lake env lean scripts/check_minimally_uncountable_headline_regressions.lean
-/
import InfinitaryLogic.Conditional.MinimallyUncountableHeadline

open Lean FirstOrder FirstOrder.Language Set

universe u v

noncomputable section

namespace MinimallyUncountableHeadlineRegressions

/-- **Both theorems, both directions, for an arbitrary countable relational language**, an
arbitrary sentence and an arbitrary isolating rank. -/
theorem generic_regression {L : Language.{u, v}} [L.IsRelational]
    [Countable (Σ l, L.Relations l)] {ρ : StructureSpace L → Ordinal.{0}}
    (hρ : IsIsolatingRank ρ) (Θ : L.Sentenceω) :
    (Θ.MinimallyUncountable → BFScattered (ModelsOf Θ) ∧ Θ.MinimallyUnbounded ρ) ∧
      (BFScattered (ModelsOf Θ) ∧ Θ.MinimallyUnbounded ρ → Θ.MinimallyUncountable) ∧
      (Θ.MinimallyUncountable → ConcentratedAtBFLevels (ModelsOf Θ) ∧
        ¬ (Quotient.mk (structureIsoSetoid L) '' ModelsOf Θ).Countable) ∧
      (ConcentratedAtBFLevels (ModelsOf Θ) ∧
        ¬ (Quotient.mk (structureIsoSetoid L) '' ModelsOf Θ).Countable →
          Θ.MinimallyUncountable) :=
  ⟨(Sentenceω.minimallyUncountable_iff hρ Θ).mp, (Sentenceω.minimallyUncountable_iff hρ Θ).mpr,
    (Sentenceω.minimallyUncountable_iff_concentrated Θ).mp,
    (Sentenceω.minimallyUncountable_iff_concentrated Θ).mpr⟩

/-- **Rank independence through the headline**: on back-and-forth scattered models, two isolating
ranks agree on minimal unboundedness of a sentence. -/
theorem rank_independence_regression {L : Language.{u, v}} [L.IsRelational]
    [Countable (Σ l, L.Relations l)] {ρ ρ' : StructureSpace L → Ordinal.{0}}
    (hρ : IsIsolatingRank ρ) (hρ' : IsIsolatingRank ρ') (Θ : L.Sentenceω)
    (hK : BFScattered (ModelsOf Θ)) :
    Θ.MinimallyUnbounded ρ ↔ Θ.MinimallyUnbounded ρ' :=
  ⟨fun h ↦ (((Sentenceω.minimallyUncountable_iff hρ' Θ).mp
      ((Sentenceω.minimallyUncountable_iff hρ Θ).mpr ⟨hK, h⟩))).2,
    fun h ↦ (((Sentenceω.minimallyUncountable_iff hρ Θ).mp
      ((Sentenceω.minimallyUncountable_iff hρ' Θ).mpr ⟨hK, h⟩))).2⟩

/-- **The landed instance**: the headline at `codeStabilizationOrdinal`. -/
theorem instance_regression {L : Language.{u, v}} [L.IsRelational]
    [Countable (Σ l, L.Relations l)] (Θ : L.Sentenceω) :
    Θ.MinimallyUncountable ↔
      BFScattered (ModelsOf Θ) ∧ Θ.MinimallyUnbounded codeStabilizationOrdinal :=
  Sentenceω.minimallyUncountable_iff isIsolatingRank_codeStabilizationOrdinal Θ

/-- **The headline rewrites goals stated with the sentence wrapper**: `rw` on a goal and
`simp only` at a hypothesis, both stated as `Θ.MinimallyUncountable`. -/
theorem rewrite_regression {L : Language.{u, v}} [L.IsRelational]
    [Countable (Σ l, L.Relations l)] {ρ : StructureSpace L → Ordinal.{0}}
    (hρ : IsIsolatingRank ρ) (Θ : L.Sentenceω) (h : Θ.MinimallyUncountable) :
    (Θ.MinimallyUncountable ↔ BFScattered (ModelsOf Θ) ∧ Θ.MinimallyUnbounded ρ) ∧
      ConcentratedAtBFLevels (ModelsOf Θ) := by
  constructor
  · rw [Sentenceω.minimallyUncountable_iff hρ]
  · simp only [Sentenceω.minimallyUncountable_iff_concentrated] at h
    exact h.1

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

/-- Every set of codes of the pure-set language meets at most one isomorphism class. -/
theorem pure_classes_countable (S : Set (StructureSpace pureLang)) :
    (Quotient.mk (structureIsoSetoid pureLang) '' S).Countable :=
  (countable_singleton (Quotient.mk (structureIsoSetoid pureLang) fun _ ↦ false)).mono
    (by rintro _ ⟨x, -, rfl⟩; exact congrArg _ (Subsingleton.elim _ _))

/-- **The pure-set language**: no sentence is minimally uncountable (countably many classes);
its models are back-and-forth scattered, so by the headline it is not minimally unbounded for
`codeStabilizationOrdinal`, nor for any isolating rank; and the concentrated form fails on its
uncountability conjunct. -/
theorem pureSet_regression (Θ : pureLang.Sentenceω) :
    ¬ Θ.MinimallyUncountable ∧ BFScattered (ModelsOf Θ) ∧
      ¬ Θ.MinimallyUnbounded codeStabilizationOrdinal ∧
      (∀ ρ, IsIsolatingRank ρ → ¬ Θ.MinimallyUnbounded ρ) ∧
      ¬ (ConcentratedAtBFLevels (ModelsOf Θ) ∧
        ¬ (Quotient.mk (structureIsoSetoid pureLang) '' ModelsOf Θ).Countable) := by
  have hnot : ¬ Θ.MinimallyUncountable := fun h ↦ h.1 (pure_classes_countable _)
  have hK : BFScattered (ModelsOf Θ) :=
    (concentratedAtBFLevels_of_countable (pure_classes_countable _)).bfScattered
  have hall : ∀ ρ, IsIsolatingRank ρ → ¬ Θ.MinimallyUnbounded ρ :=
    fun _ hρ h ↦ hnot ((Sentenceω.minimallyUncountable_iff hρ Θ).mpr ⟨hK, h⟩)
  exact ⟨hnot, hK, hall _ isIsolatingRank_codeStabilizationOrdinal, hall,
    fun h ↦ hnot ((Sentenceω.minimallyUncountable_iff_concentrated Θ).mpr h)⟩

end MinimallyUncountableHeadlineRegressions

end

open MinimallyUncountableHeadlineRegressions

/-- The module under test. -/
def targetModule : Name := `InfinitaryLogic.Conditional.MinimallyUncountableHeadline

/-- The two theorems of the module. -/
def exports : List Name :=
  [`FirstOrder.Language.Sentenceω.minimallyUncountable_iff,
   `FirstOrder.Language.Sentenceω.minimallyUncountable_iff_concentrated]

/-- Required dependencies of both proof cones: López–Escobar and the Silver chain (the Borel
subset form and the Polish core of Silver's theorem). -/
def requiredDeps : List Name :=
  [`FirstOrder.Language.lopez_escobar, `silver_countable_or_cantorAntichain, `silver_core_polish]

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

/-- The `InfinitaryLogic` modules of a closure. -/
def ilClosure (env : Environment) (m : Name) : List Name :=
  (importClosure env m).toList.filter fun n ↦ (`InfinitaryLogic).isPrefixOf n

/-- Module prefixes the closure may not reach. -/
def forbiddenPrefixes : List Name :=
  [`InfinitaryLogic.Admissible, `InfinitaryLogic.ScottProcess, `InfinitaryLogic.WIP]

/-- The `Conditional` modules the closure may reach: the Silver chain and the module. -/
def allowedConditional : List Name :=
  [`InfinitaryLogic.Conditional.BFScatteredSilver, `InfinitaryLogic.Conditional.GandyHarrington,
   `InfinitaryLogic.Conditional.SilverAntichain, `InfinitaryLogic.Conditional.SilverBurgess,
   `InfinitaryLogic.Conditional.SilverCategoryRoute,
   `InfinitaryLogic.Conditional.MinimallyUncountableHeadline]

/-- The exact `InfinitaryLogic` import closure of `Conditional.MinimallyUncountableHeadline`. -/
def allowedClosure : List Name :=
  [`InfinitaryLogic.Combinatorics.EndHomogeneousErdosRado,
   `InfinitaryLogic.Combinatorics.FiniteArityErdosRadoInduction,
   `InfinitaryLogic.Combinatorics.InfiniteRamsey,
   `InfinitaryLogic.Combinatorics.InfiniteRamseyFamily,
   `InfinitaryLogic.Combinatorics.PairErdosRadoGeneral,
   `InfinitaryLogic.Conditional.BFScatteredSilver, `InfinitaryLogic.Conditional.GandyHarrington,
   `InfinitaryLogic.Conditional.MinimallyUncountableHeadline,
   `InfinitaryLogic.Conditional.SilverAntichain, `InfinitaryLogic.Conditional.SilverBurgess,
   `InfinitaryLogic.Conditional.SilverCategoryRoute, `InfinitaryLogic.Descriptive.AnalyticClosure,
   `InfinitaryLogic.Descriptive.AnalyticTree, `InfinitaryLogic.Descriptive.AnalyticTreeBoundedness,
   `InfinitaryLogic.Descriptive.BFConcentration, `InfinitaryLogic.Descriptive.BFEquivBorel,
   `InfinitaryLogic.Descriptive.BFScattered, `InfinitaryLogic.Descriptive.BFScatteredSentence,
   `InfinitaryLogic.Descriptive.BFSeparation, `InfinitaryLogic.Descriptive.BFTree,
   `InfinitaryLogic.Descriptive.CantorAntichain, `InfinitaryLogic.Descriptive.CodeTransport,
   `InfinitaryLogic.Descriptive.CountableSplits, `InfinitaryLogic.Descriptive.CountingDichotomy,
   `InfinitaryLogic.Descriptive.FiniteCarrier, `InfinitaryLogic.Descriptive.G0Dichotomy,
   `InfinitaryLogic.Descriptive.G0Fusion, `InfinitaryLogic.Descriptive.GDeltaPolish,
   `InfinitaryLogic.Descriptive.GSGraph, `InfinitaryLogic.Descriptive.InvariantMeasurableSpace,
   `InfinitaryLogic.Descriptive.InvariantSeparation, `InfinitaryLogic.Descriptive.IsomorphismBorel,
   `InfinitaryLogic.Descriptive.KleeneBrouwer, `InfinitaryLogic.Descriptive.KuratowskiUlam,
   `InfinitaryLogic.Descriptive.LogicAction, `InfinitaryLogic.Descriptive.LopezEscobar,
   `InfinitaryLogic.Descriptive.LopezEscobarEasy, `InfinitaryLogic.Descriptive.Measurable,
   `InfinitaryLogic.Descriptive.MinimallyUnbounded,
   `InfinitaryLogic.Descriptive.MinimallyUncountable,
   `InfinitaryLogic.Descriptive.MinimallyUncountableThin,
   `InfinitaryLogic.Descriptive.ModelClassStandardBorel,
   `InfinitaryLogic.Descriptive.ModelsOfGDelta, `InfinitaryLogic.Descriptive.Mycielski,
   `InfinitaryLogic.Descriptive.PerfectAntichain, `InfinitaryLogic.Descriptive.PermPolishGroup,
   `InfinitaryLogic.Descriptive.PermTopology, `InfinitaryLogic.Descriptive.Polish,
   `InfinitaryLogic.Descriptive.PolishAction, `InfinitaryLogic.Descriptive.QueryCode,
   `InfinitaryLogic.Descriptive.SatisfactionBorel, `InfinitaryLogic.Descriptive.SatisfactionBorelOn,
   `InfinitaryLogic.Descriptive.ScatteredCounting, `InfinitaryLogic.Descriptive.SentenceObservables,
   `InfinitaryLogic.Descriptive.SentenceRecovery, `InfinitaryLogic.Descriptive.SentenceSplits,
   `InfinitaryLogic.Descriptive.SmallVocabulary, `InfinitaryLogic.Descriptive.SmallVocabularyLift,
   `InfinitaryLogic.Descriptive.SmallVocabularyTransport,
   `InfinitaryLogic.Descriptive.StructureIsoSetoid, `InfinitaryLogic.Descriptive.StructureSpace,
   `InfinitaryLogic.Descriptive.Topology, `InfinitaryLogic.Karp.CarrierTheorem,
   `InfinitaryLogic.Karp.PotentialIso, `InfinitaryLogic.Lomega1omega.Depth,
   `InfinitaryLogic.Lomega1omega.Entailment, `InfinitaryLogic.Lomega1omega.FiniteQuantification,
   `InfinitaryLogic.Lomega1omega.Fragment, `InfinitaryLogic.Lomega1omega.OpenBoundsSemantics,
   `InfinitaryLogic.Lomega1omega.Operations, `InfinitaryLogic.Lomega1omega.QuantifierClass,
   `InfinitaryLogic.Lomega1omega.QuantifierRank, `InfinitaryLogic.Lomega1omega.Semantics,
   `InfinitaryLogic.Lomega1omega.Syntax, `InfinitaryLogic.Lomega1omega.Theory,
   `InfinitaryLogic.Methods.ConstantAbstraction, `InfinitaryLogic.Methods.ConstantInstances,
   `InfinitaryLogic.Methods.ConstantSupport, `InfinitaryLogic.Methods.EM.FragmentAdapter,
   `InfinitaryLogic.Methods.EM.Indiscernible, `InfinitaryLogic.Methods.EM.Realization,
   `InfinitaryLogic.Methods.EM.TailAdapter, `InfinitaryLogic.Methods.EM.Template,
   `InfinitaryLogic.Methods.GeneratedSublanguage,
   `InfinitaryLogic.Methods.Henkin.ConsistencyProperty,
   `InfinitaryLogic.Methods.Henkin.Construction,
   `InfinitaryLogic.Methods.Henkin.CountableCompletion.ConsistencyPropertyEqOn,
   `InfinitaryLogic.Methods.Henkin.CountableCompletion.FairEnumeration,
   `InfinitaryLogic.Methods.Henkin.CountableCompletion.GeneratedUniverse,
   `InfinitaryLogic.Methods.Henkin.CountableCompletion.QuotientTermModel,
   `InfinitaryLogic.Methods.Henkin.CountableCompletion.QuotientTruthLemma,
   `InfinitaryLogic.Methods.Interpolation.BaseOccurrenceProjections,
   `InfinitaryLogic.Methods.Interpolation.ConstantElimination,
   `InfinitaryLogic.Methods.Interpolation.CraigRelational,
   `InfinitaryLogic.Methods.Interpolation.CraigSeparation,
   `InfinitaryLogic.Methods.Interpolation.CraigSublanguage,
   `InfinitaryLogic.Methods.Interpolation.GraphAxioms,
   `InfinitaryLogic.Methods.Interpolation.GraphLanguage,
   `InfinitaryLogic.Methods.Interpolation.GraphReconstruction,
   `InfinitaryLogic.Methods.Interpolation.Inseparability,
   `InfinitaryLogic.Methods.Interpolation.InseparablePairFamily,
   `InfinitaryLogic.Methods.Interpolation.PairedInsepFamily,
   `InfinitaryLogic.Methods.Interpolation.PairedInseparability,
   `InfinitaryLogic.Methods.Interpolation.QuantifierRoundTrip,
   `InfinitaryLogic.Methods.Interpolation.Relationalize,
   `InfinitaryLogic.Methods.Interpolation.RootGate,
   `InfinitaryLogic.Methods.Interpolation.TermGraph, `InfinitaryLogic.Methods.LanguageMapOccurrence,
   `InfinitaryLogic.Methods.LocalColimit, `InfinitaryLogic.Methods.LocalEMContext,
   `InfinitaryLogic.Methods.LocalEMFamily, `InfinitaryLogic.Methods.LocalEMSupport,
   `InfinitaryLogic.Methods.LocalEMTemplateRealization, `InfinitaryLogic.Methods.LocalEMTruth,
   `InfinitaryLogic.Methods.LocalEMTruthLemma, `InfinitaryLogic.Methods.LocalSkolem,
   `InfinitaryLogic.Methods.LocalSkolemUniversal, `InfinitaryLogic.Methods.LocalTower,
   `InfinitaryLogic.Methods.LopezEscobar.CodeClass, `InfinitaryLogic.Methods.LopezEscobar.Disjoint,
   `InfinitaryLogic.Methods.LopezEscobar.FunctionalTheta,
   `InfinitaryLogic.Methods.LopezEscobar.PCMem, `InfinitaryLogic.Methods.LopezEscobar.PCSentence,
   `InfinitaryLogic.Methods.LopezEscobar.RelationalizeSpike,
   `InfinitaryLogic.Methods.LopezEscobar.Separation,
   `InfinitaryLogic.Methods.LopezEscobar.SharedDecoder,
   `InfinitaryLogic.Methods.LopezEscobar.StandardModel,
   `InfinitaryLogic.Methods.LopezEscobar.TaggedGlue,
   `InfinitaryLogic.Methods.LopezEscobar.WitnessLang, `InfinitaryLogic.Methods.MarkerStage,
   `InfinitaryLogic.Methods.SchemaCompletion, `InfinitaryLogic.Methods.SchemaOmegaWitness,
   `InfinitaryLogic.Methods.Skolem, `InfinitaryLogic.Methods.SkolemClosure,
   `InfinitaryLogic.Methods.SkolemColimit, `InfinitaryLogic.Methods.SymbSublangExpansion,
   `InfinitaryLogic.Methods.TailIndiscernible, `InfinitaryLogic.ModelTheory.AElementary,
   `InfinitaryLogic.ModelTheory.CountingCountable, `InfinitaryLogic.ModelTheory.CountingModels,
   `InfinitaryLogic.ModelTheory.FragmentLowenheimSkolem,
   `InfinitaryLogic.ModelTheory.HanfSpectrum.CardinalBounds,
   `InfinitaryLogic.ModelTheory.MorleyCounting, `InfinitaryLogic.ModelTheory.PCClass,
   `InfinitaryLogic.OrdinalCountability, `InfinitaryLogic.OrdinalUtil,
   `InfinitaryLogic.Scott.AtomicDiagram, `InfinitaryLogic.Scott.BFEquivRelabel,
   `InfinitaryLogic.Scott.BackAndForth, `InfinitaryLogic.Scott.Formula,
   `InfinitaryLogic.Scott.Height, `InfinitaryLogic.Scott.Height.CanonicalSentence,
   `InfinitaryLogic.Scott.Height.Defs, `InfinitaryLogic.Scott.Height.RankBounds,
   `InfinitaryLogic.Scott.IsolatingLevel, `InfinitaryLogic.Scott.QuantifierRank,
   `InfinitaryLogic.Scott.Rank, `InfinitaryLogic.Scott.RefinementCount,
   `InfinitaryLogic.Scott.Sentence, `InfinitaryLogic.Topology.Perfect, `InfinitaryLogic.Util]

/-- The guard's own declarations whose axioms are audited. -/
def guardDecls : List Name :=
  [`generic_regression, `rank_independence_regression, `instance_regression,
   `rewrite_regression, `pureLang, `pure_classes_countable, `pureSet_regression].map
    (`MinimallyUncountableHeadlineRegressions ++ ·)

/-- The standard axioms. -/
def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

/-- Exact comparison of a computed closure with a pinned list. -/
def checkExact (what : Name) (actual expected : List Name) : Elab.Command.CommandElabM Unit := do
  let extra := actual.filter fun m ↦ !expected.contains m
  let missing := expected.filter fun m ↦ !actual.contains m
  unless extra.isEmpty && missing.isEmpty do
    throwError "[CLOSURE DRIFT] the InfinitaryLogic closure of {what} is {actual}; update the \
      pinned list deliberately (extra {extra}, missing {missing})"

run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? targetModule
    | throwError "module {targetModule} is not in the environment"
  -- ROOTS: the two theorems are exactly the public declarations of the module
  let pub := (env.header.moduleData[idx.toNat]!).constNames.toList.filter fun n ↦
    !n.isInternalDetail
  unless pub.all exports.contains && exports.all pub.contains do
    throwError "[ROOT DRIFT] the public declarations of {targetModule} are {pub}"
  -- SHAPE: both left sides are the sentence wrapper `Sentenceω.MinimallyUncountable`
  for n in exports do
    let some ci := env.find? n | throwError "{n} not found"
    let lhsOk ← Elab.Command.liftTermElabM <| Meta.forallTelescope ci.type fun _ body ↦
      pure <| body.isAppOfArity ``Iff 2 &&
        body.appFn!.appArg!.isAppOf `FirstOrder.Language.Sentenceω.MinimallyUncountable
    unless lhsOk do
      throwError "[SHAPE DRIFT] the left side of {n} is not Sentenceω.MinimallyUncountable"
  -- the concentrated form mentions no isolating rank
  let some conc := env.find? exports[1]! | throwError "{exports[1]!} not found"
  if (conc.type.find? (·.isConstOf `FirstOrder.Language.IsIsolatingRank)).isSome then
    throwError "[RANK DRIFT] the type of {exports[1]!} mentions IsIsolatingRank"
  -- DEPENDENCY CHECK (positive): López–Escobar and the Silver chain are in both proof cones
  for d in requiredDeps do
    unless (env.find? d).isSome do throwError "[VACUOUS] {d} is not in the environment"
  let mut sizes : Array String := #[]
  for n in exports do
    let some (.thmInfo _) := env.find? n | throwError "[NOT A THEOREM] {n}"
    let c ← match cone env n with
      | .ok c => pure c
      | .error e => throwError e
    for d in requiredDeps do
      unless c.contains d do
        throwError "[DEPENDENCY DRIFT] {d} is no longer in the cone of {n}; the module \
          docstring states it is, update both"
    sizes := sizes.push s!"{n.componentsRev.head!} {c.size}"
  -- CLOSURE CHECK: exact, the predicted union, and no broad cone
  let ilModules := ilClosure env targetModule
  let hits := ilModules.filter fun m ↦ forbiddenPrefixes.any (·.isPrefixOf m) ||
    ((`InfinitaryLogic.Conditional).isPrefixOf m && !allowedConditional.contains m)
  unless hits.isEmpty do
    throwError "[BROAD CONE] the closure of {targetModule} reaches {hits}"
  checkExact targetModule ilModules allowedClosure
  unless ilModules.length == 161 do
    throwError "[CLOSURE DRIFT] expected 161 InfinitaryLogic modules, found \
      {ilModules.length}"
  let parts := [`InfinitaryLogic.Conditional.BFScatteredSilver,
    `InfinitaryLogic.Descriptive.MinimallyUnbounded,
    `InfinitaryLogic.Descriptive.MinimallyUncountableThin]
  let psizes := parts.map fun p ↦ (ilClosure env p).length
  unless psizes == [57, 40, 129] do
    throwError "[CLOSURE DRIFT] the closures of {parts} have sizes {psizes}, not [57, 40, 129]"
  let union := (parts.foldl (fun s p ↦ s ++ .ofList (ilClosure env p)) ({} : NameSet)).insert
    targetModule
  checkExact targetModule ilModules union.toList
  -- AXIOM CHECK (separate): both theorems and every declaration of this guard
  let audited := exports ++ guardDecls
  let mut seen : NameSet := {}
  for n in audited do
    unless (env.find? n).isSome do throwError "declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a ↦ !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
    seen := seen ++ .ofList axs.toList
  logInfo m!"minimally uncountable headline regression guard: OK (applied: both theorems in \
    both directions for an arbitrary countable relational Language.\{u, v}, an arbitrary \
    sentence and an arbitrary isolating rank; rank independence of MinimallyUnbounded on \
    back-and-forth scattered models through the headline; the headline at \
    codeStabilizationOrdinal; concretely, no pure-set sentence is minimally uncountable, its \
    models are back-and-forth scattered, it is minimally unbounded for no isolating rank, and \
    the concentrated form fails; dependencies: lopez_escobar, \
    silver_countable_or_cantorAntichain and silver_core_polish in both proof cones \
    (cone sizes {", ".intercalate sizes.toList}); both left sides stated through \
    Sentenceω.MinimallyUncountable, rewriting by rw and simp only; the concentrated form \
    mentions no isolating rank; exact import closure ({ilModules.length} \
    modules, the union of BFScatteredSilver, MinimallyUnbounded and MinimallyUncountableThin \
    plus the module) with no Admissible, ScottProcess or WIP module and no Conditional module \
    outside the Silver chain; axioms reported for the {audited.length} audited declarations: \
    {", ".intercalate (seen.toList.map toString)}, all standard)"
