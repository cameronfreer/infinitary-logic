/-
Regression guard for thinness from sentence cuts
(`InfinitaryLogic/Descriptive/MinimallyUncountableThin.lean`).

* **Applications.**  `isThinOn_of_sentence_cuts` and `MinimallyUncountableOn.isThinOn` for an
  arbitrary countable relational `Language.{u, v}` and an arbitrary set of codes, with no
  scatteredness, analyticity or invariance hypothesis in scope; concretely, in the pure-set
  language (one code, universes `{1, 2}`), the set of all codes is thin through the sentence
  cuts and, separately, through the landed `isThinOn_of_bfScattered`.
* **López–Escobar dependency, stated positively.**  The proof cones of both declarations contain
  `lopez_escobar` (through the transported splits criterion); this is checked as a required
  dependency, not merely tolerated, and it is a separate check from the axiom audit.  No
  dependency-free claim is made for this module.
* **Exact import closure.**  The `InfinitaryLogic` closure of
  `Descriptive.MinimallyUncountableThin` is exactly `allowedClosure` (129 modules: the closures
  of `Descriptive.MinimallyUncountable` (33) and `Descriptive.SmallVocabularyTransport` (115),
  overlapping in 20, plus the module), and it is checked to be that union.  It contains
  `Descriptive.MinimallyUncountable` and does **not** contain `Descriptive.MinimallyUnbounded`
  or `Descriptive.ScatteredCounting` (so the isolating-rank contract is not imported), nor any
  `Conditional`, `Admissible`, `ScottProcess` or `WIP` module.
* **Standard axioms** for both declarations and every declaration of this guard, checked with
  `collectAxioms` after the dependency and closure checks.  The OK line is printed only after
  all checks.

Run with: lake env lean scripts/check_minimally_uncountable_thin_regressions.lean
-/
import InfinitaryLogic.Descriptive.MinimallyUncountableThin
-- so that the excluded modules exist in the environment (the module imports neither)
import InfinitaryLogic.Descriptive.MinimallyUnbounded

open Lean FirstOrder FirstOrder.Language Set

universe u v

noncomputable section

namespace MinimallyUncountableThinRegressions

/-- **Both declarations for an arbitrary countable relational language and an arbitrary set of
codes**, with no scatteredness, analyticity or invariance in scope. -/
theorem generic_regression {L : Language.{u, v}} [L.IsRelational]
    [Countable (Σ l, L.Relations l)] {K : Set (StructureSpace L)}
    (h : ∀ θ : L.Sentenceω, (Quotient.mk (structureIsoSetoid L) '' (K ∩ ModelsOf θ)).Countable ∨
      (Quotient.mk (structureIsoSetoid L) '' (K \ ModelsOf θ)).Countable) :
    IsThinOn (structureIsoSetoid L) K ∧
      (MinimallyUncountableOn K → IsThinOn (structureIsoSetoid L) K) :=
  ⟨isThinOn_of_sentence_cuts h, fun hm ↦ hm.isThinOn⟩

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

/-- **The pure-set language**: all codes are thin through the sentence cuts (first conjunct);
they are also back-and-forth scattered, hence thin through the landed `isThinOn_of_bfScattered`
(second and third conjuncts). -/
theorem pure_regression :
    IsThinOn (structureIsoSetoid pureLang) (univ : Set (StructureSpace pureLang)) ∧
      BFScattered (univ : Set (StructureSpace pureLang)) ∧
      IsThinOn (structureIsoSetoid pureLang) (univ : Set (StructureSpace pureLang)) :=
  have hK := (concentratedAtBFLevels_of_countable (pure_classes_countable univ)).bfScattered
  ⟨isThinOn_of_sentence_cuts fun _ ↦ Or.inl (pure_classes_countable _), hK,
    isThinOn_of_bfScattered hK⟩

end MinimallyUncountableThinRegressions

end

open MinimallyUncountableThinRegressions

/-- The module under test. -/
def targetModule : Name := `InfinitaryLogic.Descriptive.MinimallyUncountableThin

/-- The two declarations of the module. -/
def exports : List Name :=
  [`FirstOrder.Language.isThinOn_of_sentence_cuts,
   `FirstOrder.Language.MinimallyUncountableOn.isThinOn]

/-- The López–Escobar theorem, a required dependency of both cones. -/
def lopezEscobar : Name := `FirstOrder.Language.lopez_escobar

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

/-- Modules and prefixes the closure may not reach. -/
def forbiddenPrefixes : List Name :=
  [`InfinitaryLogic.Descriptive.MinimallyUnbounded, `InfinitaryLogic.Descriptive.ScatteredCounting,
   `InfinitaryLogic.Conditional, `InfinitaryLogic.Admissible, `InfinitaryLogic.ScottProcess,
   `InfinitaryLogic.WIP]

/-- The exact `InfinitaryLogic` import closure of `Descriptive.MinimallyUncountableThin`. -/
def allowedClosure : List Name :=
  [`InfinitaryLogic.Combinatorics.EndHomogeneousErdosRado,
   `InfinitaryLogic.Combinatorics.FiniteArityErdosRadoInduction,
   `InfinitaryLogic.Combinatorics.InfiniteRamsey,
   `InfinitaryLogic.Combinatorics.InfiniteRamseyFamily,
   `InfinitaryLogic.Combinatorics.PairErdosRadoGeneral,
   `InfinitaryLogic.Descriptive.AnalyticClosure, `InfinitaryLogic.Descriptive.AnalyticTree,
   `InfinitaryLogic.Descriptive.AnalyticTreeBoundedness,
   `InfinitaryLogic.Descriptive.BFConcentration, `InfinitaryLogic.Descriptive.BFEquivBorel,
   `InfinitaryLogic.Descriptive.BFScattered, `InfinitaryLogic.Descriptive.BFSeparation,
   `InfinitaryLogic.Descriptive.BFTree, `InfinitaryLogic.Descriptive.CantorAntichain,
   `InfinitaryLogic.Descriptive.CodeTransport, `InfinitaryLogic.Descriptive.CountableSplits,
   `InfinitaryLogic.Descriptive.GDeltaPolish, `InfinitaryLogic.Descriptive.InvariantMeasurableSpace,
   `InfinitaryLogic.Descriptive.InvariantSeparation, `InfinitaryLogic.Descriptive.KleeneBrouwer,
   `InfinitaryLogic.Descriptive.LogicAction, `InfinitaryLogic.Descriptive.LopezEscobar,
   `InfinitaryLogic.Descriptive.LopezEscobarEasy, `InfinitaryLogic.Descriptive.Measurable,
   `InfinitaryLogic.Descriptive.MinimallyUncountable,
   `InfinitaryLogic.Descriptive.MinimallyUncountableThin,
   `InfinitaryLogic.Descriptive.ModelClassStandardBorel,
   `InfinitaryLogic.Descriptive.ModelsOfGDelta, `InfinitaryLogic.Descriptive.PerfectAntichain,
   `InfinitaryLogic.Descriptive.PermPolishGroup, `InfinitaryLogic.Descriptive.PermTopology,
   `InfinitaryLogic.Descriptive.Polish, `InfinitaryLogic.Descriptive.PolishAction,
   `InfinitaryLogic.Descriptive.QueryCode, `InfinitaryLogic.Descriptive.SatisfactionBorel,
   `InfinitaryLogic.Descriptive.SatisfactionBorelOn,
   `InfinitaryLogic.Descriptive.SentenceObservables, `InfinitaryLogic.Descriptive.SentenceRecovery,
   `InfinitaryLogic.Descriptive.SentenceSplits, `InfinitaryLogic.Descriptive.SmallVocabulary,
   `InfinitaryLogic.Descriptive.SmallVocabularyLift,
   `InfinitaryLogic.Descriptive.SmallVocabularyTransport,
   `InfinitaryLogic.Descriptive.StructureIsoSetoid, `InfinitaryLogic.Descriptive.StructureSpace,
   `InfinitaryLogic.Descriptive.Topology, `InfinitaryLogic.Lomega1omega.Depth,
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
   `InfinitaryLogic.ModelTheory.FragmentLowenheimSkolem,
   `InfinitaryLogic.ModelTheory.HanfSpectrum.CardinalBounds, `InfinitaryLogic.ModelTheory.PCClass,
   `InfinitaryLogic.OrdinalUtil, `InfinitaryLogic.Scott.AtomicDiagram,
   `InfinitaryLogic.Scott.BFEquivRelabel, `InfinitaryLogic.Scott.BackAndForth,
   `InfinitaryLogic.Scott.Formula, `InfinitaryLogic.Topology.Perfect, `InfinitaryLogic.Util]

/-- The guard's own declarations whose axioms are audited. -/
def guardDecls : List Name :=
  [`generic_regression, `pureLang, `pure_classes_countable, `pure_regression].map
    (`MinimallyUncountableThinRegressions ++ ·)

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
  -- DEPENDENCY CHECK (positive): López–Escobar is in both proof cones
  unless (env.find? lopezEscobar).isSome do throwError "{lopezEscobar} is not in the environment"
  let mut sizes : Array (Name × Nat) := #[]
  for n in exports do
    let some (.thmInfo _) := env.find? n | throwError "[NOT A THEOREM] {n}"
    let c ← match cone env n with
      | .ok c => pure c
      | .error e => throwError e
    unless c.contains lopezEscobar do
      throwError "[DEPENDENCY DRIFT] {lopezEscobar} is no longer in the cone of {n}; the module \
        docstring states it is, update both"
    sizes := sizes.push (n.componentsRev.head!, c.size)
  -- CLOSURE CHECK: exact, the predicted union, and the excluded modules absent
  let some idx := env.getModuleIdx? targetModule
    | throwError "module {targetModule} is not in the environment"
  for m in forbiddenPrefixes.take 2 do
    unless (env.getModuleIdx? m).isSome do throwError "[VACUOUS] module {m} not found"
  let ilModules := ilClosure env targetModule
  let hits := ilModules.filter fun m ↦ forbiddenPrefixes.any (·.isPrefixOf m)
  unless hits.isEmpty do
    throwError "[BROAD CONE] the closure of {targetModule} reaches {hits}"
  unless ilModules.contains `InfinitaryLogic.Descriptive.MinimallyUncountable do
    throwError "[CLOSURE DRIFT] the closure of {targetModule} misses MinimallyUncountable"
  checkExact targetModule ilModules allowedClosure
  unless ilModules.length == 129 do
    throwError "[CLOSURE DRIFT] expected 129 InfinitaryLogic modules, found {ilModules.length}"
  let parts := [`InfinitaryLogic.Descriptive.MinimallyUncountable,
    `InfinitaryLogic.Descriptive.SmallVocabularyTransport]
  let psizes := parts.map fun p ↦ (ilClosure env p).length
  unless psizes == [33, 115] do
    throwError "[CLOSURE DRIFT] the closures of {parts} have sizes {psizes}, not [33, 115]"
  let union := (parts.foldl (fun s p ↦ s ++ .ofList (ilClosure env p)) ({} : NameSet)).insert
    targetModule
  checkExact targetModule ilModules union.toList
  -- AXIOM CHECK (separate): every declaration of the module and of this guard
  let enumerated := (env.header.moduleData[idx.toNat]!).constNames.toList
  let audited := enumerated ++ guardDecls
  for n in audited do
    unless (env.find? n).isSome do throwError "declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a ↦ !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo m!"minimally uncountable thin regression guard: OK (applied: both declarations for an \
    arbitrary countable relational Language.\{u, v} and an arbitrary set of codes with no \
    scatteredness, analyticity or invariance; all codes of the pure-set language thin through \
    the sentence cuts and through isThinOn_of_bfScattered; dependency: lopez_escobar in both \
    proof cones (cones {sizes.toList}); exact import closure ({ilModules.length} modules, the \
    union of MinimallyUncountable and SmallVocabularyTransport plus the module) without \
    MinimallyUnbounded, ScatteredCounting, Conditional, Admissible, ScottProcess or WIP; \
    standard axioms for {audited.length} declarations)"
