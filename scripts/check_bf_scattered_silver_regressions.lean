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
* **Rank-free and separate from the counting layer.**  The `InfinitaryLogic` import closure of
  `Conditional.BFScatteredSilver` is exactly the pinned list `allowedClosure` (57 modules,
  `[CLOSURE DRIFT]` otherwise); it does **not** contain `Descriptive.ScatteredCounting` or
  `Scott.IsolatingLevel` (`[LAYERING]`).  The converse import boundary, that
  `Descriptive.ScatteredCounting` reaches no `Conditional` module, is asserted by
  `check_scattered_counting_regressions.lean`.
* **Axioms.**  The three theorems go through Silver's theorem
  (`silver_countable_or_cantorAntichain`, hence `silverBurgessDichotomy` and the Gandy–Harrington
  machinery); the axioms reported by `collectAxioms` for them and for every declaration of this
  guard are printed and must be among `propext`, `Classical.choice` and `Quot.sound`.  The OK
  line is printed only after the closure and axiom checks.

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

/-- Modules the closure must not contain: the counting layer and the family isolating level. -/
def layeringForbidden : List Name :=
  [`InfinitaryLogic.Descriptive.ScatteredCounting, `InfinitaryLogic.Scott.IsolatingLevel]

/-- The exact `InfinitaryLogic` import closure of the module: the Silver chain
(`Conditional.SilverAntichain` and what it imports), the sentence form of `BFScattered` with the
counting theory it brings in, and the module itself. -/
def allowedClosure : List Name :=
  [`InfinitaryLogic.Conditional.BFScatteredSilver, `InfinitaryLogic.Conditional.GandyHarrington,
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

/-- The declarations whose axioms are audited: the three theorems and the guard's own. -/
def audited : List Name :=
  [`Sentenceω.bfScattered_of_isThinOnNatModels, `Sentenceω.bfScattered_iff_isThinOnNatModels,
   `Sentenceω.bfScattered_modelsOf_of_lt_continuum].map (`FirstOrder.Language ++ ·) ++
  [`generic_regression, `pureLang, `pureSet_regression].map (`BFScatteredSilverRegressions ++ ·)

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
  -- the three theorems are exactly the public declarations of the module
  let pub := (env.header.moduleData[idx.toNat]!).constNames.toList.filter fun n ↦
    !n.isInternalDetail
  let mainDecls := audited.take 3
  unless pub.all mainDecls.contains && mainDecls.all pub.contains do
    throwError "[ROOT DRIFT] the public declarations of {targetModule} are {pub}"
  let mut seen : NameSet := {}
  for n in audited do
    unless (env.find? n).isSome do throwError "declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a ↦ !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
    seen := seen ++ .ofList axs.toList
  logInfo m!"bf scattered silver regression guard: OK (applied: thin implies back-and-forth \
    scattered, the iff in both directions and the below-continuum form for an arbitrary \
    countable relational Language.\{u, v}; concretely, every pure-set sentence has fewer than \
    continuum many classes, hence back-and-forth scattered models, hence is thin; exact \
    import closure ({ilModules.length} InfinitaryLogic modules) without \
    Descriptive.ScatteredCounting or Scott.IsolatingLevel; axioms reported for the \
    {audited.length} audited declarations: {seen.toList}, all standard)"
