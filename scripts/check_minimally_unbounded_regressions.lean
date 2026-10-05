/-
Regression guard for minimally unbounded classes for a rank on codes
(`InfinitaryLogic/Descriptive/MinimallyUnbounded.lean`).

Every public declaration of the module is *applied*, not only listed for its axioms.

* **Generic applications.**  `MinimallyUnboundedOn`, `Sentenceω.MinimallyUnbounded` and the
  literal form `Sentenceω.minimallyUnbounded_iff_inf` for an arbitrary relational
  `Language.{u, v}` and an arbitrary map `ρ`, with no countability and no isolating rank in
  scope; `MinimallyUnboundedOn.bounded_bfClass_or_compl` and
  `MinimallyUnboundedOn.exists_bfClass_compl_bounded` for countably many relation symbols and an
  arbitrary `ρ`, with no isolating rank and no bound `ρ < ω₁` in scope; the four
  rank-independence statements (`IsIsolatingRank.boundedRankOn_iff_countable`,
  `boundedRankOn_iff_of_isIsolatingRank`, `minimallyUnboundedOn_iff_minimallyUncountableOn`,
  `minimallyUnboundedOn_iff_of_isIsolatingRank`) for any two isolating ranks on any
  back-and-forth scattered class, with no countability in scope.
* **At the landed instance.**  For countably many symbols, the rank-independence statements
  between `codeStabilizationOrdinal` (the instance) and the shifted rank
  `Order.succ ∘ codeStabilizationOrdinal` (isolating by `of_le`, as in
  `check_scattered_counting_regressions.lean`), which differs from it at every code.
* **A concrete class.**  In the pure-set language (one code, universes `{1, 2}`), the set of
  all codes is back-and-forth scattered and meets one isomorphism class; the constant rank `5`
  (built from the three fields) and `codeStabilizationOrdinal` are both bounded on it, agree
  through `boundedRankOn_iff_of_isIsolatingRank`, and no sentence of that language is minimally
  unbounded for either rank.
* **Not exhibited.**  No minimally unbounded class is exhibited, and no class with two isolating
  ranks that disagree on boundedness in the absence of `BFScattered` (that necessity example is
  a recorded follow-up; the generic signature checks do not replace it).
* **Signature checks.**  The types of all public declarations of the module are inspected: an
  instance `Countable (Σ l, _)` occurs in exactly the two statements about back-and-forth
  classes, and `IsIsolatingRank` in exactly the four rank-independence statements, each of which
  also takes `BFScattered` explicitly (`[COUNTABILITY DRIFT]`, `[RANK DRIFT]`); every public
  declaration is classified.
* **Exact import closure.**  The `InfinitaryLogic` closure of `Descriptive.MinimallyUnbounded` is
  exactly `allowedClosure` (40 modules: the closures of `Descriptive.ScatteredCounting` (35) and
  `Descriptive.MinimallyUncountable` (33), overlapping in 29, plus the module), and it is checked
  to be that union.  `Karp.PotentialIso` is in it, through `ScatteredCounting` and
  `Scott.Sentence`; it is the only `Karp` module.  The proofs of the module do not use it (see
  `check_minimally_unbounded_deps.lean`).  The closure contains no `ModelTheory`, `Methods`,
  `Admissible`, `Conditional`, `ScottProcess` or `WIP` module, not
  `Descriptive.BFScatteredSentence`, and no module whose name contains `LopezEscobar` or
  `SmallVocabulary` (`[BROAD CONE]`).
* **Standard axioms** for every declaration of the module (enumerated from the environment) and
  every declaration of this guard.  The OK line is printed only after the closure and axiom
  checks.

Run with: lake env lean scripts/check_minimally_unbounded_regressions.lean
-/
import InfinitaryLogic.Descriptive.MinimallyUnbounded

open Lean FirstOrder FirstOrder.Language Set

universe u v

noncomputable section

namespace MinimallyUnboundedRegressions

/-! ### Generic applications -/

/-- **The definitions and the literal form**, for an arbitrary relational language and an
arbitrary map `ρ`, with no countability and no isolating rank. -/
theorem generic_definition_regression {L : Language.{u, v}} [L.IsRelational]
    (ρ : StructureSpace L → Ordinal.{0}) (K : Set (StructureSpace L)) (Θ : L.Sentenceω) :
    (MinimallyUnboundedOn ρ K ↔ UnboundedRankOn ρ K ∧
      ∀ θ : L.Sentenceω, BoundedRankOn ρ (K ∩ ModelsOf θ) ∨ BoundedRankOn ρ (K \ ModelsOf θ)) ∧
      (Θ.MinimallyUnbounded ρ ↔ MinimallyUnboundedOn ρ (ModelsOf Θ)) ∧
      (Θ.MinimallyUnbounded ρ ↔ UnboundedRankOn ρ (ModelsOf Θ) ∧
        ∀ θ : L.Sentenceω, BoundedRankOn ρ (ModelsOf (Θ ⊓ θ)) ∨
          BoundedRankOn ρ (ModelsOf (Θ ⊓ θ.not))) :=
  ⟨Iff.rfl, Iff.rfl, Sentenceω.minimallyUnbounded_iff_inf Θ⟩

/-- **The back-and-forth classes**, for countably many symbols and an arbitrary `ρ`: no isolating
rank and no bound `ρ < ω₁` in scope. -/
theorem generic_bfClass_regression {L : Language.{u, v}} [L.IsRelational]
    [Countable (Σ l, L.Relations l)] {ρ : StructureSpace L → Ordinal.{0}}
    {K : Set (StructureSpace L)} (h : MinimallyUnboundedOn ρ K) (c : StructureSpace L)
    {α : Ordinal.{0}} (hα : α < Ordinal.omega 1)
    (hKα : Countable (Quotient ((codeBFEquivSetoid L α).comap
      (Subtype.val : K → StructureSpace L)))) :
    (BoundedRankOn ρ (K ∩ {d | CodeBFEquiv α c d}) ∨
      BoundedRankOn ρ (K \ {d | CodeBFEquiv α c d})) ∧
      ∃ a ∈ K, UnboundedRankOn ρ (K ∩ {d | CodeBFEquiv α a d}) ∧
        BoundedRankOn ρ (K \ {d | CodeBFEquiv α a d}) :=
  ⟨h.bounded_bfClass_or_compl c hα, h.exists_bfClass_compl_bounded hα hKα⟩

/-- **Rank independence for any two isolating ranks** on any back-and-forth scattered class, with
no countability in scope. -/
theorem generic_rankIndependence_regression {L : Language.{u, v}} [L.IsRelational]
    {ρ ρ' : StructureSpace L → Ordinal.{0}} (hρ : IsIsolatingRank ρ) (hρ' : IsIsolatingRank ρ')
    {K : Set (StructureSpace L)} (hK : BFScattered K) :
    (BoundedRankOn ρ K ↔ (Quotient.mk (structureIsoSetoid L) '' K).Countable) ∧
      (BoundedRankOn ρ K ↔ BoundedRankOn ρ' K) ∧
      (MinimallyUnboundedOn ρ K ↔ MinimallyUncountableOn K) ∧
      (MinimallyUnboundedOn ρ K ↔ MinimallyUnboundedOn ρ' K) :=
  ⟨hρ.boundedRankOn_iff_countable hK, boundedRankOn_iff_of_isIsolatingRank hρ hρ' hK,
    minimallyUnboundedOn_iff_minimallyUncountableOn hρ hK,
    minimallyUnboundedOn_iff_of_isIsolatingRank hρ hρ' hK⟩

/-! ### At the landed instance -/

/-- The shifted rank `Order.succ ∘ codeStabilizationOrdinal`, isolating by `of_le`. -/
theorem shifted_isIsolatingRank {L : Language.{u, v}} [L.IsRelational]
    [Countable (Σ l, L.Relations l)] :
    IsIsolatingRank (fun c : StructureSpace L ↦ Order.succ (codeStabilizationOrdinal c)) :=
  isIsolatingRank_codeStabilizationOrdinal.of_le (fun _ ↦ Order.le_succ _)
    (fun _ _ h ↦ by rw [codeStabilizationOrdinal_congr h])
    (fun c ↦ (Cardinal.isSuccLimit_omega 1).succ_lt
      (isIsolatingRank_codeStabilizationOrdinal.lt_omega1 c))

/-- **Rank independence between the instance and the shifted rank**, which differ at every
code. -/
theorem instance_regression {L : Language.{u, v}} [L.IsRelational]
    [Countable (Σ l, L.Relations l)] {K : Set (StructureSpace L)} (hK : BFScattered K) :
    (∀ c : StructureSpace L,
      Order.succ (codeStabilizationOrdinal c) ≠ codeStabilizationOrdinal c) ∧
      (BoundedRankOn codeStabilizationOrdinal K ↔
        BoundedRankOn (fun c ↦ Order.succ (codeStabilizationOrdinal c)) K) ∧
      (MinimallyUnboundedOn codeStabilizationOrdinal K ↔
        MinimallyUnboundedOn (fun c ↦ Order.succ (codeStabilizationOrdinal c)) K) ∧
      (MinimallyUnboundedOn codeStabilizationOrdinal K ↔ MinimallyUncountableOn K) :=
  ⟨fun _ ↦ (Order.lt_succ _).ne',
    boundedRankOn_iff_of_isIsolatingRank isIsolatingRank_codeStabilizationOrdinal
      shifted_isIsolatingRank hK,
    minimallyUnboundedOn_iff_of_isIsolatingRank isIsolatingRank_codeStabilizationOrdinal
      shifted_isIsolatingRank hK,
    minimallyUnboundedOn_iff_minimallyUncountableOn isIsolatingRank_codeStabilizationOrdinal hK⟩

/-! ### A concrete class: the pure-set language -/

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

/-- The constant rank `5`, built from the three fields of the contract. -/
theorem constant_rank : IsIsolatingRank (fun _ : StructureSpace pureLang ↦ (5 : Ordinal.{0})) :=
  { iso_invariant := fun _ _ _ ↦ rfl
    lt_omega1 := fun _ ↦ (Ordinal.natCast_lt_omega0 5).trans Ordinal.omega0_lt_omega_one
    isolates := fun c d _ ↦ Subsingleton.elim c d ▸ (structureIsoSetoid pureLang).iseqv.refl c }

/-- The set of all codes meets one isomorphism class. -/
theorem pure_classes_countable :
    (Quotient.mk (structureIsoSetoid pureLang) ''
      (univ : Set (StructureSpace pureLang))).Countable :=
  (countable_singleton (Quotient.mk (structureIsoSetoid pureLang) fun _ ↦ false)).mono
    (by rintro _ ⟨x, -, rfl⟩; exact congrArg _ (Subsingleton.elim _ _))

/-- **The pure-set language**: the set of all codes is back-and-forth scattered; the constant
rank and the instance are bounded on it and agree; no sentence is minimally unbounded for either
rank. -/
theorem pure_regression :
    BFScattered (univ : Set (StructureSpace pureLang)) ∧
      BoundedRankOn (fun _ : StructureSpace pureLang ↦ (5 : Ordinal.{0})) univ ∧
      BoundedRankOn (codeStabilizationOrdinal (L := pureLang)) univ ∧
      (BoundedRankOn (fun _ : StructureSpace pureLang ↦ (5 : Ordinal.{0})) univ ↔
        BoundedRankOn (codeStabilizationOrdinal (L := pureLang)) univ) ∧
      ∀ Θ : pureLang.Sentenceω,
        ¬ Θ.MinimallyUnbounded (fun _ ↦ (5 : Ordinal.{0})) ∧
          ¬ Θ.MinimallyUnbounded (codeStabilizationOrdinal (L := pureLang)) := by
  have hK : BFScattered (univ : Set (StructureSpace pureLang)) :=
    (concentratedAtBFLevels_of_countable pure_classes_countable).bfScattered
  have h5 := (constant_rank.boundedRankOn_iff_countable hK).mpr pure_classes_countable
  have hcs := (isIsolatingRank_codeStabilizationOrdinal.boundedRankOn_iff_countable hK).mpr
    pure_classes_countable
  refine ⟨hK, h5, hcs, boundedRankOn_iff_of_isIsolatingRank constant_rank
    isIsolatingRank_codeStabilizationOrdinal hK, fun Θ ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩⟩
  · exact unboundedRankOn_iff_not_boundedRankOn.mp h.1 (h5.mono (subset_univ _))
  · exact unboundedRankOn_iff_not_boundedRankOn.mp h.1 (hcs.mono (subset_univ _))

end MinimallyUnboundedRegressions

end

/-! ### Signature checks -/

open MinimallyUnboundedRegressions

/-- Prefix a list of names with `FirstOrder.Language`. -/
def fol (l : List Name) : List Name := l.map (`FirstOrder.Language ++ ·)

/-- The module under test. -/
def targetModule : Name := `InfinitaryLogic.Descriptive.MinimallyUnbounded

/-- The public declarations with neither countably many symbols nor an isolating rank. -/
def plainDecls : List Name :=
  fol [`MinimallyUnboundedOn, `Sentenceω.MinimallyUnbounded, `Sentenceω.minimallyUnbounded_iff_inf]

/-- The public declarations assuming countably many symbols (through `scottSentenceAt`), with
no isolating rank. -/
def countabilityUsing : List Name :=
  fol [`MinimallyUnboundedOn.bounded_bfClass_or_compl,
    `MinimallyUnboundedOn.exists_bfClass_compl_bounded]

/-- The public declarations assuming an isolating rank and `BFScattered`, with no countability. -/
def rankUsing : List Name :=
  fol [`IsIsolatingRank.boundedRankOn_iff_countable, `boundedRankOn_iff_of_isIsolatingRank,
    `minimallyUnboundedOn_iff_minimallyUncountableOn, `minimallyUnboundedOn_iff_of_isIsolatingRank]

run_cmd do
  let env ← getEnv
  let isCountableSigma (e : Expr) : Bool :=
    e.isAppOfArity ``Countable 1 && e.appArg!.isAppOf ``Sigma
  let mentions (n : Name) (p : Expr → Bool) : Elab.Command.CommandElabM Bool := do
    let some ci := env.find? n | throwError "declaration {n} not found"
    return (ci.type.find? p).isSome
  let isRank (e : Expr) : Bool := e.isAppOf ``FirstOrder.Language.IsIsolatingRank
  let isScattered (e : Expr) : Bool := e.isAppOf ``FirstOrder.Language.BFScattered
  for n in plainDecls ++ countabilityUsing ++ rankUsing do
    let c ← mentions n isCountableSigma
    unless c == countabilityUsing.contains n do
      throwError "[COUNTABILITY DRIFT] Countable (Σ l, _) in the type of {n}: {c}"
    let r ← mentions n isRank
    unless r == rankUsing.contains n do
      throwError "[RANK DRIFT] IsIsolatingRank in the type of {n}: {r}"
    if rankUsing.contains n then
      unless ← mentions n isScattered do
        throwError "[RANK DRIFT] the type of {n} does not take BFScattered"
  -- every public declaration of the module is classified
  let some idx := env.getModuleIdx? targetModule | throwError "module {targetModule} not found"
  let pub := (env.header.moduleData[idx.toNat]!).constNames.toList.filter fun n ↦
    !n.isInternalDetail && !(n.getString!.endsWith "congr_simp") && !isPrivateName n
  let classified := plainDecls ++ countabilityUsing ++ rankUsing
  let unclassified := pub.filter fun n ↦ !classified.contains n
  let absent := classified.filter fun n ↦ !pub.contains n
  unless unclassified.isEmpty && absent.isEmpty do
    throwError "[COUNTABILITY DRIFT] the public declarations of {targetModule} changed \
      (unclassified {unclassified}, not declared there {absent}); classify them"

/-! ### Exact import closure and axiom hygiene -/

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
  [`InfinitaryLogic.ModelTheory, `InfinitaryLogic.Methods, `InfinitaryLogic.Admissible,
   `InfinitaryLogic.Conditional, `InfinitaryLogic.ScottProcess, `InfinitaryLogic.WIP,
   `InfinitaryLogic.Descriptive.BFScatteredSentence]

/-- Substrings no module of the closure may contain. -/
def forbiddenSubstrings : List String := ["LopezEscobar", "SmallVocabulary"]

/-- The exact `InfinitaryLogic` import closure of `Descriptive.MinimallyUnbounded`.
`Karp.PotentialIso` enters through `Descriptive.ScatteredCounting` and `Scott.Sentence`. -/
def allowedClosure : List Name :=
  [`InfinitaryLogic.Util, `InfinitaryLogic.OrdinalUtil, `InfinitaryLogic.OrdinalCountability,
   `InfinitaryLogic.Topology.Perfect,
   `InfinitaryLogic.Lomega1omega.Syntax, `InfinitaryLogic.Lomega1omega.Semantics,
   `InfinitaryLogic.Lomega1omega.Operations, `InfinitaryLogic.Lomega1omega.OpenBoundsSemantics,
   `InfinitaryLogic.Lomega1omega.Theory, `InfinitaryLogic.Karp.PotentialIso,
   `InfinitaryLogic.Scott.AtomicDiagram, `InfinitaryLogic.Scott.BackAndForth,
   `InfinitaryLogic.Scott.Formula, `InfinitaryLogic.Scott.Sentence,
   `InfinitaryLogic.Scott.RefinementCount, `InfinitaryLogic.Scott.IsolatingLevel,
   `InfinitaryLogic.Scott.BFEquivRelabel,
   `InfinitaryLogic.Descriptive.StructureSpace, `InfinitaryLogic.Descriptive.Topology,
   `InfinitaryLogic.Descriptive.Measurable, `InfinitaryLogic.Descriptive.Polish,
   `InfinitaryLogic.Descriptive.GDeltaPolish, `InfinitaryLogic.Descriptive.ModelsOfGDelta,
   `InfinitaryLogic.Descriptive.SatisfactionBorel, `InfinitaryLogic.Descriptive.SatisfactionBorelOn,
   `InfinitaryLogic.Descriptive.ModelClassStandardBorel,
   `InfinitaryLogic.Descriptive.PerfectAntichain, `InfinitaryLogic.Descriptive.CantorAntichain,
   `InfinitaryLogic.Descriptive.StructureIsoSetoid, `InfinitaryLogic.Descriptive.BFEquivBorel,
   `InfinitaryLogic.Descriptive.KleeneBrouwer, `InfinitaryLogic.Descriptive.BFTree,
   `InfinitaryLogic.Descriptive.AnalyticTreeBoundedness,
   `InfinitaryLogic.Descriptive.AnalyticClosure, `InfinitaryLogic.Descriptive.BFSeparation,
   `InfinitaryLogic.Descriptive.BFScattered, `InfinitaryLogic.Descriptive.BFConcentration,
   `InfinitaryLogic.Descriptive.ScatteredCounting,
   `InfinitaryLogic.Descriptive.MinimallyUncountable,
   `InfinitaryLogic.Descriptive.MinimallyUnbounded]

/-- The guard's own declarations whose axioms are audited. -/
def guardDecls : List Name :=
  [`generic_definition_regression, `generic_bfClass_regression,
   `generic_rankIndependence_regression, `shifted_isIsolatingRank, `instance_regression,
   `pureLang, `constant_rank, `pure_classes_countable, `pure_regression].map
    (`MinimallyUnboundedRegressions ++ ·)

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
  let ilModules := ilClosure env targetModule
  let hits := ilModules.filter fun m ↦ forbiddenPrefixes.any (·.isPrefixOf m) ||
    forbiddenSubstrings.any fun s ↦ (m.toString.splitOn s).length ≠ 1
  unless hits.isEmpty do
    throwError "[BROAD CONE] the closure of {targetModule} reaches {hits}"
  checkExact targetModule ilModules allowedClosure
  unless ilModules.length == 40 do
    throwError "[CLOSURE DRIFT] expected 40 InfinitaryLogic modules, found {ilModules.length}"
  let parts := [`InfinitaryLogic.Descriptive.ScatteredCounting,
    `InfinitaryLogic.Descriptive.MinimallyUncountable]
  let sizes := parts.map fun p ↦ (ilClosure env p).length
  unless sizes == [35, 33] do
    throwError "[CLOSURE DRIFT] the closures of {parts} have sizes {sizes}, not [35, 33]"
  let union := (parts.foldl (fun s p ↦ s ++ .ofList (ilClosure env p)) ({} : NameSet)).insert
    targetModule
  checkExact targetModule ilModules union.toList
  -- Karp by import only, and only `Karp.PotentialIso`
  let karp := ilModules.filter (`InfinitaryLogic.Karp).isPrefixOf
  unless karp == [`InfinitaryLogic.Karp.PotentialIso] do
    throwError "[KARP DRIFT] the Karp modules of the closure are {karp}"
  -- axioms: every declaration of the module and the guard's declarations
  let enumerated := (env.header.moduleData[idx.toNat]!).constNames.toList
  let audited := enumerated ++ guardDecls
  for n in audited do
    unless (env.find? n).isSome do throwError "declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a ↦ !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo m!"minimally unbounded regression guard: OK (applied: the definitions and the literal \
    form for an arbitrary relational Language.\{u, v} and an arbitrary rank with no \
    countability or isolating rank; the two back-and-forth class statements for an arbitrary \
    rank with no isolating rank and no bound below ω₁; the four rank-independence statements \
    for any two isolating ranks on any BFScattered class with no countability; the same \
    between the instance and the shifted rank, which differ at every code; in the pure-set \
    language, the constant rank and the instance bounded and agreeing on all codes and no \
    sentence minimally unbounded; Countable (Σ l, _) in exactly the two back-and-forth class \
    statements and IsIsolatingRank (with BFScattered) in exactly the four rank-independence \
    statements, every public declaration classified; exact import closure \
    ({ilModules.length} modules, the union of ScatteredCounting and MinimallyUncountable plus \
    the module), Karp.PotentialIso its only Karp module (by import), no ModelTheory, Methods, \
    Admissible, Conditional, ScottProcess, WIP, BFScatteredSentence, LopezEscobar or \
    SmallVocabulary module; standard axioms for {audited.length} declarations; not exhibited: \
    a minimally unbounded class, and two isolating ranks disagreeing on boundedness without \
    BFScattered)"
