/-
Regression guard for the witnessed Morley counting theorems and the per-level Silver step
(`InfinitaryLogic/Conditional/MorleyPerfect.lean`).

* **Statement pins.**  The four previously exported theorems, `morley_counting_coded_or_perfect`,
  `counting_fin_models_countable_or_perfect`, `morley_counting_or_perfect` and
  `morley_counting_or_perfect_cardinal`, and the per-level step
  `Sentenceω.countable_bfClasses_of_isThinOnNatModels` are restated here as `pin_*` theorems
  proved by the originals.  What is compared: each original's type must equal its copy's as an
  expression up to binder names and normalization of universe levels, with the same universe
  parameters (`[STATEMENT DRIFT]` otherwise), and the binder kinds (explicit, implicit,
  instance-implicit, strict-implicit) along the `∀`-telescope must agree (`[BINDER DRIFT]`
  otherwise; expression equality alone ignores them).  A change of statement or of binder kinds
  therefore has to change the copy in this file too.  Negative control (`[BINDER CONTROL]`):
  `binderControl_morley_counting_coded_or_perfect` restates `morley_counting_coded_or_perfect`
  with `{φ}` in place of `(φ)`; expression equality accepts it, and the binder-kind comparison
  must reject it.
* **The per-level step, applied.**  Generically, for an arbitrary relational `Language.{u, v}`
  with countably many relation symbols and an arbitrary thin sentence, including its composition
  with the Scott-height bound `mk_isoSetoid_quotient_le_aleph_one`; and to a thin class: in the
  pure-set language (one code, universes `{1, 2}`) every sentence is thin, so every level has
  countably many back-and-forth classes.
* **Thinness is needed (negative control).**  Generically, a sentence with a perfect set of
  pairwise non-isomorphic models has some level `η < ω₁` with uncountably many back-and-forth
  classes (by the converse `Sentenceω.isThinOnNatModels_of_bfScattered`), so the step is an
  equivalence.  Concretely, in the language with countably many unary relation symbols, the
  models of `⊤` are all codes, they carry a Cantor antichain and hence a perfect set of pairwise
  non-isomorphic models, and level `1` has uncountably many classes, shown directly from the
  Cantor family and not through the lemmas under test.
* **One entry point for Silver at the `ℕ` tier (checked positively).**  The proof cone of the
  step contains `silver_countable_or_cantorAntichain` and `silver_core_polish`, and the cones of
  the three `ℕ`-tier theorems contain the step.  Within `Conditional.MorleyPerfect`, the public
  declarations whose own proof (the declaration and the auxiliary declarations of the module it
  reaches, but no other public declaration) mentions a form of Silver's theorem
  (`silver_countable_or_cantorAntichain`, `silver_countable_or_cantorAntichain_of_isClosed` or
  `silver_core_polish`) are exactly the step and the `Fin n`-tier theorem
  `counting_fin_models_countable_or_perfect`, which applies Silver to isomorphism itself
  (`[DUPLICATED STEP]` otherwise).
* **Import closure unchanged.**  The `InfinitaryLogic` closure of `Conditional.MorleyPerfect` has
  exactly 51 modules, as before the step was extracted (`[CLOSURE DRIFT]` otherwise).
* **Standard axioms** (`propext`, `Classical.choice`, `Quot.sound`) for the five declarations and
  the declarations listed in `guardDecls`; the remaining helpers of this guard (`uR`, `symIdx`,
  `continuous_cantorCode`, `not_countable_cantor`) are not listed and are covered indirectly,
  through the axioms of `thinness_needed_regression`, whose proof uses them.  The OK line is
  printed only after all checks.

Run with: lake env lean scripts/check_morley_perfect_regressions.lean
-/
import InfinitaryLogic.Conditional.MorleyPerfect
import InfinitaryLogic.Descriptive.BFScatteredSentence

open Lean FirstOrder FirstOrder.Language Cardinal Set

universe u v

noncomputable section

namespace MorleyPerfectRegressions

/-! ### Statement pins: copies compared below by expression and by binder kinds -/

theorem pin_morley_counting_coded_or_perfect {L : Language.{u, v}} [L.IsRelational]
    [Countable (Σ l, L.Relations l)] (φ : L.Sentenceω) :
    #(Quotient (isoSetoid φ)) ≤ Cardinal.aleph 1 ∨
      φ.HasPerfectSetOfPairwiseNonisomorphicNatModels :=
  morley_counting_coded_or_perfect φ

theorem pin_counting_fin_models_countable_or_perfect {L : Language.{u, v}} [L.IsRelational]
    [Countable (Σ l, L.Relations l)] (φ : L.Sentenceω) (n : ℕ) :
    #(Quotient (isoSetoidOn φ n)) ≤ ℵ₀ ∨
      φ.HasPerfectSetOfPairwiseNonisomorphicFinModels n :=
  counting_fin_models_countable_or_perfect φ n

theorem pin_morley_counting_or_perfect {L : Language.{u, v}} [L.IsRelational]
    [Countable (Σ l, L.Relations l)] (φ : L.Sentenceω) :
    #(AllCodedIsoClasses φ) ≤ Cardinal.aleph 1 ∨
      φ.HasPerfectSetOfPairwiseNonisomorphicNatModels ∨
      ∃ n, φ.HasPerfectSetOfPairwiseNonisomorphicFinModels n :=
  morley_counting_or_perfect φ

theorem pin_morley_counting_or_perfect_cardinal {L : Language.{u, v}} [L.IsRelational]
    [Countable (Σ l, L.Relations l)] (φ : L.Sentenceω) :
    #(AllCodedIsoClasses φ) ≤ Cardinal.aleph 1 ∨
      #(AllCodedIsoClasses φ) = Cardinal.continuum :=
  morley_counting_or_perfect_cardinal φ

theorem pin_countable_bfClasses_of_isThinOnNatModels {L : Language.{u, v}} [L.IsRelational]
    [Countable (Σ l, L.Relations l)] {φ : L.Sentenceω} (h : φ.IsThinOnNatModels) :
    ∀ η : Ordinal.{0}, η < Ordinal.omega 1 → Countable (Quotient (bfEquivSetoid φ η)) :=
  Sentenceω.countable_bfClasses_of_isThinOnNatModels h

/-- **Binder-kind control**: `morley_counting_coded_or_perfect` with its explicit `(φ)` flipped to
`{φ}`.  Its type is the original's up to binder kinds only; the comparison below must flag it. -/
theorem binderControl_morley_counting_coded_or_perfect {L : Language.{u, v}} [L.IsRelational]
    [Countable (Σ l, L.Relations l)] {φ : L.Sentenceω} :
    #(Quotient (isoSetoid φ)) ≤ Cardinal.aleph 1 ∨
      φ.HasPerfectSetOfPairwiseNonisomorphicNatModels :=
  morley_counting_coded_or_perfect φ

/-! ### The per-level step, applied -/

/-- **Generic**: a thin sentence has countably many classes at every level, and with the
Scott-height bound at most `ℵ₁` isomorphism classes; and the step is an equivalence, its converse
being `Sentenceω.isThinOnNatModels_of_bfScattered`. -/
theorem generic_regression {L : Language.{u, v}} [L.IsRelational]
    [Countable (Σ l, L.Relations l)] (φ : L.Sentenceω) :
    (φ.IsThinOnNatModels → ∀ η : Ordinal.{0}, η < Ordinal.omega 1 →
        Countable (Quotient (bfEquivSetoid φ η))) ∧
      (φ.IsThinOnNatModels → #(Quotient (isoSetoid φ)) ≤ Cardinal.aleph 1) ∧
      (φ.IsThinOnNatModels ↔ ∀ η : Ordinal.{0}, η < Ordinal.omega 1 →
        Countable (Quotient (bfEquivSetoid φ η))) := by
  refine ⟨Sentenceω.countable_bfClasses_of_isThinOnNatModels, fun h ↦ ?_,
    ⟨Sentenceω.countable_bfClasses_of_isThinOnNatModels,
      Sentenceω.isThinOnNatModels_of_bfScattered⟩⟩
  refine mk_isoSetoid_quotient_le_aleph_one φ fun η hη ↦ ?_
  have := Sentenceω.countable_bfClasses_of_isThinOnNatModels h η hη
  exact Cardinal.mk_le_aleph0

/-- **Thinness is needed, generically**: a perfect set of pairwise non-isomorphic models forces
uncountably many classes at some level `η < ω₁`. -/
theorem generic_thinness_needed {L : Language.{u, v}} [L.IsRelational]
    [Countable (Σ l, L.Relations l)] {φ : L.Sentenceω}
    (hp : φ.HasPerfectSetOfPairwiseNonisomorphicNatModels) :
    ∃ η : Ordinal.{0}, η < Ordinal.omega 1 ∧ ¬ Countable (Quotient (bfEquivSetoid φ η)) := by
  by_contra hne
  push Not at hne
  exact Sentenceω.isThinOnNatModels_of_bfScattered (fun η hη ↦ hne η hη) hp

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

/-- **A thin class**: every pure-set sentence is thin (a perfect set would give continuum many
isomorphism classes, but there is at most one), so the step gives countably many classes at
every level. -/
theorem pureSet_regression (φ : pureLang.Sentenceω) :
    φ.IsThinOnNatModels ∧ ∀ η : Ordinal.{0}, η < Ordinal.omega 1 →
      Countable (Quotient (bfEquivSetoid φ η)) := by
  have hthin : φ.IsThinOnNatModels := fun hp ↦
    (Sentenceω.HasPerfectSetOfPairwiseNonisomorphicNatModels.continuum_le hp).not_gt
      ((Cardinal.le_one_iff_subsingleton.mpr inferInstance).trans_lt
        (by simpa using Cardinal.nat_lt_continuum 1))
  exact ⟨hthin, Sentenceω.countable_bfClasses_of_isThinOnNatModels hthin⟩

/-! ### Negative control: countably many unary symbols -/

/-- Countably many unary relation symbols, nothing else. -/
def unaryLang : Language.{0, 0} where
  Functions _ := Empty
  Relations l := { _k : ℕ // l = 1 }

instance : unaryLang.IsRelational := fun _ ↦ inferInstanceAs (IsEmpty Empty)

instance : Countable (Σ l, unaryLang.Relations l) :=
  inferInstanceAs (Countable (Σ l : ℕ, { _k : ℕ // l = 1 }))

/-- The `k`-th unary symbol. -/
def uR (k : ℕ) : unaryLang.Relations 1 := ⟨k, rfl⟩

/-- The index of a symbol. -/
def symIdx (R : Σ l, unaryLang.Relations l) : ℕ := (R.2 : { _k : ℕ // R.1 = 1 }).1

/-- The Cantor family: in `cantorCode x` the `k`-th symbol holds everywhere if `x k` and
nowhere otherwise. -/
def cantorCode (x : ℕ → Bool) : StructureSpace unaryLang := fun q ↦ x (symIdx q.1)

theorem continuous_cantorCode : Continuous cantorCode :=
  continuous_pi fun q ↦ continuous_apply (symIdx q.1)

/-- Level `1` separates distinct members of the Cantor family. -/
theorem not_codeBFEquiv_one {x y : ℕ → Bool} (hxy : x ≠ y) :
    ¬ CodeBFEquiv 1 (cantorCode x) (cantorCode y) := by
  intro h
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hxy
  have h1 : (1 : Ordinal.{0}) = Order.succ 0 := by simp
  rw [CodeBFEquiv, h1] at h
  obtain ⟨n', h0⟩ := @BFEquiv.forth unaryLang ℕ (cantorCode x).toStructure ℕ
    (cantorCode y).toStructure _ _ _ _ h 0
  have hat := (@BFEquiv.zero unaryLang ℕ (cantorCode x).toStructure ℕ (cantorCode y).toStructure
    _ _ _).mp h0 (AtomicIdx.rel (uR k) fun _ ↦ 0)
  exact hk (Bool.eq_iff_iff.mpr hat)

/-- Distinct members of the Cantor family are not isomorphic. -/
theorem cantorCode_noniso {x y : ℕ → Bool} (hxy : x ≠ y) :
    ¬ (structureIsoSetoid unaryLang).r (cantorCode x) (cantorCode y) := by
  rintro ⟨e⟩
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hxy
  have := @Language.Equiv.map_rel unaryLang ℕ ℕ (cantorCode x).toStructure
    (cantorCode y).toStructure e 1 (uR k) (fun _ ↦ 0)
  exact hk (Bool.eq_iff_iff.mpr this.symm)

/-- Every code is a model of `⊤`. -/
theorem mem_modelsOf_top (c : StructureSpace unaryLang) :
    c ∈ ModelsOf (⊤ : unaryLang.Sentenceω) := by
  let := c.toStructure
  exact BoundedFormulaω.realize_top.mpr trivial

/-- Cantor space is uncountable. -/
theorem not_countable_cantor : ¬ Countable (ℕ → Bool) := by
  rw [← Cardinal.mk_le_aleph0_iff, not_le]
  simp [Cardinal.aleph0_lt_continuum]

/-- **Negative control**: `⊤` in the countably-many-unary-symbols language has a perfect set of
pairwise non-isomorphic models, so it is not thin, and level `1 < ω₁` has uncountably many
back-and-forth classes; the last conjunct is proved directly from the Cantor family, not
through the lemmas under test. -/
theorem thinness_needed_regression :
    (⊤ : unaryLang.Sentenceω).HasPerfectSetOfPairwiseNonisomorphicNatModels ∧
      ¬ (⊤ : unaryLang.Sentenceω).IsThinOnNatModels ∧
      (1 : Ordinal.{0}) < Ordinal.omega 1 ∧
      ¬ Countable (Quotient (bfEquivSetoid (⊤ : unaryLang.Sentenceω) 1)) := by
  have hp : (⊤ : unaryLang.Sentenceω).HasPerfectSetOfPairwiseNonisomorphicNatModels :=
    Sentenceω.hasPerfectSet_of_ambient_cantorAntichain
      ⟨cantorCode, continuous_cantorCode, fun x ↦ mem_modelsOf_top _,
        fun _ _ h ↦ cantorCode_noniso h⟩
  refine ⟨hp, fun h ↦ h hp, Ordinal.one_lt_omega0.trans Ordinal.omega0_lt_omega_one, ?_⟩
  intro _
  refine not_countable_cantor (Function.Injective.countable
    (f := fun x ↦ (⟦⟨cantorCode x, mem_modelsOf_top _⟩⟧ :
      Quotient (bfEquivSetoid (⊤ : unaryLang.Sentenceω) 1))) fun x y hxy ↦ ?_)
  by_contra hne
  exact not_codeBFEquiv_one hne (Quotient.exact hxy)

end MorleyPerfectRegressions

end

open MorleyPerfectRegressions

/-! ### Statement, cone, closure and axiom checks -/

/-- The module under test. -/
def targetModule : Name := `InfinitaryLogic.Conditional.MorleyPerfect

/-- The per-level Silver step. -/
def step : Name := `FirstOrder.Language.Sentenceω.countable_bfClasses_of_isThinOnNatModels

/-- Each pinned declaration with its copy. -/
def pins : List (Name × Name) :=
  [(`FirstOrder.Language.morley_counting_coded_or_perfect,
      `MorleyPerfectRegressions.pin_morley_counting_coded_or_perfect),
   (`FirstOrder.Language.counting_fin_models_countable_or_perfect,
      `MorleyPerfectRegressions.pin_counting_fin_models_countable_or_perfect),
   (`FirstOrder.Language.morley_counting_or_perfect,
      `MorleyPerfectRegressions.pin_morley_counting_or_perfect),
   (`FirstOrder.Language.morley_counting_or_perfect_cardinal,
      `MorleyPerfectRegressions.pin_morley_counting_or_perfect_cardinal),
   (step, `MorleyPerfectRegressions.pin_countable_bfClasses_of_isThinOnNatModels)]

/-- Binder-kind controls: a pinned declaration with a copy differing in one binder kind only. -/
def binderControls : List (Name × Name) :=
  [(`FirstOrder.Language.morley_counting_coded_or_perfect,
      `MorleyPerfectRegressions.binderControl_morley_counting_coded_or_perfect)]

/-- The `ℕ`-tier theorems, whose cones must contain the step. -/
def natTier : List Name :=
  [`FirstOrder.Language.morley_counting_coded_or_perfect,
   `FirstOrder.Language.morley_counting_or_perfect,
   `FirstOrder.Language.morley_counting_or_perfect_cardinal]

/-- The Silver chain, which the step's cone must contain. -/
def silverChain : List Name := [`silver_countable_or_cantorAntichain, `silver_core_polish]

/-- Silver's theorem in each of its three forms: for a Borel subset, for a closed subset, and the
Polish core.  A declaration mentioning any of them applies Silver directly. -/
def silverFamily : List Name :=
  [`silver_countable_or_cantorAntichain, `silver_countable_or_cantorAntichain_of_isClosed,
   `silver_core_polish]

/-- The declarations of the module allowed to apply Silver directly: the step, and the `Fin n`
tier, which applies Silver to isomorphism itself. -/
def directSilver : List Name :=
  [step, `FirstOrder.Language.counting_fin_models_countable_or_perfect]

/-- The guard's own declarations whose axioms are audited.  The helpers `uR`, `symIdx`,
`continuous_cantorCode` and `not_countable_cantor` are covered indirectly, through
`thinness_needed_regression`. -/
def guardDecls : List Name :=
  [`pin_morley_counting_coded_or_perfect, `pin_counting_fin_models_countable_or_perfect,
   `pin_morley_counting_or_perfect, `pin_morley_counting_or_perfect_cardinal,
   `pin_countable_bfClasses_of_isThinOnNatModels,
   `binderControl_morley_counting_coded_or_perfect, `generic_regression,
   `generic_thinness_needed, `pureLang, `pureSet_regression, `unaryLang, `cantorCode,
   `not_codeBFEquiv_one, `cantorCode_noniso, `mem_modelsOf_top,
   `thinness_needed_regression].map (`MorleyPerfectRegressions ++ ·)

/-- The standard axioms. -/
def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

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

run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? targetModule
    | throwError "module {targetModule} is not in the environment"
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
  unless env.getModuleIdxFor? step == some idx do
    throwError "[HOME DRIFT] {step} is not declared in {targetModule}"
  -- CONES (positive): the step reaches Silver, and the `ℕ`-tier theorems reach the step
  for d in silverChain do
    unless (env.find? d).isSome do throwError "[VACUOUS] {d} is not in the environment"
  let stepCone ← match cone env step with
    | .ok c => pure c
    | .error e => throwError e
  for d in silverChain do
    unless stepCone.contains d do
      throwError "[DEPENDENCY DRIFT] {d} is not in the cone of {step}"
  for n in natTier do
    let c ← match cone env n with
      | .ok c => pure c
      | .error e => throwError e
    unless c.contains step do
      throwError "[DEPENDENCY DRIFT] {step} is not in the cone of {n}"
  -- ONE ENTRY POINT: the declarations of the module applying Silver directly
  let decls := (env.header.moduleData[idx.toNat]!).constNames.toList.filter fun n ↦
    !n.isInternalDetail
  for d in silverFamily do
    unless (env.find? d).isSome do throwError "[VACUOUS] {d} is not in the environment"
  let direct := decls.filter fun n ↦ silverFamily.any (localRefs env n).contains
  unless direct.all directSilver.contains && directSilver.all direct.contains do
    throwError "[DUPLICATED STEP] the declarations of {targetModule} applying a form of \
      Silver's theorem directly are {direct}, not {directSilver}"
  -- CLOSURE: unchanged by the extraction
  let ilModules := (importClosure env targetModule).toList.filter fun m ↦
    (`InfinitaryLogic).isPrefixOf m
  unless ilModules.length == 51 do
    throwError "[CLOSURE DRIFT] expected 51 InfinitaryLogic modules in the closure of \
      {targetModule}, found {ilModules.length}: {ilModules}"
  -- AXIOMS
  let audited := pins.map (·.1) ++ guardDecls
  let mut seen : NameSet := {}
  for n in audited do
    unless (env.find? n).isSome do throwError "declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a ↦ !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
    seen := seen ++ .ofList axs.toList
  logInfo m!"morley perfect regression guard: OK (types of the {pins.length} pinned \
    declarations equal to their copies up to binder names and level normalization, with the \
    same universe parameters and binder kinds, the binder-kind comparison flagging a \
    (φ)-to-\{φ} control that expression equality accepts; the per-level step applied generically, \
    composed with the Scott-height bound, as an equivalence with its converse, and to every \
    pure-set sentence; thinness needed: a perfect set forces an uncountable level generically, \
    and concretely for ⊤ over countably many unary symbols at level 1; Silver chain in the \
    step's cone and the step in the cones of the {natTier.length} ℕ-tier theorems; the \
    declarations applying a form of Silver's theorem directly are exactly {directSilver}; \
    import closure \
    {ilModules.length} InfinitaryLogic modules, unchanged; axioms reported for the \
    {audited.length} audited declarations: {seen.toList}, all standard)"
