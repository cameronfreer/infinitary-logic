/-
Regression guard for uniform back-and-forth separation of analytic sets of non-isomorphic pairs
(`InfinitaryLogic/Descriptive/BFSeparation.lean`).

Every public theorem is *applied*, not only listed for its axioms.

* **Arbitrary universes, no countability.**  `exists_uniform_bfSeparation`,
  `exists_uniform_bfSeparation_forall_ge` and `exists_uniform_bfSeparation_of_analyticSets` are
  applied for an arbitrary relational `Language.{u, v}` with no countability instance in scope.
* **The empty set of pairs**, and the **pure-set language** (no symbols, in universes
  `{1, 2}`): every two codes are isomorphic there, so an isomorphism-free set of pairs is empty,
  and the theorem applies to it.
* **A closed set of pairs.**  In a language with one nullary relation symbol, the pairs whose
  first code makes the symbol true and whose second makes it false form a closed, hence
  analytic, set with no isomorphic pair; it is separated at one countable level, at every
  higher level (the monotone form), and at the successor of the separating level.
* **Two analytic sets.**  In a language with one unary relation symbol, `B` (the symbol holds
  everywhere, closed) and `C` (it fails somewhere, open) are analytic, and no element of `B` is
  isomorphic to an element of `C`.  The two-set form separates them at a countable level, and
  that level is at least `1`: the codes "holds everywhere" and "holds nowhere" lie in `B` and
  `C` and agree at level `0` (there is no nullary symbol), so the separation is not the empty
  tree's.
* **Standard axioms** for the headline declarations and the concrete regressions.
* **Minimal imports**: the module's `InfinitaryLogic` import closure is exactly the listed set;
  it contains `BFTree`, `AnalyticTreeBoundedness`, `KleeneBrouwer` and `StructureIsoSetoid`, and
  no module whose name contains a López–Escobar, invariant-separation, PC-class, well-order,
  tree-code, vocabulary, coding, interpolation, Henkin, Karp, methods or model-theory substring.

Run with: lake env lean scripts/check_bf_separation_regressions.lean
-/
import InfinitaryLogic.Descriptive.BFSeparation

open Lean FirstOrder FirstOrder.Language Descriptive KleeneBrouwer MeasureTheory Set

universe u v

noncomputable section

namespace BFSeparationRegressions

/-! ### Arbitrary universes, no countability -/

/-- The main theorem for an arbitrary relational language, with no countability. -/
theorem generic_regression {L : Language.{u, v}} [L.IsRelational]
    {A : Set (StructureSpace L × StructureSpace L)} (hA : AnalyticSet A)
    (hA_noniso : ∀ p ∈ A, ¬ (structureIsoSetoid L).r p.1 p.2) :
    ∃ α : Ordinal.{0}, α < Ordinal.omega 1 ∧ ∀ p ∈ A, ¬ CodeBFEquiv α p.1 p.2 :=
  exists_uniform_bfSeparation hA hA_noniso

/-- The monotone form for an arbitrary relational language, with no countability. -/
theorem generic_ge_regression {L : Language.{u, v}} [L.IsRelational]
    {A : Set (StructureSpace L × StructureSpace L)} (hA : AnalyticSet A)
    (hA_noniso : ∀ p ∈ A, ¬ (structureIsoSetoid L).r p.1 p.2) :
    ∃ α : Ordinal.{0}, α < Ordinal.omega 1 ∧
      ∀ β, α ≤ β → ∀ p ∈ A, ¬ CodeBFEquiv β p.1 p.2 :=
  exists_uniform_bfSeparation_forall_ge hA hA_noniso

/-- The two-set form for an arbitrary relational language, with no countability. -/
theorem generic_two_set_regression {L : Language.{u, v}} [L.IsRelational]
    {B C : Set (StructureSpace L)} (hB : AnalyticSet B) (hC : AnalyticSet C)
    (hdisj : ∀ x ∈ B, ∀ y ∈ C, ¬ (structureIsoSetoid L).r x y) :
    ∃ α : Ordinal.{0}, α < Ordinal.omega 1 ∧ ∀ x ∈ B, ∀ y ∈ C, ¬ CodeBFEquiv α x y :=
  exists_uniform_bfSeparation_of_analyticSets hB hC hdisj

/-! ### The empty set of pairs and the pure-set language -/

/-- The empty set of pairs, in any relational language. -/
theorem empty_regression {L : Language.{u, v}} [L.IsRelational] :
    ∃ α : Ordinal.{0}, α < Ordinal.omega 1 ∧
      ∀ p ∈ (∅ : Set (StructureSpace L × StructureSpace L)), ¬ CodeBFEquiv α p.1 p.2 :=
  exists_uniform_bfSeparation analyticSet_empty fun _ h ↦ h.elim

/-- The pure-set language: no function or relation symbols, in universes `{1, 2}`. -/
def pureLang : Language.{1, 2} where
  Functions _ := PEmpty
  Relations _ := PEmpty

instance : pureLang.IsRelational := fun _ ↦ inferInstanceAs (IsEmpty PEmpty)

/-- In the pure-set language all codes are isomorphic: there is only one code. -/
theorem pureSet_iso (c d : StructureSpace pureLang) : (structureIsoSetoid pureLang).r c d := by
  have : c = d := funext fun q ↦ PEmpty.elim q.1.2
  subst this
  exact (structureIsoSetoid _).refl c

/-- So an isomorphism-free set of pairs is empty in the pure-set language, and the theorem
applies to it. -/
theorem pureSet_regression {A : Set (StructureSpace pureLang × StructureSpace pureLang)}
    (hA_noniso : ∀ p ∈ A, ¬ (structureIsoSetoid pureLang).r p.1 p.2) :
    A = ∅ ∧ ∃ α : Ordinal.{0}, α < Ordinal.omega 1 ∧ ∀ p ∈ A, ¬ CodeBFEquiv α p.1 p.2 := by
  have hA : A = ∅ := eq_empty_of_forall_notMem fun p hp ↦ hA_noniso p hp (pureSet_iso _ _)
  exact ⟨hA, exists_uniform_bfSeparation (hA ▸ analyticSet_empty) hA_noniso⟩

/-! ### A closed set of pairs: one nullary symbol -/

/-- One nullary relation symbol, nothing else. -/
def nullLang : Language.{0, 0} where
  Functions _ := Empty
  Relations l := { _u : Unit // l = 0 }

instance : nullLang.IsRelational := fun _ ↦ inferInstanceAs (IsEmpty Empty)

instance : Subsingleton (Σ l, nullLang.Relations l) :=
  ⟨by rintro ⟨_, ⟨⟨⟩, rfl⟩⟩ ⟨_, ⟨⟨⟩, rfl⟩⟩; rfl⟩

instance : Countable (Σ l, nullLang.Relations l) := Finite.to_countable

/-- The nullary symbol. -/
def nullP : nullLang.Relations 0 := ⟨(), rfl⟩

/-- The query of the nullary symbol at the empty tuple. -/
def nullQ : RelQuery nullLang := ⟨⟨0, nullP⟩, Fin.elim0⟩

/-- The pairs whose first code makes the nullary symbol true and whose second makes it
false. -/
def nullPairs : Set (StructureSpace nullLang × StructureSpace nullLang) :=
  {p | p.1 nullQ = true ∧ p.2 nullQ = false}

/-- The set is closed: two coordinate conditions. -/
theorem isClosed_nullPairs : IsClosed nullPairs := by
  have hc : Continuous fun p : StructureSpace nullLang × StructureSpace nullLang ↦
      (p.1 nullQ, p.2 nullQ) :=
    ((continuous_apply nullQ).comp continuous_fst).prodMk
      ((continuous_apply nullQ).comp continuous_snd)
  have : nullPairs = (fun p ↦ (p.1 nullQ, p.2 nullQ)) ⁻¹' {(true, false)} := by
    ext; simp [nullPairs]
  exact this ▸ (isClosed_discrete _).preimage hc

/-- An isomorphism preserves the nullary symbol. -/
theorem nullQ_eq_of_iso {c d : StructureSpace nullLang} (h : (structureIsoSetoid nullLang).r c d) :
    c nullQ = d nullQ := by
  obtain ⟨e⟩ := h
  have := @Language.Equiv.map_rel nullLang ℕ ℕ c.toStructure d.toStructure e 0 nullP Fin.elim0
  have hv : (⇑e ∘ (Fin.elim0 : Fin 0 → ℕ)) = Fin.elim0 := funext fun i ↦ i.elim0
  rw [hv] at this
  change d nullQ = true ↔ c nullQ = true at this
  exact Bool.eq_iff_iff.mpr this.symm

/-- No pair of `nullPairs` is isomorphic. -/
theorem nullPairs_noniso : ∀ p ∈ nullPairs, ¬ (structureIsoSetoid nullLang).r p.1 p.2 := by
  rintro p ⟨h₁, h₂⟩ h
  have := nullQ_eq_of_iso h
  rw [h₁, h₂] at this
  exact Bool.false_ne_true this.symm

/-- **The closed set of pairs is separated at one countable level**, at every higher level, and
in particular at the successor of the separating level. -/
theorem null_regression :
    ∃ α : Ordinal.{0}, α < Ordinal.omega 1 ∧ (∀ p ∈ nullPairs, ¬ CodeBFEquiv α p.1 p.2) ∧
      ∀ p ∈ nullPairs, ¬ CodeBFEquiv (α + 1) p.1 p.2 := by
  obtain ⟨α, hα, hsep⟩ := exists_uniform_bfSeparation isClosed_nullPairs.analyticSet
    nullPairs_noniso
  obtain ⟨β, hβ, hge⟩ := exists_uniform_bfSeparation_forall_ge isClosed_nullPairs.analyticSet
    nullPairs_noniso
  exact ⟨β, hβ, hge β le_rfl, hge (β + 1) (le_add_of_nonneg_right zero_le)⟩

/-! ### Two analytic sets: one unary symbol -/

/-- One unary relation symbol, nothing else. -/
def unaryLang : Language.{0, 0} where
  Functions _ := Empty
  Relations l := { _u : Unit // l = 1 }

instance : unaryLang.IsRelational := fun _ ↦ inferInstanceAs (IsEmpty Empty)

instance : Subsingleton (Σ l, unaryLang.Relations l) :=
  ⟨by rintro ⟨_, ⟨⟨⟩, rfl⟩⟩ ⟨_, ⟨⟨⟩, rfl⟩⟩; rfl⟩

instance : Countable (Σ l, unaryLang.Relations l) := Finite.to_countable

/-- The unary symbol. -/
def uP : unaryLang.Relations 1 := ⟨(), rfl⟩

/-- The query of the unary symbol at `m`. -/
def uQ (m : ℕ) : RelQuery unaryLang := ⟨⟨1, uP⟩, fun _ ↦ m⟩

/-- The codes in which the unary symbol holds everywhere. -/
def holdsEverywhere : Set (StructureSpace unaryLang) := {c | ∀ m, c (uQ m) = true}

/-- The codes in which the unary symbol fails somewhere. -/
def failsSomewhere : Set (StructureSpace unaryLang) := {c | ∃ m, c (uQ m) = false}

theorem isClosed_holdsEverywhere : IsClosed holdsEverywhere := by
  simp only [holdsEverywhere, ofPred_forall]
  exact isClosed_iInter fun m ↦ (isClopen_relHolds (uQ m)).isClosed

theorem isOpen_failsSomewhere : IsOpen failsSomewhere := by
  simp only [failsSomewhere, ofPred_exists]
  refine isOpen_iUnion fun m ↦ ?_
  have : {c : StructureSpace unaryLang | c (uQ m) = false} =
      {c : StructureSpace unaryLang | c (uQ m) = true}ᶜ := by
    ext; simp
  exact this ▸ (isClopen_relHolds (uQ m)).compl.isOpen

/-- An isomorphism from a code in which the symbol holds everywhere makes it hold everywhere. -/
theorem holdsEverywhere_of_iso {c d : StructureSpace unaryLang} (hc : c ∈ holdsEverywhere)
    (h : (structureIsoSetoid unaryLang).r c d) : d ∈ holdsEverywhere := by
  obtain ⟨e⟩ := h
  intro m
  set m' := (@Language.Equiv.symm unaryLang ℕ ℕ c.toStructure d.toStructure e) m
  have := @Language.Equiv.map_rel unaryLang ℕ ℕ c.toStructure d.toStructure e 1 uP
    (fun _ ↦ m')
  have hv : (⇑e ∘ fun _ : Fin 1 ↦ m') = fun _ ↦ m :=
    funext fun _ ↦ @Language.Equiv.apply_symm_apply unaryLang ℕ ℕ c.toStructure d.toStructure e m
  rw [hv] at this
  change d (uQ m) = true ↔ c (uQ m') = true at this
  exact this.mpr (hc _)

/-- No element of `holdsEverywhere` is isomorphic to an element of `failsSomewhere`. -/
theorem unary_noniso :
    ∀ x ∈ holdsEverywhere, ∀ y ∈ failsSomewhere, ¬ (structureIsoSetoid unaryLang).r x y := by
  rintro x hx y ⟨m, hm⟩ h
  have := holdsEverywhere_of_iso hx h m
  rw [hm] at this
  exact Bool.false_ne_true this

/-- The code in which the symbol holds everywhere. -/
def uAll : StructureSpace unaryLang := fun _ ↦ true

/-- The code in which the symbol holds nowhere. -/
def uNone : StructureSpace unaryLang := fun _ ↦ false

/-- The empty tuples agree at level `0`: there is no nullary symbol. -/
theorem uAll_uNone_codeBFEquiv_zero : CodeBFEquiv 0 uAll uNone :=
  nil_mem_bfTree_iff.mp (mem_bfTree_iff.mpr fun idx ↦ by
    cases idx with
    | eq i _ => exact i.elim0
    | rel R f =>
      have hl := R.2
      subst hl
      exact (f 0).elim0)

/-- **Two analytic sets are separated at one countable level, and that level is at least
`1`**: level `0` does not separate the codes "holds everywhere" and "holds nowhere". -/
theorem unary_two_set_regression :
    ∃ α : Ordinal.{0}, α < Ordinal.omega 1 ∧ 1 ≤ α ∧
      ∀ x ∈ holdsEverywhere, ∀ y ∈ failsSomewhere, ¬ CodeBFEquiv α x y := by
  obtain ⟨α, hα, hsep⟩ := exists_uniform_bfSeparation_of_analyticSets
    isClosed_holdsEverywhere.analyticSet isOpen_failsSomewhere.measurableSet.analyticSet
    unary_noniso
  refine ⟨α, hα, Order.one_le_iff_ne_zero.mpr fun h0 ↦ ?_, hsep⟩
  subst h0
  exact hsep uAll (fun _ ↦ rfl) uNone ⟨0, rfl⟩ uAll_uNone_codeBFEquiv_zero

end BFSeparationRegressions

end

/-! ### Axiom hygiene -/

open BFSeparationRegressions

/-- The declarations whose axioms are audited. -/
def headline : List Name :=
  [`FirstOrder.Language.exists_uniform_bfSeparation,
   `FirstOrder.Language.exists_uniform_bfSeparation_forall_ge,
   `FirstOrder.Language.exists_uniform_bfSeparation_of_analyticSets,
   `MeasureTheory.AnalyticSet.prod,
   `BFSeparationRegressions.pureSet_regression, `BFSeparationRegressions.null_regression,
   `BFSeparationRegressions.unary_two_set_regression]

/-- The standard axioms. -/
def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a ↦ !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"

/-! ### Minimal imports -/

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

/-- Substrings no `InfinitaryLogic` module of the closure may contain.  This is the list of the
`AnalyticTreeBoundedness` guard without `Scott` and `Lomega1omega`, which the module reaches
legitimately through `BFTree` (back-and-forth equivalence and atomic diagrams).  A substring
match catches a module only while its name retains the substring; the guard enforces the present
boundary and does not track renames. -/
def forbiddenModuleSub : List String :=
  ["LopezEscobar", "InvariantSeparation", "PCSentence", "PCClass", "PCMem", "WellOrdering",
   "WellOrderBridge", "AnalyticWellOrderBoundedness", "TreeCodes", "SmallVocabulary",
   "Interpolation", "Henkin", "Karp", "Methods", "ModelTheory", "WellOrder", "Code"]

/-- No component of an `InfinitaryLogic` module name may start with `PC` (the PC-class
modules). -/
def hasPCComponent (m : Name) : Bool :=
  m.components.any fun c ↦ c.toString.startsWith "PC"

/-- The exact `InfinitaryLogic` import closure of the module.  Extending it is a deliberate
decision: update this list together with the module docstring.  `G0Dichotomy` (Mathlib-only
imports) supplies `MeasureTheory.AnalyticSet.prod`. -/
def allowedClosure : List Name :=
  [`InfinitaryLogic.Util, `InfinitaryLogic.OrdinalUtil,
   `InfinitaryLogic.Lomega1omega.Syntax, `InfinitaryLogic.Lomega1omega.Semantics,
   `InfinitaryLogic.Lomega1omega.Operations,
   `InfinitaryLogic.Scott.AtomicDiagram, `InfinitaryLogic.Scott.BackAndForth,
   `InfinitaryLogic.Descriptive.StructureSpace, `InfinitaryLogic.Descriptive.Topology,
   `InfinitaryLogic.Descriptive.Measurable, `InfinitaryLogic.Descriptive.Polish,
   `InfinitaryLogic.Descriptive.SatisfactionBorel, `InfinitaryLogic.Descriptive.SatisfactionBorelOn,
   `InfinitaryLogic.Descriptive.ModelClassStandardBorel,
   `InfinitaryLogic.Descriptive.PerfectAntichain, `InfinitaryLogic.Descriptive.CantorAntichain,
   `InfinitaryLogic.Descriptive.StructureIsoSetoid, `InfinitaryLogic.Descriptive.BFEquivBorel,
   `InfinitaryLogic.Descriptive.KleeneBrouwer, `InfinitaryLogic.Descriptive.BFTree,
   `InfinitaryLogic.Descriptive.AnalyticTreeBoundedness, `InfinitaryLogic.Descriptive.G0Dichotomy,
   `InfinitaryLogic.Descriptive.BFSeparation]

run_cmd do
  let env ← getEnv
  let target := `InfinitaryLogic.Descriptive.BFSeparation
  unless (env.getModuleIdx? target).isSome do
    throwError "module {target} is not in the environment"
  let cl := importClosure env target
  for m in [`InfinitaryLogic.Descriptive.BFTree,
            `InfinitaryLogic.Descriptive.AnalyticTreeBoundedness,
            `InfinitaryLogic.Descriptive.KleeneBrouwer,
            `InfinitaryLogic.Descriptive.StructureIsoSetoid] do
    unless cl.contains m do throwError "[MISSING ROUTE] {m} is not in the closure of {target}"
  let ilModules := cl.toList.filter fun m ↦ (`InfinitaryLogic).isPrefixOf m
  let hits := ilModules.filter fun m ↦
    hasPCComponent m || forbiddenModuleSub.any fun s ↦ (m.toString.splitOn s).length ≠ 1
  unless hits.isEmpty do
    throwError "[BROAD CONE] the closure of {target} reaches {hits}"
  let extra := ilModules.filter fun m ↦ !allowedClosure.contains m
  let missing := allowedClosure.filter fun m ↦ !ilModules.contains m
  unless extra.isEmpty && missing.isEmpty do
    throwError "[CLOSURE DRIFT] the InfinitaryLogic closure of {target} is {ilModules}; \
      update allowedClosure deliberately (extra {extra}, missing {missing})"
  logInfo m!"bf separation regression guard: OK (applied: all three theorems for an arbitrary \
    relational Language.\{u, v} with no countability; the empty set of pairs; the pure-set \
    language in universes 1, 2; a closed isomorphism-free set of pairs in a nullary language, \
    separated at a countable level, above it and at its successor; two analytic sets in a unary \
    language, a closed one and an open one, separated at a countable level that is at least 1; \
    standard axioms; import closure of {ilModules.length} InfinitaryLogic modules, exactly as \
    listed, with no coding, separation, PC-class, well-order, vocabulary, interpolation, Henkin, \
    Karp, methods or model-theory module)"
