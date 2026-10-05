/-
Regression guard for the placement of the two isomorphism-invariance lemmas.

* `BoundedFormulaω.realize_equiv` lives in `Lomega1omega/Semantics.lean`, after the atomic
  transport lemmas `Embedding.realize_equal_comp` and `Embedding.realize_rel_comp` it is built on.
* `modelsOf_mem_iff_of_equiv` lives in `Descriptive/SatisfactionBorel.lean`, beside `ModelsOf`.

They used to live in `Lomega1omega/Theory.lean` and `Descriptive/LopezEscobarEasy.lean`.  A module
that has `ModelsOf` but must keep `Lomega1omega.Theory` or every López–Escobar module out of
reach (for instance `Descriptive/MinimallyUncountable`, through its `LopezEscobar` substring
guard) could not use them, and kept a private copy.  The move added no import: `Theory` imports
`Semantics` and `LopezEscobarEasy` imports `SatisfactionBorel`, so every call site resolves the
same fully qualified names.  This file imports `Descriptive.MinimallyUncountable` and
`Descriptive.LopezEscobarEasy` and checks:

* **Statements**: both lemmas, pinned in argument order and types (`realize_equiv` with the
  formula's variable type in its own universe; `modelsOf_mem_iff_of_equiv` with
  `[L.IsRelational]` and no countability).  An `example : T := @lemma` checks the type up to
  definitional equality, which ignores binder kinds, so the binder kinds are read off the
  declared types and compared with the expected lists (`[BINDER DRIFT]`), and are also exercised
  by the applications below.
* **Universe parameters**: the `levelParams` are exactly `[u, v, w, u_1]` for `realize_equiv`
  (the list it had in `Lomega1omega/Theory.lean`) and `[vL, uL]` for
  `modelsOf_mem_iff_of_equiv` (relation universe first, the positional order it had in
  `Descriptive/LopezEscobarEasy.lean` as `[v, u]`), and the positional order is pinned by
  explicit instantiation with a distinct universe at every position:
  `realize_equiv.{0, 1, 2, 3}` and `modelsOf_mem_iff_of_equiv.{1, 0}` over `Language.{0, 1}`.
* **Home modules**: each lemma is declared in the module named above (`[MOVED]`), and no
  constant of the environment other than these two has the last name component
  `realize_equiv`, `modelsOf_mem_iff_of_equiv` or `modelsOf_mem_of_iso` in the
  `FirstOrder.Language` namespace or a private copy of one (`[DUPLICATE]`).
* **Import closures**, unchanged by the move: the `InfinitaryLogic` closures of
  `Lomega1omega.Semantics` (2), `Lomega1omega.Theory` (4), `Descriptive.SatisfactionBorel` (8)
  and `Descriptive.LopezEscobarEasy` (11) are exactly the listed modules, and that of
  `Descriptive.MinimallyUncountable` has 33 modules, none with `LopezEscobar` in its name
  (`[CLOSURE DRIFT]`).  `Descriptive.SatisfactionBorel` does not reach `Lomega1omega.Theory`
  (`[BROAD CONE]`): the lemma moved down, the import did not move up.

The declarations use only the standard axioms.

Run with: lake env lean scripts/check_invariance_placement_regressions.lean
-/
import InfinitaryLogic.Descriptive.MinimallyUncountable
import InfinitaryLogic.Descriptive.LopezEscobarEasy

open Lean FirstOrder FirstOrder.Language

universe u v w x

namespace InvariancePlacementGuard

/-! ### Statements: argument order and types -/

/-- Isomorphism invariance of realization, the variable type in its own universe. -/
example : ∀ {L : Language.{u, v}} {M N : Type w} [L.Structure M] [L.Structure N]
    (e : M ≃[L] N) {α : Type x} {n : ℕ} (φ : L.BoundedFormulaω α n) (v : α → M)
    (xs : Fin n → M), φ.Realize v xs ↔ φ.Realize (⇑e ∘ v) (⇑e ∘ xs) :=
  @BoundedFormulaω.realize_equiv

/-- Isomorphism invariance of `ModelsOf`: relational, no countability. -/
example : ∀ {L : Language.{u, v}} [L.IsRelational] (φ : L.Sentenceω) {c d : StructureSpace L}
    (_ : @Language.Equiv L ℕ ℕ c.toStructure d.toStructure),
    c ∈ ModelsOf φ ↔ d ∈ ModelsOf φ :=
  @modelsOf_mem_iff_of_equiv

/-! ### Positional universe order, pinned by explicit instantiation -/

section UniverseOrder

variable {L₁ : Language.{0, 1}} {A B : Type 2} [L₁.Structure A] [L₁.Structure B]

/-- `realize_equiv.{u, v, w, u_1}`: function universe, relation universe, carriers, variable
type.  Every position carries a distinct universe, so any permutation fails to typecheck. -/
example (e : A ≃[L₁] B) {α : Type 3} {n : ℕ} (φ : L₁.BoundedFormulaω α n) (v : α → A)
    (xs : Fin n → A) : φ.Realize v xs ↔ φ.Realize (⇑e ∘ v) (⇑e ∘ xs) :=
  BoundedFormulaω.realize_equiv.{0, 1, 2, 3} e φ v xs

/-- `modelsOf_mem_iff_of_equiv.{vL, uL}`: relation universe, then function universe. -/
example [L₁.IsRelational] (φ : L₁.Sentenceω) {c d : StructureSpace L₁}
    (e : @Language.Equiv L₁ ℕ ℕ c.toStructure d.toStructure) :
    c ∈ ModelsOf φ ↔ d ∈ ModelsOf φ :=
  modelsOf_mem_iff_of_equiv.{1, 0} φ e

end UniverseOrder

/-! ### Applied: the downstream forms still go through the moved lemmas -/

/-- Isomorphism invariance of a model class (`Descriptive/LopezEscobarEasy.lean`), through the
relocated lemma. -/
example {L : Language.{u, v}} [L.IsRelational] (φ : L.Sentenceω) :
    IsomorphismInvariant (ModelsOf φ) :=
  fun _ _ ⟨e⟩ ↦ modelsOf_mem_iff_of_equiv φ e

/-- Isomorphic codes are in the same model classes, from the isomorphism relation of codes. -/
theorem mem_modelsOf_of_iso {L : Language.{u, v}} [L.IsRelational] (θ : L.Sentenceω)
    {c d : StructureSpace L} (h : (structureIsoSetoid L).r c d) (hc : c ∈ ModelsOf θ) :
    d ∈ ModelsOf θ :=
  h.elim fun e ↦ (modelsOf_mem_iff_of_equiv θ e).mp hc

/-- Isomorphic structures are Lω₁ω-equivalent (`Lomega1omega/Theory.lean`), whose proof uses
the relocated `realize_equiv`. -/
example {L : Language.{u, v}} {M N : Type w} [L.Structure M] [L.Structure N] (e : M ≃[L] N) :
    LomegaEquiv L M N :=
  LomegaEquiv.of_equiv e

end InvariancePlacementGuard

/-! ### Universe lists, binder kinds, home modules, import closures and axiom audit -/

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

/-- The binder kinds of the leading `∀`s of a type. -/
partial def binderKinds : Expr → List BinderInfo
  | .forallE _ _ b bi => bi :: binderKinds b
  | _ => []

/-- Each lemma, its home module, its universe list and the binder kinds of its type. -/
def pins : List (Name × Name × List Name × List BinderInfo) :=
  [(`FirstOrder.Language.BoundedFormulaω.realize_equiv, `InfinitaryLogic.Lomega1omega.Semantics,
    [`u, `v, `w, `u_1],
    [.implicit, .implicit, .implicit, .instImplicit, .instImplicit, .default, .implicit,
     .implicit, .default, .default, .default]),
   (`FirstOrder.Language.modelsOf_mem_iff_of_equiv, `InfinitaryLogic.Descriptive.SatisfactionBorel,
    [`vL, `uL],
    [.implicit, .instImplicit, .default, .implicit, .implicit, .default])]

/-- Last name components no other `FirstOrder.Language` constant (or private copy) may carry. -/
def watchedSuffixes : List String :=
  ["realize_equiv", "modelsOf_mem_iff_of_equiv", "modelsOf_mem_of_iso"]

/-- Exact `InfinitaryLogic` import closures, unchanged by the move. -/
def exactClosures : List (Name × List Name) :=
  [(`InfinitaryLogic.Lomega1omega.Semantics,
    [`InfinitaryLogic.Lomega1omega.Syntax, `InfinitaryLogic.Lomega1omega.Semantics]),
   (`InfinitaryLogic.Lomega1omega.Theory,
    [`InfinitaryLogic.Util, `InfinitaryLogic.Lomega1omega.Syntax,
     `InfinitaryLogic.Lomega1omega.Semantics, `InfinitaryLogic.Lomega1omega.Theory]),
   (`InfinitaryLogic.Descriptive.SatisfactionBorel,
    [`InfinitaryLogic.Lomega1omega.Syntax, `InfinitaryLogic.Lomega1omega.Semantics,
     `InfinitaryLogic.Descriptive.Topology, `InfinitaryLogic.Descriptive.StructureSpace,
     `InfinitaryLogic.Descriptive.Polish, `InfinitaryLogic.Descriptive.Measurable,
     `InfinitaryLogic.Descriptive.SatisfactionBorelOn,
     `InfinitaryLogic.Descriptive.SatisfactionBorel]),
   (`InfinitaryLogic.Descriptive.LopezEscobarEasy,
    [`InfinitaryLogic.Util, `InfinitaryLogic.Lomega1omega.Syntax,
     `InfinitaryLogic.Lomega1omega.Semantics, `InfinitaryLogic.Lomega1omega.Theory,
     `InfinitaryLogic.Descriptive.Topology, `InfinitaryLogic.Descriptive.StructureSpace,
     `InfinitaryLogic.Descriptive.Polish, `InfinitaryLogic.Descriptive.Measurable,
     `InfinitaryLogic.Descriptive.SatisfactionBorelOn,
     `InfinitaryLogic.Descriptive.SatisfactionBorel,
     `InfinitaryLogic.Descriptive.LopezEscobarEasy])]

/-- The `InfinitaryLogic` closure of `m`. -/
def ilClosure (env : Environment) (m : Name) : List Name :=
  (importClosure env m).toList.filter fun n ↦ (`InfinitaryLogic).isPrefixOf n

run_cmd do
  let env ← getEnv
  for (d, home, univs, kinds) in pins do
    let some ci := env.find? d | throwError "declaration {d} not found"
    let some idx := env.getModuleIdxFor? d | throwError "declaration {d} has no module"
    let m := env.header.moduleNames[idx.toNat]!
    unless m == home do throwError "[MOVED] {d} is declared in {m}, expected {home}"
    unless ci.levelParams == univs do
      throwError "[UNIVERSE DRIFT] {d} has universe parameters {ci.levelParams}, expected {univs}"
    unless binderKinds ci.type == kinds do
      throwError "[BINDER DRIFT] {d} has binder kinds {repr (binderKinds ci.type)}, expected \
        {repr kinds}"
  let pinned := pins.map (·.1)
  let dups := env.constants.fold (init := []) fun acc n _ ↦
    let s := n.componentsRev.headD .anonymous
    let watched := match s with
      | .str _ str => watchedSuffixes.contains str
      | _ => false
    let inNs := (`FirstOrder.Language).isPrefixOf n || isPrivateName n
    if watched && inNs && !pinned.contains n then n :: acc else acc
  unless dups.isEmpty do throwError "[DUPLICATE] other copies of the invariance lemmas: {dups}"
  for (m, allowed) in exactClosures do
    unless (env.getModuleIdx? m).isSome do throwError "module {m} is not in the environment"
    let cl := ilClosure env m
    let extra := cl.filter fun n ↦ !allowed.contains n
    let missing := allowed.filter fun n ↦ !cl.contains n
    unless extra.isEmpty && missing.isEmpty do
      throwError "[CLOSURE DRIFT] the InfinitaryLogic closure of {m} is {cl} (extra {extra}, \
        missing {missing})"
  let mu := `InfinitaryLogic.Descriptive.MinimallyUncountable
  let muCl := ilClosure env mu
  unless muCl.length == 33 do
    throwError "[CLOSURE DRIFT] the InfinitaryLogic closure of {mu} has {muCl.length} modules, \
      expected 33"
  let le := muCl.filter fun n ↦ (n.toString.splitOn "LopezEscobar").length > 1
  unless le.isEmpty do throwError "[BROAD CONE] the closure of {mu} reaches {le}"
  if (ilClosure env `InfinitaryLogic.Descriptive.SatisfactionBorel).contains
      `InfinitaryLogic.Lomega1omega.Theory then
    throwError "[BROAD CONE] Descriptive.SatisfactionBorel reaches Lomega1omega.Theory"

/-- The audited declarations. -/
def auditedDecls : List Name :=
  [`FirstOrder.Language.BoundedFormulaω.realize_equiv,
   `FirstOrder.Language.modelsOf_mem_iff_of_equiv,
   `InvariancePlacementGuard.mem_modelsOf_of_iso]

/-- The standard axioms. -/
def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in auditedDecls do
    unless (env.find? n).isSome do throwError "declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a ↦ !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "Invariance placement regression guard: OK (BoundedFormulaω.realize_equiv in \
    Lomega1omega/Semantics with universe parameters [u, v, w, u_1], modelsOf_mem_iff_of_equiv \
    in Descriptive/SatisfactionBorel with [vL, uL]; statements, binder kinds and positional \
    universe order pinned; no other copy; applied: isomorphism invariance of model classes, \
    the code isomorphism relation, LomegaEquiv.of_equiv; InfinitaryLogic closures of \
    Lomega1omega.Semantics (2), Lomega1omega.Theory (4), Descriptive.SatisfactionBorel (8) and \
    Descriptive.LopezEscobarEasy (11) exact, Descriptive.MinimallyUncountable 33 without \
    LopezEscobar, SatisfactionBorel without Lomega1omega.Theory; standard axioms)"
