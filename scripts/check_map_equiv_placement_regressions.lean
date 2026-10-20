/-
Regression guard for the placement of the two isomorphism-transport lemmas.

* `SameAtomicType.map_equiv` lives in `Scott/AtomicDiagram.lean`, next to `SameAtomicType`.
* `BFEquiv.map_equiv` lives in `Scott/BFEquivRelabel.lean`, on top of `Scott/BackAndForth`.

Both used to live in `Scott/OrbitRank.lean`, whose import closure contains `Karp.PotentialIso`
and `Scott.Stabilization`; a module that must keep `Karp` out of its closure (for instance
`Descriptive/BFSeparation`, through `Descriptive/BFTree`) could not use them.  This file imports
only `InfinitaryLogic.Scott.BFEquivRelabel` and checks:

* **Statements**: both lemmas, pinned in argument order, types and universe shapes (the
  targets of `SameAtomicType.map_equiv` in arbitrary universes, those of `BFEquiv.map_equiv` in
  the universes of the sources); neither needs `[L.IsRelational]`.  An `example : T := @lemma`
  checks the type up to definitional equality, which ignores binder kinds; binder kinds are
  exercised by the applications below.
* **Positional universe order**, pinned by explicit instantiation with a distinct universe at
  every position: `SameAtomicType.map_equiv.{v, u, w, w', _, _}` and
  `BFEquiv.map_equiv.{v, u, w, w', _}` (relation universe first), the order both lemmas had in
  `Scott/OrbitRank.lean`, so explicit instantiations written against it keep working.
* **Applied**: in the pure set `ℕ`, the swap `0 ↔ 1` carries `(0, 1)` to `(1, 0)`, so the two
  tuples are back-and-forth equivalent at every level; the atomic type of `(0, 1)` is carried
  into `ULift.{1} ℕ`.
* **Home modules**: each lemma is declared in the module named above.
* **Import closure** of `Scott/BFEquivRelabel`: its `InfinitaryLogic` closure is exactly
  `Util`, `Lomega1omega.{Syntax, Semantics, Operations}`, `Scott.AtomicDiagram`,
  `Scott.BackAndForth` and the module itself; as an extra, no `Karp`, descriptive, model-theory
  or method module, and not `Scott/OrbitRank`.  Upstream (TauCeti), the closure may not reach
  the Karp-layer prefixes `BackAndForth.{TupleSystem, PotentialIso, Presentation, AllLevels,
  Countable, Karp}` or the orbit-rank prefixes `Scott.{Rank, CompleteGraphSum}` (tier R, in the
  same check), nor, because the whitelist excludes their counterparts, `Scott.Formula`,
  `Scott.{Stabilization, PureSet}`, `Infinitary.QuantifierRank` or `Scott.{Sentence,
  PotentialIso}` (tier W, a separate check over the full closure).  Both matchers are controlled
  on every frozen prefix, a child and a component-wise lookalike of each, and the permitted
  names `BackAndForth.{AtomicType, Equivalence}`, `Scott.AtomicDiagram` and
  `Infinitary.Semantics`.

The declarations use only the standard axioms.

Run with: lake env lean scripts/check_map_equiv_placement_regressions.lean
-/
import InfinitaryLogic.Scott.BFEquivRelabel

open Lean FirstOrder FirstOrder.Language

universe u v w w' x y z

namespace MapEquivPlacementGuard

/-! ### Statements: argument order, types and universe shapes -/

/-- The atomic-type transport: targets in arbitrary universes, no `IsRelational`. -/
example : ∀ {L : Language.{u, v}} {M : Type w} [L.Structure M] {N : Type w'} [L.Structure N]
    {M' : Type x} {N' : Type y} [L.Structure M'] [L.Structure N']
    (e : M ≃[L] M') (e' : N ≃[L] N') {n : ℕ} {a : Fin n → M} {b : Fin n → N},
    SameAtomicType (L := L) (⇑e ∘ a) (⇑e' ∘ b) ↔ SameAtomicType (L := L) a b :=
  @SameAtomicType.map_equiv

/-- The back-and-forth transport: targets in the universes of the sources, at every level. -/
example : ∀ {L : Language.{u, v}} {M : Type w} [L.Structure M] {N : Type w'} [L.Structure N]
    {M' : Type w} {N' : Type w'} [L.Structure M'] [L.Structure N']
    (e : M ≃[L] M') (e' : N ≃[L] N') (α : Ordinal.{z}) {n : ℕ} {a : Fin n → M}
    {b : Fin n → N},
    BFEquiv (L := L) α n (⇑e ∘ a) (⇑e' ∘ b) ↔ BFEquiv (L := L) α n a b :=
  @BFEquiv.map_equiv

/-! ### Positional universe order, pinned by explicit instantiation -/

section UniverseOrder

variable {L₁ : Language.{0, 1}} {A : Type 2} {B : Type 3} {A' : Type 4} {B' : Type 5}
  [L₁.Structure A] [L₁.Structure B] [L₁.Structure A'] [L₁.Structure B']

/-- `SameAtomicType.map_equiv.{v, u, w, w', _, _}`: relation universe, function universe,
the two sources, the two targets.  Every position carries a distinct universe, so any
permutation of the list fails to typecheck. -/
example (e : A ≃[L₁] A') (e' : B ≃[L₁] B') {n : ℕ} {a : Fin n → A} {b : Fin n → B} :
    SameAtomicType (L := L₁) (⇑e ∘ a) (⇑e' ∘ b) ↔ SameAtomicType (L := L₁) a b :=
  SameAtomicType.map_equiv.{1, 0, 2, 3, 4, 5} e e'

/-- `BFEquiv.map_equiv.{v, u, w, w', _}`: relation universe, function universe, the two
sources (the targets share them), the ordinal universe. -/
example {A₂ : Type 2} {B₂ : Type 3} [L₁.Structure A₂] [L₁.Structure B₂]
    (e : A ≃[L₁] A₂) (e' : B ≃[L₁] B₂) (α : Ordinal.{6}) {n : ℕ} {a : Fin n → A}
    {b : Fin n → B} :
    BFEquiv (L := L₁) α n (⇑e ∘ a) (⇑e' ∘ b) ↔ BFEquiv (L := L₁) α n a b :=
  BFEquiv.map_equiv.{1, 0, 2, 3, 6} e e' α

end UniverseOrder

/-! ### Applied, in the pure set `ℕ` -/

attribute [local instance] Language.emptyStructure

/-- The swap `0 ↔ 1` as an automorphism of the pure set `ℕ`. -/
def swap01 : ℕ ≃[Language.empty] ℕ := { toEquiv := Equiv.swap 0 1 }

/-- The swap carries `(0, 1)` to `(1, 0)`. -/
theorem swap01_comp : ⇑swap01 ∘ ![0, 1] = ![1, 0] := by
  funext i
  match i with
  | 0 => exact Equiv.swap_apply_left 0 1
  | 1 => exact Equiv.swap_apply_right 0 1

/-- **Applied**: `(0, 1)` and `(1, 0)` are back-and-forth equivalent at every level of the
pure set `ℕ`, by transporting reflexivity along the swap on the right. -/
theorem bfEquiv_swap (α : Ordinal.{z}) :
    BFEquiv (L := Language.empty) α 2 (![0, 1] : Fin 2 → ℕ) (![1, 0] : Fin 2 → ℕ) := by
  have h := (BFEquiv.map_equiv (Language.Equiv.refl Language.empty ℕ) swap01 α
    (a := ![0, 1]) (b := ![0, 1])).mpr (BFEquiv.refl α _)
  rwa [swap01_comp] at h

/-- The pure set `ℕ` into `ULift.{1} ℕ`. -/
def upEquiv : ℕ ≃[Language.empty] ULift.{1} ℕ := { toEquiv := Equiv.ulift.symm }

/-- **Applied, across universes**: the atomic type of `(0, 1)` is carried into `ULift.{1} ℕ`. -/
theorem sameAtomicType_up :
    SameAtomicType (L := Language.empty) (⇑upEquiv ∘ (![0, 1] : Fin 2 → ℕ))
      (⇑(Language.Equiv.refl Language.empty ℕ) ∘ (![0, 1] : Fin 2 → ℕ)) :=
  (SameAtomicType.map_equiv upEquiv (Language.Equiv.refl Language.empty ℕ)).mpr
    (SameAtomicType.refl _)

end MapEquivPlacementGuard

/-! ### Home modules, import closure and axiom audit -/

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

/-- Tier R upstream prefixes (TauCeti): the counterparts of `InfinitaryLogic.Karp` ("must keep
`Karp` out of its closure") and of `Scott/OrbitRank` ("not `Scott/OrbitRank`"): the
potential-isomorphism layer, the forward Karp theorem and the orbit ranks upstream. -/
def upstreamForbiddenPrefixes : List Name :=
  [`TauCeti.ModelTheory.BackAndForth.TupleSystem, `TauCeti.ModelTheory.BackAndForth.PotentialIso,
   `TauCeti.ModelTheory.BackAndForth.Presentation, `TauCeti.ModelTheory.BackAndForth.AllLevels,
   `TauCeti.ModelTheory.BackAndForth.Countable, `TauCeti.ModelTheory.BackAndForth.Karp,
   `TauCeti.ModelTheory.Scott.Rank, `TauCeti.ModelTheory.Scott.CompleteGraphSum]

/-- Module-name prefixes no module of the closure may have. -/
def forbiddenPrefixes : List Name :=
  [`InfinitaryLogic.Karp, `InfinitaryLogic.Descriptive, `InfinitaryLogic.ModelTheory,
   `InfinitaryLogic.Methods] ++ upstreamForbiddenPrefixes

/-- The matcher of the closure check: a forbidden prefix is a component-wise prefix of the
module's name, or the module is `Scott/OrbitRank`.  The closure walk is over all module names,
`TauCeti.*` included. -/
def isForbiddenModule (m : Name) : Bool :=
  forbiddenPrefixes.any (·.isPrefixOf m) || m == `InfinitaryLogic.Scott.OrbitRank

/-- Tier W (whitelist gap repair, in scope by ruling D2 of 2026-10-19): TauCeti modules whose
`InfinitaryLogic` counterparts (`Scott.Formula`, the internal stabilization of `Scott.Sentence`,
`Lomega1omega.QuantifierRank`, Scott sentences) are absent from `allowedClosure`, which cannot
see a TauCeti module.  Matched over the full closure. -/
def upstreamWhitelistGapPrefixes : List Name :=
  [`TauCeti.ModelTheory.Scott.Formula, `TauCeti.ModelTheory.Scott.Stabilization,
   `TauCeti.ModelTheory.Scott.PureSet, `TauCeti.ModelTheory.Infinitary.QuantifierRank,
   `TauCeti.ModelTheory.Scott.Sentence, `TauCeti.ModelTheory.Scott.PotentialIso]

/-- The matcher of the tier-W check: a module is forbidden when a tier-W prefix is a
component-wise prefix of its name. -/
def isForbiddenUpstreamGap (m : Name) : Bool :=
  upstreamWhitelistGapPrefixes.any (·.isPrefixOf m)

/-- A component-wise lookalike of a prefix: its last component with `X` appended
(`TauCeti.ModelTheory.Scott` ↦ `TauCeti.ModelTheory.ScottX`).  It shares the prefix as text and
is not a component-wise descendant, so a component-wise matcher must not flag it. -/
def controlLookalike : Name → Name
  | .str p s => .str p (s ++ "X")
  | n => n

/-- `[CONTROL]` on one upstream matcher in one mode (`label`): the matcher flags every frozen
prefix of `ps` and a child of each, and flags neither the lookalike of any prefix nor any name
of `permitted` (the permitted list of this matcher and mode only).  The two lists must have
exactly `size` and `permittedSize` entries, so a truncated list fails loudly. -/
def upstreamControl (label : String) (isForbidden : Name → Bool) (ps : List Name) (size : Nat)
    (permitted : List Name) (permittedSize : Nat) : Elab.Command.CommandElabM Unit := do
  unless ps.length == size do
    throwError "[CONTROL] {label}: {ps.length} frozen prefixes, expected {size}"
  unless permitted.length == permittedSize do
    throwError "[CONTROL] {label}: {permitted.length} permitted names, expected {permittedSize}"
  for p in ps do
    for m in [p, .str p "ControlChild"] do
      unless isForbidden m do
        throwError "[CONTROL] {label}: the upstream matcher does not flag {m}"
  for m in ps.map controlLookalike ++ permitted do
    if isForbidden m then
      throwError "[CONTROL] {label}: the upstream matcher flags {m}"

-- [CONTROL] on both upstream matchers, each with the guard's permitted list (shared)
run_cmd do
  upstreamControl "closure matcher (tier R)" isForbiddenModule upstreamForbiddenPrefixes 8
    [`TauCeti.ModelTheory.BackAndForth.AtomicType, `TauCeti.ModelTheory.BackAndForth.Equivalence,
     `TauCeti.ModelTheory.Scott.AtomicDiagram, `TauCeti.ModelTheory.Infinitary.Semantics] 4
  upstreamControl "tier-W matcher" isForbiddenUpstreamGap upstreamWhitelistGapPrefixes 6
    [`TauCeti.ModelTheory.BackAndForth.AtomicType, `TauCeti.ModelTheory.BackAndForth.Equivalence,
     `TauCeti.ModelTheory.Scott.AtomicDiagram, `TauCeti.ModelTheory.Infinitary.Semantics] 4

/-- The exact `InfinitaryLogic` import closure of `Scott/BFEquivRelabel`.  Extending it is a
deliberate decision: a consumer under an exact-closure guard (such as `Descriptive/BFSeparation`)
reaches the transport lemmas by adding these modules.  Update this list together with the module
docstring. -/
def allowedClosure : List Name :=
  [`InfinitaryLogic.Util,
   `InfinitaryLogic.Lomega1omega.Syntax, `InfinitaryLogic.Lomega1omega.Semantics,
   `InfinitaryLogic.Lomega1omega.Operations,
   `InfinitaryLogic.Scott.AtomicDiagram, `InfinitaryLogic.Scott.BackAndForth,
   `InfinitaryLogic.Scott.BFEquivRelabel]

/-- Each lemma and the module it must be declared in. -/
def homes : List (Name × Name) :=
  [(`FirstOrder.Language.SameAtomicType.map_equiv, `InfinitaryLogic.Scott.AtomicDiagram),
   (`FirstOrder.Language.BFEquiv.map_equiv, `InfinitaryLogic.Scott.BFEquivRelabel)]

run_cmd do
  let env ← getEnv
  for (d, home) in homes do
    let some idx := env.getModuleIdxFor? d | throwError "declaration {d} not found"
    let m := env.header.moduleNames[idx.toNat]!
    unless m == home do throwError "[MOVED] {d} is declared in {m}, expected {home}"
  let target := `InfinitaryLogic.Scott.BFEquivRelabel
  unless (env.getModuleIdx? target).isSome do
    throwError "module {target} is not in the environment"
  let cl := importClosure env target
  for m in [`InfinitaryLogic.Scott.AtomicDiagram, `InfinitaryLogic.Scott.BackAndForth] do
    unless cl.contains m do throwError "[MISSING ROUTE] {m} is not in the closure of {target}"
  let hits := cl.toList.filter isForbiddenModule
  unless hits.isEmpty do
    throwError "[BROAD CONE] the closure of {target} reaches {hits}"
  -- tier W, over the full closure
  let gapHits := cl.toList.filter isForbiddenUpstreamGap
  unless gapHits.isEmpty do
    throwError "[BROAD CONE] the closure of {target} reaches {gapHits}"
  let ilModules := cl.toList.filter fun m ↦ (`InfinitaryLogic).isPrefixOf m
  let extra := ilModules.filter fun m ↦ !allowedClosure.contains m
  let missing := allowedClosure.filter fun m ↦ !ilModules.contains m
  unless extra.isEmpty && missing.isEmpty do
    throwError "[CLOSURE DRIFT] the InfinitaryLogic closure of {target} is {ilModules}; \
      update allowedClosure deliberately (extra {extra}, missing {missing})"

/-- The audited declarations. -/
def auditedDecls : List Name :=
  [`FirstOrder.Language.SameAtomicType.map_equiv, `FirstOrder.Language.BFEquiv.map_equiv,
   `MapEquivPlacementGuard.swap01_comp, `MapEquivPlacementGuard.bfEquiv_swap,
   `MapEquivPlacementGuard.sameAtomicType_up]

/-- The standard axioms. -/
def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in auditedDecls do
    unless (env.find? n).isSome do throwError "declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a ↦ !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "Map-equiv placement regression guard: OK (SameAtomicType.map_equiv in \
    Scott/AtomicDiagram and BFEquiv.map_equiv in Scott/BFEquivRelabel, argument order, types \
    and universe shapes pinned, without IsRelational, binder kinds exercised by the \
    applications, positional universe order pinned by explicit instantiation; applied: \
    (0, 1) and (1, 0) back-and-forth equivalent at every level of the pure set N through the \
    swap, the atomic type of (0, 1) carried into \
    ULift.{1} N; InfinitaryLogic import closure of Scott/BFEquivRelabel exactly the 7 listed \
    modules, without Karp, descriptive, model-theory or method modules and without \
    Scott/OrbitRank, and no upstream Karp-layer, orbit-rank, Scott-formula, stabilization, \
    quantifier-rank or Scott-sentence module; standard axioms)"
