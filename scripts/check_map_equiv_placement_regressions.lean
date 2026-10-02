/-
Regression guard for the placement of the two isomorphism-transport lemmas.

* `SameAtomicType.map_equiv` lives in `Scott/AtomicDiagram.lean`, next to `SameAtomicType`.
* `BFEquiv.map_equiv` lives in `Scott/BFEquivRelabel.lean`, on top of `Scott/BackAndForth`.

Both used to live in `Scott/OrbitRank.lean`, whose import closure contains `Karp.PotentialIso`
and `Scott.Stabilization`; a module that must keep `Karp` out of its closure (for instance
`Descriptive/BFSeparation`, through `Descriptive/BFTree`) could not use them.  This file imports
only `InfinitaryLogic.Scott.BFEquivRelabel` and checks:

* **Statements**: both lemmas, at their exact binder and universe shapes (the targets of
  `SameAtomicType.map_equiv` in arbitrary universes, those of `BFEquiv.map_equiv` in the
  universes of the sources); neither needs `[L.IsRelational]`.
* **Applied**: in the pure set `ℕ`, the swap `0 ↔ 1` carries `(0, 1)` to `(1, 0)`, so the two
  tuples are back-and-forth equivalent at every level; the atomic type of `(0, 1)` is carried
  into `ULift.{1} ℕ`.
* **Home modules**: each lemma is declared in the module named above.
* **Import closure** of `Scott/BFEquivRelabel`: no `Karp`, descriptive, model-theory or method
  module, and not `Scott/OrbitRank`.

The declarations use only the standard axioms.

Run with: lake env lean scripts/check_map_equiv_placement_regressions.lean
-/
import InfinitaryLogic.Scott.BFEquivRelabel

open Lean FirstOrder FirstOrder.Language

universe u v w w' x y z

namespace MapEquivPlacementGuard

/-! ### Statements, at their exact shapes -/

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

/-- Module-name prefixes no module of the closure may have. -/
def forbiddenPrefixes : List Name :=
  [`InfinitaryLogic.Karp, `InfinitaryLogic.Descriptive, `InfinitaryLogic.ModelTheory,
   `InfinitaryLogic.Methods]

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
  let hits := cl.toList.filter fun m ↦
    forbiddenPrefixes.any (·.isPrefixOf m) || m == `InfinitaryLogic.Scott.OrbitRank
  unless hits.isEmpty do
    throwError "[BROAD CONE] the closure of {target} reaches {hits}"

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
    Scott/AtomicDiagram and BFEquiv.map_equiv in Scott/BFEquivRelabel, at their exact shapes \
    and without IsRelational; applied: (0, 1) and (1, 0) back-and-forth equivalent at every \
    level of the pure set N through the swap, the atomic type of (0, 1) carried into \
    ULift.{1} N; import closure of Scott/BFEquivRelabel without Karp, descriptive, \
    model-theory or method modules and without Scott/OrbitRank; standard axioms)"
