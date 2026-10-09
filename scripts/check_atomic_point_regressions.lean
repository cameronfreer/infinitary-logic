/-
Regression guard for `InfinitaryLogic/CategoryTheory/Sites/AtomicPoint.lean`: atomic sites,
the dense topology, and the atomic covering condition on functors.

This file imports only that module, so its environment is the module's import closure.

Mathlib namespaces the module adds declarations to (collision watch list):

* `CategoryTheory.GrothendieckTopology` (`mem_atomic_iff`, `dense_covering_nonempty`,
  `atomic_eq_dense`, `atomic_jointlySurjective_iff`);
* `CategoryTheory.GrothendieckTopology.Point` (`fiber_map_surjective`).

It checks:

* **Positive control (G1), an ATOMIC-CONTINUITY example, NOT a point**: the Cantor inverse
  system `n ↦ (Fin n → Bool)` on `ℕᵒᵖ`, with restriction along `Fin.castLE`. The right Ore
  condition holds (`W := max`), every restriction map is surjective (extend by `false`), so the
  atomic covering condition holds by `atomic_jointlySurjective_iff`. Its category of elements
  is NOT cofiltered (incompatible prefixes have no common refinement), proved here as a
  negative control, so it is not the fiber of any point. A Fraïssé positive case (ℚ as the
  limit of finite linear orders) is not cheap here, since it needs the category of finite
  substructures; it is deferred to the joining-point tranche.
* **Negative control**: `Fin 2` as a preorder category (right Ore with `W := min`) and the
  functor sending `0` to an empty type and `1` to a one-point type (as `PLift (i = 1)`). Its map
  `0 ⟶ 1` is not surjective, so the atomic covering condition fails, and no atomic point has
  this fiber (`Point.fiber_map_surjective`).
* **Universe parameters and binder kinds**: each export's `levelParams` is pinned to a literal
  list, and explicit instantiation at distinct universes pins the positional order; the
  statements are pinned up to definitional equality by `example : T := @lemma`, and binder
  kinds are exercised by the applications.
* **Home module and collision guard**: each export is declared in the module; near-miss names
  that a future Mathlib could add (`dense_eq_atomic`, `atomic_covering`, `mem_atomic`,
  `Point.ofSurjective`) are asserted absent, so a repin adding them fails loudly here. (Exact
  name clashes already fail compilation on a repin.) This cannot guarantee future
  compatibility.
* **Import closure**: no `Mathlib.ModelTheory`, `Mathlib.CategoryTheory.Presentable` or
  `Mathlib.CategoryTheory.Topos` module and no other `InfinitaryLogic` module; contains
  `Mathlib.CategoryTheory.Sites.Point.Basic`; the total module count is pinned.
* **Axioms**: every export and every control uses only the standard axioms.

Run with: lake env lean scripts/check_atomic_point_regressions.lean
-/
import InfinitaryLogic.CategoryTheory.Sites.AtomicPoint

open Lean CategoryTheory CategoryTheory.GrothendieckTopology Opposite

universe w v u

namespace AtomicPointGuard

/-! ### Statements, pinned up to definitional equality -/

example : ∀ {C : Type u} [Category.{v} C] (hro : RightOreCondition C) {X : C} (S : Sieve X),
    S ∈ atomic hro X ↔ ∃ (Y : C) (f : Y ⟶ X), S f :=
  @mem_atomic_iff

example : ∀ {C : Type u} [Category.{v} C] {X : C} {S : Sieve X}, S ∈ dense X →
    ∃ (Y : C) (f : Y ⟶ X), S f :=
  @dense_covering_nonempty

example : ∀ {C : Type u} [Category.{v} C] (hro : RightOreCondition C), atomic hro = dense :=
  @atomic_eq_dense

example : ∀ {C : Type u} [Category.{v} C] (hro : RightOreCondition C) (F : C ⥤ Type w),
    (∀ {X : C} (R : Sieve X), R ∈ atomic hro X → ∀ x : F.obj X,
      ∃ (Y : C) (f : Y ⟶ X) (_ : R f) (y : F.obj Y), F.map f y = x) ↔
    ∀ ⦃X Y : C⦄ (f : Y ⟶ X), Function.Surjective (F.map f) :=
  @atomic_jointlySurjective_iff

example : ∀ {C : Type u} [Category.{v} C] {hro : RightOreCondition C}
    (Φ : (atomic hro).Point.{w}) ⦃X Y : C⦄ (f : Y ⟶ X), Function.Surjective (Φ.fiber.map f) :=
  @Point.fiber_map_surjective

/-! ### Positional universe order, by explicit instantiation at distinct universes -/

section UniverseOrder

variable {C : Type 3} [Category.{2} C] (hro : RightOreCondition C)

example {X : C} (S : Sieve X) : S ∈ atomic hro X ↔ ∃ (Y : C) (f : Y ⟶ X), S f :=
  mem_atomic_iff.{2, 3} hro S

example {X : C} {S : Sieve X} (hS : S ∈ dense X) : ∃ (Y : C) (f : Y ⟶ X), S f :=
  dense_covering_nonempty.{2, 3} hS

example : atomic hro = dense := atomic_eq_dense.{2, 3} hro

example (F : C ⥤ Type 1) (hF : ∀ ⦃X Y : C⦄ (f : Y ⟶ X), Function.Surjective (F.map f))
    {X : C} (R : Sieve X) (hR : R ∈ atomic hro X) (x : F.obj X) :
    ∃ (Y : C) (f : Y ⟶ X) (_ : R f) (y : F.obj Y), F.map f y = x :=
  (atomic_jointlySurjective_iff.{1, 2, 3} hro F).2 hF R hR x

example (Φ : (atomic hro).Point.{1}) {X Y : C} (f : Y ⟶ X) :
    Function.Surjective (Φ.fiber.map f) :=
  Point.fiber_map_surjective.{1, 2, 3} Φ f

end UniverseOrder

/-! ### Positive control: the Cantor inverse system on `ℕᵒᵖ` -/

/-- The right Ore condition on `ℕᵒᵖ`, with `W := max`. -/
theorem rightOre_natOp : RightOreCondition ℕᵒᵖ := fun {_ Y Z} _ _ ↦
  ⟨op (max Y.unop Z.unop), (homOfLE (le_max_left Y.unop Z.unop)).op,
    (homOfLE (le_max_right Y.unop Z.unop)).op, Subsingleton.elim _ _⟩

/-- The Cantor inverse system: `op n ↦ (Fin n → Bool)`, restriction along `Fin.castLE`. -/
def cantor : ℕᵒᵖ ⥤ Type where
  obj n := Fin n.unop → Bool
  map f := TypeCat.ofHom fun v ↦ v ∘ Fin.castLE (leOfHom f.unop)

/-- Every restriction map of the Cantor system is surjective: extend by `false`. -/
theorem cantor_map_surjective ⦃X Y : ℕᵒᵖ⦄ (f : Y ⟶ X) : Function.Surjective (cantor.map f) :=
  fun w ↦ ⟨fun i ↦ if h : i.val < X.unop then w ⟨i, h⟩ else false, funext fun i ↦
    (by simp [i.isLt] : (if h : i.val < X.unop then w ⟨i, h⟩ else false) = w i)⟩

/-- **Positive control (atomic continuity, not a point)**: the atomic covering condition holds
for the Cantor system. -/
theorem cantor_atomic {X : ℕᵒᵖ} (R : Sieve X) (hR : R ∈ atomic rightOre_natOp X)
    (x : cantor.obj X) : ∃ (Y : ℕᵒᵖ) (f : Y ⟶ X) (_ : R f) (y : cantor.obj Y),
      cantor.map f y = x :=
  (atomic_jointlySurjective_iff rightOre_natOp cantor).2 cantor_map_surjective R hR x

/-- **Negative control**: the category of elements of the Cantor system is not cofiltered: the
prefixes `(true)` and `(false)` of length one have no common refinement. So the Cantor system
satisfies the atomic covering condition without being the fiber of a point. -/
theorem cantor_elements_not_cofiltered : ¬ IsCofiltered cantor.Elements := by
  intro h
  obtain ⟨W, f, g, -⟩ := h.toIsCofilteredOrEmpty.cone_objs
    (cantor.elementsMk (op 1) fun _ ↦ true) (cantor.elementsMk (op 1) fun _ ↦ false)
  have hf : W.val ⟨0, _⟩ = true := congrFun f.map_val 0
  have hg : W.val ⟨0, _⟩ = false := congrFun g.map_val 0
  exact Bool.noConfusion (hf.symm.trans hg)

/-! ### Negative control: `Fin 2` with an empty-to-unit map -/

/-- The right Ore condition on the preorder category `Fin 2`, with `W := min`. -/
theorem rightOre_fin2 : RightOreCondition (Fin 2) := fun {_ Y Z} _ _ ↦
  ⟨min Y Z, homOfLE (min_le_left Y Z), homOfLE (min_le_right Y Z), Subsingleton.elim _ _⟩

/-- The functor `0 ↦ ∅`, `1 ↦ point` on `Fin 2`, as `i ↦ PLift (i = 1)`. -/
def emptyToUnit : Fin 2 ⥤ Type where
  obj i := PLift (i = 1)
  map {i j} f := TypeCat.ofHom fun x ↦
    ⟨le_antisymm (Fin.le_last j) (x.down ▸ leOfHom f)⟩

/-- The map `0 ⟶ 1` of `emptyToUnit` is not surjective. -/
theorem emptyToUnit_not_surjective :
    ¬ Function.Surjective (emptyToUnit.map (homOfLE (Fin.zero_le 1) : (0 : Fin 2) ⟶ 1)) :=
  fun h ↦ absurd (h ⟨rfl⟩).choose.down (by decide)

/-- **Negative control**: the atomic covering condition fails for `emptyToUnit`. -/
theorem emptyToUnit_not_atomic :
    ¬ ∀ {X : Fin 2} (R : Sieve X), R ∈ atomic rightOre_fin2 X → ∀ x : emptyToUnit.obj X,
      ∃ (Y : Fin 2) (f : Y ⟶ X) (_ : R f) (y : emptyToUnit.obj Y), emptyToUnit.map f y = x :=
  fun h ↦ emptyToUnit_not_surjective
    ((atomic_jointlySurjective_iff rightOre_fin2 emptyToUnit).1 h _)

/-- **Negative control**: no point of the atomic site on `Fin 2` has fiber `emptyToUnit`. -/
theorem emptyToUnit_not_fiber : ∀ Φ : (atomic rightOre_fin2).Point.{0}, Φ.fiber ≠ emptyToUnit :=
  fun Φ hΦ ↦ emptyToUnit_not_surjective (hΦ ▸ Point.fiber_map_surjective Φ _)

end AtomicPointGuard

/-! ### Universe parameters, home module, collision guard, closure, axioms -/

/-- The module under guard. -/
def guardedModule : Name := `InfinitaryLogic.CategoryTheory.Sites.AtomicPoint

/-- Each export with its literal `levelParams`. -/
def exportLevels : List (Name × List Name) :=
  [(``GrothendieckTopology.mem_atomic_iff, [`v, `u]),
   (``GrothendieckTopology.dense_covering_nonempty, [`v, `u]),
   (``GrothendieckTopology.atomic_eq_dense, [`v, `u]),
   (``GrothendieckTopology.atomic_jointlySurjective_iff, [`w, `v, `u]),
   (``GrothendieckTopology.Point.fiber_map_surjective, [`w, `v, `u])]

/-- Near-miss names a future Mathlib could add; each must be absent at this pin. -/
def nearMisses : List Name :=
  [`CategoryTheory.GrothendieckTopology.dense_eq_atomic,
   `CategoryTheory.GrothendieckTopology.atomic_covering,
   `CategoryTheory.GrothendieckTopology.mem_atomic,
   `CategoryTheory.GrothendieckTopology.Point.ofSurjective]

/-- Module-name prefixes no module of the closure may have. -/
def forbiddenPrefixes : List Name :=
  [`Mathlib.ModelTheory, `Mathlib.CategoryTheory.Presentable, `Mathlib.CategoryTheory.Topos,
   `InfinitaryLogic]

/-- The exact number of modules in the closure (the module included). -/
def closureSize : Nat := 2862

run_cmd do
  let env ← getEnv
  for (d, lvls) in exportLevels do
    let some ci := env.find? d | throwError "declaration {d} not found"
    unless ci.levelParams == lvls do
      throwError "[UNIVERSE DRIFT] {d} has levelParams {ci.levelParams}, expected {lvls}"
    let some idx := env.getModuleIdxFor? d | throwError "{d} has no home module"
    let m := env.header.moduleNames[idx.toNat]!
    unless m == guardedModule do throwError "[MOVED] {d} is declared in {m}"
  for n in nearMisses do
    if (env.find? n).isSome then
      throwError "[COLLISION] {n} now exists; review the AtomicPoint exports against it"
  let mods := env.header.moduleNames
  unless mods.contains `Mathlib.CategoryTheory.Sites.Point.Basic do
    throwError "[MISSING ROUTE] Mathlib.CategoryTheory.Sites.Point.Basic is not in the closure"
  let hits := mods.toList.filter fun m ↦
    m != guardedModule && forbiddenPrefixes.any (·.isPrefixOf m)
  unless hits.isEmpty do throwError "[BROAD CONE] the closure reaches {hits}"
  unless mods.size == closureSize do
    throwError "[CLOSURE DRIFT] the closure has {mods.size} modules, expected {closureSize}; \
      update closureSize deliberately"

/-- The audited declarations. -/
def auditedDecls : List Name :=
  exportLevels.map (·.1) ++
  [``AtomicPointGuard.rightOre_natOp, ``AtomicPointGuard.cantor_map_surjective,
   ``AtomicPointGuard.cantor_atomic, ``AtomicPointGuard.cantor_elements_not_cofiltered,
   ``AtomicPointGuard.rightOre_fin2,
   ``AtomicPointGuard.emptyToUnit_not_surjective, ``AtomicPointGuard.emptyToUnit_not_atomic,
   ``AtomicPointGuard.emptyToUnit_not_fiber]

/-- The standard axioms. -/
def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  for n in auditedDecls do
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a ↦ !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "Atomic-point regression guard: OK (statements, levelParams and positional universe \
    order of the five exports pinned; home module pinned; near-miss names absent; \
    atomic-continuity example: the Cantor system on Nat^op satisfies the atomic covering \
    condition, and its category of elements is not cofiltered (not a point); negative \
    control: Fin 2 with an empty-to-unit map fails it and is the fiber of no atomic point; \
    closure \
    free of ModelTheory, Presentable, Topos and other project modules, size pinned; standard \
    axioms)"
