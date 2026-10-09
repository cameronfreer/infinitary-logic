/-
Guard: the default import surface (`import InfinitaryLogic`, i.e. `InfinitaryLogic.All`) stays
free of the category-theory machinery that the atomic-site and AEC work brings in.

That work is exposed through `InfinitaryLogic.Everything` only (rulings D-7, D-9). This file
imports only `InfinitaryLogic` and asserts that its import closure

* contains no module with prefix `Mathlib.CategoryTheory.Sites`,
  `Mathlib.CategoryTheory.Presentable`, `Mathlib.CategoryTheory.Topos`,
  `Mathlib.CategoryTheory.Filtered` or `Mathlib.CategoryTheory.Limits`;
* contains no `InfinitaryLogic.CategoryTheory.*` and no `InfinitaryLogic.AEC.*` module;
* contains, among all `Mathlib.CategoryTheory.*` modules, exactly the allow-listed ones (today
  only `Mathlib.CategoryTheory.ConcreteCategory.Bundled`, reached from
  `Mathlib.ModelTheory.Bundled`).

Run with: lake env lean scripts/check_default_surface_category_free.lean
-/
import InfinitaryLogic

open Lean

/-- Module-name prefixes the default surface must not reach. -/
def forbiddenPrefixes : List Name :=
  [`Mathlib.CategoryTheory.Sites, `Mathlib.CategoryTheory.Presentable,
   `Mathlib.CategoryTheory.Topos, `Mathlib.CategoryTheory.Filtered,
   `Mathlib.CategoryTheory.Limits, `InfinitaryLogic.CategoryTheory, `InfinitaryLogic.AEC]

/-- The exact set of `Mathlib.CategoryTheory` modules allowed in the default surface. -/
def allowedCategoryModules : List Name :=
  [`Mathlib.CategoryTheory.ConcreteCategory.Bundled]

run_cmd do
  let mods := (← getEnv).header.moduleNames.toList
  let hits := mods.filter fun m ↦ forbiddenPrefixes.any (·.isPrefixOf m)
  unless hits.isEmpty do
    throwError "[BROAD CONE] the default surface reaches {hits}"
  let cat := mods.filter (`Mathlib.CategoryTheory).isPrefixOf
  let extra := cat.filter fun m ↦ !allowedCategoryModules.contains m
  let missing := allowedCategoryModules.filter fun m ↦ !cat.contains m
  unless extra.isEmpty && missing.isEmpty do
    throwError "[CLOSURE DRIFT] the Mathlib.CategoryTheory modules of the default surface are \
      {cat}; update allowedCategoryModules deliberately (extra {extra}, missing {missing})"
  logInfo m!"Default-surface category guard: OK (the {mods.length}-module closure of \
    InfinitaryLogic reaches no Sites, Presentable, Topos, Filtered or Limits module and no \
    InfinitaryLogic.CategoryTheory or InfinitaryLogic.AEC module; its only \
    Mathlib.CategoryTheory module is ConcreteCategory.Bundled)"
