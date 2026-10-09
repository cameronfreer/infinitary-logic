/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# Atomic sites: covering sieves, the dense topology, and points

For a category `C` satisfying the right Ore condition, Mathlib defines the atomic Grothendieck
topology `GrothendieckTopology.atomic hro` (covering sieves = nonempty sieves) and, for any `C`,
the dense topology `GrothendieckTopology.dense`, but at the pinned Mathlib it states no covering
lemma for `atomic` and no comparison between the two. This file supplies both, and the
description of the atomic covering condition on an arbitrary functor `F : C ⥤ Type w`.

## Main results

* `mem_atomic_iff`: the covering sieves of `atomic hro` are exactly the nonempty sieves.
* `dense_covering_nonempty`: a dense covering sieve is nonempty. This is the unconditional
  direction of the comparison, and needs no hypothesis on `C`.
* `atomic_eq_dense`: under the right Ore condition the two topologies coincide. The converse
  direction (a nonempty sieve is dense-covering) is where the Ore condition is used; there is no
  comparison without it, since `atomic` itself cannot be formed without `hro`.
* `atomic_jointlySurjective_iff`: for **every** functor `F : C ⥤ Type w`, the joint-surjectivity
  condition of a point with respect to `atomic hro` holds iff every `F.map f` is surjective.
* `Point.fiber_map_surjective`: every map of the fiber functor of a point of the atomic site is
  surjective.

## Non-claims

* Nothing about flatness: `atomic_jointlySurjective_iff` holds for every functor.
* No construction of points. Packaging a functor `F` with surjective maps as a Mathlib
  `GrothendieckTopology.Point` of the atomic site needs, in addition to the covering condition
  supplied here, that `F.Elements` be cofiltered and initially small; these are separate
  obligations, not addressed in this file.
* Nothing about the existence of points, enough points, or Booleanness of the sheaf topos, and
  no classifying-topos equivalence.
* Nothing about preservation of `κ`-limits.
* No model theory: this module imports no `ModelTheory` file and no other project module.
-/

universe w v u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C]

/-- Covering sieves of the atomic topology are exactly the nonempty sieves. -/
theorem mem_atomic_iff (hro : RightOreCondition C) {X : C} (S : Sieve X) :
    S ∈ atomic hro X ↔ ∃ (Y : C) (f : Y ⟶ X), S f :=
  Iff.rfl

/-- The unconditional direction: a dense covering sieve is nonempty. (Apply density at the
identity of `X`.) No hypothesis on `C` is needed. -/
theorem dense_covering_nonempty {X : C} {S : Sieve X} (hS : S ∈ dense X) :
    ∃ (Y : C) (f : Y ⟶ X), S f := by
  obtain ⟨Z, g, hg⟩ := hS (𝟙 X)
  exact ⟨Z, g ≫ 𝟙 X, hg⟩

/-- Under the right Ore condition the atomic and dense topologies coincide. The inclusion of
dense-covering sieves among the nonempty ones is `dense_covering_nonempty` and holds for every
category; the other inclusion completes each span `Y ⟶ X ⟵ Z` by the Ore condition. -/
theorem atomic_eq_dense (hro : RightOreCondition C) : atomic hro = dense := by
  refine GrothendieckTopology.ext (funext fun X ↦ Set.ext fun S ↦ ⟨?_, ?_⟩)
  · rintro ⟨Z, s, hs⟩ Y f
    obtain ⟨W, wy, wz, h⟩ := hro f s
    exact ⟨W, wy, h ▸ S.downward_closed hs wz⟩
  · exact dense_covering_nonempty

/-- **Atomic covering condition for a functor.** For any functor `F : C ⥤ Type w` on a category
satisfying the right Ore condition, the joint-surjectivity condition of a point of the atomic
site holds iff every map `F.map f` is surjective. No flatness, smallness or model theory is
involved. -/
theorem atomic_jointlySurjective_iff (hro : RightOreCondition C) (F : C ⥤ Type w) :
    (∀ {X : C} (R : Sieve X), R ∈ atomic hro X → ∀ x : F.obj X,
      ∃ (Y : C) (f : Y ⟶ X) (_ : R f) (y : F.obj Y), F.map f y = x) ↔
    ∀ ⦃X Y : C⦄ (f : Y ⟶ X), Function.Surjective (F.map f) := by
  constructor
  · intro h X Y f x
    obtain ⟨Z, g, hg, y, hy⟩ := h (Sieve.generate (Presieve.singleton f))
      ⟨Y, f, Sieve.le_generate _ Y f (Presieve.singleton_self f)⟩ x
    obtain ⟨Y', k, g', hs, rfl⟩ := hg
    cases hs
    exact ⟨F.map k y, by rw [← Functor.map_comp_apply]; exact hy⟩
  · rintro hF X R ⟨Y, f, hf⟩ x
    obtain ⟨y, hy⟩ := hF f x
    exact ⟨Y, f, hf, y, hy⟩

namespace Point

/-- Every map of the fiber functor of a point of the atomic site is surjective. -/
theorem fiber_map_surjective {hro : RightOreCondition C} (Φ : (atomic hro).Point.{w})
    ⦃X Y : C⦄ (f : Y ⟶ X) : Function.Surjective (Φ.fiber.map f) :=
  (atomic_jointlySurjective_iff hro Φ.fiber).1 (fun R h x ↦ Φ.jointly_surjective R h x) f

end Point

end CategoryTheory.GrothendieckTopology
