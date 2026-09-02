/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Borel graphs with singleton vertical sections

A **functional** Borel graph — a Borel `G ⊆ X × Y` with at most one `y` above each `x` — has a
Borel domain, and the partial function it names is Borel measurable.

Both facts are Lusin–Souslin, which Mathlib supplies; this file packages the argument so consumers
never restate it.  Nothing here is model-theoretic.

## The results

* `measurableSet_domain` — the domain `Prod.fst '' G` is Borel.  Proved directly, with no subtype:
  `MeasurableSet.image_of_measurable_injOn` asks for `InjOn`, and `InjOn Prod.fst G` is exactly the
  functionality hypothesis.
* `measurableEmbedding_proj` — the projection `↥G → X` is a measurable embedding.  Restricting the
  projection to `↥G` turns `injOn_fst` into the global injectivity required by
  `Measurable.measurableEmbedding`.
* `equivDomain` — hence a measurable equivalence `↥G ≃ᵐ ↥domain`, whose inverse is measurable by
  construction.
* `value`, `measurable_value`, `value_mem`, `value_eq_of_mem` — the induced partial function on the
  domain, measurable, and **identified**: a measurable-but-unspecified map would be unusable, so
  the two specifications are part of the interface rather than an afterthought.

## Scope

Only the canonical subtype-domain value map is built.  Totalized forms — `X → Option Y`, or a
junk-valued `X → Y` — are derivable from it and are deliberately deferred until a consumer needs
one; building all three now would fix an interface no caller has yet exercised.
-/

open MeasureTheory Set

universe u v

variable {X : Type u} {Y : Type v}
  [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace Y] [StandardBorelSpace Y]

/-- A Borel graph whose vertical sections are singletons or empty: it names a partial function. -/
structure BorelFunctionalGraph (G : Set (X × Y)) : Prop where
  /-- The graph is Borel. -/
  measurableSet_graph : MeasurableSet G
  /-- At most one point lies above each first coordinate. -/
  functional : ∀ {x y z}, (x, y) ∈ G → (x, z) ∈ G → y = z

namespace BorelFunctionalGraph

variable {G : Set (X × Y)}

/-- The domain: the first coordinates covered by the graph.

Depends only on `G` — the evidence is taken so that `h.domain` reads naturally at use sites. -/
def domain (_h : BorelFunctionalGraph G) : Set X := Prod.fst '' G

omit [StandardBorelSpace X] [StandardBorelSpace Y] in
theorem mem_domain_iff (h : BorelFunctionalGraph G) {x : X} :
    x ∈ h.domain ↔ ∃ y, (x, y) ∈ G :=
  ⟨fun ⟨p, hp, hx⟩ => ⟨p.2, by rw [← hx]; exact hp⟩, fun ⟨y, hy⟩ => ⟨(x, y), hy, rfl⟩⟩

omit [StandardBorelSpace X] [StandardBorelSpace Y] in
/-- Functionality, as injectivity of the projection **on** `G`.  This is the exact hypothesis
`MeasurableSet.image_of_measurable_injOn` consumes. -/
theorem injOn_fst (h : BorelFunctionalGraph G) : Set.InjOn Prod.fst G := by
  rintro ⟨x, y⟩ hp ⟨x', z⟩ hq (hxx : x = x')
  subst hxx
  exact Prod.ext rfl (h.functional hp hq)

/-- **The domain is Borel** (Lusin–Souslin). -/
theorem measurableSet_domain (h : BorelFunctionalGraph G) : MeasurableSet h.domain :=
  h.measurableSet_graph.image_of_measurable_injOn measurable_fst h.injOn_fst

/-! ### The subtype layer

Restricting the projection to `↥G` turns `injOn_fst` into the global injectivity required by
`Measurable.measurableEmbedding`. -/

/-- The projection of the graph onto its first coordinate. -/
def proj (G : Set (X × Y)) : ↥G → X := fun p => (p : X × Y).1

omit [StandardBorelSpace X] [StandardBorelSpace Y] in
theorem injective_proj (h : BorelFunctionalGraph G) : Function.Injective (proj G) :=
  fun p q hpq => Subtype.ext (h.injOn_fst p.2 q.2 hpq)

omit [StandardBorelSpace X] [StandardBorelSpace Y] in
theorem measurable_proj : Measurable (proj G) := measurable_fst.comp measurable_subtype_coe

omit [StandardBorelSpace X] [StandardBorelSpace Y] in
theorem range_proj (h : BorelFunctionalGraph G) : Set.range (proj G) = h.domain := by
  ext x
  exact ⟨fun ⟨p, hp⟩ => ⟨(p : X × Y), p.2, hp⟩, fun ⟨p, hp, hx⟩ => ⟨⟨p, hp⟩, hx⟩⟩

/-- **The projection is a measurable embedding** (Lusin–Souslin). -/
theorem measurableEmbedding_proj (h : BorelFunctionalGraph G) :
    MeasurableEmbedding (proj G) := by
  have := h.measurableSet_graph.standardBorel
  exact measurable_proj.measurableEmbedding h.injective_proj

/-- Reindex a domain point as a point of the projection's range. -/
private def toRange (h : BorelFunctionalGraph G) (x : ↥h.domain) : ↥(Set.range (proj G)) :=
  ⟨(x : X), by rw [h.range_proj]; exact x.2⟩

/-- **The graph is measurably equivalent to its domain.**  In particular the inverse of the
projection is measurable — the point of the whole construction.

Built explicitly with a transparent forward map, so `coe_equivDomain` holds by `rfl`;
measurability of the inverse comes from `MeasurableEmbedding.measurable_rangeSplitting`. -/
noncomputable def equivDomain (h : BorelFunctionalGraph G) : ↥G ≃ᵐ ↥h.domain where
  toFun p := ⟨proj G p, ⟨(p : X × Y), p.2, rfl⟩⟩
  invFun x := Set.rangeSplitting (proj G) (h.toRange x)
  left_inv _p := h.injective_proj (Set.apply_rangeSplitting (proj G) _)
  right_inv x := Subtype.ext (Set.apply_rangeSplitting (proj G) (h.toRange x))
  measurable_toFun := measurable_proj.subtype_mk
  measurable_invFun :=
    h.measurableEmbedding_proj.measurable_rangeSplitting.comp
      measurable_subtype_coe.subtype_mk

/-- The forward map is the projection — true by construction, and what identifies `value`. -/
theorem coe_equivDomain (h : BorelFunctionalGraph G) (p : ↥G) :
    ((h.equivDomain p : ↥h.domain) : X) = proj G p := rfl

/-! ### The value map

`value` alone would be unusable: a measurable map with no stated relation to `G` identifies
nothing.  `value_mem` and `value_eq_of_mem` are therefore part of the interface — the first says
the selected value is the one the graph names, the second is uniqueness in the form callers
actually apply. -/

/-- The partial function named by the graph, on its domain. -/
noncomputable def value (h : BorelFunctionalGraph G) (x : ↥h.domain) : Y :=
  ((h.equivDomain.symm x : ↥G) : X × Y).2

/-- **The selected value is the one the graph names.** -/
theorem value_mem (h : BorelFunctionalGraph G) (x : ↥h.domain) : ((x : X), h.value x) ∈ G := by
  have hfst : ((h.equivDomain.symm x : ↥G) : X × Y).1 = (x : X) :=
    congrArg Subtype.val (h.equivDomain.apply_symm_apply x)
  have hmem := (h.equivDomain.symm x).2
  rwa [show ((x : X), h.value x) = ((h.equivDomain.symm x : ↥G) : X × Y) from
    Prod.ext hfst.symm rfl]

/-- **Uniqueness**, in the form callers apply: any value the graph names at a domain point *is*
the selected one. -/
theorem value_eq_of_mem (h : BorelFunctionalGraph G) {x : ↥h.domain} {y : Y}
    (hy : ((x : X), y) ∈ G) : h.value x = y :=
  h.functional (h.value_mem x) hy

/-- **The value map is measurable.** -/
theorem measurable_value (h : BorelFunctionalGraph G) : Measurable h.value :=
  measurable_snd.comp (measurable_subtype_coe.comp h.equivDomain.symm.measurable)

end BorelFunctionalGraph
