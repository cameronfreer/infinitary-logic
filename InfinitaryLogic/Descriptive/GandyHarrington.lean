/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.SilverBurgess
import Mathlib.Topology.Defs.Induced

/-!
# Gandy-Harrington Reduction and Silver's Theorem for Borel Relations

This file provides:
1. The Borel-to-closed reduction (`borel_to_closed_reduction`): if a Borel
   equivalence relation on a Polish space has uncountably many classes, there
   exists a Polish space Y with a continuous injective map to α on which the
   pulled-back relation is closed and still has uncountably many classes.
2. `silver_core_polish`: Silver's theorem for Borel equivalence relations,
   derived from the reduction + `silver_core_closed`.
3. `silverBurgessDichotomy`: the full dichotomy for standard Borel spaces.

## Status

`borel_to_closed_reduction` requires the Gandy-Harrington topology
construction (sorry). Once filled, `silver_core_polish` and
`silverBurgessDichotomy` become sorry-free, making `morley_counting`
fully unconditional.
-/

universe u v

open Set Cardinal Topology MeasureTheory

/-! ### Helper lemmas -/

/-- Each equivalence class of a Borel relation is measurable (Borel section). -/
private theorem class_measurableSet {α : Type u}
    [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    (r : Setoid α) (hr : MeasurableSet {p : α × α | r.r p.1 p.2}) (x : α) :
    MeasurableSet {y : α | r.r x y} := by
  have : {y : α | r.r x y} = (fun y => (x, y)) ⁻¹' {p : α × α | r.r p.1 p.2} := by
    ext y; simp
  rw [this]
  exact hr.preimage (measurable_const.prodMk measurable_id)

/-- Each equivalence class of a Borel relation is analytic. -/
private theorem class_analyticSet {α : Type u}
    [TopologicalSpace α] [PolishSpace α] [MeasurableSpace α] [BorelSpace α]
    (r : Setoid α) (hr : MeasurableSet {p : α × α | r.r p.1 p.2}) (x : α) :
    AnalyticSet {y : α | r.r x y} :=
  (class_measurableSet r hr x).analyticSet

/-- If every r-class on α is hit by the image of i, the comap quotient
surjects onto the original quotient — so uncountability transfers. -/
private theorem not_countable_comap_of_hits_all_classes {α : Type u} {Y : Type u}
    (r : Setoid α) (i : Y → α)
    (hhit : ∀ x : α, ∃ y : Y, r.r (i y) x)
    (hunc : ¬ Countable (Quotient r)) :
    ¬ Countable (Quotient (Setoid.comap i r)) := by
  intro hcount
  apply hunc
  -- Build surjection: Quotient (comap i r) → Quotient r
  -- The natural map Quotient(comap i r) → Quotient r
  let φ : Quotient (Setoid.comap i r) → Quotient r :=
    Quotient.lift (fun y => ⟦i y⟧) (fun a b h => Quotient.sound h)
  have hsurj : Function.Surjective φ := by
    intro q
    refine Quotient.inductionOn q fun x => ?_
    obtain ⟨y, hy⟩ := hhit x
    exact ⟨Quotient.mk _ y, Quotient.sound hy⟩
  exact hsurj.countable

/-! ### GH core: analytic class-condensation points -/

/-- A point x is a GH core point for r if every analytic set containing x
meets uncountably many r-classes. -/
def IsGHCorePt {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    (r : Setoid α) (x : α) : Prop :=
  ∀ {s : Set α}, AnalyticSet s → x ∈ s →
    ¬Set.Countable {q : Quotient r | ∃ y ∈ s, ⟦y⟧ = q}

/-- The GH core: the set of all GH core points. -/
def ghCore {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    (r : Setoid α) : Set α :=
  {x | IsGHCorePt r x}

/-! ### Step 2: Every class meets the GH core -/

/-- Every r-class of a Borel relation with uncountably many classes meets
the GH core. Uses the analytic condensation argument: the non-core classes
form a countable set (covered by countably many "small" analytic sets). -/
private theorem class_hits_ghCore {α : Type u}
    [MetricSpace α] [CompleteSpace α] [SecondCountableTopology α]
    [MeasurableSpace α] [BorelSpace α]
    (r : Setoid α) (hr : MeasurableSet {p : α × α | r.r p.1 p.2})
    (hunc : ¬ Countable (Quotient r)) :
    ∀ x : α, ∃ y ∈ ghCore r, r.r y x := by
  sorry

/-! ### Step 3: Analytic rectangle separation on the core -/

/-- On the GH core, non-related points can be separated by analytic rectangles
with no cross-equivalence. Uses `AnalyticSet.measurablySeparable` on the
r-saturations of analytic neighborhoods. -/
private theorem core_separates_not_related {α : Type u}
    [MetricSpace α] [CompleteSpace α] [SecondCountableTopology α]
    [MeasurableSpace α] [BorelSpace α]
    (r : Setoid α) (hr : MeasurableSet {p : α × α | r.r p.1 p.2})
    {x y : α} (hx : x ∈ ghCore r) (hy : y ∈ ghCore r) (hxy : ¬ r.r x y) :
    ∃ U V : Set α,
      AnalyticSet U ∧ AnalyticSet V ∧
      x ∈ U ∧ y ∈ V ∧
      ∀ u ∈ U, ∀ v ∈ V, ¬ r.r u v := by
  sorry

/-! ### Gandy-Harrington for a specific relation -/

/-- **Gandy-Harrington for a Borel relation**: Given a Borel equivalence
relation r on a Polish space with uncountably many classes, there exists a
Polish Ω with a continuous injective map to α such that:
1. Every r-class meets the range of i.
2. The pullback of Eᶜ is open in Ω × Ω.

The proof combines all GH ingredients:
- `class_hits_ghCore`: every class meets the GH core
- `core_separates_not_related`: analytic rectangle separation on the core
- The GH topology on the core + Polish subcore extraction

The sorry encompasses the full GH topology construction. -/
theorem gandy_harrington_for_relation {α : Type u}
    [MetricSpace α] [CompleteSpace α] [SecondCountableTopology α]
    [MeasurableSpace α] [BorelSpace α]
    (r : Setoid α) (hr : MeasurableSet {p : α × α | r.r p.1 p.2})
    (hunc : ¬ Countable (Quotient r)) :
    ∃ (Ω : Type u) (_ : MetricSpace Ω) (_ : CompleteSpace Ω)
      (_ : SecondCountableTopology Ω) (i : Ω → α),
      Continuous i ∧ Function.Injective i ∧
      (∀ x : α, ∃ y : Ω, r.r (i y) x) ∧
      IsOpen ((fun p : Ω × Ω => ((i p.1), (i p.2))) ⁻¹'
        {p : α × α | ¬ r.r p.1 p.2}) := by
  sorry

/-! ### GH core existence (derived from relation-specific GH) -/

/-- The GH core for a specific Borel equivalence relation. Derived from
`gandy_harrington_for_relation`: closedness comes from `isOpen_compl_iff`,
class-hitting is directly one of the fields. -/
private theorem gh_exists_core {α : Type u}
    [MetricSpace α] [CompleteSpace α] [SecondCountableTopology α]
    [MeasurableSpace α] [BorelSpace α]
    (r : Setoid α) (hr : MeasurableSet {p : α × α | r.r p.1 p.2})
    (hunc : ¬ Countable (Quotient r)) :
    ∃ (Y : Type u) (_ : MetricSpace Y) (_ : CompleteSpace Y)
      (_ : SecondCountableTopology Y) (i : Y → α),
      Continuous i ∧ Function.Injective i ∧
      IsClosed {p : Y × Y | r.r (i p.1) (i p.2)} ∧
      (∀ x : α, ∃ y : Y, r.r (i y) x) := by
  obtain ⟨Ω, instM, instC, instS, i, hi_cont, hi_inj, hi_hit, hi_open⟩ :=
    gandy_harrington_for_relation r hr hunc
  refine ⟨Ω, instM, instC, instS, i, hi_cont, hi_inj, ?_, hi_hit⟩
  -- Closedness: the complement of E's pullback is open
  rw [← isOpen_compl_iff]
  convert hi_open using 1

/-! ### Borel-to-closed reduction -/

/-- **Gandy-Harrington reduction**: A Borel equivalence relation on a Polish
space with uncountably many classes admits a Polish space Y with a continuous
injective map to α on which the pulled-back relation is closed and still has
uncountably many classes.

Derived from `gh_exists_core` + `not_countable_comap_of_hits_all_classes`. -/
theorem borel_to_closed_reduction {α : Type u}
    [MetricSpace α] [CompleteSpace α] [SecondCountableTopology α]
    [MeasurableSpace α] [BorelSpace α]
    (r : Setoid α) (hr : MeasurableSet {p : α × α | r.r p.1 p.2})
    (hunc : ¬ Countable (Quotient r)) :
    ∃ (Y : Type u) (_ : MetricSpace Y) (_ : CompleteSpace Y)
      (_ : SecondCountableTopology Y) (i : Y → α),
      Continuous i ∧ Function.Injective i ∧
      IsClosed {p : Y × Y | r.r (i p.1) (i p.2)} ∧
      ¬ Countable (Quotient (Setoid.comap i r)) := by
  obtain ⟨Y, instM, instC, instS, i, hi_cont, hi_inj, hi_closed, hi_hit⟩ :=
    gh_exists_core r hr hunc
  exact ⟨Y, instM, instC, instS, i, hi_cont, hi_inj, hi_closed,
    not_countable_comap_of_hits_all_classes r i hi_hit hunc⟩

/-- **Silver's theorem** for Borel equivalence relations on Polish spaces.
Reduces to the closed case via `borel_to_closed_reduction`, then applies
`silver_core_closed` on the subspace and composes with the embedding. -/
theorem silver_core_polish {α : Type u}
    [MetricSpace α] [CompleteSpace α] [SecondCountableTopology α]
    [MeasurableSpace α] [BorelSpace α]
    (r : Setoid α) (hr : MeasurableSet {p : α × α | r.r p.1 p.2}) :
    Countable (Quotient r) ∨
      ∃ f : (ℕ → Bool) → α,
        Continuous f ∧ Function.Injective f ∧
        ∀ a b, a ≠ b → ¬ r.r (f a) (f b) := by
  by_cases hcount : Countable (Quotient r)
  · exact Or.inl hcount
  · right
    -- Apply the Borel-to-closed reduction
    obtain ⟨Y, instM, instC, instS, i, hi_cont, hi_inj, hi_closed, hi_unc⟩ :=
      borel_to_closed_reduction r hr hcount
    -- Apply silver_core_closed on Y
    have hY := @silver_core_closed Y instM instC instS (Setoid.comap i r) hi_closed
    rcases hY with hY_count | ⟨f, hf_cont, hf_inj, hf_ineq⟩
    · exact absurd hY_count hi_unc
    · -- Compose f with i
      exact ⟨i ∘ f,
        hi_cont.comp hf_cont,
        hi_inj.comp hf_inj,
        fun a b hab h => hf_ineq a b hab (by rwa [Setoid.comap_rel])⟩

/-! ### Silver-Burgess dichotomy -/

namespace FirstOrder.Language

/-- The Silver-Burgess dichotomy for Borel equivalence relations on standard Borel
spaces, derived from `silver_core_polish`. -/
theorem silverBurgessDichotomy : SilverBurgessDichotomy.{v} := by
  intro X _ _ r hr
  -- Upgrade the standard Borel space to a Polish topology
  letI := upgradeStandardBorel X
  -- Further upgrade to a compatible complete metric
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable X
  rcases silver_core_polish r hr with h_count | ⟨f, hf_cont, hf_inj, hf_ineq⟩
  · left; exact mk_le_aleph0
  · right
    apply le_antisymm
    · haveI : Nonempty X := ⟨f (fun _ => false)⟩
      exact mk_quotient_le_continuum_of_polish r
    · have hinj : Function.Injective (fun x : ULift.{v} (ℕ → Bool) =>
          Quotient.mk r (f x.down)) := by
        intro ⟨a⟩ ⟨b⟩ h
        apply ULift.ext
        by_contra hab
        exact hf_ineq a b hab (Quotient.exact h)
      calc Cardinal.continuum
          = lift.{v} #(ℕ → Bool) := by
            rw [show #(ℕ → Bool) = Cardinal.continuum from
              (Cardinal.power_def Bool ℕ).symm.trans (by rw [Cardinal.mk_bool, Cardinal.mk_nat,
                Cardinal.two_power_aleph0])
            , Cardinal.lift_continuum]
        _ = #(ULift.{v} (ℕ → Bool)) := (Cardinal.mk_uLift _).symm
        _ ≤ #(Quotient r) := mk_le_of_injective hinj

end FirstOrder.Language
