/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.PerfectAntichain
import InfinitaryLogic.Descriptive.CantorStabilization

/-!
# Transporting antichains across a measurable embedding

A measurable embedding `g : X → Y` between Polish spaces that preserves and reflects two
equivalence relations (`r' (g x) (g y) ↔ r x y`) transports Cantor antichains in both
directions (`hasCantorAntichainOn_image_iff`), hence thinness
(`isThinOn_image_iff`).  The ambient class `A` need not be Borel, and neither relation need be
Borel: only the witnesses are Borel.

The argument transports a Borel witness and then extracts a new Cantor copy; it does not claim
that any composed map is continuous.  Forward: the image under `g` of the range of a Cantor
antichain is an uncountable Borel set (Lusin–Souslin, through the measurable embedding) of
pairwise inequivalent points, so it contains a Cantor copy
(`MeasurableSet.exists_nat_bool_injection_of_not_countable`), which is a Cantor antichain in the
image class.  Backward: the preimage under `g` of the range of a Cantor antichain in the image
is an uncountable Borel subset of `A` of pairwise inequivalent points, and the same extraction
applies.

Ambient Polish spaces and Cantor-copy extraction are used; no logic topology and no spectrum
characterization.
-/

open MeasureTheory Set Function

variable {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- Cantor space is uncountable. -/
private theorem not_countable_cantor : ¬ Countable (ℕ → Bool) := by
  intro h
  obtain ⟨g, hg⟩ := exists_surjective_nat (ℕ → Bool)
  obtain ⟨n, hn⟩ := hg fun k => !(g k k)
  have he := congrFun hn n
  simp at he

omit [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- Pairwise inequivalent images are distinct. -/
private theorem injective_of_pairwise_inequiv' {r : Setoid X} {f : (ℕ → Bool) → X}
    (hineq : ∀ x y, x ≠ y → ¬r.r (f x) (f y)) : Injective f := fun x y hxy => by
  by_contra hne
  exact hineq x y hne (hxy ▸ r.refl _)

/-- The range of a Cantor antichain is an uncountable Borel set. -/
private theorem range_antichain_props {r : Setoid X} (f : (ℕ → Bool) → X) (hcont : Continuous f)
    (hineq : ∀ x y, x ≠ y → ¬r.r (f x) (f y)) :
    MeasurableSet (range f) ∧ ¬ (range f).Countable := by
  have hinj : Injective f := injective_of_pairwise_inequiv' hineq
  refine ⟨(isCompact_range hcont).isClosed.measurableSet, fun hc => not_countable_cantor ?_⟩
  have : Countable (range f) := hc.to_subtype
  exact (Set.rangeFactorization_injective.mpr hinj).countable

/-- **Antichain transport, both directions.**  For a measurable embedding preserving and
reflecting the relations, the image class carries a Cantor antichain iff the class does. -/
theorem hasCantorAntichainOn_image_iff {r : Setoid X} {r' : Setoid Y} {g : X → Y}
    (hg : MeasurableEmbedding g) (hrel : ∀ x y, r'.r (g x) (g y) ↔ r.r x y) (A : Set X) :
    HasCantorAntichainOn r' (g '' A) ↔ HasCantorAntichainOn r A := by
  constructor
  · rintro ⟨f, hcont, hmem, hineq⟩
    obtain ⟨hB, hunc⟩ := range_antichain_props f hcont hineq
    -- the preimage of the witness: Borel, uncountable, inside `A`
    have hpre : MeasurableSet (g ⁻¹' range f) := hg.measurable hB
    have hpre_unc : ¬ (g ⁻¹' range f).Countable := by
      intro hc
      apply hunc
      have : range f ⊆ g '' (g ⁻¹' range f) := by
        rintro _ ⟨x, rfl⟩
        obtain ⟨a, -, ha⟩ := hmem x
        exact ⟨a, by rw [Set.mem_preimage, ha]; exact ⟨x, rfl⟩, ha⟩
      exact (hc.image g).mono this
    obtain ⟨h, hrange, hhcont, hhinj⟩ :=
      MeasurableSet.exists_nat_bool_injection_of_not_countable hpre hpre_unc
    refine ⟨h, hhcont, fun x => ?_, fun x y hxy hr => ?_⟩
    · -- `h x ∈ g ⁻¹' range f`, so `g (h x) = f b` for some `b`, and `f b ∈ g '' A`
      have hx : g (h x) ∈ range f := hrange ⟨x, rfl⟩
      obtain ⟨b, hb⟩ := hx
      obtain ⟨a', ha', hga'⟩ := hmem b
      rw [hg.injective (hga'.trans hb).symm]
      exact ha'
    · have hx : g (h x) ∈ range f := hrange ⟨x, rfl⟩
      have hy : g (h y) ∈ range f := hrange ⟨y, rfl⟩
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      have hab : a ≠ b := by
        rintro rfl
        exact hhinj.ne hxy (hg.injective (ha.symm.trans hb))
      exact hineq a b hab (by rw [ha, hb]; exact (hrel _ _).mpr hr)
  · rintro ⟨f, hcont, hmem, hineq⟩
    obtain ⟨hB, hunc⟩ := range_antichain_props f hcont hineq
    have himg : MeasurableSet (g '' range f) := hg.measurableSet_image.mpr hB
    have himg_unc : ¬ (g '' range f).Countable := fun hc =>
      hunc ((hc.preimage_of_injOn hg.injective.injOn).mono (Set.subset_preimage_image g _))
    obtain ⟨h, hrange, hhcont, hhinj⟩ :=
      MeasurableSet.exists_nat_bool_injection_of_not_countable himg himg_unc
    refine ⟨h, hhcont, fun x => ?_, fun x y hxy hr => ?_⟩
    · obtain ⟨_, ⟨a, rfl⟩, hga⟩ := hrange ⟨x, rfl⟩
      exact ⟨f a, hmem a, hga⟩
    · obtain ⟨_, ⟨a, rfl⟩, ha⟩ := hrange ⟨x, rfl⟩
      obtain ⟨_, ⟨b, rfl⟩, hb⟩ := hrange ⟨y, rfl⟩
      have hab : a ≠ b := by
        rintro rfl
        exact hhinj.ne hxy (ha.symm.trans hb)
      rw [← ha, ← hb, hrel] at hr
      exact hineq a b hab hr

/-- **Thinness transport.**  In Polish ambient spaces perfect and Cantor antichains coincide, so
the image class is thin iff the class is. -/
theorem isThinOn_image_iff {r : Setoid X} {r' : Setoid Y} {g : X → Y}
    (hg : MeasurableEmbedding g) (hrel : ∀ x y, r'.r (g x) (g y) ↔ r.r x y) (A : Set X) :
    IsThinOn r' (g '' A) ↔ IsThinOn r A := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable X
  let := TopologicalSpace.upgradeIsCompletelyMetrizable Y
  unfold IsThinOn
  rw [not_iff_not]
  constructor
  · intro h
    exact (hasCantorAntichainOn_image_iff hg hrel A).mp h.hasCantorAntichainOn
      |>.hasPerfectAntichainOn
  · intro h
    exact (hasCantorAntichainOn_image_iff hg hrel A).mpr h.hasCantorAntichainOn
      |>.hasPerfectAntichainOn
