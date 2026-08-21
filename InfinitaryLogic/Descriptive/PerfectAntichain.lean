/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.CantorAntichain
import Mathlib.Topology.MetricSpace.Perfect
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.SetTheory.Cardinal.Continuum

/-!
# Perfect and Cantor antichains, and thinness

The vocabulary a dichotomy theorem is stated in, separated from any particular dichotomy.

* `HasPerfectAntichainOn r A` — a nonempty perfect subset of `A` of pairwise `r`-inequivalent
  points;
* `HasCantorAntichainOn r A` — a *continuous* Cantor-space parametrization of such an antichain,
  the constructive form the Cantor-scheme builders actually produce;
* `IsThinOn r A` — the negation of the first.

The two positive forms are related by `HasPerfectAntichainOn.hasCantorAntichainOn`, which is
`Perfect.exists_nat_bool_injection` plus bookkeeping.  Injectivity of a Cantor antichain is not
an extra hypothesis: it follows from *reflexivity* of the setoid, since distinct arguments have
inequivalent images and every point is equivalent to itself.

Also here, moved unchanged from `Conditional/SilverBurgess.lean`: the cardinal facts about
perfect sets and Polish quotients.  None of them mentions a dichotomy, an equivalence relation
being closed, or a splitting hypothesis — they are about perfect sets and Polish spaces, and
belonged in the conditional file only by accident of where they were first needed.
-/

open Cardinal Set

universe u v

/-! ### Perfect set cardinality -/

/-- A nonempty perfect subset of a Polish space has cardinality = continuum.
Lower bound via `Perfect.exists_nat_bool_injection`; upper bound via
second-countability of Polish spaces. -/
theorem Perfect.mk_eq_continuum {α : Type u} [MetricSpace α] [CompleteSpace α]
    [SecondCountableTopology α]
    {C : Set α} (hperf : Perfect C) (hne : C.Nonempty) :
    #C = Cardinal.continuum := by
  apply le_antisymm
  · -- Upper bound: #C ≤ 𝔠
    calc #C ≤ #α := mk_set_le C
      _ ≤ Cardinal.continuum := by
        haveI : Nonempty α := let ⟨x, _⟩ := hne; ⟨x⟩
        obtain ⟨f, _, hf_surj⟩ := PolishSpace.exists_nat_nat_continuous_surjective α
        have h1 := lift_mk_le_lift_mk_of_surjective hf_surj
        simp only [lift_uzero] at h1
        exact h1.trans (by simp [aleph0_power_aleph0])
  · -- Lower bound: 𝔠 ≤ #C
    obtain ⟨f, hf_range, _, hf_inj⟩ := hperf.exists_nat_bool_injection hne
    let g : (ℕ → Bool) → C := fun x => ⟨f x, hf_range (mem_range_self x)⟩
    have hg_inj : Function.Injective g := fun a b hab => hf_inj (Subtype.mk.inj hab)
    have h1 := lift_mk_le_lift_mk_of_injective hg_inj
    simp only [lift_uzero] at h1
    rw [show lift.{u} #(ℕ → Bool) = Cardinal.continuum from by simp] at h1
    exact h1

/-! ### Perfect transversal → continuum classes -/

/-- If an equivalence relation on a Polish space has a perfect set of
pairwise inequivalent elements, it has at least continuum classes. -/
theorem continuum_classes_of_perfect_transversal {α : Type u}
    [MetricSpace α] [CompleteSpace α] [SecondCountableTopology α]
    (r : Setoid α) {C : Set α} (hperf : Perfect C) (hne : C.Nonempty)
    (hinequiv : ∀ x ∈ C, ∀ y ∈ C, r.r x y → x = y) :
    Cardinal.continuum ≤ #(Quotient r) := by
  have hcard := hperf.mk_eq_continuum hne
  rw [← hcard]
  -- The quotient map restricted to C is injective
  exact Cardinal.mk_le_of_injective (f := fun ⟨x, hx⟩ => Quotient.mk r x)
    (fun ⟨x, hx⟩ ⟨y, hy⟩ hq => by
      exact Subtype.ext (hinequiv x hx y hy (Quotient.exact hq)))

/-- If an equivalence relation on a Polish space has a perfect set of
pairwise inequivalent elements, it has exactly continuum classes
(assuming the ambient space has cardinality ≤ continuum). -/
theorem eq_continuum_classes_of_perfect_transversal {α : Type u}
    [MetricSpace α] [CompleteSpace α] [SecondCountableTopology α]
    (r : Setoid α) {C : Set α} (hperf : Perfect C) (hne : C.Nonempty)
    (hinequiv : ∀ x ∈ C, ∀ y ∈ C, r.r x y → x = y)
    (hle : #α ≤ Cardinal.continuum) :
    #(Quotient r) = Cardinal.continuum := by
  apply le_antisymm
  · calc #(Quotient r) ≤ #α := Cardinal.mk_le_of_surjective (Quotient.mk_surjective)
      _ ≤ Cardinal.continuum := hle
  · exact continuum_classes_of_perfect_transversal r hperf hne hinequiv

/-! ### Polish space cardinality upper bound -/

/-- A Polish space has cardinality ≤ continuum. -/
theorem mk_le_continuum_of_polish {α : Type u} [MetricSpace α] [CompleteSpace α]
    [SecondCountableTopology α] [Nonempty α] :
    #α ≤ Cardinal.continuum := by
  obtain ⟨f, _, hf_surj⟩ := PolishSpace.exists_nat_nat_continuous_surjective α
  have h1 := lift_mk_le_lift_mk_of_surjective hf_surj
  simp only [lift_uzero] at h1
  exact h1.trans (by simp [aleph0_power_aleph0])

/-- The quotient of a Polish space has cardinality ≤ continuum. -/
theorem mk_quotient_le_continuum_of_polish {α : Type u} [MetricSpace α] [CompleteSpace α]
    [SecondCountableTopology α] [Nonempty α] (r : Setoid α) :
    #(Quotient r) ≤ Cardinal.continuum :=
  (Cardinal.mk_le_of_surjective Quotient.mk_surjective).trans mk_le_continuum_of_polish

/-! ### The generic vocabulary -/

variable {X : Type u} [TopologicalSpace X]

/-- `A` carries a **perfect antichain** for `r`: a nonempty perfect subset of `A` whose points
are pairwise `r`-inequivalent. -/
def HasPerfectAntichainOn (r : Setoid X) (A : Set X) : Prop :=
  ∃ P, Perfect P ∧ P.Nonempty ∧ P ⊆ A ∧ ∀ x ∈ P, ∀ y ∈ P, r.r x y → x = y

/-- `A` carries a **Cantor antichain** for `r`: a continuous map from Cantor space into `A`
sending distinct points to `r`-inequivalent ones.  This is what the Cantor-scheme builders
produce directly, and it is the form a thinness proof must refute. -/
def HasCantorAntichainOn (r : Setoid X) (A : Set X) : Prop :=
  ∃ f : (ℕ → Bool) → X,
    Continuous f ∧ (∀ x, f x ∈ A) ∧ ∀ x y, x ≠ y → ¬r.r (f x) (f y)

/-- `A` is **thin** for `r`: no perfect antichain. -/
def IsThinOn (r : Setoid X) (A : Set X) : Prop :=
  ¬HasPerfectAntichainOn r A

/-! ### Adapters -/

variable {r : Setoid X} {A : Set X}

/-- A Cantor antichain is injective — by *reflexivity*, not by an added hypothesis: distinct
arguments have inequivalent images, and equal images would be equivalent to themselves. -/
theorem HasCantorAntichainOn.injective (h : HasCantorAntichainOn r A) :
    ∃ f : (ℕ → Bool) → X, Continuous f ∧ Function.Injective f ∧ (∀ x, f x ∈ A) ∧
      ∀ x y, x ≠ y → ¬r.r (f x) (f y) := by
  obtain ⟨f, hcont, hmem, hineq⟩ := h
  refine ⟨f, hcont, fun x y hxy => ?_, hmem, hineq⟩
  by_contra hne
  exact hineq x y hne (hxy ▸ r.refl (f x))

/-- In a Polish space, a perfect antichain yields a Cantor antichain.  This is
`Perfect.exists_nat_bool_injection` together with the observation that the injection's range
lies in the perfect set, hence in `A`. -/
theorem HasPerfectAntichainOn.hasCantorAntichainOn {α : Type u} [MetricSpace α]
    [CompleteSpace α] [SecondCountableTopology α] {r : Setoid α} {A : Set α}
    (h : HasPerfectAntichainOn r A) : HasCantorAntichainOn r A := by
  obtain ⟨P, hperf, hne, hsub, hanti⟩ := h
  obtain ⟨f, hrange, hcont, hinj⟩ := hperf.exists_nat_bool_injection hne
  refine ⟨f, hcont, fun x => hsub (hrange (mem_range_self x)), fun x y hxy hr => ?_⟩
  exact hxy (hinj (hanti _ (hrange (mem_range_self x)) _ (hrange (mem_range_self y)) hr))

/-- A Cantor antichain forces continuum-many classes, in a Polish space. -/
theorem HasCantorAntichainOn.continuum_le_quotient {α : Type u} [MetricSpace α]
    [CompleteSpace α] [SecondCountableTopology α] {r : Setoid α} {A : Set α}
    (h : HasCantorAntichainOn r A) : Cardinal.continuum ≤ #(Quotient r) := by
  obtain ⟨f, -, hinj, -, hineq⟩ := h.injective
  have hq : Function.Injective (fun x : ℕ → Bool => Quotient.mk r (f x)) := by
    intro x y hxy
    by_contra hne
    exact hineq x y hne (Quotient.exact hxy)
  have h1 := lift_mk_le_lift_mk_of_injective hq
  simp only [lift_uzero] at h1
  rw [show lift.{u} #(ℕ → Bool) = Cardinal.continuum from by simp] at h1
  exact h1

/-- Refuting Cantor antichains suffices for thinness, in a Polish space. -/
theorem IsThinOn.of_no_cantorAntichain {α : Type u} [MetricSpace α] [CompleteSpace α]
    [SecondCountableTopology α] {r : Setoid α} {A : Set α}
    (h : ¬HasCantorAntichainOn r A) : IsThinOn r A :=
  fun hp => h hp.hasCantorAntichainOn

/-! ### Packaging the Cantor-scheme builders

Wrappers only: the existential content is `CantorAntichain.lean`'s, restated in the vocabulary
above so that consumers need not unpack it. -/

/-- `CantorScheme.exists_antichain_map` in antichain vocabulary. -/
theorem CantorScheme.hasCantorAntichainOn {α : Type u} [PseudoMetricSpace α]
    (r : Setoid α) {A : List Bool → Set α} {E : Set α}
    (hlim : ∀ x : ℕ → Bool, (⋂ n, A (PiNat.res x n)).Nonempty)
    (hdiam : CantorScheme.VanishingDiam A)
    (hcross : ∀ l : List Bool, ∀ x ∈ A (false :: l), ∀ y ∈ A (true :: l), ¬ r.r x y)
    (hE : ∀ (a : ℕ → Bool) (n : ℕ), A (PiNat.res a n) ⊆ E) :
    HasCantorAntichainOn r E := by
  obtain ⟨f, hcont, -, hmem, hineq⟩ := CantorScheme.exists_antichain_map r hlim hdiam hcross
  exact ⟨f, hcont, fun a => hE a 0 (hmem a 0), hineq⟩

/-- `CantorScheme.exists_antichain_map_of_splitting` in antichain vocabulary. -/
theorem CantorScheme.hasCantorAntichainOn_of_splitting {α : Type u} [MetricSpace α]
    [CompleteSpace α] (r : Setoid α) (P : Set α → Prop)
    (hcl : ∀ F, P F → IsClosed F) (hne : ∀ F, P F → F.Nonempty)
    {E : Set α} (hE : P E)
    (hsplit : ∀ F, P F → ∀ ε : ENNReal, 0 < ε →
      ∃ F₀ F₁ : Set α, P F₀ ∧ P F₁ ∧ F₀ ⊆ F ∧ F₁ ⊆ F ∧
        Metric.ediam F₀ ≤ ε ∧ Metric.ediam F₁ ≤ ε ∧
        ∀ x ∈ F₀, ∀ y ∈ F₁, ¬ r.r x y) :
    HasCantorAntichainOn r E := by
  obtain ⟨f, hcont, -, hmem, hineq⟩ :=
    CantorScheme.exists_antichain_map_of_splitting r P hcl hne hE hsplit
  exact ⟨f, hcont, hmem, hineq⟩
