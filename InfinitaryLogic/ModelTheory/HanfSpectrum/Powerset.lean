/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.HanfSpectrum.LadderSyntax
import InfinitaryLogic.ModelTheory.HanfSpectrum.CardinalBounds
import InfinitaryLogic.ModelTheory.MorleyHanf
import Mathlib.SetTheory.Cardinal.Continuum

/-!
# The powerset witness: ladder stage `α = 0`

The `α = 0` instance of the common ladder sentence (`HanfSpectrum/LadderSyntax.lean`): the index
order `Index 0` has exactly the two levels `⊥ ⋖ ⊤`, so a ladder model is a set of "elements"
(`U_⊤` = everything) whose `E`-predecessors all lie in the countable base `U_⊥` (enumerated by
the constants), with `E`-extensionality. The maximal model is the full powerset:

* `powersetStructure` — `Set ℕ` with `cₙ = {n}`, `U_⊥` = the singletons, `E x y ↔ ∃ n, x = {n} ∧
  n ∈ y`; it satisfies `IsLadderModel 0` and has size `2 ^ ℵ₀`;
* `mk_le_continuum_of_isLadderModel` — EVERY ladder model at `α = 0` has size `≤ 2 ^ ℵ₀`
  (`E`-extensionality injects `M` into the powerset of the countable `U_⊥`);
* `beth_one_lt_Lomega1omegaHanfNumber` — the second sharpness step, through the generic
  bounded-spectrum endpoint `lt_Lomega1omegaHanfNumber_of_maximal_model`.

The two-element order facts (`covBy_of_lt_index_zero`, `not_isSuccLimit_index_zero`) are
isolated here so they do not contaminate the model verification; the general-stage analogues
(`typein`-recursion) belong to `BethLadder.lean`.

Reference: Marker, *Lectures on Infinitary Model Theory*, Exercise 5.3 (the `φ_1` stage).
-/

namespace FirstOrder

namespace Language

namespace HanfLadder

open Cardinal

/-! ## The two-element index order `Index 0` -/

instance : Countable (Index 0) := by
  refine Cardinal.mk_le_aleph0_iff.mp ?_
  rw [Cardinal.mk_toType, zero_add, Ordinal.card_ofNat]
  exact le_of_lt Cardinal.ofNat_lt_aleph0

theorem bot_lt_top_index : (⊥ : Index 0) < ⊤ := by
  have h1 : (1 : Ordinal) < 0 + 2 := by
    rw [zero_add, ← one_add_one_eq_two]
    exact (Order.lt_succ 1).trans_eq (Order.succ_eq_add_one 1)
  have h0 : (0 : Ordinal) < 0 + 2 := lt_trans zero_lt_one h1
  have hlt : (Ordinal.ToType.mk ⟨0, Set.mem_Iio.mpr h0⟩ : Index 0)
      < Ordinal.ToType.mk ⟨1, Set.mem_Iio.mpr h1⟩ :=
    Ordinal.ToType.mk.lt_iff_lt.mpr (Subtype.mk_lt_mk.mpr zero_lt_one)
  exact lt_of_le_of_lt bot_le (lt_of_lt_of_le hlt le_top)

/-- In the two-element order `Index 0`, every strict inequality is a covering: there is no
middle element (the `typein` values would form a strict 3-chain below `2`). -/
theorem covBy_of_lt_index_zero {i j : Index 0} (hij : i < j) : i ⋖ j := by
  refine ⟨hij, fun {c} hic hcj => ?_⟩
  have h1 : ((Ordinal.ToType.mk.symm i : Set.Iio ((0 : Ordinal) + 2)) : Ordinal)
      < (Ordinal.ToType.mk.symm c : Set.Iio ((0 : Ordinal) + 2)) :=
    Ordinal.ToType.mk.symm.lt_iff_lt.mpr hic
  have h2 : ((Ordinal.ToType.mk.symm c : Set.Iio ((0 : Ordinal) + 2)) : Ordinal)
      < (Ordinal.ToType.mk.symm j : Set.Iio ((0 : Ordinal) + 2)) :=
    Ordinal.ToType.mk.symm.lt_iff_lt.mpr hcj
  have h3 : ((Ordinal.ToType.mk.symm j : Set.Iio ((0 : Ordinal) + 2)) : Ordinal) < 0 + 2 :=
    (Ordinal.ToType.mk.symm j).2
  have he : ((0 : Ordinal) + 2) = Order.succ 1 := by
    rw [zero_add, Order.succ_eq_add_one, one_add_one_eq_two]
  have h4 := Order.lt_succ_iff.mp (lt_of_lt_of_eq h3 he)
  have h5 := Order.lt_one_iff.mp (lt_of_lt_of_le h2 h4)
  rw [h5] at h1
  exact absurd h1 not_lt_zero

/-- The two-element order `Index 0` has no successor-limit elements. -/
theorem not_isSuccLimit_index_zero (j : Index 0) : ¬Order.IsSuccLimit j := fun hj =>
  hj.isSuccPrelimit ⊥ (covBy_of_lt_index_zero hj.bot_lt)

/-! ## The powerset model on `Set ℕ` -/

/-- The powerset structure: constants are the singletons, `U_⊥` is the set of singletons
(`U_i` trivial for `i ≠ ⊥`), and `E x y` says `x` is a singleton `{n}` with `n ∈ y`. -/
@[reducible] def powersetStructure : (ladderLang 0).Structure (Set ℕ) where
  funMap {n} f _ := match n, f with
    | 0, m => ({m} : Set ℕ)
  RelMap {n} r v := match n, r with
    | 1, i => i = (⊥ : Index 0) → ∃ m : ℕ, v 0 = ({m} : Set ℕ)
    | 2, _ => ∃ m : ℕ, v 0 = ({m} : Set ℕ) ∧ m ∈ v 1

theorem powerset_isLadderModel :
    letI := powersetStructure
    IsLadderModel 0 (M := Set ℕ) := by
  letI := powersetStructure
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- base: `U_⊥` is exactly the constants (the singletons)
    intro x
    exact ⟨fun h => h rfl, fun ⟨n, hn⟩ _ => ⟨n, hn⟩⟩
  · -- top: `U_⊤` is everything (`⊤ ≠ ⊥` discharges the guard)
    intro x
    exact fun htop => absurd (show (⊤ : Index 0) = ⊥ from htop) (ne_of_gt bot_lt_top_index)
  · -- nested: `i < j` forces `j ≠ ⊥`
    intro i j hij x _
    exact fun hj => absurd (lt_of_lt_of_le hij (le_of_eq (show (j : Index 0) = ⊥ from hj)))
      not_lt_bot
  · -- limit covering: vacuous
    intro j hj
    exact absurd hj (not_isSuccLimit_index_zero j)
  · -- predecessor descent: `E y x` already exhibits `y` as a singleton
    intro i j _ x y _ hedge
    obtain ⟨m, hy, _⟩ := hedge
    exact fun _ => ⟨m, hy⟩
  · -- extensionality: membership is recovered from the singleton predecessors
    intro y z h
    ext n
    have hn := h ({n} : Set ℕ)
    constructor
    · intro hny
      obtain ⟨m, hm, hmz⟩ := hn.mp ⟨n, rfl, hny⟩
      rwa [← Set.singleton_eq_singleton_iff.mp hm.symm]
    · intro hnz
      obtain ⟨m, hm, hmy⟩ := hn.mpr ⟨n, rfl, hnz⟩
      rwa [← Set.singleton_eq_singleton_iff.mp hm.symm]

/-! ## The upper bound: every `α = 0` ladder model has size `≤ 2 ^ ℵ₀` -/

/-- In any `α = 0` ladder model, `E`-predecessors lie in the base level: `⊥ ⋖ ⊤`, everything is
in `U_⊤`, and predecessor descent lands in `U_⊥`. -/
theorem edge_mem_base_of_isLadderModel {M : Type} [(ladderLang 0).Structure M]
    (h : IsLadderModel 0 (M := M)) {x y : M} (hxy : Edge 0 x y) : Level 0 ⊥ x :=
  h.pred_down (covBy_of_lt_index_zero bot_lt_top_index) y x (h.top y) hxy

/-- **The maximal-size bound at `α = 0`**: `E`-extensionality injects the model into the
powerset of the countable base level. -/
theorem mk_le_continuum_of_isLadderModel {M : Type} [(ladderLang 0).Structure M]
    (h : IsLadderModel 0 (M := M)) : Cardinal.mk M ≤ 2 ^ Cardinal.aleph0 := by
  have hcnt : Countable {x : M // Level 0 ⊥ x} := by
    have hsurj : Function.Surjective (fun n : ℕ =>
        (⟨constVal 0 n, (h.base _).mpr ⟨n, rfl⟩⟩ : {x : M // Level 0 ⊥ x})) := by
      rintro ⟨x, hx⟩
      obtain ⟨n, hn⟩ := (h.base x).mp hx
      exact ⟨n, Subtype.ext hn.symm⟩
    exact hsurj.countable
  have hinj : Function.Injective
      (fun y : M => {x : {x : M // Level 0 ⊥ x} | Edge 0 x.1 y}) := by
    intro y z hyz
    have hyz' : {x : {x : M // Level 0 ⊥ x} | Edge 0 x.1 y}
        = {x : {x : M // Level 0 ⊥ x} | Edge 0 x.1 z} := hyz
    refine h.ext y z fun x => ?_
    constructor
    · intro hxy
      have hmem : (⟨x, edge_mem_base_of_isLadderModel h hxy⟩ : {x : M // Level 0 ⊥ x})
          ∈ {x : {x : M // Level 0 ⊥ x} | Edge 0 x.1 y} := hxy
      rw [hyz'] at hmem
      exact hmem
    · intro hxz
      have hmem : (⟨x, edge_mem_base_of_isLadderModel h hxz⟩ : {x : M // Level 0 ⊥ x})
          ∈ {x : {x : M // Level 0 ⊥ x} | Edge 0 x.1 z} := hxz
      rw [← hyz'] at hmem
      exact hmem
  calc Cardinal.mk M ≤ 2 ^ Cardinal.mk {x : M // Level 0 ⊥ x} :=
        FirstOrder.HanfLadder.mk_le_two_power_of_injective_set hinj
    _ ≤ 2 ^ Cardinal.aleph0 :=
        Cardinal.power_le_power_left two_ne_zero Cardinal.mk_le_aleph0

end HanfLadder

open HanfLadder in
/-- **The second sharpness step**: `ℶ_1 < Lomega1omegaHanfNumber` — the `α = 0` ladder sentence
has the powerset `Set ℕ` as a maximal model of size exactly `2 ^ ℵ₀ = ℶ_1`. -/
theorem beth_one_lt_Lomega1omegaHanfNumber :
    Cardinal.beth 1 < Lomega1omegaHanfNumber := by
  rw [Cardinal.beth_one, ← Cardinal.two_power_aleph0]
  letI := powersetStructure
  refine lt_Lomega1omegaHanfNumber_of_maximal_model
    ⟨Set ℕ, inferInstance, (realize_ladderSentence_iff (α := 0)).mpr powerset_isLadderModel,
      by rw [Cardinal.mk_set, Cardinal.mk_nat]⟩
    (fun M instM hM => mk_le_continuum_of_isLadderModel
      ((realize_ladderSentence_iff (α := 0)).mp hM))

end Language

end FirstOrder
