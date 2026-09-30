/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.TwoGeneratorCardinality
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Finite.Lattice

/-!
# Free sets for small-valued maps on finite subsets

A map `f : Finset X → Set X` assigns to each finite subset of `X` a set of points.  A finite set
`A` is `f`-independent (`FIndependent f A`) when no point of `A` lies in the value of `f` at a
subset of `A` omitting that point.

* `exists_fIndependent`: if every value of `f` has cardinality `< ℵ_α` and `ℵ_(α + k) ≤ #X`,
  then there is an `f`-independent set with `k + 1` elements.

The proof is by induction on `k`: close a subset of size `ℵ_(α + k)` under `f` (an `ω`-stage
iteration, `fClosure`), pick a point `a` outside the closure, and apply the induction hypothesis
inside the closure to the two-summand map `B ↦ f B ∪ f (insert a B)`.  The first summand handles
subsets omitting `a`, the second those containing it.

Source: Baldwin, Friedman, Koerwien, Laskowski, Three red herrings (2014), Lemma 2.3.
-/

set_option autoImplicit false

universe u

namespace InfinitaryLogic.FreeSet

open Cardinal

variable {X : Type u}

/-- `A` is `f`-independent: no point of `A` lies in the value of `f` at a subset of `A` omitting
it. -/
def FIndependent (f : Finset X → Set X) (A : Finset X) : Prop :=
  ∀ B ⊆ A, ∀ a ∈ A, a ∉ B → a ∉ f B

/-! ### Closing a set under `f` -/

/-- One closure step: add the values of `f` at all finite subsets of `S`. -/
def closeStep (f : Finset X → Set X) (S : Set X) : Set X :=
  S ∪ ⋃ A : {A : Finset X // (A : Set X) ⊆ S}, f A

/-- The `n`-th stage of the closure of `Y₀` under `f`. -/
def closeStage (f : Finset X → Set X) (Y₀ : Set X) : ℕ → Set X
  | 0 => Y₀
  | n + 1 => closeStep f (closeStage f Y₀ n)

/-- The closure of `Y₀` under `f`: the union of the `ω` stages. -/
def fClosure (f : Finset X → Set X) (Y₀ : Set X) : Set X :=
  ⋃ n : ULift.{u} ℕ, closeStage f Y₀ n.down

/-- The closure stages increase. -/
theorem closeStage_mono (f : Finset X → Set X) (Y₀ : Set X) : Monotone (closeStage f Y₀) :=
  monotone_nat_of_le_succ fun _ ↦ Set.subset_union_left

/-- The starting set lies in its closure. -/
theorem subset_fClosure (f : Finset X → Set X) (Y₀ : Set X) : Y₀ ⊆ fClosure f Y₀ :=
  Set.subset_iUnion (fun n : ULift.{u} ℕ ↦ closeStage f Y₀ n.down) ⟨0⟩

/-- The closure is closed under `f`: the value at a finite subset of it stays inside it. -/
theorem fClosure_closed (f : Finset X → Set X) (Y₀ : Set X) {A : Finset X}
    (hA : (A : Set X) ⊆ fClosure f Y₀) : f A ⊆ fClosure f Y₀ := by
  have hdir : Directed (· ⊆ ·) (fun n : ULift.{u} ℕ ↦ closeStage f Y₀ n.down) :=
    fun i j ↦ ⟨⟨max i.down j.down⟩, closeStage_mono f Y₀ (le_max_left _ _),
      closeStage_mono f Y₀ (le_max_right _ _)⟩
  obtain ⟨i, hi⟩ := Directed.exists_mem_subset_of_finset_subset_biUnion hdir hA
  refine subset_trans ?_ (Set.subset_iUnion _ (⟨i.down + 1⟩ : ULift.{u} ℕ))
  exact subset_trans
    (Set.subset_iUnion (fun B : {B : Finset X // (B : Set X) ⊆ closeStage f Y₀ i.down} ↦ f B)
      ⟨A, hi⟩) Set.subset_union_right

/-- There are at most `max ℵ₀ #S` finite subsets of `S`. -/
theorem mk_finsetsIn_le (S : Set X) :
    #{A : Finset X // (A : Set X) ⊆ S} ≤ max ℵ₀ #S := by
  classical
  refine le_trans (mk_le_of_surjective (f := fun l : List S ↦
    (⟨(l.map Subtype.val).toFinset, fun x hx ↦ by
      simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map] at hx
      obtain ⟨y, -, rfl⟩ := hx
      exact y.2⟩ : {A : Finset X // (A : Set X) ⊆ S})) ?_) (mk_list_le_max S)
  rintro ⟨A, hA⟩
  refine ⟨(A.subtype (· ∈ S)).toList, Subtype.ext ?_⟩
  ext x
  simp only [List.mem_toFinset, List.mem_map, Finset.mem_toList, Finset.mem_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hA hx⟩, hx, rfl⟩

/-- One closure step keeps the cardinality below an infinite bound. -/
theorem mk_closeStep_le (f : Finset X → Set X) {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ)
    (hf : ∀ A, #(f A) ≤ κ) {S : Set X} (hS : #S ≤ κ) : #(closeStep f S) ≤ κ := by
  have hidx : #{A : Finset X // (A : Set X) ⊆ S} ≤ κ :=
    (mk_finsetsIn_le S).trans (max_le hκ hS)
  have hU : #(⋃ A : {A : Finset X // (A : Set X) ⊆ S}, f A) ≤ κ :=
    calc #(⋃ A : {A : Finset X // (A : Set X) ⊆ S}, f A)
        ≤ sum fun A : {A : Finset X // (A : Set X) ⊆ S} ↦ #(f A) := mk_iUnion_le_sum_mk
      _ ≤ sum fun _ : {A : Finset X // (A : Set X) ⊆ S} ↦ κ := sum_le_sum _ _ fun A ↦ hf A
      _ = #{A : Finset X // (A : Set X) ⊆ S} * κ := sum_const' _ _
      _ ≤ κ * κ := mul_le_mul_left hidx κ
      _ = κ := mul_eq_self hκ
  calc #(closeStep f S) ≤ #S + #(⋃ A : {A : Finset X // (A : Set X) ⊆ S}, f A) :=
        mk_union_le _ _
    _ ≤ κ + κ := add_le_add hS hU
    _ = κ := add_eq_self hκ

/-- The closure keeps the cardinality below an infinite bound. -/
theorem mk_fClosure_le (f : Finset X → Set X) {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ)
    (hf : ∀ A, #(f A) ≤ κ) {Y₀ : Set X} (hY₀ : #Y₀ ≤ κ) : #(fClosure f Y₀) ≤ κ := by
  have hstage : ∀ n, #(closeStage f Y₀ n) ≤ κ := by
    intro n
    induction n with
    | zero => exact hY₀
    | succ n ih => exact mk_closeStep_le f hκ hf ih
  calc #(fClosure f Y₀) ≤ sum fun n : ULift.{u} ℕ ↦ #(closeStage f Y₀ n.down) :=
        mk_iUnion_le_sum_mk
    _ ≤ sum fun _ : ULift.{u} ℕ ↦ κ := sum_le_sum _ _ fun n ↦ hstage n.down
    _ = #(ULift.{u} ℕ) * κ := sum_const' _ _
    _ ≤ κ * κ := by
      refine mul_le_mul_left ?_ κ
      simpa using hκ
    _ = κ := mul_eq_self hκ

/-! ### The free-set lemma -/

/-- A set of cardinality below `#X` misses some point. -/
theorem exists_not_mem_of_mk_lt {S : Set X} (h : #S < #X) : ∃ x, x ∉ S := by
  by_contra hne
  have : #X ≤ #S := by
    rw [← mk_univ]
    exact mk_le_mk_of_subset fun x _ ↦ by_contra fun hx ↦ hne ⟨x, hx⟩
  exact h.not_ge this

/-- The induction behind `exists_fIndependent`, quantified over all carriers in the universe. -/
theorem exists_fIndependent_aux (k : ℕ) :
    ∀ {X : Type u} (f : Finset X → Set X) (α : Ordinal.{u}),
      (∀ A, #(f A) < ℵ_ α) → ℵ_ (α + k) ≤ #X →
        ∃ A : Finset X, A.card = k + 1 ∧ FIndependent f A := by
  classical
  induction k with
  | zero =>
    intro X f α hf hX
    simp only [Nat.cast_zero, add_zero] at hX
    obtain ⟨x, hx⟩ := exists_not_mem_of_mk_lt ((hf ∅).trans_le hX)
    refine ⟨{x}, by simp, ?_⟩
    intro B hB a ha haB
    rw [Finset.mem_singleton] at ha
    subst ha
    rcases Finset.subset_singleton_iff.mp hB with rfl | rfl
    · simpa using hx
    · simp at haB
  | succ k ih =>
    intro X f α hf hX
    set κ : Cardinal.{u} := ℵ_ (α + k) with hκdef
    have hκ : ℵ₀ ≤ κ := aleph0_le_aleph _
    have hlt : κ < ℵ_ (α + (k + 1 : ℕ)) := by
      rw [aleph_lt_aleph, Nat.cast_succ, ← add_assoc]
      exact Order.lt_add_one_iff.mpr le_rfl
    obtain ⟨Y₀, hY₀⟩ := le_mk_iff_exists_set.mp (hlt.le.trans hX)
    set Y : Set X := fClosure f Y₀ with hYdef
    have hfκ : ∀ A, #(f A) ≤ κ := fun A ↦
      ((hf A).trans_le (aleph_le_aleph.mpr (le_self_add))).le
    have hYle : #Y ≤ κ := mk_fClosure_le f hκ hfκ hY₀.le
    obtain ⟨a, haY⟩ := exists_not_mem_of_mk_lt (hYle.trans_lt (hlt.trans_le hX))
    let e : Y ↪ X := Function.Embedding.subtype (· ∈ Y)
    let g : Finset Y → Set Y := fun B ↦ Subtype.val ⁻¹' (f (B.map e) ∪ f (insert a (B.map e)))
    have hg : ∀ B, #(g B) < ℵ_ α := fun B ↦
      (mk_preimage_of_injective _ _ Subtype.val_injective).trans_lt
        ((mk_union_le _ _).trans_lt (add_lt_of_lt (aleph0_le_aleph α) (hf _) (hf _)))
    have hYbig : ℵ_ (α + k) ≤ #Y := by
      rw [← hκdef, ← hY₀]
      exact mk_le_mk_of_subset (subset_fClosure f Y₀)
    obtain ⟨B, hBcard, hBind⟩ := ih g α hg hYbig
    have haB : a ∉ B.map e := by
      simp only [Finset.mem_map]
      rintro ⟨y, -, rfl⟩
      exact haY y.2
    refine ⟨insert a (B.map e), ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem haB, Finset.card_map, hBcard]
    intro C hC p hp hpC
    rcases Finset.mem_insert.mp hp with rfl | hpB
    · -- `C` omits `a`, so it is a finite subset of the closure.
      have hCY : (C : Set X) ⊆ Y := by
        intro x hx
        rcases Finset.mem_insert.mp (hC hx) with rfl | hxB
        · exact absurd hx hpC
        · obtain ⟨y, -, rfl⟩ := Finset.mem_map.mp hxB
          exact y.2
      exact fun hp' ↦ haY (fClosure_closed f Y₀ hCY hp')
    · obtain ⟨q, hqB, rfl⟩ := Finset.mem_map.mp hpB
      set C' : Finset Y := B.filter fun r ↦ (r : X) ∈ C with hC'def
      have hC'B : C' ⊆ B := Finset.filter_subset _ _
      have hqC' : q ∉ C' := by
        simp only [hC'def, Finset.mem_filter, not_and]
        exact fun _ ↦ hpC
      have hmap : ∀ x, x ∈ C'.map e ↔ x ∈ C ∧ x ≠ a := by
        intro x
        simp only [hC'def, Finset.mem_map, Finset.mem_filter]
        constructor
        · rintro ⟨y, ⟨-, hyC⟩, rfl⟩
          exact ⟨hyC, fun h ↦ haY (h ▸ y.2)⟩
        · rintro ⟨hxC, hxa⟩
          rcases Finset.mem_insert.mp (hC hxC) with rfl | hxB
          · exact absurd rfl hxa
          · obtain ⟨y, hyB, rfl⟩ := Finset.mem_map.mp hxB
            exact ⟨y, ⟨hyB, hxC⟩, rfl⟩
      have hnot : q ∉ g C' := hBind C' hC'B q hqB hqC'
      simp only [g, Set.mem_preimage, Set.mem_union, not_or] at hnot
      by_cases haC : a ∈ C
      · have hCeq : insert a (C'.map e) = C := by
          ext x
          rw [Finset.mem_insert, hmap]
          constructor
          · rintro (rfl | ⟨hx, -⟩)
            · exact haC
            · exact hx
          · intro hx
            by_cases hxa : x = a
            · exact Or.inl hxa
            · exact Or.inr ⟨hx, hxa⟩
        rw [← hCeq]
        exact hnot.2
      · have hCeq : C'.map e = C := by
          ext x
          rw [hmap]
          exact ⟨fun h ↦ h.1, fun hx ↦ ⟨hx, fun h ↦ haC (h ▸ hx)⟩⟩
        rw [← hCeq]
        exact hnot.1

/-- Lemma 2.3: small-valued maps on finite subsets of a large set admit large independent sets. -/
theorem exists_fIndependent (f : Finset X → Set X) (α : Ordinal.{u}) (k : ℕ)
    (hf : ∀ A, Cardinal.mk (f A) < Cardinal.aleph α)
    (hX : Cardinal.aleph (α + k) ≤ Cardinal.mk X) :
    ∃ A : Finset X, A.card = k + 1 ∧ FIndependent f A :=
  exists_fIndependent_aux k f α hf hX

/-! ### Two-generated hulls -/

section TwoGeneration

variable {M : Type u}

/-- Whole-hull two-generation forbids independent triples for the hull map. -/
theorem not_fIndependent_of_two_generation (c : ClosureOperator (Finset M))
    (hgen : ∀ S, ∃ T ⊆ S, T.card ≤ 2 ∧ c T = c S) (A : Finset M) (hA : A.card = 3) :
    ¬ FIndependent (fun S ↦ (↑(c S) : Set M)) A := by
  intro hind
  obtain ⟨T, hTA, hTcard, hTc⟩ := hgen A
  obtain ⟨p, hpA, hpT⟩ : ∃ p ∈ A, p ∉ T := by
    by_contra hall
    have hAT : A ⊆ T := fun p hp ↦ by_contra fun hpT ↦ hall ⟨p, hp, hpT⟩
    have := Finset.card_le_card hAT
    omega
  have hpc : p ∈ c T := hTc ▸ c.le_closure A hpA
  exact hind T hTA p hpA hpT (Finset.mem_coe.mpr hpc)

/-- The `ℵ₁` bound of `mk_le_aleph_one`, rederived from the free-set lemma. -/
theorem mk_le_aleph_one_of_freeSet (c : ClosureOperator (Finset M))
    (hgen : ∀ S, ∃ T ⊆ S, T.card ≤ 2 ∧ c T = c S) : Cardinal.mk M ≤ Cardinal.aleph 1 := by
  by_contra h
  have hX : ℵ_ ((0 : Ordinal.{u}) + (2 : ℕ)) ≤ #M := by
    have h2 : ℵ_ ((0 : Ordinal.{u}) + (2 : ℕ)) = Order.succ (ℵ_ 1) := by
      rw [succ_aleph, zero_add, one_add_one_eq_two, Nat.cast_ofNat]
    rw [h2]
    exact Order.succ_le_of_lt (lt_of_not_ge h)
  have hf : ∀ S : Finset M, #(↑(c S) : Set M) < ℵ_ 0 := fun S ↦ by
    rw [aleph_zero]
    exact (c S).finite_toSet.lt_aleph0
  obtain ⟨A, hAcard, hA⟩ := exists_fIndependent (fun S ↦ (↑(c S) : Set M)) 0 2 hf hX
  exact not_fIndependent_of_two_generation c hgen A hAcard hA

end TwoGeneration

end InfinitaryLogic.FreeSet
