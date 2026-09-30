/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Order.Closure
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Data.Set.Finite.Lattice

/-!
# Free sets for small-valued maps on finite subsets

A map `f : Finset X → Set X` assigns to each finite subset of `X` a set of points.  A finite set
`A` is `f`-independent (`FIndependent f A`) when no point of `A` lies in the value of `f` at a
subset of `A` omitting that point.

## Main results

* `exists_fIndependent`: if every value of `f` has cardinality `< ℵ_ α` and `ℵ_ (α + k) ≤ #X`,
  then some `f`-independent set has exactly `k + 1` elements.
* `not_fIndependent_of_generation`: if every hull of a closure operator `c` on `Finset M` is the
  hull of a subset with at most `n` elements, then no set with more than `n` elements is
  independent for the hull map `S ↦ c S`.
* `mk_lt_aleph_of_generation`: under the same hypothesis, `#M < ℵ_ n`.

## Closing a set under `f`

* `fClosure f Y₀`: the closure of `Y₀` under `f`, the union of `ω` stages, each adding the
  values of `f` at the finite subsets of the previous one.
* `subset_fClosure`, `fClosure_closed` and `fClosure_subset`: `fClosure f Y₀` is the least
  superset of `Y₀` containing the value of `f` at each of its finite subsets.
* `mk_fClosure_le`: if `κ` is infinite and bounds `#Y₀` and every value of `f`, then
  `#(fClosure f Y₀) ≤ κ`.

## Proof

The proof is by induction on `k`: close a subset of size `ℵ_ (α + k)` under `f`, pick a point `a`
outside the closure `Y`, and apply the induction hypothesis inside `Y` to the two-summand map
`A ↦ (f A ∪ f (insert a A)) ∩ Y`.  The first summand handles the subsets omitting `a`, the second
those containing it.

## Source

Baldwin, Friedman, Koerwien, Laskowski, *Three red herrings* (2014), Definition 2.2 and
Lemma 2.3; the source credits the origin of the argument to Laskowski–Shelah.  This
formalization departs from the printed version in two places.

* The printed proof uses the auxiliary map `f ({a} ∪ A) ∩ Y`.  That map is only sufficient for
  monotone `f`: it controls the subsets containing `a` but not those omitting it, and the
  printed statement does not assume monotonicity.  This formalization uses the two-summand map
  `(f A ∪ f (insert a A)) ∩ Y` instead.
* The cardinality hypothesis is `ℵ_ (α + k) ≤ #X`, where the printed statement has `=`.  The
  two forms are equivalent: restrict `f` to a subset of cardinality `ℵ_ (α + k)`.
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
private def closeStep (f : Finset X → Set X) (S : Set X) : Set X :=
  S ∪ ⋃ A : Finset S, f (A.map (Function.Embedding.subtype _))

/-- The `n`-th stage of the closure of `Y₀` under `f`. -/
private def closeStage (f : Finset X → Set X) (Y₀ : Set X) : ℕ → Set X
  | 0 => Y₀
  | n + 1 => closeStep f (closeStage f Y₀ n)

/-- The closure of `Y₀` under `f`: the union of the `ω` stages, each adding the values of `f` at
the finite subsets of the previous one. -/
def fClosure (f : Finset X → Set X) (Y₀ : Set X) : Set X :=
  ⋃ n : ℕ, closeStage f Y₀ n

private theorem closeStage_mono (f : Finset X → Set X) (Y₀ : Set X) :
    Monotone (closeStage f Y₀) :=
  monotone_nat_of_le_succ fun _ ↦ Set.subset_union_left

/-- The starting set lies in its closure. -/
theorem subset_fClosure (f : Finset X → Set X) (Y₀ : Set X) : Y₀ ⊆ fClosure f Y₀ :=
  Set.subset_iUnion (closeStage f Y₀) 0

/-- The closure is closed under `f`: the value at a finite subset of it stays inside it. -/
theorem fClosure_closed (f : Finset X → Set X) (Y₀ : Set X) {A : Finset X}
    (hA : (A : Set X) ⊆ fClosure f Y₀) : f A ⊆ fClosure f Y₀ := by
  classical
  obtain ⟨i, hi⟩ :=
    (closeStage_mono f Y₀).directed_le.exists_mem_subset_of_finset_subset_biUnion hA
  refine subset_trans ?_ (Set.subset_iUnion _ (i + 1))
  refine subset_trans ?_ Set.subset_union_right
  rw [← Finset.subtype_map_of_mem (p := (· ∈ closeStage f Y₀ i)) fun x hx ↦ hi hx]
  exact Set.subset_iUnion (fun B : Finset (closeStage f Y₀ i) ↦
    f (B.map (Function.Embedding.subtype _))) _

/-- The closure is the least superset of `Y₀` containing the value of `f` at each of its finite
subsets: every such superset contains it. -/
theorem fClosure_subset (f : Finset X → Set X) {Y₀ Z : Set X} (hY₀ : Y₀ ⊆ Z)
    (hZ : ∀ A : Finset X, (A : Set X) ⊆ Z → f A ⊆ Z) : fClosure f Y₀ ⊆ Z := by
  refine Set.iUnion_subset fun n ↦ ?_
  induction n with
  | zero => exact hY₀
  | succ n ih =>
    exact Set.union_subset ih
      (Set.iUnion_subset fun A ↦ hZ _ (A.map_subtype_subset.trans ih))

/-- If `κ` is infinite and bounds `#S` and every value of `f`, then one closure step has
cardinality at most `κ`. -/
private theorem mk_closeStep_le (f : Finset X → Set X) {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ)
    (hf : ∀ A, #(f A) ≤ κ) {S : Set X} (hS : #S ≤ κ) : #(closeStep f S) ≤ κ := by
  classical
  have hidx : #(Finset S) ≤ κ :=
    ((mk_le_of_surjective List.toFinset_surjective).trans (mk_list_le_max S)).trans
      (max_le hκ hS)
  have hU : #(⋃ A : Finset S, f (A.map (Function.Embedding.subtype _))) ≤ κ :=
    calc #(⋃ A : Finset S, f (A.map (Function.Embedding.subtype _)))
        ≤ #(Finset S) * ⨆ A : Finset S, #(f (A.map (Function.Embedding.subtype _))) :=
          mk_iUnion_le _
      _ ≤ κ * κ := mul_le_mul' hidx (ciSup_le' fun A ↦ hf _)
      _ = κ := mul_eq_self hκ
  calc #(closeStep f S) ≤ #S + #(⋃ A : Finset S, f (A.map (Function.Embedding.subtype _))) :=
        mk_union_le _ _
    _ ≤ κ + κ := add_le_add hS hU
    _ = κ := add_eq_self hκ

/-- If `κ` is infinite and bounds `#Y₀` and every value of `f`, then the closure of `Y₀` under
`f` has cardinality at most `κ`. -/
theorem mk_fClosure_le (f : Finset X → Set X) {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ)
    (hf : ∀ A, #(f A) ≤ κ) {Y₀ : Set X} (hY₀ : #Y₀ ≤ κ) : #(fClosure f Y₀) ≤ κ := by
  have hstage : ∀ n, #(closeStage f Y₀ n) ≤ κ := by
    intro n
    induction n with
    | zero => exact hY₀
    | succ n ih => exact mk_closeStep_le f hκ hf ih
  have h := mk_iUnion_le_lift (closeStage f Y₀)
  rw [lift_uzero, mk_nat, lift_aleph0] at h
  refine h.trans ((mul_le_mul' hκ (ciSup_le' fun n ↦ ?_)).trans (mul_eq_self hκ).le)
  rw [lift_uzero]
  exact hstage n

/-! ### The free-set lemma -/

/-- The auxiliary map on the finite subsets of `Y` used to add the point `a`: the two-summand
map `B ↦ (f B ∪ f (insert a B)) ∩ Y`, read inside `Y`. -/
private def liftMap [DecidableEq X] (f : Finset X → Set X) (Y : Set X) (a : X)
    (B : Finset Y) : Set Y :=
  Subtype.val ⁻¹' (f (B.map (Function.Embedding.subtype _)) ∪
    f (insert a (B.map (Function.Embedding.subtype _))))

/-- The lifting step: if `Y` is closed under `f` and `a ∉ Y`, then adding `a` to a set that is
independent inside `Y` for `liftMap f Y a` gives an `f`-independent set. -/
private theorem fIndependent_insert [DecidableEq X] (f : Finset X → Set X) {Y : Set X}
    (hY : ∀ A : Finset X, (A : Set X) ⊆ Y → f A ⊆ Y) {a : X} (haY : a ∉ Y) {B : Finset Y}
    (hB : FIndependent (liftMap f Y a) B) :
    FIndependent f (insert a (B.map (Function.Embedding.subtype _))) := by
  classical
  intro C hC p hp hpC
  -- Every point of `C` other than `a` lies in `Y`.
  have hCY : ∀ x ∈ C, x ≠ a → x ∈ Y := fun x hx hxa ↦ by
    rcases Finset.mem_insert.mp (hC hx) with rfl | hxB
    · exact absurd rfl hxa
    · obtain ⟨y, -, rfl⟩ := Finset.mem_map.mp hxB
      exact y.2
  rcases Finset.mem_insert.mp hp with rfl | hpB
  · -- `C` omits `p = a`, so it is a finite subset of `Y`, and `f C ⊆ Y` misses `a`.
    exact fun h ↦ haY (hY C (fun x hx ↦ hCY x hx (ne_of_mem_of_not_mem hx hpC)) h)
  · -- `p ∈ Y`: pull `C` back into `Y` as `C'`; then `C` is `C' ∪ {a}` or `C'` as a set of `X`.
    obtain ⟨q, hqB, rfl⟩ := Finset.mem_map.mp hpB
    set C' : Finset Y := C.subtype (· ∈ Y)
    have hC' : C'.map (Function.Embedding.subtype _) = C.erase a := by
      rw [Finset.subtype_map]
      ext x
      simp only [Finset.mem_filter, Finset.mem_erase]
      exact ⟨fun h ↦ ⟨fun hxa ↦ haY (hxa ▸ h.2), h.1⟩, fun h ↦ ⟨h.2, hCY x h.2 h.1⟩⟩
    have hC'B : C' ⊆ B := fun y hy ↦ by
      have hyC : (y : X) ∈ C := Finset.mem_subtype.mp hy
      rcases Finset.mem_insert.mp (hC hyC) with hya | hyB
      · exact absurd (hya ▸ y.2) haY
      · exact (Finset.mem_map' _).mp hyB
    have hqC' : q ∉ C' := fun h ↦ hpC (Finset.mem_subtype.mp h)
    have hq := hB C' hC'B q hqB hqC'
    simp only [liftMap, hC', Set.mem_preimage, Set.mem_union, not_or] at hq
    by_cases haC : a ∈ C
    · rw [Finset.insert_erase haC] at hq
      exact hq.2
    · rw [Finset.erase_eq_of_notMem haC] at hq
      exact hq.1

/-- The induction behind `exists_fIndependent`, quantified over all carriers in the universe. -/
private theorem exists_fIndependent_aux (k : ℕ) :
    ∀ {X : Type u} (f : Finset X → Set X) (α : Ordinal.{u}),
      (∀ A, #(f A) < ℵ_ α) → ℵ_ (α + k) ≤ #X →
        ∃ A : Finset X, A.card = k + 1 ∧ FIndependent f A := by
  classical
  induction k with
  | zero =>
    intro X f α hf hX
    rw [Nat.cast_zero, add_zero] at hX
    obtain ⟨x, hx⟩ := compl_nonempty_of_mk_lt_mk ((hf ∅).trans_le hX)
    refine ⟨{x}, Finset.card_singleton x, fun B hB a ha haB ↦ ?_⟩
    rw [Finset.mem_singleton] at ha
    subst ha
    rcases Finset.subset_singleton_iff.mp hB with rfl | rfl
    · exact hx
    · exact absurd (Finset.mem_singleton_self a) haB
  | succ k ih =>
    intro X f α hf hX
    have hlt : ℵ_ (α + k) < ℵ_ (α + (k + 1 : ℕ)) := by
      rw [aleph_lt_aleph, Nat.cast_succ, ← add_assoc]
      exact Order.lt_add_one_iff.mpr le_rfl
    obtain ⟨Y₀, hY₀⟩ := le_mk_iff_exists_set.mp (hlt.le.trans hX)
    have hfκ : ∀ A, #(f A) ≤ ℵ_ (α + k) := fun A ↦
      ((hf A).trans_le (aleph_le_aleph.mpr le_self_add)).le
    have hYle : #(fClosure f Y₀) ≤ ℵ_ (α + k) :=
      mk_fClosure_le f (aleph0_le_aleph _) hfκ hY₀.le
    obtain ⟨a, haY⟩ := compl_nonempty_of_mk_lt_mk (hYle.trans_lt (hlt.trans_le hX))
    have hg : ∀ B, #(liftMap f (fClosure f Y₀) a B) < ℵ_ α := fun B ↦
      (mk_preimage_of_injective _ _ Subtype.val_injective).trans_lt
        ((mk_union_le _ _).trans_lt (add_lt_of_lt (aleph0_le_aleph α) (hf _) (hf _)))
    obtain ⟨B, hBcard, hBind⟩ :=
      ih (liftMap f (fClosure f Y₀) a) α hg (hY₀ ▸ mk_le_mk_of_subset (subset_fClosure f Y₀))
    refine ⟨_, ?_, fIndependent_insert f (fun A ↦ fClosure_closed f Y₀) haY hBind⟩
    have haB : a ∉ B.map (Function.Embedding.subtype _) := fun h ↦
      haY (Finset.map_subtype_subset B h)
    rw [Finset.card_insert_of_notMem haB, Finset.card_map, hBcard]

/-- If every value of `f` has cardinality `< ℵ_ α` and `ℵ_ (α + k) ≤ #X`, then some
`f`-independent set has exactly `k + 1` elements.

This is Baldwin, Friedman, Koerwien, Laskowski, *Three red herrings* (2014), Lemma 2.3, with `≤`
in place of the printed `=` in the cardinality hypothesis; the source credits the origin of the
argument to Laskowski–Shelah.  The printed proof's auxiliary map `f ({a} ∪ A) ∩ Y` is only
sufficient for monotone `f`; the proof here uses `(f A ∪ f (insert a A)) ∩ Y`. -/
theorem exists_fIndependent (f : Finset X → Set X) (α : Ordinal.{u}) (k : ℕ)
    (hf : ∀ A, Cardinal.mk (f A) < Cardinal.aleph α)
    (hX : Cardinal.aleph (α + k) ≤ Cardinal.mk X) :
    ∃ A : Finset X, A.card = k + 1 ∧ FIndependent f A :=
  exists_fIndependent_aux k f α hf hX

/-! ### Hulls generated by boundedly many points -/

section Generation

variable {M : Type u}

/-- If every hull of `c` is the hull of a subset with at most `n` elements, then no set with more
than `n` elements is independent for the hull map `S ↦ c S`. -/
theorem not_fIndependent_of_generation (c : ClosureOperator (Finset M)) {n : ℕ}
    (hgen : ∀ S, ∃ T ⊆ S, T.card ≤ n ∧ c T = c S) {A : Finset M} (hA : n < A.card) :
    ¬ FIndependent (fun S ↦ (↑(c S) : Set M)) A := by
  intro hind
  obtain ⟨T, hTA, hTcard, hTc⟩ := hgen A
  obtain ⟨p, hpA, hpT⟩ := Finset.exists_mem_notMem_of_card_lt_card (hTcard.trans_lt hA)
  exact hind T hTA p hpA hpT (Finset.mem_coe.mpr (hTc ▸ c.le_closure A hpA))

/-- If every hull of `c` is the hull of a subset with at most `n` elements, then the carrier has
cardinality `< ℵ_ n`. -/
theorem mk_lt_aleph_of_generation (c : ClosureOperator (Finset M)) {n : ℕ}
    (hgen : ∀ S, ∃ T ⊆ S, T.card ≤ n ∧ c T = c S) : Cardinal.mk M < Cardinal.aleph n := by
  by_contra h
  have hX : ℵ_ ((0 : Ordinal.{u}) + n) ≤ #M := by
    rw [zero_add]
    exact le_of_not_gt h
  have hf : ∀ S : Finset M, #(↑(c S) : Set M) < ℵ_ 0 := fun S ↦ by
    rw [aleph_zero]
    exact (c S).finite_toSet.lt_aleph0
  obtain ⟨A, hAcard, hA⟩ := exists_fIndependent (fun S ↦ (↑(c S) : Set M)) 0 n hf hX
  exact not_fIndependent_of_generation c hgen (hAcard ▸ Nat.lt_succ_self n) hA

end Generation

end InfinitaryLogic.FreeSet
