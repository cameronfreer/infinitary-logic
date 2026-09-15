/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.FiberProfilePerm
import Mathlib.Data.Set.Card

/-!
# Finite-level thresholds for pure sets

Back-and-forth equivalence between an **infinite** pure set `X` and a **finite** pure set `Y`
(empty language, arbitrary empty-language structure instances) is decided by a count: for tuples
`a`, `b` with the same equality pattern and a natural level `k`,

  `BFEquiv k n a b ↔ k ≤ spare b`,

where `spare b` is the number of elements of `Y` outside the range of `b`
(`bfEquiv_natCast_iff`).  The positive direction answers a fresh element on the infinite side
by a spare one and an old element by its match; failure is pinned exactly at `spare b + 1`
(`not_bfEquiv_spare_succ`): the infinite side plays a fresh element and the finite side must
answer with a fresh one, using up a spare, until none is left.

For empty tuples of `ℕ` and `Fin m` this is `k ≤ m`, with failure at `m + 1`
(`bfEquiv_nat_fin_iff`, `not_bfEquiv_nat_fin_succ`).

Also: every tuple of **any** pure set has orbit rank `0` (`orbitRank_pure_eq_zero`), the finite
counterpart of `orbitRank_pureSet`: a tuple with the same pattern is the image under a
permutation extended from the finite matching (`exists_equiv_of_matching` with the trivial
equivalence relation).
-/

namespace FirstOrder.Language

/-- The empty language is relational (Mathlib supplies this under an auto-generated name; the
explicit instance here documents the dependency). -/
instance instEmptyIsRelational : Language.empty.IsRelational :=
  fun _ => inferInstanceAs (IsEmpty Empty)

namespace PureSet

universe u v

variable {X : Type u} {Y : Type v} [Language.empty.Structure X] [Language.empty.Structure Y]

/-- Atomic agreement in the empty language, between two carriers, is agreement of the equality
pattern. -/
theorem sameAtomicType_iff {n : ℕ} (a : Fin n → X) (b : Fin n → Y) :
    SameAtomicType (L := Language.empty) (M := X) (N := Y) a b ↔
      ∀ i j, a i = a j ↔ b i = b j := by
  constructor
  · intro h i j
    have := h (AtomicIdx.eq i j)
    simpa [AtomicIdx.holds] using this
  · intro h idx
    cases idx with
    | eq i j => simpa [AtomicIdx.holds] using h i j
    | rel R _ => exact (IsEmpty.false R).elim

/-- The number of elements outside the range of a tuple. -/
noncomputable def spare {n : ℕ} (b : Fin n → Y) : ℕ := Set.ncard ((Set.range b)ᶜ : Set Y)

omit [Language.empty.Structure Y] in
theorem range_snoc {n : ℕ} (b : Fin n → Y) (y : Y) :
    Set.range (Fin.snoc b y : Fin (n + 1) → Y) = insert y (Set.range b) := by
  ext z
  simp only [Set.mem_range, Set.mem_insert_iff]
  constructor
  · rintro ⟨i, rfl⟩
    refine Fin.lastCases ?_ (fun i => ?_) i
    · exact Or.inl (by simp)
    · exact Or.inr ⟨i, by simp⟩
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨Fin.last n, by simp⟩
    · exact ⟨i.castSucc, by simp⟩

omit [Language.empty.Structure Y] in
theorem spare_snoc_of_mem {n : ℕ} (b : Fin n → Y) {y : Y} (hy : y ∈ Set.range b) :
    spare (Fin.snoc b y : Fin (n + 1) → Y) = spare b := by
  unfold spare
  rw [range_snoc, Set.insert_eq_of_mem hy]

omit [Language.empty.Structure Y] in
theorem spare_snoc_of_notMem [Finite Y] {n : ℕ} (b : Fin n → Y) {y : Y}
    (hy : y ∉ Set.range b) : spare (Fin.snoc b y : Fin (n + 1) → Y) + 1 = spare b := by
  unfold spare
  have hT : (insert y (Set.range b))ᶜ = (Set.range b)ᶜ \ {y} := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff, not_or]
    exact and_comm
  rw [range_snoc, hT, ← Set.ncard_insert_of_notMem (fun h => h.2 rfl), Set.insert_sdiff_singleton,
    Set.insert_eq_of_mem (Set.mem_compl hy)]

omit [Language.empty.Structure X] [Language.empty.Structure Y] in
/-- The equality pattern after appending matched coordinates. -/
theorem pattern_snoc {n : ℕ} {a : Fin n → X} {b : Fin n → Y} (h : ∀ i j, a i = a j ↔ b i = b j)
    {x : X} {y : Y} (hxy : ∀ i, a i = x ↔ b i = y) :
    ∀ i j, (Fin.snoc a x : Fin (n + 1) → X) i = (Fin.snoc a x : Fin (n + 1) → X) j ↔
      (Fin.snoc b y : Fin (n + 1) → Y) i = (Fin.snoc b y : Fin (n + 1) → Y) j := by
  intro p q
  refine Fin.lastCases ?_ (fun p => ?_) p <;> refine Fin.lastCases ?_ (fun q => ?_) q <;>
    simp only [Fin.snoc_last, Fin.snoc_castSucc]
  · exact ⟨fun e => (hxy q).mp e.symm |>.symm, fun e => (hxy q).mpr e.symm |>.symm⟩
  · exact hxy p
  · exact h p q

/-- **Positive direction**: a common pattern and `k ≤ spare b` give `BFEquiv k`. -/
theorem bfEquiv_of_le_spare [Infinite X] [Finite Y] :
    ∀ (k : ℕ) {n : ℕ} (a : Fin n → X) (b : Fin n → Y), (∀ i j, a i = a j ↔ b i = b j) →
      k ≤ spare b →
      BFEquiv (L := Language.empty) (M := X) (N := Y) (k : Ordinal.{max u v}) n a b := by
  intro k
  induction k with
  | zero =>
    intro n a b h _
    rw [Nat.cast_zero, BFEquiv.zero]
    exact (sameAtomicType_iff a b).mpr h
  | succ k ih =>
    intro n a b h hk
    rw [Nat.cast_succ, ← Order.succ_eq_add_one, BFEquiv.succ]
    refine ⟨ih a b h (Nat.le_of_succ_le hk), fun x => ?_, fun y => ?_⟩
    · by_cases hx : ∃ i, a i = x
      · obtain ⟨i, rfl⟩ := hx
        refine ⟨b i, ih _ _ (pattern_snoc h fun j => h j i) ?_⟩
        rw [spare_snoc_of_mem b ⟨i, rfl⟩]
        exact Nat.le_of_succ_le hk
      · push Not at hx
        have hpos : 0 < spare b := lt_of_lt_of_le (Nat.succ_pos k) hk
        obtain ⟨y, hy⟩ := Set.nonempty_of_ncard_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
        have hpat : ∀ j, a j = x ↔ b j = y :=
          fun j => ⟨fun e => (hx j e).elim, fun e => (hy ⟨j, e⟩).elim⟩
        have hsp : k ≤ spare (Fin.snoc b y : Fin (n + 1) → Y) := by
          have := spare_snoc_of_notMem b hy
          omega
        exact ⟨y, ih _ _ (pattern_snoc h hpat) hsp⟩
    · by_cases hy : ∃ i, b i = y
      · obtain ⟨i, rfl⟩ := hy
        refine ⟨a i, ih _ _ (pattern_snoc h fun j => h j i) ?_⟩
        rw [spare_snoc_of_mem b ⟨i, rfl⟩]
        exact Nat.le_of_succ_le hk
      · push Not at hy
        obtain ⟨x, -, hx⟩ := (Set.infinite_univ (α := X)).exists_notMem_finite
          (Set.finite_range a)
        have hy' : y ∉ Set.range b := fun ⟨j, e⟩ => hy j e
        have hpat : ∀ j, a j = x ↔ b j = y :=
          fun j => ⟨fun e => (hx ⟨j, e⟩).elim, fun e => (hy j e).elim⟩
        have hsp : k ≤ spare (Fin.snoc b y : Fin (n + 1) → Y) := by
          have := spare_snoc_of_notMem b hy'
          omega
        exact ⟨x, ih _ _ (pattern_snoc h hpat) hsp⟩

/-- **Failure at `spare b + 1`**, for any tuples: the infinite side plays fresh elements until
the finite side has no fresh answer. -/
theorem not_bfEquiv_spare_succ [Infinite X] [Finite Y] :
    ∀ (s : ℕ) {n : ℕ} (a : Fin n → X) (b : Fin n → Y), spare b = s →
      ¬ BFEquiv (L := Language.empty) (M := X) (N := Y) ((s + 1 : ℕ) : Ordinal.{max u v})
        n a b := by
  intro s
  induction s with
  | zero =>
    intro n a b hs hbf
    rw [Nat.cast_succ, ← Order.succ_eq_add_one, BFEquiv.succ] at hbf
    obtain ⟨x, -, hx⟩ := (Set.infinite_univ (α := X)).exists_notMem_finite (Set.finite_range a)
    obtain ⟨y, hy⟩ := hbf.2.1 x
    have h0 := (sameAtomicType_iff _ _).mp ((BFEquiv.zero _ _).mp
      (BFEquiv.monotone (by simp) hy))
    have hfresh : y ∉ Set.range b := by
      rintro ⟨j, hj⟩
      have := (h0 j.castSucc (Fin.last n)).mpr (by simp [Fin.snoc_castSucc, Fin.snoc_last, hj])
      simp only [Fin.snoc_castSucc, Fin.snoc_last] at this
      exact hx ⟨j, this⟩
    have : (Set.range b)ᶜ = ∅ := (Set.ncard_eq_zero (Set.toFinite _)).mp hs
    exact Set.eq_empty_iff_forall_notMem.mp this y hfresh
  | succ s ih =>
    intro n a b hs hbf
    rw [Nat.cast_succ, ← Order.succ_eq_add_one, BFEquiv.succ] at hbf
    obtain ⟨x, -, hx⟩ := (Set.infinite_univ (α := X)).exists_notMem_finite (Set.finite_range a)
    obtain ⟨y, hy⟩ := hbf.2.1 x
    have h0 := (sameAtomicType_iff _ _).mp ((BFEquiv.zero _ _).mp
      (BFEquiv.monotone (by simp) hy))
    have hfresh : y ∉ Set.range b := by
      rintro ⟨j, hj⟩
      have := (h0 j.castSucc (Fin.last n)).mpr (by simp [Fin.snoc_castSucc, Fin.snoc_last, hj])
      simp only [Fin.snoc_castSucc, Fin.snoc_last] at this
      exact hx ⟨j, this⟩
    have hs' : spare (Fin.snoc b y : Fin (n + 1) → Y) = s := by
      have := spare_snoc_of_notMem b hfresh
      omega
    exact ih _ _ hs' hy

/-- **The threshold**: at a natural level `k`, equivalence holds iff the patterns agree and
`k ≤ spare b`. -/
theorem bfEquiv_natCast_iff [Infinite X] [Finite Y] (k : ℕ) {n : ℕ} (a : Fin n → X)
    (b : Fin n → Y) :
    BFEquiv (L := Language.empty) (M := X) (N := Y) (k : Ordinal.{max u v}) n a b ↔
      (∀ i j, a i = a j ↔ b i = b j) ∧ k ≤ spare b := by
  constructor
  · intro h
    refine ⟨(sameAtomicType_iff a b).mp ((BFEquiv.zero _ _).mp
      (BFEquiv.monotone (by simp) h)), ?_⟩
    by_contra hk
    push Not at hk
    exact not_bfEquiv_spare_succ (spare b) a b rfl
      (BFEquiv.monotone (by exact_mod_cast hk) h)
  · rintro ⟨h, hk⟩
    exact bfEquiv_of_le_spare k a b h hk

/-- **Every tuple of any pure set has orbit rank `0`**, finite or infinite. -/
theorem orbitRank_pure_eq_zero {n : ℕ} (a : Fin n → Y) :
    orbitRank (L := Language.empty) (M := Y) a = 0 := by
  apply le_antisymm _ _root_.zero_le
  apply orbitRank_le_of_mem
  intro b hb γ
  have h := (sameAtomicType_iff a b).mp ((BFEquiv.zero _ _).mp hb)
  obtain ⟨e, he, -, -⟩ := FiberAssembly.exists_equiv_of_matching
    (E := fun (_ _ : Y) => True) ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩ n a b
    h (fun _ => trivial)
  let g : Y ≃[Language.empty] Y :=
    { toEquiv := e
      map_fun' := fun {_} f _ => (IsEmpty.false f).elim
      map_rel' := fun {_} R _ => (IsEmpty.false R).elim }
  exact bfEquiv_all_of_automorphism g (funext fun j => (he j : g (a j) = b j)) γ

/-- No isomorphism between an infinite and a finite structure. -/
theorem isEmpty_equiv_of_infinite_finite [Infinite X] [Finite Y] :
    IsEmpty (X ≃[Language.empty] Y) :=
  ⟨fun e => haveI : Finite X := Finite.of_equiv Y e.toEquiv.symm; not_finite X⟩

/-! ### `ℕ` against `Fin m` -/

instance instStructureNat : Language.empty.Structure ℕ := Language.emptyStructure

instance instStructureFin (m : ℕ) : Language.empty.Structure (Fin m) := Language.emptyStructure

theorem spare_elim0 (m : ℕ) : spare (Fin.elim0 : Fin 0 → Fin m) = m := by
  unfold spare
  rw [Set.range_eq_empty, Set.compl_empty, Set.ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_fin]

/-- Empty tuples of `ℕ` and `Fin m` are equivalent at `k` iff `k ≤ m`. -/
theorem bfEquiv_nat_fin_iff (k m : ℕ) :
    BFEquiv (L := Language.empty) (M := ℕ) (N := Fin m) (k : Ordinal.{0}) 0
      Fin.elim0 Fin.elim0 ↔ k ≤ m := by
  refine (bfEquiv_natCast_iff k _ _).trans ?_
  rw [spare_elim0]
  exact ⟨fun h => h.2, fun h => ⟨fun i => i.elim0, h⟩⟩

/-- Failure pinned at `m + 1`. -/
theorem not_bfEquiv_nat_fin_succ (m : ℕ) :
    ¬ BFEquiv (L := Language.empty) (M := ℕ) (N := Fin m) ((m + 1 : ℕ) : Ordinal.{0}) 0
      Fin.elim0 Fin.elim0 := by
  intro h
  have := (bfEquiv_nat_fin_iff (m + 1) m).mp h
  omega

end PureSet

end FirstOrder.Language
