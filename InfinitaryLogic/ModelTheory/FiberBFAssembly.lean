/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.FiberIsoAssembly
import InfinitaryLogic.Scott.BFEquivRelabel

/-!
# Back-and-forth assembly under a fixed row bijection

Over arbitrary row types `R, S` and fiber families `C, D` with `Lc`-structures on every fiber,
fix a **total** row bijection `e : R ≃ S`.  Two tuples `a : Fin n → Carrier R C` and
`b : Fin n → Carrier S D` are **matched along `e`** (`Matched e a b`) when, coordinatewise,
`a i` is the row `r` iff `b i` is the row `e r`, and `a i` lies in the fiber `(r, τ)` iff `b i`
lies in the fiber `(e r, τ)`.  Repeated coordinates are allowed.

**Fiber back-and-forth data** (`FiberBF α e a b`): for every row `r`, every label `τ`, and
every finite selection `ι : Fin k → Fin n` of coordinates lying in the fiber `(r, τ)`
(repetitions allowed), the selected component tuples of `a` in `C r τ` and of `b` in
`D (e r) τ` are back-and-forth equivalent at level `α`.  With `k = 0` this includes the empty
tuples of **every** fiber, occupied or not: unoccupied fibers must be `α`-equivalent as
structures.

**Theorem** (`bfEquiv_of_fiberBF`): matched tuples with fiber back-and-forth data at level `α`
are back-and-forth equivalent at level `α` in the assembled language, the **same** level.  The
fixed bijection already tracks the owners absent from the tuple, so no level is spent on rows.

The proof is by induction on `α`.  At level `0` every atom of the assembled language is decided
by the matching and by one atom of one fiber.  At a successor, a move by a row is answered by
its image row, and a move by a fiber point is answered by the fiber's own forth (or back) move
applied to the canonical enumeration of that fiber's coordinates; every other selection of
coordinates in the extended tuple is a relabeling of that one (`BFEquiv.relabel`), and the
other fibers are unchanged up to relabeling.  Full-profile bounds and companion matching are
outside this module.
-/

namespace FirstOrder.Language

namespace FiberAssembly

universe u v w

variable {U : Type u} {Lc : Language.{v, w}} {R S : Type u} {C : R → Label U → Type u}
  {D : S → Label U → Type u} [∀ r τ, Lc.Structure (C r τ)] [∀ s τ, Lc.Structure (D s τ)]

/-! ### Fiber membership and component elements -/

/-- The coordinate `i` of `a` lies in the fiber `(r, τ)`. -/
def InFiber {n : ℕ} (a : Fin n → Carrier R C) (r : R) (τ : Label U) (i : Fin n) : Prop :=
  ∃ x, a i = Carrier.pt r τ x

/-- The component element at a coordinate lying in the fiber `(r, τ)`. -/
noncomputable def elt {n : ℕ} {a : Fin n → Carrier R C} {r : R} {τ : Label U} {i : Fin n}
    (h : InFiber a r τ i) : C r τ :=
  h.choose

theorem elt_spec {n : ℕ} {a : Fin n → Carrier R C} {r : R} {τ : Label U} {i : Fin n}
    (h : InFiber a r τ i) : a i = Carrier.pt r τ (elt h) :=
  h.choose_spec

/-- The component element is determined by the coordinate. -/
theorem elt_eq {n : ℕ} {a : Fin n → Carrier R C} {r : R} {τ : Label U} {i : Fin n}
    (h : InFiber a r τ i) {x : C r τ} (hx : a i = Carrier.pt r τ x) : elt h = x :=
  Carrier.pt_inj_same ((elt_spec h).symm.trans hx)

/-- Membership at a coordinate known to be a fiber point. -/
theorem inFiber_iff_of_eq_pt {n : ℕ} {a : Fin n → Carrier R C} {i : Fin n} {r₀ : R}
    {τ₀ : Label U} {x₀ : C r₀ τ₀} (h : a i = Carrier.pt r₀ τ₀ x₀) (r : R) (τ : Label U) :
    InFiber a r τ i ↔ r = r₀ ∧ τ = τ₀ := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨hr, hτ, -⟩ := Carrier.pt_inj (hx.symm.trans h)
    exact ⟨hr, hτ⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨x₀, h⟩

/-- A row coordinate lies in no fiber. -/
theorem not_inFiber_of_eq_row {n : ℕ} {a : Fin n → Carrier R C} {i : Fin n} {r₀ : R}
    (h : a i = Carrier.row r₀) (r : R) (τ : Label U) : ¬ InFiber a r τ i := by
  rintro ⟨x, hx⟩
  rw [h] at hx
  cases hx

/-! ### Matching along a row bijection -/

/-- `b` is matched to `a` along `e`: coordinatewise, rows correspond to image rows and fiber
points to points of the image fiber with the same label, in both directions. -/
def Matched (e : R ≃ S) {n : ℕ} (a : Fin n → Carrier R C) (b : Fin n → Carrier S D) : Prop :=
  ∀ i, (∀ r, a i = Carrier.row r ↔ b i = Carrier.row (e r)) ∧
    (∀ r τ, InFiber a r τ i ↔ InFiber b (e r) τ i)

namespace Matched

variable {e : R ≃ S} {n : ℕ} {a : Fin n → Carrier R C} {b : Fin n → Carrier S D}

theorem row_iff (hm : Matched e a b) (i : Fin n) (r : R) :
    a i = Carrier.row r ↔ b i = Carrier.row (e r) := (hm i).1 r

theorem inFiber_iff (hm : Matched e a b) (i : Fin n) (r : R) (τ : Label U) :
    InFiber a r τ i ↔ InFiber b (e r) τ i := (hm i).2 r τ

/-- The `b`-side component element at a coordinate of the fiber `(r, τ)` of `a`. -/
noncomputable def eltB (hm : Matched e a b) {r : R} {τ : Label U} {i : Fin n}
    (h : InFiber a r τ i) : D (e r) τ :=
  elt ((hm.inFiber_iff i r τ).mp h)

theorem eltB_spec (hm : Matched e a b) {r : R} {τ : Label U} {i : Fin n}
    (h : InFiber a r τ i) : b i = Carrier.pt (e r) τ (hm.eltB h) :=
  elt_spec _

theorem eltB_eq (hm : Matched e a b) {r : R} {τ : Label U} {i : Fin n}
    (h : InFiber a r τ i) {y : D (e r) τ} (hy : b i = Carrier.pt (e r) τ y) : hm.eltB h = y :=
  elt_eq _ hy

/-- Extending a matching by a row and its image row. -/
theorem snoc_row (hm : Matched e a b) (r : R) :
    Matched e (Fin.snoc a (Carrier.row r)) (Fin.snoc b (Carrier.row (e r))) := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [InFiber, Fin.snoc_last]
    refine ⟨fun r' => ?_, fun r' τ => ?_⟩
    · constructor
      · intro h; rw [Carrier.row.inj h]
      · intro h; rw [e.injective (Carrier.row.inj h)]
    · constructor
      · rintro ⟨x, hx⟩; cases hx
      · rintro ⟨y, hy⟩; cases hy
  · simp only [InFiber, Fin.snoc_castSucc]
    exact hm j

/-- Extending a matching by a fiber point and a point of the image fiber. -/
theorem snoc_pt (hm : Matched e a b) (r : R) (τ : Label U) (x : C r τ) (y : D (e r) τ) :
    Matched e (Fin.snoc a (Carrier.pt r τ x)) (Fin.snoc b (Carrier.pt (e r) τ y)) := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [InFiber, Fin.snoc_last]
    refine ⟨fun r' => ?_, fun r' τ' => ?_⟩
    · constructor
      · intro h; cases h
      · intro h; cases h
    · constructor
      · rintro ⟨x', hx⟩
        obtain ⟨rfl, rfl, -⟩ := Carrier.pt_inj hx
        exact ⟨y, rfl⟩
      · rintro ⟨y', hy⟩
        obtain ⟨hr, rfl, -⟩ := Carrier.pt_inj hy
        have hr' := e.injective hr
        subst hr'
        exact ⟨x, rfl⟩
  · simp only [InFiber, Fin.snoc_castSucc]
    exact hm j

end Matched

/-! ### Fiber back-and-forth data -/

/-- **Fiber back-and-forth data at level `α`**: every selection of coordinates in one fiber,
repetitions allowed and the empty selection included, has back-and-forth equivalent component
tuples on the two sides. -/
def FiberBF (Lc : Language.{v, w}) [∀ r τ, Lc.Structure (C r τ)] [∀ s τ, Lc.Structure (D s τ)]
    (α : Ordinal) (e : R ≃ S) {n : ℕ} {a : Fin n → Carrier R C}
    {b : Fin n → Carrier S D} (hm : Matched e a b) : Prop :=
  ∀ (r : R) (τ : Label U) (k : ℕ) (ι : Fin k → Fin n) (h : ∀ j, InFiber a r τ (ι j)),
    BFEquiv (L := Lc) α k (fun j => elt (h j)) (fun j => hm.eltB (h j))

theorem FiberBF.monotone {α β : Ordinal} (hβα : β ≤ α) {e : R ≃ S} {n : ℕ}
    {a : Fin n → Carrier R C} {b : Fin n → Carrier S D} {hm : Matched e a b}
    (h : FiberBF Lc α e hm) : FiberBF Lc β e hm :=
  fun r τ k ι hι => BFEquiv.monotone hβα (h r τ k ι hι)

/-! ### Level zero: atoms -/

/-- Matched tuples with level-`0` fiber data have the same atomic type in the assembled
language. -/
theorem sameAtomicType_of_fiberBF_zero {e : R ≃ S} {n : ℕ} {a : Fin n → Carrier R C}
    {b : Fin n → Carrier S D} (hm : Matched e a b) (hf : FiberBF Lc 0 e hm) :
    SameAtomicType (L := lang U Lc) a b := by
  -- the fiber atoms, unpacked once
  have fib : ∀ (r : R) (τ : Label U) (k : ℕ) (ι : Fin k → Fin n) (h : ∀ j, InFiber a r τ (ι j)),
      SameAtomicType (L := Lc) (fun j => elt (h j)) (fun j => hm.eltB (h j)) :=
    fun r τ k ι h => (BFEquiv.zero _ _).mp (hf r τ k ι h)
  intro idx
  cases idx with
  | eq i j =>
    simp only [AtomicIdx.holds]
    cases hai : a i with
    | row r =>
      have hbi : b i = Carrier.row (e r) := (hm.row_iff i r).mp hai
      cases haj : a j with
      | row r' =>
        have hbj : b j = Carrier.row (e r') := (hm.row_iff j r').mp haj
        rw [hbi, hbj]
        constructor
        · intro h; rw [Carrier.row.inj h]
        · intro h; rw [e.injective (Carrier.row.inj h)]
      | pt r' τ' x' =>
        obtain ⟨y', hy'⟩ := (hm.inFiber_iff j r' τ').mp ⟨x', haj⟩
        rw [hbi, hy']
        constructor <;> intro h <;> cases h
    | pt r τ x =>
      obtain ⟨y, hy⟩ := (hm.inFiber_iff i r τ).mp ⟨x, hai⟩
      cases haj : a j with
      | row r' =>
        have hbj : b j = Carrier.row (e r') := (hm.row_iff j r').mp haj
        rw [hy, hbj]
        constructor <;> intro h <;> cases h
      | pt r' τ' x' =>
        obtain ⟨y', hy'⟩ := (hm.inFiber_iff j r' τ').mp ⟨x', haj⟩
        rw [hy, hy']
        by_cases hr : r = r'
        · subst hr
          by_cases hτ : τ = τ'
          · subst hτ
            -- same fiber: the equality atom of that fiber at the two coordinates
            have hi : InFiber a r τ i := ⟨x, hai⟩
            have hj : InFiber a r τ j := ⟨x', haj⟩
            have h2 := fib r τ 2 ![i, j] (fun k => by fin_cases k <;> assumption)
              (AtomicIdx.eq 0 1)
            simp only [AtomicIdx.holds] at h2
            constructor
            · intro h
              obtain ⟨-, -, hx⟩ := Carrier.pt_inj h
              have hxx : x = x' := eq_of_heq hx
              have h3 := h2.mp ((elt_eq _ hai).trans (hxx.trans (elt_eq _ haj).symm))
              have hyy : y = y' := (hm.eltB_eq _ hy).symm.trans (h3.trans (hm.eltB_eq _ hy'))
              rw [hyy]
            · intro h
              obtain ⟨-, -, hy2⟩ := Carrier.pt_inj h
              have hyy : y = y' := eq_of_heq hy2
              have h3 := h2.mpr ((hm.eltB_eq _ hy).trans (hyy.trans (hm.eltB_eq _ hy').symm))
              have hxx : x = x' := (elt_eq _ hai).symm.trans (h3.trans (elt_eq _ haj))
              rw [hxx]
          · constructor
            · intro h; exact absurd (Carrier.pt_inj h).2.1 hτ
            · intro h; exact absurd (Carrier.pt_inj h).2.1 hτ
        · constructor
          · intro h; exact absurd (Carrier.pt_inj h).1 hr
          · intro h; exact absurd (e.injective (Carrier.pt_inj h).1) hr
  | rel Sy f =>
    simp only [AtomicIdx.holds]
    cases Sy with
    | row =>
      constructor
      · rintro ⟨r, hr⟩
        exact ⟨e r, (hm.row_iff (f 0) r).mp hr⟩
      · rintro ⟨s, hs⟩
        obtain ⟨r, rfl⟩ := e.surjective s
        exact ⟨r, (hm.row_iff (f 0) r).mpr hs⟩
    | own =>
      constructor
      · rintro ⟨r, τ, x, h0, h1⟩
        obtain ⟨y, hy⟩ := (hm.inFiber_iff (f 0) r τ).mp ⟨x, h0⟩
        exact ⟨e r, τ, y, hy, (hm.row_iff (f 1) r).mp h1⟩
      · rintro ⟨s, τ, y, h0, h1⟩
        obtain ⟨r, rfl⟩ := e.surjective s
        obtain ⟨x, hx⟩ := (hm.inFiber_iff (f 0) r τ).mpr ⟨y, h0⟩
        exact ⟨r, τ, x, hx, (hm.row_iff (f 1) r).mpr h1⟩
    | lab τ =>
      constructor
      · rintro ⟨r, x, h⟩
        obtain ⟨y, hy⟩ := (hm.inFiber_iff (f 0) r τ).mp ⟨x, h⟩
        exact ⟨e r, y, hy⟩
      · rintro ⟨s, y, h⟩
        obtain ⟨r, rfl⟩ := e.surjective s
        obtain ⟨x, hx⟩ := (hm.inFiber_iff (f 0) r τ).mpr ⟨y, h⟩
        exact ⟨r, x, hx⟩
    | lift Sy =>
      constructor
      · rintro ⟨r, τ, x, hx, hS⟩
        have hι : ∀ j, InFiber a r τ (f j) := fun j => ⟨x j, hx j⟩
        refine ⟨e r, τ, fun j => hm.eltB (hι j), fun j => hm.eltB_spec (hι j), ?_⟩
        have h2 := fib r τ _ f hι (AtomicIdx.rel Sy id)
        simp only [AtomicIdx.holds, Function.comp_id] at h2
        have ex : (fun j => elt (hι j)) = x := funext fun j => elt_eq _ (hx j)
        rw [ex] at h2
        exact h2.mp hS
      · rintro ⟨s, τ, y, hy, hS⟩
        obtain ⟨r, rfl⟩ := e.surjective s
        have hι : ∀ j, InFiber a r τ (f j) := fun j =>
          (hm.inFiber_iff (f j) r τ).mpr ⟨y j, hy j⟩
        refine ⟨r, τ, fun j => elt (hι j), fun j => elt_spec (hι j), ?_⟩
        have h2 := fib r τ _ f hι (AtomicIdx.rel Sy id)
        simp only [AtomicIdx.holds, Function.comp_id] at h2
        have ey : (fun j => hm.eltB (hι j)) = y := funext fun j => hm.eltB_eq _ (hy j)
        rw [ey] at h2
        exact h2.mpr hS
    | lift0 Sy τ =>
      constructor
      · rintro ⟨r, hr, hS⟩
        refine ⟨e r, (hm.row_iff (f 0) r).mp hr, ?_⟩
        have h2 := fib r τ 0 Fin.elim0 (fun j => j.elim0) (AtomicIdx.rel Sy Fin.elim0)
        simp only [AtomicIdx.holds] at h2
        rw [show (fun j : Fin 0 => elt (show InFiber a r τ (Fin.elim0 j) from j.elim0)) ∘
            Fin.elim0 = Fin.elim0 from funext fun j => j.elim0,
          show (fun j : Fin 0 => hm.eltB (show InFiber a r τ (Fin.elim0 j) from j.elim0)) ∘
            Fin.elim0 = Fin.elim0 from funext fun j => j.elim0] at h2
        exact h2.mp hS
      · rintro ⟨s, hs, hS⟩
        obtain ⟨r, rfl⟩ := e.surjective s
        refine ⟨r, (hm.row_iff (f 0) r).mpr hs, ?_⟩
        have h2 := fib r τ 0 Fin.elim0 (fun j => j.elim0) (AtomicIdx.rel Sy Fin.elim0)
        simp only [AtomicIdx.holds] at h2
        rw [show (fun j : Fin 0 => elt (show InFiber a r τ (Fin.elim0 j) from j.elim0)) ∘
            Fin.elim0 = Fin.elim0 from funext fun j => j.elim0,
          show (fun j : Fin 0 => hm.eltB (show InFiber a r τ (Fin.elim0 j) from j.elim0)) ∘
            Fin.elim0 = Fin.elim0 from funext fun j => j.elim0] at h2
        exact h2.mpr hS


/-! ### Selections in an extended tuple -/

section Extend

variable {e : R ≃ S} {n : ℕ} {a : Fin n → Carrier R C} {b : Fin n → Carrier S D}

/-- A coordinate below the new last one lies in a fiber of the extended tuple iff it does in
the original tuple. -/
theorem inFiber_snoc_castSucc (m : Carrier R C) (r : R) (τ : Label U) (i : Fin n) :
    InFiber (Fin.snoc a m) r τ (Fin.castSucc i) ↔ InFiber a r τ i := by
  simp only [InFiber, Fin.snoc_castSucc]

/-- The component element at a coordinate below the new last one is unchanged. -/
theorem elt_snoc_castSucc {m : Carrier R C} {r : R} {τ : Label U} {i : Fin n}
    (h' : InFiber (Fin.snoc a m) r τ (Fin.castSucc i)) (h : InFiber a r τ i) :
    elt h' = elt h :=
  elt_eq h' (by rw [Fin.snoc_castSucc]; exact elt_spec h)

theorem eltB_snoc_castSucc {m : Carrier R C} {m' : Carrier S D} {hm : Matched e a b}
    (hm' : Matched e (Fin.snoc a m) (Fin.snoc b m')) {r : R} {τ : Label U} {i : Fin n}
    (h' : InFiber (Fin.snoc a m) r τ (Fin.castSucc i)) (h : InFiber a r τ i) :
    hm'.eltB h' = hm.eltB h :=
  hm'.eltB_eq h' (by rw [Fin.snoc_castSucc]; exact hm.eltB_spec h)

/-- If the new last element is not in the fiber `(r, τ)`, every selected coordinate of that
fiber is below it. -/
theorem ne_last_of_inFiber {m : Carrier R C} {r : R} {τ : Label U}
    (hlast : ¬ InFiber (Fin.snoc a m) r τ (Fin.last n)) {i : Fin (n + 1)}
    (h : InFiber (Fin.snoc a m) r τ i) : i ≠ Fin.last n :=
  fun hi => hlast (hi ▸ h)

/-- Fiber data survive a move whose new element is not in the fiber: the selection is a
selection in the original tuple. -/
theorem fiberBF_snoc_of_not_inFiber {β : Ordinal} {hm : Matched e a b}
    (hf : FiberBF Lc β e hm) {m : Carrier R C} {m' : Carrier S D}
    (hm' : Matched e (Fin.snoc a m) (Fin.snoc b m')) (r : R) (τ : Label U)
    (hlast : ¬ InFiber (Fin.snoc a m) r τ (Fin.last n)) (k : ℕ) (ι : Fin k → Fin (n + 1))
    (hι : ∀ j, InFiber (Fin.snoc a m) r τ (ι j)) :
    BFEquiv (L := Lc) β k (fun j => elt (hι j)) (fun j => hm'.eltB (hι j)) := by
  let ι₀ : Fin k → Fin n := fun j => Fin.castPred (ι j) (ne_last_of_inFiber hlast (hι j))
  have hcast : ∀ j, Fin.castSucc (ι₀ j) = ι j := fun j => Fin.castSucc_castPred _ _
  have h₀ : ∀ j, InFiber a r τ (ι₀ j) := fun j =>
    (inFiber_snoc_castSucc m r τ (ι₀ j)).mp (by rw [hcast]; exact hι j)
  have ea : (fun j => elt (hι j)) = fun j => elt (h₀ j) := funext fun j => by
    have h' : InFiber (Fin.snoc a m) r τ (Fin.castSucc (ι₀ j)) := by rw [hcast]; exact hι j
    have : elt (hι j) = elt h' := rfl
    rw [this, elt_snoc_castSucc h' (h₀ j)]
  have eb : (fun j => hm'.eltB (hι j)) = fun j => hm.eltB (h₀ j) := funext fun j => by
    have h' : InFiber (Fin.snoc a m) r τ (Fin.castSucc (ι₀ j)) := by rw [hcast]; exact hι j
    have : hm'.eltB (hι j) = hm'.eltB h' := rfl
    rw [this, eltB_snoc_castSucc hm' h' (h₀ j)]
  rw [ea, eb]
  exact hf r τ k ι₀ h₀

/-- Fiber data survive a row move. -/
theorem fiberBF_snoc_row {β : Ordinal} {hm : Matched e a b} (hf : FiberBF Lc β e hm) (r : R) :
    FiberBF Lc β e (hm.snoc_row r) := by
  intro r' τ k ι hι
  refine fiberBF_snoc_of_not_inFiber hf (hm.snoc_row r) r' τ ?_ k ι hι
  rintro ⟨x, hx⟩
  rw [Fin.snoc_last] at hx
  cases hx

end Extend

/-! ### The canonical enumeration of a fiber's coordinates -/

section Enum

variable {e : R ≃ S} {n : ℕ} {a : Fin n → Carrier R C} {b : Fin n → Carrier S D}

open Classical in
/-- The number of coordinates of `a` in the fiber `(r, τ)`. -/
noncomputable def fiberCard (a : Fin n → Carrier R C) (r : R) (τ : Label U) : ℕ :=
  Fintype.card {i : Fin n // InFiber a r τ i}

open Classical in
/-- The canonical enumeration of the coordinates of `a` in the fiber `(r, τ)`. -/
noncomputable def fiberEnum (a : Fin n → Carrier R C) (r : R) (τ : Label U) :
    {i : Fin n // InFiber a r τ i} ≃ Fin (fiberCard a r τ) :=
  Fintype.equivFin _

/-- The canonical component tuple of `a` in the fiber `(r, τ)`. -/
noncomputable def fiberTuple (a : Fin n → Carrier R C) (r : R) (τ : Label U) :
    Fin (fiberCard a r τ) → C r τ :=
  fun j => elt ((fiberEnum a r τ).symm j).2

/-- The canonical component tuple of `b` over the same coordinates. -/
noncomputable def fiberTupleB (hm : Matched e a b) (r : R) (τ : Label U) :
    Fin (fiberCard a r τ) → D (e r) τ :=
  fun j => hm.eltB ((fiberEnum a r τ).symm j).2

/-- The canonical tuple at an enumerated coordinate is that coordinate's component element. -/
theorem fiberTuple_enum (a : Fin n → Carrier R C) (r : R) (τ : Label U)
    (i : {i : Fin n // InFiber a r τ i}) :
    fiberTuple a r τ (fiberEnum a r τ i) = elt i.2 := by
  simp only [fiberTuple]
  exact elt_eq _ (by rw [_root_.Equiv.symm_apply_apply (fiberEnum a r τ) i]; exact elt_spec i.2)

theorem fiberTupleB_enum (hm : Matched e a b) (r : R) (τ : Label U)
    (i : {i : Fin n // InFiber a r τ i}) :
    fiberTupleB hm r τ (fiberEnum a r τ i) = hm.eltB i.2 := by
  simp only [fiberTupleB]
  exact hm.eltB_eq _ (by
    rw [_root_.Equiv.symm_apply_apply (fiberEnum a r τ) i]
    exact hm.eltB_spec i.2)

theorem fiberBF_fiberTuple {β : Ordinal} {hm : Matched e a b} (hf : FiberBF Lc β e hm) (r : R)
    (τ : Label U) : BFEquiv (L := Lc) β _ (fiberTuple a r τ) (fiberTupleB hm r τ) :=
  hf r τ _ (fun j => ((fiberEnum a r τ).symm j).1) (fun j => ((fiberEnum a r τ).symm j).2)

/-- The relabeling that sends a selection in the extended tuple, all in the fiber `(r, τ)` of
the new point, to positions in `snoc (fiberTuple a r τ) x`: the new coordinate goes to the last
position and an old coordinate to its position in the canonical enumeration. -/
noncomputable def extendIdx (a : Fin n → Carrier R C) (r : R) (τ : Label U) (x : C r τ)
    {k : ℕ} (ι : Fin k → Fin (n + 1))
    (hι : ∀ j, InFiber (Fin.snoc a (Carrier.pt r τ x)) r τ (ι j)) :
    Fin k → Fin (fiberCard a r τ + 1) :=
  fun j =>
    if h : ι j = Fin.last n then Fin.last _
    else Fin.castSucc (fiberEnum a r τ ⟨Fin.castPred (ι j) h,
      (inFiber_snoc_castSucc _ r τ _).mp (by rw [Fin.castSucc_castPred]; exact hι j)⟩)

/-- Fiber data survive a fiber-point move once the fiber's own move has been answered: the
selections of the new point's fiber are relabelings of the extended canonical tuples, and the
other fibers are unchanged. -/
theorem fiberBF_snoc_pt {β : Ordinal} {hm : Matched e a b} (hf : FiberBF Lc β e hm)
    (r : R) (τ : Label U) (x : C r τ) (y : D (e r) τ)
    (hxy : BFEquiv (L := Lc) β _ (Fin.snoc (fiberTuple a r τ) x)
      (Fin.snoc (fiberTupleB hm r τ) y)) :
    FiberBF Lc β e (hm.snoc_pt r τ x y) := by
  intro r' τ' k ι hι
  by_cases hrt : r' = r ∧ τ' = τ
  · obtain ⟨rfl, rfl⟩ := hrt
    -- the new point's fiber: relabel the extended canonical tuples
    have hrel := BFEquiv.relabel β hxy (extendIdx a r' τ' x ι hι)
    have ea : (fun j => elt (hι j)) =
        Fin.snoc (fiberTuple a r' τ') x ∘ extendIdx a r' τ' x ι hι := by
      funext j
      simp only [Function.comp, extendIdx]
      split_ifs with h
      · rw [Fin.snoc_last]
        exact elt_eq _ (by rw [h, Fin.snoc_last])
      · rw [Fin.snoc_castSucc, fiberTuple_enum]
        refine elt_eq (hι j) ?_
        change (Fin.snoc a (Carrier.pt r' τ' x) : Fin (n + 1) → Carrier R C)
          (Fin.castSucc (Fin.castPred (ι j) h)) = _
        rw [Fin.snoc_castSucc]
        exact elt_spec _
    have eb : (fun j => (hm.snoc_pt r' τ' x y).eltB (hι j)) =
        Fin.snoc (fiberTupleB hm r' τ') y ∘ extendIdx a r' τ' x ι hι := by
      funext j
      simp only [Function.comp, extendIdx]
      split_ifs with h
      · rw [Fin.snoc_last]
        exact (hm.snoc_pt r' τ' x y).eltB_eq _ (by rw [h, Fin.snoc_last])
      · rw [Fin.snoc_castSucc, fiberTupleB_enum]
        refine (hm.snoc_pt r' τ' x y).eltB_eq (hι j) ?_
        change (Fin.snoc b (Carrier.pt (e r') τ' y) : Fin (n + 1) → Carrier S D)
          (Fin.castSucc (Fin.castPred (ι j) h)) = _
        rw [Fin.snoc_castSucc]
        exact hm.eltB_spec _
    rw [ea, eb]
    exact hrel
  · -- another fiber: the new point is not in it
    refine fiberBF_snoc_of_not_inFiber hf (hm.snoc_pt r τ x y) r' τ' ?_ k ι hι
    rintro ⟨x', hx'⟩
    rw [Fin.snoc_last] at hx'
    obtain ⟨hr, hτ, -⟩ := Carrier.pt_inj hx'
    exact hrt ⟨hr.symm, hτ.symm⟩

end Enum

/-! ### The theorem -/

/-- **Back-and-forth assembly under a fixed row bijection**: matched tuples with fiber
back-and-forth data at level `α` are back-and-forth equivalent at level `α` in the assembled
language.  No level is spent on rows. -/
theorem bfEquiv_of_fiberBF (α : Ordinal) {e : R ≃ S} :
    ∀ {n : ℕ} {a : Fin n → Carrier R C} {b : Fin n → Carrier S D} (hm : Matched e a b),
      FiberBF Lc α e hm → BFEquiv (L := lang U Lc) α n a b := by
  induction α using Ordinal.limitRecOn with
  | zero =>
    intro n a b hm hf
    exact (BFEquiv.zero _ _).mpr (sameAtomicType_of_fiberBF_zero hm hf)
  | add_one β ih =>
    intro n a b hm hf
    rw [← Order.succ_eq_add_one, BFEquiv.succ]
    refine ⟨ih hm (hf.monotone (Order.le_succ β)), fun m => ?_, fun m' => ?_⟩
    · cases m with
      | row r =>
        exact ⟨Carrier.row (e r), ih (hm.snoc_row r)
          (fiberBF_snoc_row (hf.monotone (Order.le_succ β)) r)⟩
      | pt r τ x =>
        obtain ⟨y, hy⟩ := BFEquiv.forth (fiberBF_fiberTuple hf r τ) x
        exact ⟨Carrier.pt (e r) τ y, ih (hm.snoc_pt r τ x y)
          (fiberBF_snoc_pt (hf.monotone (Order.le_succ β)) r τ x y hy)⟩
    · cases m' with
      | row s =>
        obtain ⟨r, rfl⟩ := e.surjective s
        exact ⟨Carrier.row r, ih (hm.snoc_row r)
          (fiberBF_snoc_row (hf.monotone (Order.le_succ β)) r)⟩
      | pt s τ y =>
        obtain ⟨r, rfl⟩ := e.surjective s
        obtain ⟨x, hx⟩ := BFEquiv.back (fiberBF_fiberTuple hf r τ) y
        exact ⟨Carrier.pt r τ x, ih (hm.snoc_pt r τ x y)
          (fiberBF_snoc_pt (hf.monotone (Order.le_succ β)) r τ x y hx)⟩
  | limit β hβ ih =>
    intro n a b hm hf
    rw [BFEquiv.limit β hβ]
    exact fun γ hγ => ih γ hγ hm (hf.monotone hγ.le)

end FiberAssembly

end FirstOrder.Language
