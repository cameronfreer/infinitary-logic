/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.FiberProfileBound
import InfinitaryLogic.ModelTheory.FiberProfilePerm
import InfinitaryLogic.ModelTheory.FiberOwnerRows
import InfinitaryLogic.ModelTheory.FiberIsoCarrying
import Mathlib.Algebra.Order.SuccPred

/-!
# The finite-tuple orbit bound

For the prefix specialization `M := PrefixCarrier Bstar B A` over `lang U Lc`, a **conditional
upper bound** on orbit ranks and on the internal Scott rank, from:

* (H_sep) `SepBounded` and (H_up) `UpwardClosed (DefaultLike …)`, the hypotheses of the
  row-profile bound;
* (H_orb) `OrbitBounded`: every tuple of every fiber has orbit rank below `α`, pointwise;
* component relationality and countability (`[Lc.IsRelational]`, `[Countable Bstar]`,
  `[∀ u, Countable (B u)]`); the carrier itself is not assumed countable;
* `AddNatClosed α`: closure below `α` under adding a finite ordinal on the right, supplied by any
  nonzero limit ordinal (`AddNatClosed.of_isSuccLimit`).

**Theorem** (`exists_automorphism_bound`): for every tuple `a` there is `β < α` such that every
`b` with `a ≡_β b` is the image of `a` under an automorphism.  The level is chosen from `a`
**before** `b`: extend `a` by its owner rows (`a⁺`), fix a cover of `a⁺`, and let `β₀` be the
finite maximum of the profile bounds of the finitely many owner rows and the orbit ranks of the
finitely many occupied fiber tuples; the witness is `β₀ + n`.  Given `b`, the owner rows are
added (`bfEquiv_append_ownerRows`, cost `n`), the owner block gives a compatible same-profile
matching of rows extended to a profile-preserving permutation (`exists_profilePerm`), the
level-`0` atoms give the matching of the extended tuples along it
(`matched_of_sameAtomicType_ownerRows`), and the fiber isomorphisms are adjusted to carry the
extended tuple (`exists_fiber_isos_carrying`); the assembled automorphism restricts to `a`.

**Corollary** (`internalScottRank_le_of_bounds`): `internalScottRank M ≤ α`.

This is an upper bound under hypotheses; it is neither an exact rank nor a uniform
orbit-determining level for all tuples.
-/

namespace FirstOrder.Language

namespace FiberAssembly

universe u v w

/-! ### Closure under finite addition -/

/-- Closure below `α` under adding a finite ordinal on the right. -/
def AddNatClosed (α : Ordinal.{u}) : Prop := ∀ β < α, ∀ n : ℕ, β + n < α

/-- A nonzero limit ordinal is closed below under finite right addition. -/
theorem AddNatClosed.of_isSuccLimit {α : Ordinal.{u}} (h : Order.IsSuccLimit α) :
    AddNatClosed α :=
  fun _ hβ n => h.add_natCast_lt hβ n

/-! ### The level-`0` matching of owner-extended tuples -/

section Matching

variable {U : Type u} {Lc : Language.{v, w}} {R : Type u} {C : R → Label U → Type u}
  [∀ r τ, Lc.Structure (C r τ)]

/-- Owner-extended tuples with the same atomic type are matched along any row bijection agreeing
with the owner matching, in both directions and on both blocks. -/
theorem matched_of_sameAtomicType_ownerRows {n : ℕ} {a b : Fin n → Carrier R C} (e : R ≃ R)
    (h0 : SameAtomicType (L := lang U Lc) (Fin.append a (ownerRow a)) (Fin.append b (ownerRow b)))
    (he : ∀ j, e (owner (a j)) = owner (b j)) :
    Matched e (Fin.append a (ownerRow a)) (Fin.append b (ownerRow b)) := by
  -- the row atom: a coordinate of the first block is a row on one side iff on the other
  have hrow : ∀ j : Fin n, (∃ r, a j = Carrier.row r) ↔ ∃ r, b j = Carrier.row r := by
    intro j
    have := h0 (AtomicIdx.rel Sym.row ![Fin.castAdd n j])
    simpa only [AtomicIdx.holds, relMap_row, Function.comp_apply, Matrix.cons_val_zero,
      Fin.append_left] using this
  -- the own atom against the owner coordinate
  have hown : ∀ j : Fin n, (∃ r τ x, a j = Carrier.pt r τ x ∧ ownerRow a j = Carrier.row r) ↔
      ∃ r τ y, b j = Carrier.pt r τ y ∧ ownerRow b j = Carrier.row r := by
    intro j
    have := h0 (AtomicIdx.rel Sym.own ![Fin.castAdd n j, Fin.natAdd n j])
    simpa only [AtomicIdx.holds, relMap_own, Function.comp_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.append_left, Fin.append_right] using this
  -- the label atom
  have hlab : ∀ (j : Fin n) (τ : Label U), (∃ r x, a j = Carrier.pt r τ x) ↔
      ∃ r y, b j = Carrier.pt r τ y := by
    intro j τ
    have := h0 (AtomicIdx.rel (Sym.lab τ) ![Fin.castAdd n j])
    simpa only [AtomicIdx.holds, relMap_lab, Function.comp_apply, Matrix.cons_val_zero,
      Fin.append_left] using this
  intro i
  refine Fin.addCases (fun j => ⟨fun r => ?_, fun r τ => ?_⟩)
    (fun j => ⟨fun r => ?_, fun r τ => ?_⟩) i
  · -- first block, rows
    simp only [Fin.append_left]
    constructor
    · intro ha
      obtain ⟨r', hr'⟩ := (hrow j).mp ⟨r, ha⟩
      have : owner (b j) = r' := by rw [hr']; rfl
      rw [hr', ← this, ← he j, ha]
      rfl
    · intro hb
      obtain ⟨r', hr'⟩ := (hrow j).mpr ⟨_, hb⟩
      have h1 : owner (a j) = r' := by rw [hr']; rfl
      have h2 : owner (b j) = e r := by rw [hb]; rfl
      have := he j
      rw [h1, h2] at this
      rw [hr', e.injective this]
  · -- first block, fibers
    simp only [InFiber, Fin.append_left]
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨r', τ', y, hb, hb'⟩ := (hown j).mp ⟨r, τ, x, hx, by rw [ownerRow_apply, hx]; rfl⟩
      obtain ⟨r'', y', hb''⟩ := (hlab j τ).mp ⟨r, x, hx⟩
      obtain ⟨-, rfl, -⟩ := Carrier.pt.inj (hb.symm.trans hb'')
      have hr : r' = e r := by
        have := he j
        rw [show owner (a j) = r by rw [hx]; rfl, show owner (b j) = r' by rw [hb]; rfl] at this
        exact this.symm
      subst hr
      exact ⟨y, hb⟩
    · rintro ⟨y, hy⟩
      obtain ⟨r', τ', x, ha, -⟩ := (hown j).mpr ⟨e r, τ, y, hy, by rw [ownerRow_apply, hy]; rfl⟩
      obtain ⟨r'', x', ha'⟩ := (hlab j τ).mpr ⟨_, y, hy⟩
      obtain ⟨-, rfl, -⟩ := Carrier.pt.inj (ha.symm.trans ha')
      have hr : r' = r := by
        have := he j
        rw [show owner (a j) = r' by rw [ha]; rfl, show owner (b j) = e r by rw [hy]; rfl] at this
        exact e.injective this
      subst hr
      exact ⟨x, ha⟩
  · -- owner block, rows
    simp only [Fin.append_right, ownerRow_apply, Carrier.row.injEq, ← he j]
    exact e.injective.eq_iff.symm
  · -- owner block, no fibers
    simp only [InFiber, Fin.append_right, ownerRow_apply]
    exact iff_of_false (by simp) (by simp)

/-- In an owner-extended tuple every fiber point has its owner row present: only first-block
coordinates are points, and their owners sit in the second block. -/
theorem owners_present_append_ownerRows {n : ℕ} (a : Fin n → Carrier R C) :
    ∀ i r τ, InFiber (Fin.append a (ownerRow a)) r τ i →
      ∃ j, Fin.append a (ownerRow a) j = Carrier.row r := by
  intro i r τ hi
  refine Fin.addCases (fun j hj => ?_) (fun j hj => ?_) i hi
  · obtain ⟨x, hx⟩ := hj
    rw [Fin.append_left] at hx
    exact ⟨Fin.natAdd n j, by rw [Fin.append_right, ownerRow_apply, hx]; rfl⟩
  · obtain ⟨x, hx⟩ := hj
    rw [Fin.append_right, ownerRow_apply] at hx
    exact absurd hx (by simp)

end Matching

/-! ### The orbit bound -/

variable {U : Type u} [LinearOrder U] {Lc : Language.{v, w}} {Bstar : Type u} {B : U → Type u}
  [Lc.Structure Bstar] [∀ u, Lc.Structure (B u)] {A : ℕ → Set U}

/-- (H_orb) **Pointwise component orbit bounds**: every tuple of every fiber has orbit rank
below `α`. -/
def OrbitBounded (Lc : Language.{v, w}) (Bstar : Type u) (B : U → Type u) [Lc.Structure Bstar]
    [∀ u, Lc.Structure (B u)] (A : ℕ → Set U) (α : Ordinal.{u}) : Prop :=
  ∀ (r : Row A) (τ : Label U) (k : ℕ) (t : Fin k → prefixFiber Bstar B A r τ),
    orbitRank (L := Lc) t < α

/-- **Finite-tuple orbit bound**, pointwise automorphism form.  For every tuple `a` there is
`β < α`, chosen from `a`, such that every `b` with `a ≡_β b` is the image of `a` under an
automorphism of the assembled structure. -/
theorem exists_automorphism_bound [Lc.IsRelational] [Countable Bstar] [∀ u, Countable (B u)]
    (α : Ordinal.{u}) (hsep : SepBounded Lc Bstar B A α)
    (hup : UpwardClosed (DefaultLike Lc Bstar B)) (horb : OrbitBounded Lc Bstar B A α)
    (hα : AddNatClosed α) (n : ℕ) (a : Fin n → PrefixCarrier Bstar B A) :
    ∃ β < α, ∀ b : Fin n → PrefixCarrier Bstar B A, BFEquiv (L := lang U Lc) β n a b →
      ∃ g : PrefixCarrier Bstar B A ≃[lang U Lc] PrefixCarrier Bstar B A, ⇑g ∘ a = b := by
  classical
  -- `α` is positive: H_sep at `N = 0` exhibits a level below it
  have hα0 : (⊥ : Ordinal.{u}) < α := by
    obtain ⟨β, hβ, -⟩ := hsep 0
    exact lt_of_le_of_lt bot_le hβ
  -- the profile bounds, one per row
  choose βr hβr hprof using fun r : Row A =>
    exists_profile_bound (Lc := Lc) (Bstar := Bstar) (B := B) (A := A) α hsep hup r
  -- the owner-extended tuple and its cover, fixed before `b`
  set aplus : Fin (n + n) → PrefixCarrier Bstar B A := Fin.append a (ownerRow a) with haplus
  let cov : FiberCover aplus := FiberCover.ofTuple aplus
  let rows : Finset (Row A) := Finset.univ.image fun j : Fin n => owner (a j)
  let occ : Finset (Row A × Label U) := cov.occupied_finite.toFinset
  let β₀ : Ordinal.{u} :=
    rows.sup βr ⊔ occ.sup fun p => orbitRank (L := Lc) (cov.srcTuple p.1 p.2)
  have hβ₀ : β₀ < α := by
    refine max_lt ?_ ?_
    · exact (Finset.sup_lt_iff hα0).mpr fun r _ => hβr r
    · exact (Finset.sup_lt_iff hα0).mpr fun p _ => horb _ _ _ _
  refine ⟨β₀ + n, hα β₀ hβ₀ n, fun b hb => ?_⟩
  -- add the owner rows
  have h1 : BFEquiv (L := lang U Lc) β₀ (n + n) aplus (Fin.append b (ownerRow b)) :=
    bfEquiv_append_ownerRows hb
  set bplus : Fin (n + n) → PrefixCarrier Bstar B A := Fin.append b (ownerRow b) with hbplus
  have h0 : SameAtomicType (L := lang U Lc) aplus bplus :=
    (BFEquiv.zero _ _).mp (BFEquiv.monotone _root_.zero_le h1)
  -- the owner block: a compatible same-profile matching of rows
  have hcomp : ∀ j j' : Fin n, owner (a j) = owner (a j') ↔ owner (b j) = owner (b j') := by
    intro j j'
    have := h0 (AtomicIdx.eq (Fin.natAdd n j) (Fin.natAdd n j'))
    simpa only [AtomicIdx.holds, haplus, hbplus, Fin.append_right, ownerRow_apply,
      Carrier.row.injEq] using this
  have hsp : ∀ j, SameProfile Lc Bstar B A (owner (a j)) (owner (b j)) := by
    intro j
    have h2 := BFEquiv.relabel β₀ h1 ![Fin.natAdd n j]
    have ea : aplus ∘ ![Fin.natAdd n j] = ![Carrier.row (owner (a j))] := by
      funext i; fin_cases i
      show aplus (Fin.natAdd n j) = Carrier.row (owner (a j))
      rw [haplus, Fin.append_right, ownerRow_apply]
    have eb : bplus ∘ ![Fin.natAdd n j] = ![Carrier.row (owner (b j))] := by
      funext i; fin_cases i
      show bplus (Fin.natAdd n j) = Carrier.row (owner (b j))
      rw [hbplus, Fin.append_right, ownerRow_apply]
    rw [ea, eb] at h2
    have hle : βr (owner (a j)) ≤ β₀ :=
      (Finset.le_sup (f := βr) (Finset.mem_image_of_mem _ (Finset.mem_univ j))).trans le_sup_left
    exact hprof _ _ (BFEquiv.monotone hle h2)
  obtain ⟨e, he, hsame, -⟩ := exists_profilePerm (Lc := Lc) (Bstar := Bstar) (B := B)
    (fun j => owner (a j)) (fun j => owner (b j)) hcomp hsp
  let f₀ : ∀ t τ, prefixFiber Bstar B A t τ ≃[Lc] prefixFiber Bstar B A (e t) τ :=
    fun t τ => Classical.choice (hsame t τ)
  -- the extended tuples are matched along `e`, with owners present
  have hm : Matched e aplus bplus := matched_of_sameAtomicType_ownerRows e h0 he
  have how := owners_present_append_ownerRows a
  -- the orbit premise: occupied fibers are in the maximum, unoccupied ones have rank `0`
  have horb' : ∀ r τ, orbitRank (L := Lc) (cov.srcTuple r τ) ≤ β₀ := by
    intro r τ
    by_cases h : 0 < cov.k r τ
    · have hmem : (r, τ) ∈ occ := cov.occupied_finite.mem_toFinset.mpr h
      exact (Finset.le_sup (f := fun p : Row A × Label U =>
        orbitRank (L := Lc) (cov.srcTuple p.1 p.2)) hmem).trans le_sup_right
    · rw [orbitRank_of_length_zero (Nat.eq_zero_of_not_pos h)]
      exact _root_.zero_le
  obtain ⟨f, hf, -⟩ := exists_fiber_isos_carrying β₀ e f₀ hm how h1 cov horb'
  refine ⟨assemble e f, funext fun i => ?_⟩
  have := congrFun hf (Fin.castAdd n i)
  simpa only [Function.comp_apply, haplus, hbplus, Fin.append_left] using this

/-- **Internal Scott rank bound.**  Under the same hypotheses, the internal Scott rank of the
assembled structure is at most `α`. -/
theorem internalScottRank_le_of_bounds [Lc.IsRelational] [Countable Bstar]
    [∀ u, Countable (B u)] (α : Ordinal.{u}) (hsep : SepBounded Lc Bstar B A α)
    (hup : UpwardClosed (DefaultLike Lc Bstar B)) (horb : OrbitBounded Lc Bstar B A α)
    (hα : AddNatClosed α) :
    internalScottRank (L := lang U Lc) (PrefixCarrier Bstar B A) ≤ α :=
  internalScottRank_le_of_orbits_determined fun n a =>
    exists_automorphism_bound α hsep hup horb hα n a

end FiberAssembly

end FirstOrder.Language
