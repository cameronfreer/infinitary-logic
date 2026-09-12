/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.FiberIsoAssembly
import InfinitaryLogic.ModelTheory.FiberBFAssembly
import InfinitaryLogic.ModelTheory.FiberBFRestriction
import InfinitaryLogic.Scott.BFEquivRelabel
import InfinitaryLogic.Scott.OrbitRank
import Mathlib.Data.Set.Finite.Lattice

/-!
# Fiber isomorphisms carrying a tuple

Given a row bijection `e` with fiber isomorphisms `f₀ r τ : C r τ ≃[Lc] C (e r) τ`, and tuples
`a`, `b` matched along `e` with the owner rows present, the fiber isomorphisms are **adjusted**
on the finitely many occupied fibers so that the assembled automorphism carries `a` to `b`.

* `FiberCover a`: one enumeration of all positions of `a` in each fiber (repeated values kept;
  coverage is by position).  `FiberCover.ofTuple` constructs one from any tuple, with no
  countability; `FiberCover.pos_iff` says `0 < k r τ` iff the fiber contains a coordinate, so the
  occupied fibers form a finite set (`FiberCover.occupied_finite`).
* The orbit-rank facts for empty tuples (`orbitRank_elim0`, `orbitRank_of_length_zero`) live in
  `Scott/OrbitRank.lean`; generic rank users need no fiber machinery.
* `exists_fiber_isos_carrying`: if `a ≡_β b`, and for every fiber the complete source tuple of
  the cover has orbit rank at most `β`, then there are fiber isomorphisms `f` with
  `assemble e f ∘ a = b`; `f` agrees with `f₀` on unoccupied fibers.

For an occupied fiber the pointed restriction lemma gives the level-`β` equivalence of the source
tuple with the matched target tuple (the owner row is present); the target tuple is pulled back
through `f₀`, the orbit-rank bound with `[Lc.IsRelational]` and countability gives an
automorphism of the source component moving the source tuple onto it, and composing with `f₀`
gives the adjusted isomorphism.  The premise on unoccupied fibers is automatic by
`orbitRank_elim0`, not vacuous: the hypothesis still quantifies over them.
-/

namespace FirstOrder.Language

namespace FiberAssembly

universe u' v' w'

variable {U : Type u'} {Lc : Language.{v', w'}} {R : Type u'} {C : R → Label U → Type u'}
  [∀ r τ, Lc.Structure (C r τ)]

/-! ### Fiber covers -/

/-- One enumeration of all positions of `a` in each fiber; repeated values are kept and coverage
is by position. -/
structure FiberCover {n : ℕ} (a : Fin n → Carrier R C) where
  /-- The length of the covering enumeration (positions may be enumerated more than once). -/
  k : R → Label U → ℕ
  /-- The enumeration of positions. -/
  ι : ∀ r τ, Fin (k r τ) → Fin n
  /-- Every enumerated position lies in the fiber. -/
  inFiber : ∀ r τ j, InFiber a r τ (ι r τ j)
  /-- Every position in the fiber is enumerated. -/
  covers : ∀ r τ i, InFiber a r τ i → ∃ j, ι r τ j = i

namespace FiberCover

variable {n : ℕ} {a : Fin n → Carrier R C}

/-- A cover exists for every tuple, with no countability assumption. -/
noncomputable def ofTuple (a : Fin n → Carrier R C) : FiberCover a := by
  classical
  exact
    { k := fun r τ => Fintype.card {i : Fin n // InFiber a r τ i}
      ι := fun r τ j => ((Fintype.equivFin {i : Fin n // InFiber a r τ i}).symm j).1
      inFiber := fun r τ j => ((Fintype.equivFin {i : Fin n // InFiber a r τ i}).symm j).2
      covers := fun r τ i hi =>
        ⟨Fintype.equivFin {i : Fin n // InFiber a r τ i} ⟨i, hi⟩, by simp⟩ }

/-- A fiber has a positive count iff it contains a coordinate of the tuple. -/
theorem pos_iff (cov : FiberCover a) (r : R) (τ : Label U) :
    0 < cov.k r τ ↔ ∃ i, InFiber a r τ i := by
  constructor
  · intro h
    exact ⟨_, cov.inFiber r τ ⟨0, h⟩⟩
  · rintro ⟨i, hi⟩
    obtain ⟨j, -⟩ := cov.covers r τ i hi
    exact lt_of_le_of_lt (Nat.zero_le _) j.2

/-- The fibers containing a given coordinate: at most one. -/
private theorem subsingleton_fibers_of_coord (i : Fin n) :
    {p : R × Label U | InFiber a p.1 p.2 i}.Subsingleton := by
  rintro ⟨r, τ⟩ ⟨x, hx⟩ ⟨r', τ'⟩ ⟨x', hx'⟩
  have h := hx.symm.trans hx'
  cases h
  rfl

/-- The occupied fibers form a finite set. -/
theorem occupied_finite (cov : FiberCover a) :
    {p : R × Label U | 0 < cov.k p.1 p.2}.Finite := by
  refine Set.Finite.subset (Set.finite_iUnion fun i : Fin n =>
    (subsingleton_fibers_of_coord (a := a) i).finite) ?_
  rintro ⟨r, τ⟩ hp
  obtain ⟨i, hi⟩ := (cov.pos_iff r τ).mp hp
  exact Set.mem_iUnion.mpr ⟨i, hi⟩

/-- The complete source tuple of a fiber. -/
noncomputable def srcTuple (cov : FiberCover a) (r : R) (τ : Label U) :
    Fin (cov.k r τ) → C r τ :=
  fun j => elt (cov.inFiber r τ j)

/-- The matched target tuple of a fiber, at the same positions. -/
noncomputable def tgtTuple (cov : FiberCover a) {e : R ≃ R} {b : Fin n → Carrier R C}
    (hm : Matched e a b) (r : R) (τ : Label U) : Fin (cov.k r τ) → C (e r) τ :=
  fun j => hm.eltB (cov.inFiber r τ j)

end FiberCover

/-- A tuple is matched, along `e`, with its image under an assembled isomorphism. -/
theorem matched_assemble {S : Type u'} {D : S → Label U → Type u'} [∀ s τ, Lc.Structure (D s τ)]
    (e : R ≃ S) (f : ∀ r τ, C r τ ≃[Lc] D (e r) τ) {n : ℕ} (a : Fin n → Carrier R C) :
    Matched e a (⇑(assemble e f) ∘ a) := by
  intro i
  refine ⟨fun r => ?_, fun r τ => ?_⟩
  · rcases ha : a i with ⟨r'⟩ | ⟨r', τ', x⟩
    · simp only [Function.comp_apply, ha, assemble_row, Carrier.row.injEq]
      exact e.injective.eq_iff.symm
    · simp only [Function.comp_apply, ha, assemble_pt]
      exact iff_of_false (by simp) (by simp)
  · rcases ha : a i with ⟨r'⟩ | ⟨r', τ', x⟩
    · simp only [InFiber, Function.comp_apply, ha, assemble_row]
      exact iff_of_false (by simp) (by simp)
    · simp only [InFiber, Function.comp_apply, ha, assemble_pt]
      constructor
      · rintro ⟨y, hy⟩
        obtain ⟨rfl, rfl, -⟩ := Carrier.pt.inj hy
        exact ⟨_, rfl⟩
      · rintro ⟨y, hy⟩
        obtain ⟨hr, rfl, -⟩ := Carrier.pt.inj hy
        obtain rfl := e.injective hr
        exact ⟨_, rfl⟩

/-! ### Adjusting the fiber isomorphisms -/

/-- On an occupied fiber, with its owner row present, the complete source and target tuples are
equivalent at the level of the ambient tuples. -/
private theorem bfEquiv_fiber_tuples {β : Ordinal} {e : R ≃ R} {n : ℕ}
    {a b : Fin n → Carrier R C} (hm : Matched e a b)
    (howners : ∀ i r τ, InFiber a r τ i → ∃ j, a j = Carrier.row r)
    (hbf : BFEquiv (L := lang U Lc) β n a b) (cov : FiberCover a) (r : R) (τ : Label U)
    (hk : 0 < cov.k r τ) :
    BFEquiv (L := Lc) β (cov.k r τ) (cov.srcTuple r τ) (cov.tgtTuple hm r τ) := by
  obtain ⟨j₀, hj₀⟩ := howners _ r τ (cov.inFiber r τ ⟨0, hk⟩)
  let σ : Fin (cov.k r τ + 1) → Fin n := Fin.cons j₀ (cov.ι r τ)
  have ha : a ∘ σ = rowPts r τ (cov.srcTuple r τ) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Function.comp_apply, σ, Fin.cons_zero, rowPts_zero, hj₀]
    · simp only [Function.comp_apply, σ, Fin.cons_succ, rowPts_succ, FiberCover.srcTuple]
      exact elt_spec _
  have hb : b ∘ σ = rowPts (e r) τ (cov.tgtTuple hm r τ) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Function.comp_apply, σ, Fin.cons_zero, rowPts_zero]
      exact ((hm j₀).1 r).mp hj₀
    · simp only [Function.comp_apply, σ, Fin.cons_succ, rowPts_succ, FiberCover.tgtTuple]
      exact hm.eltB_spec _
  have h := BFEquiv.relabel β hbf σ
  rw [ha, hb] at h
  exact bfEquiv_restrict_pointed β τ h

/-- **Fiber isomorphisms carrying the tuple.**  Given fiber isomorphisms `f₀` along `e`, tuples
`a ≡_β b` matched along `e` with owner rows present, a cover of `a`, and for every fiber an
orbit-rank bound `≤ β` on the complete source tuple, there are fiber isomorphisms `f` with
`assemble e f ∘ a = b`, agreeing with `f₀` on unoccupied fibers. -/
theorem exists_fiber_isos_carrying [Lc.IsRelational] [∀ r τ, Countable (C r τ)] (β : Ordinal)
    (e : R ≃ R) (f₀ : ∀ r τ, C r τ ≃[Lc] C (e r) τ) {n : ℕ} {a b : Fin n → Carrier R C}
    (hm : Matched e a b) (howners : ∀ i r τ, InFiber a r τ i → ∃ j, a j = Carrier.row r)
    (hbf : BFEquiv (L := lang U Lc) β n a b) (cov : FiberCover a)
    (horb : ∀ r τ, orbitRank (L := Lc) (cov.srcTuple r τ) ≤ β) :
    ∃ f : ∀ r τ, C r τ ≃[Lc] C (e r) τ, ⇑(assemble e f) ∘ a = b ∧
      ∀ r τ, ¬ 0 < cov.k r τ → f r τ = f₀ r τ := by
  classical
  -- an automorphism of each occupied source component moving the source tuple onto the target
  -- tuple pulled back through `f₀`
  have hg : ∀ r τ, 0 < cov.k r τ → ∃ g : C r τ ≃[Lc] C r τ,
      ⇑g ∘ cov.srcTuple r τ = ⇑(f₀ r τ).symm ∘ cov.tgtTuple hm r τ := by
    intro r τ hk
    have h1 := bfEquiv_fiber_tuples hm howners hbf cov r τ hk
    have h2 : BFEquiv (L := Lc) β _ (cov.srcTuple r τ)
        (⇑(f₀ r τ).symm ∘ cov.tgtTuple hm r τ) := by
      rw [← BFEquiv.map_equiv (Language.Equiv.refl Lc (C r τ)) (f₀ r τ)]
      convert h1 using 1
      · funext j
        rfl
      · funext j
        exact Language.Equiv.apply_symm_apply _ _
    have h3 : BFEquiv (L := Lc) (orbitRank (L := Lc) (cov.srcTuple r τ)) _ (cov.srcTuple r τ)
        (⇑(f₀ r τ).symm ∘ cov.tgtTuple hm r τ) :=
      (mem_orbitStable_iff_orbitRank_le.mpr (horb r τ)) _ h2 _
    exact bfEquiv_orbitRank_iff_exists_automorphism.mp h3
  choose g hg using hg
  refine ⟨fun r τ => if h : 0 < cov.k r τ then Language.Equiv.comp (f₀ r τ) (g r τ h)
    else f₀ r τ, ?_, fun r τ h => dite_eq_right h⟩
  funext i
  rcases ha : a i with ⟨r⟩ | ⟨r, τ, x⟩
  · simp only [Function.comp_apply, ha, assemble_row]
    exact (((hm i).1 r).mp ha).symm
  · have hi : InFiber a r τ i := ⟨x, ha⟩
    obtain ⟨j, hj⟩ := cov.covers r τ i hi
    have hk : 0 < cov.k r τ := (cov.pos_iff r τ).mpr ⟨i, hi⟩
    simp only [Function.comp_apply, ha, assemble_pt, dite_eq_left hk]
    rw [hm.eltB_spec hi]
    congr 1
    have hx : cov.srcTuple r τ j = x := by
      have hij : a (cov.ι r τ j) = Carrier.pt r τ x := by rw [hj]; exact ha
      exact elt_eq _ hij
    have hy : cov.tgtTuple hm r τ j = hm.eltB hi :=
      hm.eltB_eq _ (by rw [hj]; exact hm.eltB_spec hi)
    have hgj := congrFun (hg r τ hk) j
    simp only [Function.comp_apply] at hgj
    show (f₀ r τ) ((g r τ hk) x) = _
    rw [← hx, hgj, hy]
    exact Language.Equiv.apply_symm_apply _ _


end FiberAssembly

end FirstOrder.Language
