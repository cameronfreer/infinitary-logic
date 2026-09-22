/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.FiberCompanion
import InfinitaryLogic.ModelTheory.FiberIsoAssembly
import InfinitaryLogic.ModelTheory.FiberProfileBound
import Mathlib.Order.Interval.Finset.Nat

/-!
# Companions are not isomorphic to the base, nor to each other

For an **arbitrary** path `π` (no allowedness: the companion carrier is defined for every path,
and labels include inadmissible words) with **infinitely many non-default positions**
(`InfinitelyNonDefault`: positions are counted, so repeated occurrences of one non-default
component suffice), and a relational component language:

* `companion_not_iso`: the companion along `π` is not isomorphic to the base.
* `companions_not_iso`: for `π ≠ σ`, the companion along `π` is not isomorphic to the companion
  along `σ`; only the **source** path's non-default positions are used.

Route: an isomorphism restricts to rows (`restrictRows`) and, with `[Lc.IsRelational]`, to fiber
isomorphisms at every label (`restrictFiber`).  The path row's image is a finite row `s` or the
other path row.  In the first case take a non-default position `k > s.length`: at the prefix
label `π|ₖ₊₁` the path row has `B (π k)` while `s` has the default.  In the second case take any
coordinate `k₀` where the paths differ and a non-default position `k ≥ k₀`: `π|ₖ₊₁` is not on
`σ` (`not_isPathPrefix_prefixLabel_of_ne`), so again `B (π k)` faces the default.  Both cases
end in the shared helper: a fiber isomorphism from the index `some (π k)` to the index `none`
would make `π k` default-like.  Transport is through the component indices and their canonical
structures.

No approximation, countability, nesting, or rank hypothesis enters.
-/

namespace FirstOrder.Language

namespace FiberAssembly

universe u v w

variable {U : Type u} [LinearOrder U] {Lc : Language.{v, w}} (Bstar : Type u) (B : U → Type u)
  [Lc.Structure Bstar] [∀ u, Lc.Structure (B u)] {A : ℕ → Set U}

/-- (H_path-nondefault) **infinitely many non-default positions** on the path.  Positions are
counted, not distinct letters. -/
def InfinitelyNonDefault (Lc : Language.{v, w}) (Bstar : Type u) (B : U → Type u)
    [Lc.Structure Bstar] [∀ u, Lc.Structure (B u)] (π : ℕ → U) : Prop :=
  {k | ¬ DefaultLike Lc Bstar B (π k)}.Infinite

/-- The shared contradiction: at the prefix label `π|ₖ₊₁` of a non-default position `k`, no fiber
isomorphism can go from the path row's component to a default index. -/
private theorem no_iso_at_nondefault {π : ℕ → U} {k : ℕ} (hk : ¬ DefaultLike Lc Bstar B (π k))
    {o : Option U} (ho : o = none)
    (f : Comp Bstar B (pathIndex π (prefixLabel π k)) ≃[Lc] Comp Bstar B o) : False := by
  subst ho
  revert f
  rw [pathIndex_prefixLabel]
  intro f
  exact hk ⟨f⟩

/-- A finite row gives the default at every label longer than itself. -/
private theorem compIndex_eq_none_of_length_lt {s : Row A} {τ : Label U}
    (h : s.1.length < τ.1.length) : compIndex s.1 τ = none :=
  compIndex_of_not_prefix fun hp => by
    have := hp.length_le
    omega

/-- **The companion is not isomorphic to the base.** -/
theorem companion_not_iso [Lc.IsRelational] (π : ℕ → U)
    (hnd : InfinitelyNonDefault Lc Bstar B π) :
    IsEmpty (CompanionCarrier Bstar B A π ≃[lang U Lc] PrefixCarrier Bstar B A) := by
  refine ⟨fun g => ?_⟩
  obtain ⟨k, hk, hlt⟩ := hnd.exists_gt (restrictRows g (Sum.inr ())).1.length
  have f := restrictFiber g (Sum.inr ()) (prefixLabel π k)
  exact no_iso_at_nondefault Bstar B hk
    (compIndex_eq_none_of_length_lt (s := restrictRows g (Sum.inr ())) (by simp; omega)) f

/-- **Distinct paths give non-isomorphic companions**, from the source path's non-default
positions only. -/
theorem companions_not_iso [Lc.IsRelational] {π σ : ℕ → U} (hne : π ≠ σ)
    (hnd : InfinitelyNonDefault Lc Bstar B π) :
    IsEmpty (CompanionCarrier Bstar B A π ≃[lang U Lc] CompanionCarrier Bstar B A σ) := by
  refine ⟨fun g => ?_⟩
  rcases hr : restrictRows g (Sum.inr ()) with s | _
  · -- the path row goes to a finite row
    obtain ⟨k, hk, hlt⟩ := hnd.exists_gt s.1.length
    have f := restrictFiber g (Sum.inr ()) (prefixLabel π k)
    rw [hr] at f
    exact no_iso_at_nondefault Bstar B hk
      (compIndex_eq_none_of_length_lt (s := s) (by simp; omega)) f
  · -- the path row goes to the other path row
    obtain ⟨k₀, hk₀⟩ : ∃ k₀, π k₀ ≠ σ k₀ := by
      by_contra h
      push Not at h
      exact hne (funext h)
    obtain ⟨k, hk, hlt⟩ := hnd.exists_gt k₀
    have f := restrictFiber g (Sum.inr ()) (prefixLabel π k)
    rw [hr] at f
    exact no_iso_at_nondefault Bstar B hk
      (pathIndex_of_not_isPathPrefix (not_isPathPrefix_prefixLabel_of_ne hk₀ hlt.le)) f

end FiberAssembly

end FirstOrder.Language
