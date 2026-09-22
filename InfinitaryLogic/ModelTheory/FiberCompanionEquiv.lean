/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.FiberCompanionShift
import InfinitaryLogic.ModelTheory.FiberBFAssembly
import InfinitaryLogic.ModelTheory.FiberTwoRow

/-!
# Companion equivalence below a level

Under allowedness of the path and **level-uniform approximation** along it, the companion and
the base are equivalent as empty tuples.

* `PathApproxAt Lc Bstar B π β N`: from position `N` on, the component `B (π k)` is
  `β`-equivalent to the default as empty tuples.  `PathApprox … α`: every `β < α` has such a
  threshold.
* `companion_bfEquiv_of_pathApproxAt`: at one level `β` with threshold `N`, the companion and
  the base are `β`-equivalent.  The proof is the same-level assembly `bfEquiv_of_fiberBF` along
  the Hilbert-hotel bijection `shiftRows hπ N` with the vacuous empty-tuple matching and
  `fiberBF_of_no_points`; the fiberwise obligation splits as: fibers of a non-tail row are
  equal; a tail prefix `π|ₖ` against `π|ₖ₊₁` differs only at `prefixLabel π k`, where `B_*`
  faces `B (π k)` in that orientation; the path row against `π|ₙ` agrees at labels of length
  `≤ N`, and at a longer on-path label `prefixLabel π j` (`j ≥ N`) the pair is `B (π j)`
  against `B_*`, the symmetric orientation.
* `companion_bfEquiv`: below `α`, with the threshold chosen separately for each level.  No single
  bijection is claimed to work at every level.

Hypotheses are the component structure instances only: no countability, relationality,
nesting, non-defaultness, rank bounds, or ordinal-limit assumption.
-/

namespace FirstOrder.Language

namespace FiberAssembly

universe u v w

variable {U : Type u} [LinearOrder U] {Lc : Language.{v, w}} (Bstar : Type u) (B : U → Type u)
  [Lc.Structure Bstar] [∀ u, Lc.Structure (B u)] {A : ℕ → Set U} {π : ℕ → U}

/-! ### Level-uniform path approximation -/

/-- (H_path-approx) at level `β` with threshold `N`. -/
def PathApproxAt (Lc : Language.{v, w}) (Bstar : Type u) (B : U → Type u) [Lc.Structure Bstar]
    [∀ u, Lc.Structure (B u)] (π : ℕ → U) (β : Ordinal.{u}) (N : ℕ) : Prop :=
  ∀ k, N ≤ k →
    BFEquiv (L := Lc) β 0 (Fin.elim0 : Fin 0 → Bstar) (Fin.elim0 : Fin 0 → B (π k))

/-- (H_path-approx) below `α`: every level has a threshold. -/
def PathApprox (Lc : Language.{v, w}) (Bstar : Type u) (B : U → Type u) [Lc.Structure Bstar]
    [∀ u, Lc.Structure (B u)] (π : ℕ → U) (α : Ordinal.{u}) : Prop :=
  ∀ β < α, ∃ N, PathApproxAt Lc Bstar B π β N

/-! ### Transport along component-index equalities -/

omit [LinearOrder U] in
private theorem bfEquiv_comp_of_eq {β : Ordinal.{u}} {o o' : Option U} (h : o = o') :
    BFEquiv (L := Lc) β 0 (Fin.elim0 : Fin 0 → Comp Bstar B o)
      (Fin.elim0 : Fin 0 → Comp Bstar B o') := by
  subst h
  exact BFEquiv.refl β _

omit [LinearOrder U] in
private theorem bfEquiv_comp_none_some {β : Ordinal.{u}} {u : U}
    (h : BFEquiv (L := Lc) β 0 (Fin.elim0 : Fin 0 → Bstar) (Fin.elim0 : Fin 0 → B u))
    {o o' : Option U} (ho : o = none) (ho' : o' = some u) :
    BFEquiv (L := Lc) β 0 (Fin.elim0 : Fin 0 → Comp Bstar B o)
      (Fin.elim0 : Fin 0 → Comp Bstar B o') := by
  subst ho ho'
  exact h

omit [LinearOrder U] in
private theorem bfEquiv_comp_some_none {β : Ordinal.{u}} {u : U}
    (h : BFEquiv (L := Lc) β 0 (Fin.elim0 : Fin 0 → B u) (Fin.elim0 : Fin 0 → Bstar))
    {o o' : Option U} (ho : o = some u) (ho' : o' = none) :
    BFEquiv (L := Lc) β 0 (Fin.elim0 : Fin 0 → Comp Bstar B o)
      (Fin.elim0 : Fin 0 → Comp Bstar B o') := by
  subst ho ho'
  exact h

omit [LinearOrder U] in
/-- A nonempty label on the path is the prefix label of its predecessor length. -/
theorem isPathPrefix_eq_prefixLabel {τ : Label U} (h : IsPathPrefix π τ) :
    τ = prefixLabel π (τ.1.length - 1) := by
  apply Subtype.ext
  rw [prefixLabel_val, Nat.sub_add_cancel (List.length_pos_of_ne_nil τ.2)]
  exact h

/-! ### The equivalence -/

/-- **Companion equivalence at one level.**  Under allowedness and approximation from threshold
`N` at level `β`, the companion and the base are `β`-equivalent as empty tuples. -/
theorem companion_bfEquiv_of_pathApproxAt (hπ : IsAllowedPath A π) {β : Ordinal.{u}} {N : ℕ}
    (happ : PathApproxAt Lc Bstar B π β N) :
    BFEquiv (L := lang U Lc) β 0 (Fin.elim0 : Fin 0 → CompanionCarrier Bstar B A π)
      (Fin.elim0 : Fin 0 → PrefixCarrier Bstar B A) := by
  have hm : Matched (shiftRows hπ N) (Fin.elim0 : Fin 0 → CompanionCarrier Bstar B A π)
      (Fin.elim0 : Fin 0 → PrefixCarrier Bstar B A) := fun i => i.elim0
  refine bfEquiv_of_fiberBF β hm (fiberBF_of_no_points hm (fun i => i.elim0) ?_)
  rintro (r | _) τ
  · by_cases ht : IsTailPrefix hπ N r
    · -- a tail prefix `π|ₖ` against `π|ₖ₊₁`
      obtain ⟨k, hk, rfl⟩ := ht
      rw [shiftRows_inl_prefixRow hπ hk]
      show BFEquiv (L := Lc) β 0 (Fin.elim0 : Fin 0 → Comp Bstar B (compIndex (pathPrefix π k) τ))
        (Fin.elim0 : Fin 0 → Comp Bstar B (compIndex (pathPrefix π (k + 1)) τ))
      by_cases hτ : τ = prefixLabel π k
      · subst hτ
        exact bfEquiv_comp_none_some Bstar B (happ k hk) (compIndex_pathPrefix_prefixLabel π k)
          (compIndex_pathPrefix_succ_prefixLabel π k)
      · exact bfEquiv_comp_of_eq Bstar B (compIndex_pathPrefix_succ_of_ne hτ).symm
    · -- a non-tail row: the same row on both sides
      rw [shiftRows_inl_of_not hπ ht]
      exact BFEquiv.refl β _
  · -- the path row against `π|ₙ`
    rw [shiftRows_inr]
    show BFEquiv (L := Lc) β 0 (Fin.elim0 : Fin 0 → Comp Bstar B (pathIndex π τ))
      (Fin.elim0 : Fin 0 → Comp Bstar B (compIndex (pathPrefix π N) τ))
    by_cases hlen : τ.1.length ≤ N
    · exact bfEquiv_comp_of_eq Bstar B (compIndex_pathPrefix_of_le hlen).symm
    · push Not at hlen
      by_cases hp : IsPathPrefix π τ
      · obtain ⟨j, hj, rfl⟩ : ∃ j, N ≤ j ∧ τ = prefixLabel π j :=
          ⟨τ.1.length - 1, by omega, isPathPrefix_eq_prefixLabel hp⟩
        exact bfEquiv_comp_some_none Bstar B (happ j hj).symm (pathIndex_prefixLabel π j)
          (compIndex_pathPrefix_of_lt (by simp; omega))
      · exact bfEquiv_comp_of_eq Bstar B
          ((pathIndex_of_not_isPathPrefix hp).trans (compIndex_pathPrefix_of_lt hlen).symm)

/-- **Companion equivalence below `α`**, with the threshold chosen separately for each level. -/
theorem companion_bfEquiv (hπ : IsAllowedPath A π) {α : Ordinal.{u}}
    (happ : PathApprox Lc Bstar B π α) :
    ∀ β < α, BFEquiv (L := lang U Lc) β 0 (Fin.elim0 : Fin 0 → CompanionCarrier Bstar B A π)
      (Fin.elim0 : Fin 0 → PrefixCarrier Bstar B A) := by
  intro β hβ
  obtain ⟨N, hN⟩ := happ β hβ
  exact companion_bfEquiv_of_pathApproxAt Bstar B hπ hN

end FiberAssembly

end FirstOrder.Language
