/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.FiberOrbitBound
import InfinitaryLogic.ModelTheory.FiberTwoRow

/-!
# The exact internal Scott rank, conditionally

The upper bound `internalScottRank_le_of_bounds` combined with the two-row lower bound of
`FiberTwoRow`.

* `CofinalApprox`: below every level `β < α` some **nonempty allowed row** ends in a letter whose
  component is `β`-equivalent to the default (empty tuples) but not isomorphic to it.  The row
  is part of the hypothesis: nesting alone does not produce an allowed row ending in a given
  allowed letter.  This is consistent with (H_sep): separation levels bound only positions up to
  `N`, so the approximating rows end at positions growing with `β`.
* `le_internalScottRank_of_cofinalApprox`: under nesting and cofinal approximation, the internal
  Scott rank is at least `α`.  The two-row pair `row p`, `row (concatRow p)` is `β`-equivalent
  (`twoRow_bfEquiv`) but not automorphic (`twoRow_not_automorphic`).  The lower bound goes
  through the orbit-rank automorphism criterion on the **assembled** structure, so the carrier
  must be countable: `[Countable U]` is assumed in addition to component countability, and rows
  and carrier are then countable by the existing instances.  The upper bound alone does not need
  this.
* `internalScottRank_eq_of_bounds`: `le_antisymm` of the upper and lower bounds.

The result is conditional on all the listed hypotheses; no concrete exact-rank instance is
supplied here.
-/

namespace FirstOrder.Language

namespace FiberAssembly

universe u v w

variable {U : Type u} [LinearOrder U] {Lc : Language.{v, w}} {Bstar : Type u} {B : U → Type u}
  [Lc.Structure Bstar] [∀ u, Lc.Structure (B u)] {A : ℕ → Set U}

/-- **Cofinal approximation by allowed rows.**  Below every level `β < α` some nonempty allowed
row ends in a letter whose component is `β`-equivalent to the default (empty tuples) but not
isomorphic to it. -/
def CofinalApprox (Lc : Language.{v, w}) (Bstar : Type u) (B : U → Type u) [Lc.Structure Bstar]
    [∀ u, Lc.Structure (B u)] (A : ℕ → Set U) (α : Ordinal.{u}) : Prop :=
  ∀ β < α, ∃ (p : Row A) (hne : p.1 ≠ []),
    BFEquiv (L := Lc) β 0 (Fin.elim0 : Fin 0 → Bstar)
      (Fin.elim0 : Fin 0 → B (p.1.getLast hne)) ∧
    IsEmpty (Bstar ≃[Lc] B (p.1.getLast hne))

/-- **Lower bound.**  Under nesting and cofinal approximation, in the (countable) assembled
structure the internal Scott rank is at least `α`. -/
theorem le_internalScottRank_of_cofinalApprox [Lc.IsRelational] [Countable U] [Countable Bstar]
    [∀ u, Countable (B u)] (hA : Nested A) (α : Ordinal.{u})
    (hcof : CofinalApprox Lc Bstar B A α) :
    α ≤ internalScottRank (L := lang U Lc) (PrefixCarrier Bstar B A) := by
  refine le_internalScottRank_of_not_automorphic fun β hβ => ?_
  obtain ⟨p, hne, hbf, hniso⟩ := hcof β hβ
  refine ⟨1, ![Carrier.row p], ![Carrier.row (concatRow hA p hne)],
    twoRow_bfEquiv hA p hne β hbf, ?_⟩
  rintro ⟨g, hg⟩
  exact twoRow_not_automorphic hA p hne hniso ⟨g, congrFun hg 0⟩

/-- **Exact internal Scott rank**, conditionally: the upper bound of `FiberOrbitBound` and the
lower bound above. -/
theorem internalScottRank_eq_of_bounds [Lc.IsRelational] [Countable U] [Countable Bstar]
    [∀ u, Countable (B u)] (hA : Nested A) (α : Ordinal.{u})
    (hsep : SepBounded Lc Bstar B A α) (hup : UpwardClosed (DefaultLike Lc Bstar B))
    (horb : OrbitBounded Lc Bstar B A α) (hα : AddNatClosed α)
    (hcof : CofinalApprox Lc Bstar B A α) :
    internalScottRank (L := lang U Lc) (PrefixCarrier Bstar B A) = α :=
  le_antisymm (internalScottRank_le_of_bounds α hsep hup horb hα)
    (le_internalScottRank_of_cofinalApprox hA α hcof)

end FiberAssembly

end FirstOrder.Language
