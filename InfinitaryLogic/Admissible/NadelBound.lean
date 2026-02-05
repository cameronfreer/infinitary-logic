/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Admissible.Fragment
import InfinitaryLogic.Scott.Height

/-!
# Nadel Bound

This file states the Nadel bound on Scott height: for a structure coded in an
admissible set A, the Scott height is bounded by o(A) (the height of A).

## Main Results

- `nadel_bound`: The Scott height of a structure coded in an admissible fragment
  is bounded by the fragment's height.

## References

- [Keisler-Knight, "Barwise: Infinitary Logic and Admissible Sets", 2004], Theorem 4.3.2
- [Nadel, "Scott sentences and admissible sets", 1974]
-/

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable [Countable (Σ l, L.Relations l)]

open FirstOrder Structure Ordinal

/-- **Nadel Bound** (KK04 Theorem 4.3.2): The Scott height of a countable structure
coded in an admissible fragment A is bounded by o(A), the ordinal height of A.

The hypothesis `hM_coded` expresses (schematically) that M is coded in the
admissible set corresponding to A. The full statement would require formalizing
what it means for a structure to be an element of an admissible set, which in
turn requires significant set-theoretic infrastructure (HYP(M), etc.). -/
theorem nadel_bound (A : AdmissibleFragment L)
    (M : Type w) [L.Structure M] [Countable M]
    (hM_coded : True) :  -- schematic: "M is coded in A"
    scottHeight (L := L) M < A.height := by
  sorry

end Language

end FirstOrder
