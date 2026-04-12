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

- [KK04], Theorem 4.3.2
- [Nad74]
-/

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable [Countable (Σ l, L.Relations l)]

open FirstOrder Structure Ordinal

/-- Predicate expressing that a structure M is coded in an admissible fragment A.

Informally, this means that M (as a set-theoretic object) is an element of the
admissible set corresponding to A. The full formalization would require
set-theoretic infrastructure (KP set theory, HYP(M), etc.).

This is a typeclass so that instances can be provided for specific admissible sets
(e.g., `HYP(M)` for countable structures). The real mathematical content lives in
constructing instances; the `scottHeight_lt_height` field captures the conclusion
of Nadel's theorem as the interface. -/
class AdmissibleFragment.CodedIn (A : AdmissibleFragment L)
    (M : Type w) [L.Structure M] [Countable M] : Prop where
  scottHeight_lt_height : scottHeight (L := L) M < A.height

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- **Nadel Bound** (KK04 Theorem 4.3.2): The Scott height of a countable structure
coded in an admissible fragment A is bounded by o(A), the ordinal height of A.

The coding hypothesis `CodedIn` is a typeclass whose instances encode the
set-theoretic relationship between M and A. The real proof work is in constructing
such instances (requiring KP set theory, HYP(M), etc.). -/
theorem nadel_bound (A : AdmissibleFragment L)
    (M : Type w) [L.Structure M] [Countable M]
    [hM : A.CodedIn M] :
    scottHeight (L := L) M < A.height :=
  hM.scottHeight_lt_height

end Language

end FirstOrder
