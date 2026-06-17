/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Methods.SkolemClosure

/-!
# Ehrenfeucht–Mostowski term model (M-deep-interpretation), step 1: skeleton support

The bespoke EM term model realizes the tail-template theory over `(skolemColim L)[[J]]` without
full compactness. Its carrier is the closed terms quotiented by **deep equality in the source model
`M`**: two closed terms are identified when, interpreting their finitely-many `J`-constants as a
strictly-increasing *deep* tuple of the tail-indiscernible sequence, they evaluate equally in `M`
(eventually, as the depth grows). Congruence is then inherited from `M` being a genuine structure.

This file builds the first ingredient: the finite set of `J`-constants ("skeleton constants")
mentioned in a closed term, which the deep interpretation enumerates in increasing `J`-order.
-/

namespace FirstOrder.Language

variable (L : Language.{0, 0}) (J : Type) [LinearOrder J]

/-- The `J`-constant carried by a function symbol of `(skolemColim L)[[J]]`: only an arity-`0`
symbol from the `constantsOn J` summand is a skeleton constant. -/
def jConstOf : {n : ℕ} → (skolemColim L)[[J]].Functions n → Finset J
  | 0, Sum.inr j => {j}
  | _, _ => ∅

/-- The finite set of `J`-constants (skeleton constants) mentioned in a term of
`(skolemColim L)[[J]]`. The deep interpretation enumerates this support in increasing `J`-order. -/
def jSupport {α : Type} : (skolemColim L)[[J]].Term α → Finset J
  | .var _ => ∅
  | .func f ts => (Finset.univ.biUnion fun i => jSupport (ts i)) ∪ jConstOf L J f

end FirstOrder.Language
