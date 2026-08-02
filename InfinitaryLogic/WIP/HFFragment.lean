/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Lomega1omega.FirstOrderImage
import InfinitaryLogic.Lomega1omega.Fragment

/-!
# The HF fragment as an ordinary `Fragment` (issue #18, step 1)

Architecture-independent: this file mentions no admissible-set interface at all.  It builds the
all-arity `toLω`-image as a `Fragment` and proves its sentence slice is exactly the spike's
`finitaryFragment`.

That makes the downward-closure argument **executable** rather than asserted, and gives every later
interface proposal a compiler-enforced oracle: whatever `AdmissibleFragment` turns out to be, its HF
instance must have *this* underlying `Fragment`.

## The load-bearing observation

Every closure field of `Fragment` is **downward** — "a component of a member is a member" — never
upward.  So the infinitary fields hold **vacuously** here: `toLω` emits no `iInf`/`iSup`
constructor, so no member is one.

By contrast `AdmissibleFragmentCore.closed_iInf` is *upward* over arbitrary external ℕ-families, and
HF cannot satisfy it: a constant family of members has a genuine `iInf` node as its conjunction, and
that node is outside the image.  Unsatisfiable, not merely inconvenient.
-/

namespace FirstOrder.Language

universe u v

variable {L : Language.{u, v}}

/-- The all-arity first-order image: every formula containing no infinitary node. -/
def hfSet (L : Language.{u, v}) : Set (Σ n, L.BoundedFormulaω Empty n) :=
  {p | p.2.IsFirstOrder}

@[simp] theorem mem_hfSet_iff {n : ℕ} {φ : L.BoundedFormulaω Empty n} :
    (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ hfSet L ↔ φ.IsFirstOrder := Iff.rfl

/-- **The HF fragment.**  Each field is now one appeal to the first-order-image API: three
structural equations and the two negative facts.  Compare the five hand-rolled constructor
inversions this replaces. -/
def hfFragment (L : Language.{u, v}) : Fragment L where
  toSet := hfSet L
  imp_left_mem h := (BoundedFormulaω.isFirstOrder_imp_iff.mp h).1
  imp_right_mem h := (BoundedFormulaω.isFirstOrder_imp_iff.mp h).2
  all_mem h := BoundedFormulaω.isFirstOrder_all_iff.mp h
  iInf_mem h := absurd h (BoundedFormulaω.not_isFirstOrder_iInf _)
  iSup_mem h := absurd h (BoundedFormulaω.not_isFirstOrder_iSup _)

end FirstOrder.Language
