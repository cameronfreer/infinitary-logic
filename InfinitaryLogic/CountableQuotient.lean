/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Set.Countable
import Mathlib.Data.Setoid.Basic

/-!
# Countable quotients from countable-range refinements

One lemma, kept away from any model-theoretic or back-and-forth machinery: a quotient is
countable when some map with countable range refines the relation.  Consumers are the
successor-level back-and-forth counting and the fragment-spectrum classification corollaries.
-/

namespace FirstOrder.Language

/-- A quotient is countable when a map with countable range refines the relation: fibres of the
map lie inside classes.  The proof chooses one preimage for each value in the range (classical
choice; not a Borel selector and not a choice of canonical structures). -/
theorem countable_quotient_of_countable_range {X T : Type*} (s : Setoid X) (t : X → T)
    (hrange : (Set.range t).Countable) (h : ∀ x y, t x = t y → s.r x y) :
    Countable (Quotient s) := by
  classical
  have : Countable (Set.range t) := hrange.to_subtype
  refine Function.Surjective.countable (f := fun v : Set.range t => Quotient.mk s v.2.choose) ?_
  intro q
  induction q using Quotient.inductionOn with | _ x =>
  refine ⟨⟨t x, x, rfl⟩, Quotient.sound (h _ _ ?_)⟩
  exact (⟨x, rfl⟩ : t x ∈ Set.range t).choose_spec

end FirstOrder.Language
