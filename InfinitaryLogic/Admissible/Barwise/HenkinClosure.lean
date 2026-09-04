/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Admissible.Barwise.SourceFragment
import InfinitaryLogic.Lomega1omega.NegationClosure

/-!
# The Henkin closure of a set of formulas

The producer side of the source-fragment adapter (issue #19): a closure operator that turns any
set of formulas into a fragment with a `Fragment.HenkinBasis`, so that the v4.5.0 endpoint
`Fragment.exists_countable_model_of_aconsistent_withConstants` applies without supplying the
basis by hand.

```
henkinBasisSeed L   -- falsum, the equality template, every relation template
henkinClosure S     := negationClosure (S ∪ henkinBasisSeed L)
```

`Fragment.negationClosure` (generic, `Lomega1omega/NegationClosure.lean`) supplies component
and negation closure; the seed supplies the atoms.  Countability needs the relation-symbol
sigma countable in addition to `S`, because the seed contains one template per symbol.  The
exact HF regression `henkinClosure (hfFragment L).toSet = hfFragment L` fixes the operator on
the finitary fragment.

The construction is purely syntactic externally.  Admissibility enters only when internalizing
that construction and showing its codes remain inside the admissible language.  No fragment
structure gains a field.
-/

namespace FirstOrder.Language

variable {L : Language.{0, 0}}

namespace Fragment

/-! ## The seed -/

/-- **The Henkin basis seed**: falsum, the equality template at arity two, and the relation
template of every symbol at its arity. -/
def henkinBasisSeed (L : Language.{0, 0}) : Set (Σ n, L.BoundedFormulaω Empty n) :=
  {⟨0, BoundedFormulaω.falsum⟩, ⟨2, equalTemplate L⟩} ∪
    Set.range (fun R : Σ l, L.Relations l =>
      (⟨R.1, relTemplate R.2⟩ : Σ n, L.BoundedFormulaω Empty n))

theorem henkinBasisSeed_countable [Countable (Σ l, L.Relations l)] :
    (henkinBasisSeed L).Countable :=
  ((Set.countable_singleton _).insert _).union (Set.countable_range _)

/-- A fragment with a Henkin basis contains the seed. -/
theorem henkinBasisSeed_subset {A : Fragment L} (hB : A.HenkinBasis) :
    henkinBasisSeed L ⊆ A.toSet := by
  rintro p (hp | ⟨R, rfl⟩)
  · rcases hp with rfl | rfl
    · exact hB.falsum_mem
    · exact hB.equalTemplate_mem
  · exact hB.relTemplate_mem R.2

/-! ## The closure -/

/-- **The Henkin closure**: the negation closure of `S` together with the seed. -/
def henkinClosure (S : Set (Σ n, L.BoundedFormulaω Empty n)) : Fragment L :=
  negationClosure (S ∪ henkinBasisSeed L)

theorem subset_henkinClosure (S : Set (Σ n, L.BoundedFormulaω Empty n)) :
    S ⊆ (henkinClosure S).toSet :=
  Set.subset_union_left.trans (subset_negationClosure _)

theorem generated_le_henkinClosure (S : Set (Σ n, L.BoundedFormulaω Empty n)) :
    generated S ≤ henkinClosure S :=
  generated_le_iff.mpr (subset_henkinClosure S)

theorem negationClosed_henkinClosure (S : Set (Σ n, L.BoundedFormulaω Empty n)) :
    (henkinClosure S).NegationClosed :=
  negationClosed_negationClosure _

/-- **The closure has a Henkin basis.** -/
theorem henkinBasis_henkinClosure (S : Set (Σ n, L.BoundedFormulaω Empty n)) :
    (henkinClosure S).HenkinBasis where
  falsum_mem := subset_negationClosure _ (Set.mem_union_right _ (Or.inl (Or.inl rfl)))
  not_mem h := negationClosed_henkinClosure S h
  equalTemplate_mem := subset_negationClosure _ (Set.mem_union_right _ (Or.inl (Or.inr rfl)))
  relTemplate_mem R := subset_negationClosure _ (Set.mem_union_right _ (Or.inr ⟨⟨_, R⟩, rfl⟩))

/-- The Henkin closure is below every fragment with a basis containing `S`. -/
theorem henkinClosure_le {S : Set (Σ n, L.BoundedFormulaω Empty n)} {A : Fragment L}
    (hSA : S ⊆ A.toSet) (hB : A.HenkinBasis) : (henkinClosure S).toSet ⊆ A.toSet :=
  negationClosure_le (Set.union_subset hSA (henkinBasisSeed_subset hB)) fun h => hB.not_mem h

/-- A fragment with a basis is its own Henkin closure. -/
theorem henkinClosure_toSet_eq {A : Fragment L} (hB : A.HenkinBasis) :
    henkinClosure A.toSet = A :=
  ext fun _ => ⟨fun h => henkinClosure_le subset_rfl hB h, fun h => subset_henkinClosure _ h⟩

/-- **Countability**: the seed contributes one template per relation symbol. -/
theorem henkinClosure_countable [Countable (Σ l, L.Relations l)]
    {S : Set (Σ n, L.BoundedFormulaω Empty n)} (hS : S.Countable) :
    (henkinClosure S).toSet.Countable :=
  negationClosure_countable (hS.union henkinBasisSeed_countable)

/-- **The HF regression, exact**: the finitary fragment is its own Henkin closure. -/
theorem henkinClosure_hfFragment : henkinClosure (hfFragment L).toSet = hfFragment L :=
  henkinClosure_toSet_eq henkinBasis_hfFragment

/-! ## The endpoint with the basis discharged -/

/-- The constants-expanded universe of a Henkin closure is Henkin-closed. -/
theorem henkinClosed_withNatConstantsSentences_henkinClosure
    (S : Set (Σ n, L.BoundedFormulaω Empty n)) :
    HenkinClosed (henkinClosure S).withNatConstantsSentences :=
  henkinClosed_withNatConstantsSentences (henkinBasis_henkinClosure S)

/-- **Countable model existence over the Henkin closure of a countable set.**  The v4.5.0
source-fragment endpoint with the basis discharged by the closure; the consistency hypothesis is
in the constants-expanded universe of the closure, as before. -/
theorem exists_countable_model_of_aconsistent_henkinClosure [L.IsRelational]
    [Countable (Σ l, L.Relations l)] {S : Set (Σ n, L.BoundedFormulaω Empty n)}
    (hS : S.Countable) {T : L.Theoryω} (hT : T ⊆ (henkinClosure S).sentenceSlice)
    (hcons : AConsistent (henkinClosure S).withNatConstantsSentences
      (BoundedFormulaω.mapLanguage (L.lhomWithConstants ℕ) '' T)) :
    ∃ (M : Type) (_ : L.Structure M) (_ : Nonempty M) (_ : Countable M), Theoryω.Model T M :=
  exists_countable_model_of_aconsistent_withConstants (henkinClosure_countable hS)
    (henkinBasis_henkinClosure S) hT hcons

end Fragment

end FirstOrder.Language
