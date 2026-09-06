/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.AnalyticWellOrderBoundedness
import InfinitaryLogic.Descriptive.TreeCodes
import InfinitaryLogic.Descriptive.StructureIsoSetoid

/-!
# Thinness of the coded well-orders in the pure one-strict-order language

In `kbLanguage`, whose only symbol is the binary `kbRelSym.lt`, the coded well-order class is thin
for isomorphism (`kbLanguage.wellOrderClass_isThinOn`): no perfect set of pairwise non-isomorphic
coded well-orders.  The route is the existing analytic boundedness theorem, not any counting of
types:

1. a continuous Cantor antichain in the class has compact, hence analytic, range inside the class;
2. `analytic_wellOrder_type_boundedness` bounds its order types below one countable ordinal `β`;
3. in the pure language, equal order types give order isomorphisms (`Ordinal.type_eq`), which are
   structure isomorphisms (`equivOfRelIso`, the converse of `relIsoOfEquiv`);
4. the antichain would therefore inject Cantor space into the countable set of ordinals below
   `β` (`countable_Iio_of_lt_omega1`), which is impossible.

## Why the language is restricted

For an arbitrary relational `L`, `wellOrderClass lt` constrains only the distinguished relation.
With one extra unary predicate `U`, keep the usual order on `ℕ` and let `U` vary over Cantor
space: the order is rigid, so distinct colourings are non-isomorphic, and the codes depend
continuously on the colouring, giving a continuous Cantor antichain inside `wellOrderClass lt`.
So thinness of `wellOrderClass lt` is **false** in general, and the theorem below is stated for the
pure language only; the general definition of `wellOrderClass` is unchanged.

Nothing here uses the sentence-spectrum or fragment-spectrum characterizations, and no
determining cover appears: this consumer validates the boundedness handoff, not the counting
machinery.
-/

namespace FirstOrder.Language

open MeasureTheory

namespace kbLanguage

/-- The distinguished relation of a `kbLanguage` code, as a binary relation on `ℕ`. -/
abbrev codeRel (c : StructureSpace kbLanguage) (x y : ℕ) : Prop :=
  @Structure.RelMap kbLanguage ℕ c.toStructure 2 kbRelSym.lt ![x, y]

/-- In the pure language, an order isomorphism of the distinguished relations is a structure
isomorphism: the converse of `relIsoOfEquiv`. -/
def equivOfRelIso {c d : StructureSpace kbLanguage} (e : codeRel c ≃r codeRel d) :
    @Language.Equiv kbLanguage ℕ ℕ c.toStructure d.toStructure :=
  @Language.Equiv.mk kbLanguage ℕ ℕ c.toStructure d.toStructure e.toEquiv
    (fun {n} f => (kbLanguage.instIsRelational n).elim f)
    (fun {n} R v => by
      cases R
      obtain ⟨x, y, rfl⟩ : ∃ x y, v = ![x, y] :=
        ⟨v 0, v 1, funext fun i => by fin_cases i <;> rfl⟩
      have he : (e.toFun ∘ ![x, y]) = ![e x, e y] := funext fun i => by fin_cases i <;> rfl
      exact (iff_of_eq (congrArg
        (@Structure.RelMap kbLanguage ℕ d.toStructure 2 kbRelSym.lt) he)).trans e.map_rel_iff)

/-- Cantor space is uncountable. -/
private theorem not_countable_cantor : ¬ Countable (ℕ → Bool) := by
  intro h
  obtain ⟨g, hg⟩ := exists_surjective_nat (ℕ → Bool)
  obtain ⟨n, hn⟩ := hg fun k => !(g k k)
  have he := congrFun hn n
  simp at he

/-- **Coded well-orders in the pure language carry no Cantor isomorphism antichain.** -/
theorem not_hasCantorAntichainOn_wellOrderClass :
    ¬ HasCantorAntichainOn (structureIsoSetoid kbLanguage) (wellOrderClass kbRelSym.lt) := by
  rintro ⟨f, hcont, hmem, hineq⟩
  -- the range is compact, hence analytic, and lies in the class
  have hA : AnalyticSet (Set.range f) := (isCompact_range hcont).isClosed.measurableSet.analyticSet
  obtain ⟨β, hβ, hbound⟩ := analytic_wellOrder_type_boundedness kbRelSym.lt hA
    (Set.range_subset_iff.mpr hmem)
  have hβ' : β < Ordinal.omega 1 := by rwa [Cardinal.ord_aleph] at hβ
  -- the order type of each member of the antichain, as a point of `Iio β`
  let wo : ∀ x, IsWellOrder ℕ (codeRel (f x)) := fun x => hmem x
  let g : (ℕ → Bool) → Set.Iio β := fun x =>
    ⟨@Ordinal.type ℕ (codeRel (f x)) (wo x), hbound (f x) ⟨x, rfl⟩ (wo x)⟩
  have hg : Function.Injective g := by
    intro x y hxy
    by_contra hne
    have htype : @Ordinal.type ℕ (codeRel (f x)) (wo x) = @Ordinal.type ℕ (codeRel (f y)) (wo y) :=
      congrArg Subtype.val hxy
    obtain ⟨e⟩ := (@Ordinal.type_eq ℕ ℕ _ _ (wo x) (wo y)).mp htype
    exact hineq x y hne ⟨equivOfRelIso e⟩
  have : Countable (Set.Iio β) := InfinitaryLogic.countable_Iio_of_lt_omega1 β hβ'
  exact not_countable_cantor hg.countable

/-- **Thinness of the coded well-orders in the pure one-strict-order language.** -/
theorem wellOrderClass_isThinOn :
    IsThinOn (structureIsoSetoid kbLanguage) (wellOrderClass kbRelSym.lt) := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable (StructureSpace kbLanguage)
  exact IsThinOn.of_no_cantorAntichain not_hasCantorAntichainOn_wellOrderClass

end kbLanguage

end FirstOrder.Language
