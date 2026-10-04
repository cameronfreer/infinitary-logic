/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Scott.RefinementCount

/-!
# An isolating level for a countable family of countable structures

An *isolating level* for a family of structures is an ordinal `γ` such that `BFEquiv0` at `γ`
between two members of the family implies that they are isomorphic.  (This is unrelated to the
isolating formula of a type, `isolatingFormula`.)

Let `L` be a countable relational language and `M : ι → Type w` a family of countable
`L`-structures indexed by a countable type `ι`.  There is one countable ordinal `γ < ω₁` at which
back-and-forth equivalence on the empty tuple already decides isomorphism between any two members
of the family (`exists_isolating_level`):

```
∃ γ < ω₁, ∀ i j, BFEquiv0 (M i) (M j) γ → Nonempty (M i ≃[L] M j).
```

The converse implication holds at every level: isomorphic structures are back-and-forth
equivalent at all levels (`equiv_implies_BFEquiv`, reduced to the empty tuple by
`comp_fin_elim0`).  So at `γ` the relation `BFEquiv0 · · γ` *is* isomorphism on the family
(`exists_isolating_level_iff`).  Contrapositively, a family in which every countable level
leaves some non-isomorphic pair back-and-forth equivalent is indexed by an uncountable type
(`not_countable_of_forall_unisolated`).

## Main declarations

* `exists_isolating_level`: a countable isolating level for a countable family.
* `exists_isolating_level_iff`: the same level, with `BFEquiv0` at it equivalent to isomorphism.
* `not_countable_of_forall_unisolated`: if every level below `ω₁` has an unisolated pair, the
  index type is not countable.

## Proof

The level is the supremum `⨆ i, stabilizationOrdinal (M i)`.  Each stabilization ordinal is
countable (`stabilizationOrdinal_lt_omega1'`), so the supremum of countably many of them is
below `ω₁` (Mathlib's `Ordinal.iSup_lt_omega_one`).  At the stabilization ordinal of `M i`,
`BFEquiv0` against any countable `N` in the same carrier universe is isomorphism
(`stabilizationOrdinal_spec`), and `BFEquiv0` is monotone in the level, so `BFEquiv0` at the
supremum gives `BFEquiv0` at `stabilizationOrdinal (M i)` and hence an isomorphism.

## A countable family of representatives, not a countable set of codes

The theorem counts *representatives*: `ι` indexes chosen structures, one per index.  This is not
the same as a countable set of codes.  A single isomorphism class of countable structures can be
presented by uncountably many codes, so a set of codes meeting only countably many classes can
itself be uncountable; the family form applies to it only after choosing one representative per
class.  The code form, a level isolating the classes of a set of codes, is not stated here; it
belongs with an isolating-rank contract on codes.

## Non-claims

* **No Scott-rank convention.**  The level is not identified with the Scott rank of any member
  or of the family under any convention; it is only a level at which `BFEquiv0` decides
  isomorphism on the family.
* **Not the least isolating level.**  The supremum of the stabilization ordinals is *some*
  isolating level; nothing is said about the least one.
* **Nothing for uncountable families.**  For an uncountable index type no countable isolating
  level is claimed; the only statement made there is the contrapositive above.
* **Within one universe.**  A family `ι → Type w` lives in one universe by construction.  The
  level is only claimed to decide isomorphism between members of the family:
  `stabilizationOrdinal_spec` compares `M i` only with structures in `Type w` (`BFEquiv0` itself
  is universe-heterogeneous, but `StabilizesAt` quantifies over the same universe), so nothing is
  said about comparing a member with a structure in another universe, such as `ULift (M i)`.
* **Language hypotheses inherited.**  `[L.IsRelational]` and `[Countable (Σ l, L.Relations l)]`
  are the hypotheses of `stabilizationOrdinal_lt_omega1'` and `stabilizationOrdinal_spec`, and
  both are used; that they are necessary for the family statement is not claimed.
-/

universe u v w

namespace FirstOrder.Language

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

/-- **A countable isolating level for a countable family.**  Over a countable relational
language, for a countable family `M : ι → Type w` of countable structures, some level `γ < ω₁`
has the property that `BFEquiv0` at `γ` between two members yields an isomorphism.  The level
produced is the supremum of the members' stabilization ordinals; it need not be the least such
level. -/
theorem exists_isolating_level {ι : Type*} [Countable ι] (M : ι → Type w)
    [∀ i, L.Structure (M i)] [∀ i, Countable (M i)] :
    ∃ γ : Ordinal.{0}, γ < Ordinal.omega 1 ∧
      ∀ i j, BFEquiv0 (L := L) (M i) (M j) γ → Nonempty (M i ≃[L] M j) :=
  ⟨⨆ i, stabilizationOrdinal (L := L) (M i),
    Ordinal.iSup_lt_omega_one fun i ↦ stabilizationOrdinal_lt_omega1' (M i), fun i j h ↦
    (stabilizationOrdinal_spec (M i) (M j)).mp
      (BFEquiv.monotone (Ordinal.le_iSup (fun i ↦ stabilizationOrdinal (L := L) (M i)) i) h)⟩

/-- **The isolating level, both directions.**  At the level of `exists_isolating_level`,
`BFEquiv0` between two members is equivalent to isomorphism; the converse direction holds at
every level (`equiv_implies_BFEquiv`). -/
theorem exists_isolating_level_iff {ι : Type*} [Countable ι] (M : ι → Type w)
    [∀ i, L.Structure (M i)] [∀ i, Countable (M i)] :
    ∃ γ : Ordinal.{0}, γ < Ordinal.omega 1 ∧
      ∀ i j, BFEquiv0 (L := L) (M i) (M j) γ ↔ Nonempty (M i ≃[L] M j) := by
  obtain ⟨γ, hγ, h⟩ := exists_isolating_level (L := L) M
  refine ⟨γ, hγ, fun i j ↦ ⟨h i j, fun ⟨e⟩ ↦ ?_⟩⟩
  simpa only [comp_fin_elim0] using equiv_implies_BFEquiv e γ 0 Fin.elim0

/-- **Unisolated at every countable level forces an uncountable index.**  If for every level
`γ < ω₁` some two members of the family are `BFEquiv0` at `γ` but not isomorphic, then the index
type is not countable.  This is the contrapositive of `exists_isolating_level`. -/
theorem not_countable_of_forall_unisolated {ι : Type*} (M : ι → Type w)
    [∀ i, L.Structure (M i)] [∀ i, Countable (M i)]
    (h : ∀ γ : Ordinal.{0}, γ < Ordinal.omega 1 →
      ∃ i j, BFEquiv0 (L := L) (M i) (M j) γ ∧ IsEmpty (M i ≃[L] M j)) :
    ¬ Countable ι := by
  intro hι
  obtain ⟨γ, hγ, hiso⟩ := exists_isolating_level (L := L) M
  obtain ⟨i, j, hbf, hne⟩ := h γ hγ
  exact hne.false (hiso i j hbf).some

end FirstOrder.Language
