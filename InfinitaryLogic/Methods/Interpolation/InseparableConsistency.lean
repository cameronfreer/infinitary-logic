/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Methods.Interpolation.InseparablePairFamily
import InfinitaryLogic.Methods.Interpolation.FairEnumeration

/-!
# The inseparable-pair consistency property and its Henkin completion (issue #8, commit 4b)

**Status: the correct one-sided predecessor, superseded for Craig assembly.** The Craig
endpoint is assembled from the *paired* construction (`PairedInsepFamily.lean`:
`pairedInsepConsistencyProperty` / `exists_paired_model`), which tracks both coordinates of the
inseparable pair through the completion. This file's single-root completion
(`exists_henkinComplete_of_root`) remains the mathematically correct one-sided statement and is
kept (WIP target only) as the simpler reference form of the argument.

Packaging step: the family-closure lemmas of `InseparablePairFamily.lean` are exactly the fields of
a `ConsistencyPropertyEqOn (GenU r₁ r₂)`, so the finite inseparable-pair family *is* a consistency
property over the generated universe. Feeding it (and the root inseparable pair `{r₁}`) to the fair
enumeration `exists_henkinComplete` yields a Henkin-complete `S* ⊇ {r₁}` inside `GenU r₁ r₂`.

* `insepConsistencyProperty`: the `ConsistencyPropertyEqOn` bundle. Its fields are the
  `insepFamily_*` closures, each converted from `insert _ S` to the field's `S ∪ {_}` shape by
  `Set.union_singleton`.
* `exists_henkinComplete_of_root`: from a root inseparability hypothesis `InsepAt F R A₀ {r₁} Δ`
  (over a countable relational vocabulary), a Henkin-complete `S*`.

Deliberately **no term model here** — building a structure from `S*` and the forward
polarity-sensitive truth lemma is commit 5. The `neg_all_witness` field consumes the roots'/`Δ`'s
finite-support hypotheses; the relation-symbol countability enters only at the Henkin endpoint (it
is what makes `GenU r₁ r₂` and the request type countable).
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}}

/-- **The inseparable-pair consistency property.** The finite inseparable-pair family over the
generated universe `GenU r₁ r₂`, with the `ConsistencyPropertyEqOn` closure fields discharged by the
`insepFamily_*` structural lemmas. The `neg_all_witness` field needs the roots' and `Δ`'s constant
support to be finite (to choose a fresh witness). -/
def insepConsistencyProperty (F : Set (Σ n, L.Functions n)) (R : Set (Σ n, L.Relations n))
    (Δ : Set L[[ℕ]].Sentenceω) (r₁ r₂ : L[[ℕ]].Sentenceω)
    (hr₁ : (sentenceJConsts (L' := L) (J := ℕ) r₁).Finite)
    (hr₂ : (sentenceJConsts (L' := L) (J := ℕ) r₂).Finite)
    (hΔfin : (⋃ δ ∈ Δ, sentenceJConsts (L' := L) (J := ℕ) δ).Finite) :
    ConsistencyPropertyEqOn (GenU r₁ r₂) where
  sets := {Γ | InsepFamilyMem F R Δ r₁ r₂ Γ}
  subset_U := fun _ hS => hS.subset_genU
  C0_no_falsum := fun _ hS => insepFamily_no_falsum hS
  C0_no_contradiction := fun _ hS => insepFamily_no_contradiction hS
  C1_imp := fun _ hS φ ψ hmem => by
    rcases insepFamily_imp hmem hS with h | h
    · exact Or.inl (by rw [Set.union_singleton]; exact h)
    · exact Or.inr (by rw [Set.union_singleton]; exact h)
  C1_neg_imp := fun _ hS φ ψ hmem => by
    obtain ⟨ha, hb⟩ := insepFamily_neg_imp hmem hS
    exact ⟨by rw [Set.union_singleton]; exact ha, by rw [Set.union_singleton]; exact hb⟩
  C2_not_not := fun _ hS φ hmem => by rw [Set.union_singleton]; exact insepFamily_not_not hmem hS
  C3_iInf := fun _ hS φs hmem k => by rw [Set.union_singleton]; exact insepFamily_iInf hmem hS k
  C3_neg_iInf := fun _ hS φs hmem => by
    obtain ⟨k, hk⟩ := insepFamily_neg_iInf hmem hS
    exact ⟨k, by rw [Set.union_singleton]; exact hk⟩
  C4_iSup := fun _ hS φs hmem => by
    obtain ⟨k, hk⟩ := insepFamily_iSup hmem hS
    exact ⟨k, by rw [Set.union_singleton]; exact hk⟩
  C4_neg_iSup := fun _ hS φs hmem k => by
    rw [Set.union_singleton]; exact insepFamily_neg_iSup hmem hS k
  eq_refl := fun _ hS c => by rw [Set.union_singleton]; exact insepFamily_eq_refl hS c
  eq_symm := fun _ hS a b hmem => by rw [Set.union_singleton]; exact insepFamily_eq_symm hmem hS
  eq_trans := fun _ hS a b d h1 h2 => by
    rw [Set.union_singleton]; exact insepFamily_eq_trans h1 h2 hS
  rel_congr := fun _ hS l Rr g i b h1 h2 => by
    rw [Set.union_singleton]; exact insepFamily_rel_congr Rr g i b h1 h2 hS
  all_inst := fun _ hS φ hmem c => by rw [Set.union_singleton]; exact insepFamily_all_inst hmem hS c
  neg_all_witness := fun _ hS φ hmem => by
    obtain ⟨c, hc⟩ := insepFamily_neg_all_witness hr₁ hr₂ hΔfin hS hmem
    exact ⟨c, by rw [Set.union_singleton]; exact hc⟩

/-- **The Henkin completion of the root inseparable pair.** Over a countable relational vocabulary,
if the root `{r₁}` is inseparable from `Δ` (at some finite support `A₀`) and the roots' and `Δ`'s
constant supports are finite, the fair enumeration produces a Henkin-complete `S* ⊇ {r₁}` inside
`GenU r₁ r₂`. -/
theorem exists_henkinComplete_of_root [Countable (Σ l, L.Relations l)]
    (F : Set (Σ n, L.Functions n)) (R : Set (Σ n, L.Relations n))
    (Δ : Set L[[ℕ]].Sentenceω) (r₁ r₂ : L[[ℕ]].Sentenceω)
    (hr₁ : (sentenceJConsts (L' := L) (J := ℕ) r₁).Finite)
    (hr₂ : (sentenceJConsts (L' := L) (J := ℕ) r₂).Finite)
    (hΔfin : (⋃ δ ∈ Δ, sentenceJConsts (L' := L) (J := ℕ) δ).Finite)
    (A₀ : Finset ℕ) (hroot : InsepAt F R A₀ {r₁} Δ) :
    ∃ Sstar : Set L[[ℕ]].Sentenceω,
      {r₁} ⊆ Sstar ∧ Sstar ⊆ GenU r₁ r₂ ∧ HenkinComplete (GenU r₁ r₂) Sstar := by
  haveI : Countable ↥(GenU (L := L) r₁ r₂) := genU_countable.to_subtype
  have hmem : InsepFamilyMem F R Δ r₁ r₂ {r₁} :=
    ⟨Set.finite_singleton _, Set.singleton_subset_iff.mpr root₁_mem, A₀, hroot⟩
  exact exists_henkinComplete
    (P := insepConsistencyProperty F R Δ r₁ r₂ hr₁ hr₂ hΔfin) ⟨{r₁}, hmem⟩

end FirstOrder.Language
