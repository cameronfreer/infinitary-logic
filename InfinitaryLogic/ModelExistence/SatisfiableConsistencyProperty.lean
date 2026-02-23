/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelExistence.HenkinConstruction
import InfinitaryLogic.Lomega1omega.Operations

/-!
# Consistency Property from a Model

This file constructs a `ConsistencyPropertyEq` from a model M equipped with a naming
function. The consistency property is: S is consistent iff every sentence in S is true in M.

The naming function `ι : M → L.Term Empty` assigns a closed term to each element,
with the soundness condition that each term evaluates to the element it names.

## Main Results

- `NamingFunction`: A function mapping elements to closed terms that evaluate to them.
- `trueInModelConsistencyPropertyEq`: The sets of sentences true in M form a
  `ConsistencyPropertyEq`, enabling the model existence theorem to produce a
  countable model satisfying the same sentences.

## Application

This is used in the proof of the downward Löwenheim-Skolem theorem: given a model M
of a sentence φ, we construct a consistency property where {φ} is consistent (true in M),
then apply model existence to get a countable model of φ.

## References

- [Marker, "Lectures on Infinitary Model Theory", 2016], §4.1
-/

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

open FirstOrder Structure BoundedFormulaω

/-- A naming function maps each element of M to a closed term that evaluates to it. -/
structure NamingFunction (L : Language.{u, v}) (M : Type w) [L.Structure M] where
  /-- The function assigning a closed term to each element. -/
  name : M → L.Term Empty
  /-- The soundness condition: each term evaluates to the element it names. -/
  sound : ∀ m : M, (name m).realize (Empty.elim : Empty → M) = m

variable {M : Type w} [L.Structure M]

/-- The set of sentences true in M. -/
def trueInModel (M : Type w) [L.Structure M] : Set L.Sentenceω :=
  { σ | Sentenceω.Realize σ M }

/-- The family of sets of sentences where every element is true in M. -/
def trueInModelFamily (M : Type w) [L.Structure M] : Set (Set L.Sentenceω) :=
  { S | S ⊆ trueInModel M }

private theorem union_subset_trueInModel {S : Set L.Sentenceω} {σ : L.Sentenceω}
    (hS : S ⊆ trueInModel M) (hσ : Sentenceω.Realize σ M) :
    S ∪ {σ} ⊆ trueInModel M := by
  intro τ hτ
  cases hτ with
  | inl h => exact hS h
  | inr h => rw [Set.mem_singleton_iff.mp h]; exact hσ

/-- The family of true-in-M sets forms a `ConsistencyProperty`. -/
def trueInModelConsistencyProperty (M : Type w) [L.Structure M] :
    ConsistencyProperty L where
  sets := trueInModelFamily M
  C0_no_falsum := fun S hS hf => hS hf
  C0_no_contradiction := by
    intro S hS φ ⟨hφ, hφn⟩
    have h1 : Sentenceω.Realize φ M := hS hφ
    have h2 : Sentenceω.Realize φ.not M := hS hφn
    simp only [Sentenceω.Realize, realize_not] at h1 h2
    exact h2 h1
  C1_imp := by
    intro S hS φ ψ hmem
    have hsat : Sentenceω.Realize (φ.imp ψ) M := hS hmem
    simp only [Sentenceω.Realize, realize_imp] at hsat
    by_cases hφ : Sentenceω.Realize φ M
    · right; exact union_subset_trueInModel hS (hsat hφ)
    · left; exact union_subset_trueInModel hS
        (show Sentenceω.Realize φ.not M by
          simp only [Sentenceω.Realize, realize_not]; exact hφ)
  C1_neg_imp := by
    intro S hS φ ψ hmem
    have hsat : Sentenceω.Realize (φ.imp ψ).not M := hS hmem
    simp only [Sentenceω.Realize, realize_not, realize_imp] at hsat
    push_neg at hsat
    obtain ⟨hφ, hψ⟩ := hsat
    exact ⟨union_subset_trueInModel hS hφ,
           union_subset_trueInModel hS
             (show Sentenceω.Realize ψ.not M by
              simp only [Sentenceω.Realize, realize_not]; exact hψ)⟩
  C2_not_not := by
    intro S hS φ hmem
    have hsat : Sentenceω.Realize φ.not.not M := hS hmem
    simp only [Sentenceω.Realize, realize_not] at hsat
    exact union_subset_trueInModel hS (by push_neg at hsat; exact hsat)
  C3_iInf := by
    intro S hS φs hmem k
    have hsat : Sentenceω.Realize (iInf φs) M := hS hmem
    simp only [Sentenceω.Realize, realize_iInf] at hsat
    exact union_subset_trueInModel hS (hsat k)
  C3_neg_iInf := by
    intro S hS φs hmem
    have hsat : Sentenceω.Realize (iInf φs).not M := hS hmem
    simp only [Sentenceω.Realize, realize_not, realize_iInf] at hsat
    push_neg at hsat
    obtain ⟨k, hk⟩ := hsat
    exact ⟨k, union_subset_trueInModel hS
      (show Sentenceω.Realize (φs k).not M by
        simp only [Sentenceω.Realize, realize_not]; exact hk)⟩
  C4_iSup := by
    intro S hS φs hmem
    have hsat : Sentenceω.Realize (iSup φs) M := hS hmem
    simp only [Sentenceω.Realize, realize_iSup] at hsat
    obtain ⟨k, hk⟩ := hsat
    exact ⟨k, union_subset_trueInModel hS hk⟩
  C4_neg_iSup := by
    intro S hS φs hmem k
    have hsat : Sentenceω.Realize (iSup φs).not M := hS hmem
    simp only [Sentenceω.Realize, realize_not, realize_iSup] at hsat
    push_neg at hsat
    exact union_subset_trueInModel hS
      (show Sentenceω.Realize (φs k).not M by
        simp only [Sentenceω.Realize, realize_not]; exact hsat k)
  extension := by
    intro S hS φ
    by_cases hφ : Sentenceω.Realize φ M
    · left; exact union_subset_trueInModel hS hφ
    · right; exact union_subset_trueInModel hS
        (show Sentenceω.Realize φ.not M by
          simp only [Sentenceω.Realize, realize_not]; exact hφ)
  chain_closure := by
    intro chain hchain _hIsChain _hne σ hσ
    obtain ⟨S, hSmem, hσS⟩ := Set.mem_sUnion.mp hσ
    exact hchain hSmem hσS

/-- φ.subst at a named element equals φ.Realize at that element. -/
private theorem realize_subst_name (ι : NamingFunction L M) (φ : L.Formulaω (Fin 1)) (m : M) :
    Sentenceω.Realize (φ.subst (fun _ => ι.name m)) M ↔ Formulaω.Realize φ (fun _ => m) := by
  simp only [Sentenceω.Realize, realize_subst, Formulaω.Realize]
  have : (fun (a : Fin 1) => (ι.name m).realize (Empty.elim : Empty → M)) = (fun _ => m) := by
    funext ⟨i, hi⟩
    exact ι.sound m
  rw [this]

/-- openBounds.subst at a named element equals Realize at that element. -/
private theorem realize_openBounds_subst_name (ι : NamingFunction L M)
    (φ : L.BoundedFormulaω Empty 1) (m : M) :
    Sentenceω.Realize ((φ.openBounds).subst (fun _ => ι.name m)) M ↔
    φ.Realize Empty.elim (fun _ => m) := by
  rw [realize_subst_name ι]
  exact realize_openBounds φ (fun _ => m)

/-- For `Fin 1`, `Fin.snoc Fin.elim0 m = fun _ => m`. -/
private theorem snoc_elim0_eq_const (m : M) :
    (Fin.snoc (Fin.elim0 : Fin 0 → M) m : Fin 1 → M) = (fun _ => m) := by
  funext ⟨i, hi⟩
  have : i = 0 := Nat.lt_one_iff.mp hi
  subst this
  rfl

/-- Given a model M with a naming function, the true-in-M family forms a `ConsistencyPropertyEq`.

All C7 axioms are proved using `realize_relabel_sumInr_zero` (for the `relabel Sum.inr` variants)
and `realize_openBounds` (for the `openBounds` variants). -/
noncomputable def trueInModelConsistencyPropertyEq
    (M : Type w) [L.Structure M] (ι : NamingFunction L M) :
    ConsistencyPropertyEq L where
  toConsistencyProperty := trueInModelConsistencyProperty M
  C5_eq_refl := by
    intro S hS t
    exact union_subset_trueInModel hS
      (show Sentenceω.Realize (BoundedFormulaω.equal t t) M by
        simp only [Sentenceω.Realize, realize_equal])
  C6_eq_subst := by
    intro S hS t₁ t₂ φ heq hφt₁
    have h_eq : t₁.realize (Empty.elim : Empty → M) = t₂.realize (Empty.elim : Empty → M) := by
      have := hS heq
      simp only [trueInModel, Set.mem_setOf_eq, Sentenceω.Realize, realize_equal,
                  Term.realize_relabel] at this
      simpa using this
    have h_φ : Sentenceω.Realize (φ.subst (fun _ => t₁)) M := hS hφt₁
    exact union_subset_trueInModel hS (by
      simp only [Sentenceω.Realize, realize_subst] at h_φ ⊢
      have key : (fun (a : Fin 1) => (t₂).realize (Empty.elim : Empty → M)) =
                 (fun (a : Fin 1) => (t₁).realize (Empty.elim : Empty → M)) := by
        funext; exact h_eq.symm
      rw [key]; exact h_φ)
  C7_quantifier := by
    intro S hS φ hmem
    have hsat := hS hmem
    simp only [trueInModel, Set.mem_setOf_eq, Sentenceω.Realize, realize_ex] at hsat
    obtain ⟨m, hm⟩ := hsat
    rw [snoc_elim0_eq_const, realize_relabel_sumInr_zero] at hm
    exact ⟨ι.name m, union_subset_trueInModel hS ((realize_subst_name ι φ m).mpr hm)⟩
  C7_all := by
    intro S hS φ hmem t
    have hsat := hS hmem
    simp only [trueInModel, Set.mem_setOf_eq, Sentenceω.Realize, realize_all] at hsat
    have hm := hsat (t.realize (Empty.elim : Empty → M))
    rw [snoc_elim0_eq_const, realize_relabel_sumInr_zero] at hm
    exact union_subset_trueInModel hS (by
      simp only [Sentenceω.Realize, realize_subst]
      convert hm)
  C7_neg_all := by
    intro S hS φ hmem
    have hsat := hS hmem
    simp only [trueInModel, Set.mem_setOf_eq, Sentenceω.Realize, realize_not, realize_all] at hsat
    push_neg at hsat
    obtain ⟨m, hm⟩ := hsat
    rw [snoc_elim0_eq_const, realize_relabel_sumInr_zero] at hm
    refine ⟨ι.name m, union_subset_trueInModel hS ?_⟩
    show Sentenceω.Realize (φ.subst (fun _ => ι.name m)).not M
    simp only [Sentenceω.Realize, realize_not]
    intro h
    exact hm ((realize_subst_name ι φ m).mp h)
  C7_neg_ex := by
    intro S hS φ hmem t
    have hsat := hS hmem
    simp only [trueInModel, Set.mem_setOf_eq, Sentenceω.Realize, realize_not, realize_ex] at hsat
    push_neg at hsat
    have hm := hsat (t.realize (Empty.elim : Empty → M))
    rw [snoc_elim0_eq_const, realize_relabel_sumInr_zero] at hm
    exact union_subset_trueInModel hS (by
      simp only [Sentenceω.Realize, realize_not, realize_subst]
      intro h; apply hm
      convert h)
  C7_all_bound := by
    intro S hS φ hmem t
    have hsat := hS hmem
    simp only [trueInModel, Set.mem_setOf_eq, Sentenceω.Realize, realize_all] at hsat
    have h := hsat (t.realize (Empty.elim : Empty → M))
    rw [snoc_elim0_eq_const] at h
    exact union_subset_trueInModel hS (by
      simp only [Sentenceω.Realize, realize_subst]
      exact (realize_openBounds φ
        (fun _ => t.realize (Empty.elim : Empty → M))).mpr h)
  C7_neg_all_bound := by
    intro S hS φ hmem
    have hsat := hS hmem
    simp only [trueInModel, Set.mem_setOf_eq, Sentenceω.Realize, realize_not,
               realize_all] at hsat
    push_neg at hsat
    obtain ⟨m, hm⟩ := hsat
    rw [snoc_elim0_eq_const] at hm
    refine ⟨ι.name m, union_subset_trueInModel hS ?_⟩
    simp only [Sentenceω.Realize, realize_not, realize_subst]
    intro h
    have h' := (realize_openBounds φ
      (fun _ => (ι.name m).realize (Empty.elim : Empty → M))).mp h
    rw [ι.sound m] at h'
    exact hm h'

/-- A model of a sentence φ in a language with a naming function gives a consistency
property where {φ} is consistent. -/
theorem singleton_in_trueInModelSets (ι : NamingFunction L M)
    (φ : L.Sentenceω) (hM : Sentenceω.Realize φ M) :
    {φ} ∈ (trueInModelConsistencyPropertyEq M ι).toConsistencyProperty.sets := by
  intro σ hσ
  rw [Set.mem_singleton_iff.mp hσ]
  exact hM

/-- A set of sentences true in M is in the consistency property. -/
theorem subset_trueInModel_in_sets (ι : NamingFunction L M)
    (S : Set L.Sentenceω) (hS : ∀ φ ∈ S, Sentenceω.Realize φ M) :
    S ∈ (trueInModelConsistencyPropertyEq M ι).toConsistencyProperty.sets :=
  hS

end Language

end FirstOrder
