/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelExistence.ConsistencyProperty
import Mathlib.Order.Zorn
import Mathlib.Data.Fintype.Quotient

/-!
# Henkin Construction

This file provides the infrastructure for the Henkin-style proof of the model
existence theorem for Lω₁ω. The construction proceeds in several stages:

1. **Maximal consistent extension**: Extend a consistent set of sentences to a
   maximal one within the consistency property (using Zorn's lemma or sequential
   enumeration for countable languages).
2. **Term model**: Build a model from equivalence classes of closed terms.
3. **Truth lemma**: Show that truth in the term model corresponds to membership
   in the maximal consistent set.

## Main Results

- `ConsistencyProperty.exists_maximal`: Every consistent set extends to a
  maximal consistent set (requires chain-closure of C.sets).
- `ConsistencyProperty.MaximalConsistent`: Predicate for maximal consistency.
- Properties of maximal consistent sets (closure under connectives).

## References

- [Marker, "Lectures on Infinitary Model Theory", 2016], §4.1
- [Keisler, "Model Theory for Infinitary Logic", 1971]
-/

universe u v

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

open FirstOrder Structure

/-! ### Maximal Consistent Sets -/

/-- A set is maximal consistent in a consistency property if it is consistent
and no proper superset is consistent. Uses Mathlib's `Maximal` predicate:
`Maximal (· ∈ C.sets) S` means `S ∈ C.sets ∧ ∀ S', S' ∈ C.sets → S ⊆ S' → S = S'`. -/
def ConsistencyProperty.MaximalConsistent (C : ConsistencyProperty L)
    (S : Set L.Sentenceω) : Prop :=
  Maximal (· ∈ C.sets) S

/-- Every consistent set in a consistency property can be extended to a maximal
consistent set, by Zorn's lemma.

The chain-closure axiom of `ConsistencyProperty` ensures that the union of any
nonempty chain of consistent sets remains consistent, providing the upper bound
required by Zorn's lemma. -/
theorem ConsistencyProperty.exists_maximal (C : ConsistencyProperty L)
    (S : Set L.Sentenceω) (hS : S ∈ C.sets) :
    ∃ S', S ⊆ S' ∧ C.MaximalConsistent S' := by
  obtain ⟨m, hSm, hmax⟩ := zorn_subset_nonempty C.sets
    (fun chain hchain hIsChain hne => ⟨⋃₀ chain, C.chain_closure chain hchain hIsChain hne,
      fun s hs => Set.subset_sUnion_of_mem hs⟩) S hS
  exact ⟨m, hSm, hmax⟩

/-! ### Properties of Maximal Consistent Sets

These properties follow from maximality: if adding a sentence preserves
consistency, then it must already be in the maximal set. -/

/-- A maximal consistent set is consistent. -/
theorem ConsistencyProperty.MaximalConsistent.consistent
    {C : ConsistencyProperty L} {S : Set L.Sentenceω}
    (hmax : C.MaximalConsistent S) : S ∈ C.sets :=
  hmax.prop

/-- If S ∪ {φ} is consistent and S is maximal, then φ ∈ S. -/
theorem ConsistencyProperty.MaximalConsistent.mem_of_union_consistent
    {C : ConsistencyProperty L} {S : Set L.Sentenceω}
    (hmax : C.MaximalConsistent S) {φ : L.Sentenceω} (h : S ∪ {φ} ∈ C.sets) :
    φ ∈ S := by
  have heq := hmax.eq_of_ge h Set.subset_union_left
  exact heq ▸ Set.mem_union_right S (Set.mem_singleton φ)

/-- In a maximal consistent set, for every implication φ → ψ in S,
either ¬φ ∈ S or ψ ∈ S. -/
theorem ConsistencyProperty.MaximalConsistent.imp_mem
    {C : ConsistencyProperty L} {S : Set L.Sentenceω}
    (hmax : C.MaximalConsistent S)
    {φ ψ : L.Sentenceω} (h : BoundedFormulaω.imp φ ψ ∈ S) :
    φ.not ∈ S ∨ ψ ∈ S := by
  rcases C.C1_imp S hmax.consistent φ ψ h with h1 | h2
  · exact Or.inl (hmax.mem_of_union_consistent h1)
  · exact Or.inr (hmax.mem_of_union_consistent h2)

/-- In a maximal consistent set, double negation elimination holds. -/
theorem ConsistencyProperty.MaximalConsistent.not_not_mem
    {C : ConsistencyProperty L} {S : Set L.Sentenceω}
    (hmax : C.MaximalConsistent S)
    {φ : L.Sentenceω} (h : φ.not.not ∈ S) :
    φ ∈ S :=
  hmax.mem_of_union_consistent (C.C2_not_not S hmax.consistent φ h)

/-- In a maximal consistent set, if ⋀ᵢ φᵢ ∈ S, then φₖ ∈ S for all k. -/
theorem ConsistencyProperty.MaximalConsistent.iInf_mem
    {C : ConsistencyProperty L} {S : Set L.Sentenceω}
    (hmax : C.MaximalConsistent S)
    {φs : ℕ → L.Sentenceω} (h : BoundedFormulaω.iInf φs ∈ S) (k : ℕ) :
    φs k ∈ S :=
  hmax.mem_of_union_consistent (C.C3_iInf S hmax.consistent φs h k)

/-- In a maximal consistent set, if ⋁ᵢ φᵢ ∈ S, then φₖ ∈ S for some k. -/
theorem ConsistencyProperty.MaximalConsistent.iSup_mem
    {C : ConsistencyProperty L} {S : Set L.Sentenceω}
    (hmax : C.MaximalConsistent S)
    {φs : ℕ → L.Sentenceω} (h : BoundedFormulaω.iSup φs ∈ S) :
    ∃ k, φs k ∈ S := by
  obtain ⟨k, hk⟩ := C.C4_iSup S hmax.consistent φs h
  exact ⟨k, hmax.mem_of_union_consistent hk⟩

/-- A maximal consistent set decides every sentence: either φ ∈ S* or ¬φ ∈ S*. -/
theorem ConsistencyProperty.MaximalConsistent.decide
    {C : ConsistencyProperty L} {S : Set L.Sentenceω}
    (hmax : C.MaximalConsistent S)
    (φ : L.Sentenceω) : φ ∈ S ∨ φ.not ∈ S := by
  rcases C.extension S hmax.consistent φ with h | h
  · exact Or.inl (hmax.mem_of_union_consistent h)
  · exact Or.inr (hmax.mem_of_union_consistent h)

/-- In a maximal consistent set, ¬φ ∈ S ↔ φ ∉ S. -/
theorem ConsistencyProperty.MaximalConsistent.not_mem_iff
    {C : ConsistencyProperty L} {S : Set L.Sentenceω}
    (hmax : C.MaximalConsistent S) (φ : L.Sentenceω) :
    φ.not ∈ S ↔ φ ∉ S := by
  constructor
  · intro hneg hmem
    exact C.C0_no_contradiction S hmax.consistent φ ⟨hmem, hneg⟩
  · intro h
    rcases hmax.decide φ with hmem | hneg
    · exact absurd hmem h
    · exact hneg

/-- In a maximal consistent set with ConsistencyPropertyEq, universal quantification:
    `(∀x.φ) ∈ S*` iff for all closed terms t, `φ[x/t] ∈ S*`. -/
theorem ConsistencyPropertyEq.MaximalConsistent.all_mem
    {C : ConsistencyPropertyEq L} {S : Set L.Sentenceω}
    (hmax : C.toConsistencyProperty.MaximalConsistent S)
    {φ : L.Formulaω (Fin 1)}
    (h : (φ.relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)).all ∈ S)
    (t : L.Term Empty) : φ.subst (fun _ => t) ∈ S :=
  hmax.mem_of_union_consistent (C.C7_all S hmax.consistent φ h t)

/-- In a maximal consistent set with ConsistencyPropertyEq, existential quantification:
    if `(∃x.φ) ∈ S*` then there exists a closed term t with `φ[x/t] ∈ S*`. -/
theorem ConsistencyPropertyEq.MaximalConsistent.ex_mem
    {C : ConsistencyPropertyEq L} {S : Set L.Sentenceω}
    (hmax : C.toConsistencyProperty.MaximalConsistent S)
    {φ : L.Formulaω (Fin 1)}
    (h : (φ.relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)).ex ∈ S) :
    ∃ t : L.Term Empty, φ.subst (fun _ => t) ∈ S := by
  obtain ⟨t, ht⟩ := C.C7_quantifier S hmax.consistent φ h
  exact ⟨t, hmax.mem_of_union_consistent ht⟩

/-! ### Term Model Construction

The term model for the Henkin construction is built from closed terms of
language L. Two terms are equivalent if the maximal consistent set contains
the equation `t₁ = t₂`. The quotient model satisfies all sentences in S. -/

/-- Equivalence relation on closed terms induced by a maximal consistent set. -/
def termEquiv (C : ConsistencyPropertyEq L) (S : Set L.Sentenceω)
    (hmax : C.toConsistencyProperty.MaximalConsistent S) :
    L.Term Empty → L.Term Empty → Prop :=
  fun t₁ t₂ => BoundedFormulaω.equal
    (t₁.relabel (Sum.inl : Empty → Empty ⊕ Fin 0))
    (t₂.relabel (Sum.inl : Empty → Empty ⊕ Fin 0)) ∈ S

/-- The term equivalence is an equivalence relation. -/
theorem termEquiv_equivalence (C : ConsistencyPropertyEq L) (S : Set L.Sentenceω)
    (hmax : C.toConsistencyProperty.MaximalConsistent S) :
    Equivalence (termEquiv C S hmax) := by
  refine ⟨fun t => ?_, fun h => ?_, fun h₁ h₂ => ?_⟩
  · -- Reflexivity: t = t ∈ S by C5
    exact hmax.mem_of_union_consistent (C.C5_eq_refl S hmax.consistent _)
  · -- Symmetry: from t₁ = t₂ ∈ S, derive t₂ = t₁ ∈ S via C6
    rename_i t₁ t₂
    -- Helper: for any t : L.Term Empty, (t.relabel (Sum.inl ∘ Empty.elim)).subst σ = t.relabel Sum.inl
    -- This holds because t has no variables (Empty), so relabel/subst only act on func nodes.
    have term_subst_empty : ∀ (t t' : L.Term Empty),
        (t.relabel (Sum.inl ∘ Empty.elim : Empty → Fin 1 ⊕ Fin 0)).subst
          (Sum.elim (Term.relabel Sum.inl ∘ fun (_ : Fin 1) => t') (Term.var ∘ Sum.inr)) =
        t.relabel (Sum.inl : Empty → Empty ⊕ Fin 0) := by
      intro t t'
      induction t with
      | var e => exact Empty.elim e
      | func f ts ih =>
        simp only [Term.relabel, Term.subst]
        congr 1; funext i; exact ih i
    -- Use the formula φ(x) = "x = t₁" with one free variable
    let φ : L.Formulaω (Fin 1) :=
      BoundedFormulaω.equal
        (Term.var (Sum.inl (0 : Fin 1)))
        (t₁.relabel (Sum.inl ∘ Empty.elim))
    -- Show φ.subst computes as expected
    have hφ : ∀ t : L.Term Empty,
        φ.subst (fun _ => t) = BoundedFormulaω.equal
          (t.relabel (Sum.inl : Empty → Empty ⊕ Fin 0))
          (t₁.relabel (Sum.inl : Empty → Empty ⊕ Fin 0)) := by
      intro t
      show BoundedFormulaω.equal
        ((Term.var (Sum.inl (0 : Fin 1))).subst
          (Sum.elim (Term.relabel Sum.inl ∘ fun _ => t) (Term.var ∘ Sum.inr)))
        ((t₁.relabel (Sum.inl ∘ Empty.elim)).subst
          (Sum.elim (Term.relabel Sum.inl ∘ fun _ => t) (Term.var ∘ Sum.inr))) =
        BoundedFormulaω.equal (t.relabel Sum.inl) (t₁.relabel Sum.inl)
      simp only [Term.subst, Sum.elim_inl, Function.comp_apply]
      congr 1
      exact term_subst_empty t₁ t
    -- C6 gives S ∪ {φ(t₂)} ∈ C.sets from (t₁ = t₂) ∈ S and φ(t₁) ∈ S
    -- φ(t₁) = (t₁ = t₁) ∈ S by C5
    have hrefl : φ.subst (fun _ => t₁) ∈ S := by
      rw [hφ]
      exact hmax.mem_of_union_consistent (C.C5_eq_refl S hmax.consistent _)
    have hc6 : S ∪ {φ.subst (fun _ => t₂)} ∈ C.toConsistencyProperty.sets :=
      C.C6_eq_subst S hmax.consistent t₁ t₂ φ h hrefl
    rw [hφ] at hc6
    exact hmax.mem_of_union_consistent hc6
  · -- Transitivity: from t₁ = t₂ ∈ S and t₂ = t₃ ∈ S, derive t₁ = t₃ via C6
    rename_i t₁ t₂ t₃
    -- Helper for empty-variable terms
    have term_subst_empty : ∀ (t t' : L.Term Empty),
        (t.relabel (Sum.inl ∘ Empty.elim : Empty → Fin 1 ⊕ Fin 0)).subst
          (Sum.elim (Term.relabel Sum.inl ∘ fun (_ : Fin 1) => t') (Term.var ∘ Sum.inr)) =
        t.relabel (Sum.inl : Empty → Empty ⊕ Fin 0) := by
      intro t t'
      induction t with
      | var e => exact Empty.elim e
      | func f ts ih =>
        simp only [Term.relabel, Term.subst]
        congr 1; funext i; exact ih i
    -- Use the formula φ(x) = "t₁ = x" with one free variable
    let φ : L.Formulaω (Fin 1) :=
      BoundedFormulaω.equal
        (t₁.relabel (Sum.inl ∘ Empty.elim))
        (Term.var (Sum.inl (0 : Fin 1)))
    have hφ : ∀ t : L.Term Empty,
        φ.subst (fun _ => t) = BoundedFormulaω.equal
          (t₁.relabel (Sum.inl : Empty → Empty ⊕ Fin 0))
          (t.relabel (Sum.inl : Empty → Empty ⊕ Fin 0)) := by
      intro t
      show BoundedFormulaω.equal
        ((t₁.relabel (Sum.inl ∘ Empty.elim)).subst
          (Sum.elim (Term.relabel Sum.inl ∘ fun _ => t) (Term.var ∘ Sum.inr)))
        ((Term.var (Sum.inl (0 : Fin 1))).subst
          (Sum.elim (Term.relabel Sum.inl ∘ fun _ => t) (Term.var ∘ Sum.inr))) =
        BoundedFormulaω.equal (t₁.relabel Sum.inl) (t.relabel Sum.inl)
      simp only [Term.subst, Sum.elim_inl, Function.comp_apply]
      congr 1
      exact term_subst_empty t₁ t
    -- C6: from (t₂ = t₃) ∈ S and φ(t₂) = (t₁ = t₂) ∈ S, get S ∪ {φ(t₃)} ∈ C.sets
    have hφt₂ : φ.subst (fun _ => t₂) ∈ S := by rw [hφ]; exact h₁
    have hc6 : S ∪ {φ.subst (fun _ => t₃)} ∈ C.toConsistencyProperty.sets :=
      C.C6_eq_subst S hmax.consistent t₂ t₃ φ h₂ hφt₂
    rw [hφ] at hc6
    exact hmax.mem_of_union_consistent hc6

/-! ### Term Setoid and Quotient -/

/-- The Setoid on closed terms induced by the equivalence relation from S*. -/
def termSetoid (C : ConsistencyPropertyEq L) (S : Set L.Sentenceω)
    (hmax : C.toConsistencyProperty.MaximalConsistent S) : Setoid (L.Term Empty) where
  r := termEquiv C S hmax
  iseqv := termEquiv_equivalence C S hmax

/-- The carrier of the term model: closed terms quotiented by the equivalence
relation `t₁ ~ t₂ ↔ (t₁ = t₂) ∈ S*`. -/
def TermModel (C : ConsistencyPropertyEq L) (S : Set L.Sentenceω)
    (hmax : C.toConsistencyProperty.MaximalConsistent S) : Type _ :=
  Quotient (termSetoid C S hmax)

variable {C : ConsistencyPropertyEq L} {S : Set L.Sentenceω}
  {hmax : C.toConsistencyProperty.MaximalConsistent S}

/-! ### Language Structure on the Term Model

The structure interprets function symbols by applying them to representative terms,
and relation symbols by checking membership in the maximal consistent set S*. -/

/-- Embed a closed term into the term model as its equivalence class. -/
def TermModel.mk (t : L.Term Empty) : TermModel C S hmax :=
  Quotient.mk (termSetoid C S hmax) t

/-- The constant family of setoids for the quotient lifting. -/
private def termSetoidFamily (C : ConsistencyPropertyEq L) (S : Set L.Sentenceω)
    (hmax : C.toConsistencyProperty.MaximalConsistent S) (n : ℕ) :
    ∀ (_ : Fin n), Setoid (L.Term Empty) :=
  fun _ => termSetoid C S hmax

/-- Auxiliary: substituting a closed term into a term with no real variables. -/
private theorem term_subst_empty_aux (t t' : L.Term Empty) :
    (t.relabel (Sum.inl ∘ Empty.elim : Empty → Fin 1 ⊕ Fin 0)).subst
      (Sum.elim (Term.relabel Sum.inl ∘ fun (_ : Fin 1) => t') (Term.var ∘ Sum.inr)) =
    t.relabel (Sum.inl : Empty → Empty ⊕ Fin 0) := by
  induction t with
  | var e => exact Empty.elim e
  | func f ts ih =>
    simp only [Term.relabel, Term.subst]
    congr 1; funext i; exact ih i

/-- Single-step congruence: replacing one argument preserves term equivalence. -/
private theorem func_congr_step (f : L.Functions n) (args : Fin n → L.Term Empty)
    (i : Fin n) (t : L.Term Empty)
    (ht : termEquiv C S hmax (args i) t) :
    termEquiv C S hmax (Term.func f args) (Term.func f (Function.update args i t)) := by
  -- Build the formula φ(x) = "f(args_with_x_at_i) = f(args)"
  -- where the i-th argument on the left is the free variable x
  let φ : L.Formulaω (Fin 1) :=
    BoundedFormulaω.equal
      (Term.func f (fun j =>
        if j = i then Term.var (Sum.inl (0 : Fin 1))
        else (args j).relabel (Sum.inl ∘ Empty.elim)))
      (Term.func f (fun j => (args j).relabel (Sum.inl ∘ Empty.elim)))
  -- Compute what φ.subst (fun _ => s) gives for any closed term s
  have hφ_subst : ∀ s : L.Term Empty,
      φ.subst (fun _ => s) = BoundedFormulaω.equal
        (Term.func f (fun j =>
          if j = i then s.relabel (Sum.inl : Empty → Empty ⊕ Fin 0)
          else (args j).relabel (Sum.inl : Empty → Empty ⊕ Fin 0)))
        (Term.func f (fun j => (args j).relabel (Sum.inl : Empty → Empty ⊕ Fin 0))) := by
    intro s
    show BoundedFormulaω.equal
      ((Term.func f (fun j =>
        if j = i then Term.var (Sum.inl (0 : Fin 1))
        else (args j).relabel (Sum.inl ∘ Empty.elim))).subst
          (Sum.elim (Term.relabel Sum.inl ∘ fun _ => s) (Term.var ∘ Sum.inr)))
      ((Term.func f (fun j => (args j).relabel (Sum.inl ∘ Empty.elim))).subst
          (Sum.elim (Term.relabel Sum.inl ∘ fun _ => s) (Term.var ∘ Sum.inr))) = _
    simp only [Term.subst]
    congr 1
    · congr 1; funext j
      split
      · simp [Term.subst, Sum.elim_inl, Function.comp_apply]
      · exact term_subst_empty_aux (args j) s
    · congr 1; funext j; exact term_subst_empty_aux (args j) s
  -- φ(args i) = "f(args) = f(args)" which is in S by C5 (reflexivity)
  have hφ_ai : φ.subst (fun _ => args i) ∈ S := by
    rw [hφ_subst]
    have : (fun j => if j = i then (args i).relabel (Sum.inl : Empty → Empty ⊕ Fin 0)
        else (args j).relabel (Sum.inl : Empty → Empty ⊕ Fin 0)) =
        (fun j => (args j).relabel (Sum.inl : Empty → Empty ⊕ Fin 0)) := by
      funext j; split <;> simp_all
    rw [this]
    exact hmax.mem_of_union_consistent (C.C5_eq_refl S hmax.consistent _)
  -- C6 gives S ∪ {φ(t)} ∈ C.sets from (args i = t) ∈ S and φ(args i) ∈ S
  have hc6 : S ∪ {φ.subst (fun _ => t)} ∈ C.toConsistencyProperty.sets :=
    C.C6_eq_subst S hmax.consistent (args i) t φ ht hφ_ai
  rw [hφ_subst] at hc6
  -- φ(t) = "f(update args i t) = f(args)", which gives termEquiv symmetrically
  have hkey : BoundedFormulaω.equal
      (Term.func f (fun j =>
        if j = i then t.relabel (Sum.inl : Empty → Empty ⊕ Fin 0)
        else (args j).relabel (Sum.inl : Empty → Empty ⊕ Fin 0)))
      (Term.func f (fun j => (args j).relabel (Sum.inl : Empty → Empty ⊕ Fin 0))) ∈ S :=
    hmax.mem_of_union_consistent hc6
  -- Rewrite the if-then-else to Function.update
  have hlhs : (fun j =>
      if j = i then t.relabel (Sum.inl : Empty → Empty ⊕ Fin 0)
      else (args j).relabel (Sum.inl : Empty → Empty ⊕ Fin 0)) =
      (fun j => (Function.update args i t j).relabel (Sum.inl : Empty → Empty ⊕ Fin 0)) := by
    funext j; simp [Function.update]; split <;> simp_all
  rw [hlhs] at hkey
  -- Now hkey : "f(update args i t) = f(args)" ∈ S, which is the symmetric version
  -- We need "f(args) = f(update args i t)" ∈ S, so use symmetry of termEquiv
  -- termEquiv is defined as: termEquiv _ _ _ t₁ t₂ ↔ equal (t₁.relabel Sum.inl) (t₂.relabel Sum.inl) ∈ S
  -- hkey gives the reverse direction, so we use the symmetry from termEquiv_equivalence
  exact (termEquiv_equivalence C S hmax).symm hkey

/-- Function congruence for term equivalence: if `a i ~ b i` for all i, then
`f(a₁,...,aₙ) ~ f(b₁,...,bₙ)`. Proved by inductively replacing arguments using C6. -/
private theorem func_congr (f : L.Functions n) (a b : Fin n → L.Term Empty)
    (hab : ∀ i, termEquiv C S hmax (a i) (b i)) :
    termEquiv C S hmax (Term.func f a) (Term.func f b) := by
  -- Replace arguments one at a time from a to b
  -- Define mixed k = (fun j => if j.val < k then b j else a j)
  -- mixed 0 = a, mixed n = b
  -- Each step: mixed k → mixed (k+1) by replacing argument at position k
  suffices h : ∀ k : ℕ, (hk : k ≤ n) →
      termEquiv C S hmax (Term.func f a)
        (Term.func f (fun j => if j.val < k then b j else a j)) from by
    have hmixed_n := h n le_rfl
    have heq : (fun j : Fin n => if j.val < n then b j else a j) = b := by
      funext j; simp [j.isLt]
    rwa [heq] at hmixed_n
  intro k
  induction k with
  | zero =>
    intro _
    simp only [Nat.not_lt_zero, ite_false]
    exact (termEquiv_equivalence C S hmax).refl _
  | succ k ih =>
    intro hk
    have hk' : k < n := Nat.lt_of_succ_le hk
    have hkn : k ≤ n := Nat.le_of_lt hk'
    -- By IH: func f a ~ func f (mixed k)
    have step_k := ih hkn
    -- Now replace argument at position ⟨k, hk'⟩
    let i : Fin n := ⟨k, hk'⟩
    let args_k : Fin n → L.Term Empty := fun j => if j.val < k then b j else a j
    -- func_congr_step: func f args_k ~ func f (update args_k i (b i))
    have hab_i : termEquiv C S hmax (args_k i) (b i) := by
      show termEquiv C S hmax (if (i : Fin n).val < k then b i else a i) (b i)
      simp only [show (i : Fin n).val = k from rfl, lt_irrefl, ite_false]
      exact hab ⟨k, hk'⟩
    have step := func_congr_step f args_k i (b i) hab_i
    -- update args_k i (b i) = mixed (k+1)
    have hupdate : Function.update args_k i (b i) =
        (fun j => if j.val < k + 1 then b j else a j) := by
      funext j
      simp only [Function.update]
      split
      · -- j = i, i.e., j.val = k
        rename_i heq
        subst heq
        simp only [show (i : Fin n).val = k from rfl, Nat.lt_succ_iff, le_refl, ite_true]
      · -- j ≠ i
        rename_i hne
        have hne_val : j.val ≠ k := by
          intro h; exact hne (Fin.ext h)
        show (if j.val < k then b j else a j) = (if j.val < k + 1 then b j else a j)
        by_cases hjk : j.val < k
        · simp only [hjk, ite_true, Nat.lt_succ_of_lt hjk]
        · have hjk1 : ¬(j.val < k + 1) := by omega
          simp only [hjk, ite_false, hjk1]
    rw [hupdate] at step
    exact (termEquiv_equivalence C S hmax).trans step_k step

/-- Single-step relation congruence: replacing one argument preserves membership in S. -/
private theorem rel_mem_of_update (R : L.Relations n) (args : Fin n → L.Term Empty)
    (i : Fin n) (t : L.Term Empty)
    (ht : termEquiv C S hmax (args i) t)
    (hmem : BoundedFormulaω.rel R
      (fun j => (args j).relabel (Sum.inl : Empty → Empty ⊕ Fin 0)) ∈ S) :
    BoundedFormulaω.rel R
      (fun j => (Function.update args i t j).relabel (Sum.inl : Empty → Empty ⊕ Fin 0)) ∈ S := by
  -- Build the formula φ(x) = "R(args_with_x_at_i)" with one free variable
  let φ : L.Formulaω (Fin 1) :=
    BoundedFormulaω.rel R (fun j =>
      if j = i then Term.var (Sum.inl (0 : Fin 1))
      else (args j).relabel (Sum.inl ∘ Empty.elim))
  -- Compute what φ.subst (fun _ => s) gives for any closed term s
  have hφ_subst : ∀ s : L.Term Empty,
      φ.subst (fun _ => s) = BoundedFormulaω.rel R (fun j =>
        if j = i then s.relabel (Sum.inl : Empty → Empty ⊕ Fin 0)
        else (args j).relabel (Sum.inl : Empty → Empty ⊕ Fin 0)) := by
    intro s
    show BoundedFormulaω.rel R
      (fun j => ((if j = i then Term.var (Sum.inl (0 : Fin 1))
        else (args j).relabel (Sum.inl ∘ Empty.elim)).subst
          (Sum.elim (Term.relabel Sum.inl ∘ fun _ => s) (Term.var ∘ Sum.inr)))) = _
    congr 1; funext j
    split
    · simp [Term.subst, Sum.elim_inl, Function.comp_apply]
    · exact term_subst_empty_aux (args j) s
  -- φ(args i) = "R(args)" which is in S by hypothesis
  have hφ_ai : φ.subst (fun _ => args i) ∈ S := by
    rw [hφ_subst]
    convert hmem using 2
    funext j; split <;> simp_all
  -- C6 gives S ∪ {φ(t)} ∈ C.sets
  have hc6 : S ∪ {φ.subst (fun _ => t)} ∈ C.toConsistencyProperty.sets :=
    C.C6_eq_subst S hmax.consistent (args i) t φ ht hφ_ai
  rw [hφ_subst] at hc6
  have hkey := hmax.mem_of_union_consistent hc6
  -- Rewrite the if-then-else to Function.update
  convert hkey using 2
  funext j; simp [Function.update]; split <;> simp_all

/-- Relation congruence for term equivalence: if `a i ~ b i` for all i, then
`R(a₁,...,aₙ) ∈ S ↔ R(b₁,...,bₙ) ∈ S`. -/
private theorem rel_congr (R : L.Relations n) (a b : Fin n → L.Term Empty)
    (hab : ∀ i, termEquiv C S hmax (a i) (b i)) :
    (BoundedFormulaω.rel R (fun i => (a i).relabel (Sum.inl : Empty → Empty ⊕ Fin 0)) ∈ S) =
    (BoundedFormulaω.rel R (fun i => (b i).relabel (Sum.inl : Empty → Empty ⊕ Fin 0)) ∈ S) := by
  -- Replace arguments one at a time from a to b (same strategy as func_congr)
  suffices h : ∀ k : ℕ, (hk : k ≤ n) →
      (BoundedFormulaω.rel R (fun j => (a j).relabel (Sum.inl : Empty → Empty ⊕ Fin 0)) ∈ S ↔
       BoundedFormulaω.rel R (fun j =>
        ((if j.val < k then b j else a j).relabel (Sum.inl : Empty → Empty ⊕ Fin 0))) ∈ S) from by
    have hmixed_n := h n le_rfl
    have heq : (fun j : Fin n => (if j.val < n then b j else a j).relabel
        (Sum.inl : Empty → Empty ⊕ Fin 0)) =
        (fun j => (b j).relabel (Sum.inl : Empty → Empty ⊕ Fin 0)) := by
      funext j; simp [j.isLt]
    rw [heq] at hmixed_n
    exact propext hmixed_n
  intro k
  induction k with
  | zero =>
    intro _
    simp only [Nat.not_lt_zero, ite_false]
  | succ k ih =>
    intro hk
    have hk' : k < n := Nat.lt_of_succ_le hk
    have hkn : k ≤ n := Nat.le_of_lt hk'
    have step_k := ih hkn
    let idx : Fin n := ⟨k, hk'⟩
    let args_k : Fin n → L.Term Empty := fun j => if j.val < k then b j else a j
    -- Show args_k idx = a idx (since idx.val = k, not < k)
    have hab_idx : termEquiv C S hmax (args_k idx) (b idx) := by
      show termEquiv C S hmax (if (idx : Fin n).val < k then b idx else a idx) (b idx)
      simp only [show (idx : Fin n).val = k from rfl, lt_irrefl, ite_false]
      exact hab ⟨k, hk'⟩
    -- Show Function.update args_k idx (b idx) = mixed (k+1)
    have hupdate : (fun j => (Function.update args_k idx (b idx) j).relabel
        (Sum.inl : Empty → Empty ⊕ Fin 0)) =
        (fun j => ((if j.val < k + 1 then b j else a j).relabel
          (Sum.inl : Empty → Empty ⊕ Fin 0))) := by
      funext j
      simp only [Function.update]
      split
      · rename_i heq; subst heq
        simp only [show (idx : Fin n).val = k from rfl, Nat.lt_succ_iff, le_refl, ite_true]
      · rename_i hne
        have hne_val : j.val ≠ k := fun h => hne (Fin.ext h)
        show ((if j.val < k then b j else a j).relabel _) =
            ((if j.val < k + 1 then b j else a j).relabel _)
        congr 1
        by_cases hjk : j.val < k
        · simp only [hjk, ite_true, Nat.lt_succ_of_lt hjk]
        · have hjk1 : ¬(j.val < k + 1) := by omega
          simp only [hjk, ite_false, hjk1]
    constructor
    · intro hmem
      have hmem_k := step_k.mp hmem
      have hmem_step := rel_mem_of_update R args_k idx (b idx) hab_idx hmem_k
      rwa [hupdate] at hmem_step
    · intro hmem
      have hmem_k : BoundedFormulaω.rel R
          (fun j => (Function.update args_k idx (b idx) j).relabel
            (Sum.inl : Empty → Empty ⊕ Fin 0)) ∈ S := by
        rwa [hupdate]
      -- Need to go backwards: from update to args_k, using symmetry of termEquiv
      have hab_idx_sym : termEquiv C S hmax (b idx) (args_k idx) := by
        show termEquiv C S hmax (b idx) (if (idx : Fin n).val < k then b idx else a idx)
        simp only [show (idx : Fin n).val = k from rfl, lt_irrefl, ite_false]
        exact (termEquiv_equivalence C S hmax).symm (hab ⟨k, hk'⟩)
      -- Function.update (Function.update args_k idx (b idx)) idx (args_k idx) = args_k
      have hrevert : Function.update (Function.update args_k idx (b idx)) idx (args_k idx) =
          args_k := by
        rw [Function.update_idem, Function.update_eq_self]
      have htermequiv : termEquiv C S hmax
          (Function.update args_k idx (b idx) idx) (args_k idx) := by
        rw [Function.update_self]
        exact hab_idx_sym
      have hmem_revert := rel_mem_of_update R (Function.update args_k idx (b idx))
        idx (args_k idx) htermequiv hmem_k
      rw [hrevert] at hmem_revert
      exact step_k.mpr hmem_revert

/-- The language structure on the term model.

**Function interpretation**: `funMap f [⟦t₁⟧,...,⟦tₙ⟧] = ⟦f(t₁,...,tₙ)⟧`.
**Relation interpretation**: `RelMap R [⟦t₁⟧,...,⟦tₙ⟧] ↔ rel R [t₁,...,tₙ] ∈ S*`. -/
noncomputable instance termModelStructure :
    L.Structure (TermModel C S hmax) where
  funMap {n} f xs :=
    @Quotient.finLiftOn (Fin n) _ _ (fun _ => L.Term Empty) (termSetoidFamily C S hmax n)
      (TermModel C S hmax) xs
      (fun ts => TermModel.mk (Term.func f ts))
      (fun a b hab => Quotient.sound (func_congr f a b hab))
  RelMap {n} R xs :=
    @Quotient.finLiftOn (Fin n) _ _ (fun _ => L.Term Empty) (termSetoidFamily C S hmax n)
      Prop xs
      (fun ts => BoundedFormulaω.rel R
        (fun i => (ts i).relabel (Sum.inl : Empty → Empty ⊕ Fin 0)) ∈ S)
      (fun a b hab => rel_congr R a b hab)

/-! ### Truth Lemma

The fundamental theorem connecting membership in the maximal consistent set with
truth in the term model. -/

/-- **Truth Lemma**: A sentence belongs to the maximal consistent set S* if and
only if it is true in the term model.

This is proved by structural induction on the sentence, using:
- (C0) for `falsum`
- (C1) for `imp`
- (C2) for double negation
- (C3) for `iInf` (countable conjunction)
- (C4) for `iSup` (countable disjunction)
- (C5,C6) for `equal`
- (C7,C7_all) for `all` / `ex`
- Maximality (decidability) for the reverse directions -/
theorem truthLemma (σ : L.Sentenceω) :
    σ ∈ S ↔ Sentenceω.Realize σ (TermModel C S hmax) := by
  sorry

/-! ### Model Existence from Truth Lemma -/

/-- The term model satisfies every sentence in S*. -/
theorem termModel_models_maximal :
    Theoryω.Model S (TermModel C S hmax) := by
  intro φ hφ
  exact (truthLemma φ).mp hφ

end Language

end FirstOrder
