/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelExistence.Theorem
import InfinitaryLogic.ModelExistence.SatisfiableConsistencyProperty
import InfinitaryLogic.Lomega1omega.Operations
import Architect

/-!
# Karp Completeness

This file states the completeness theorem for Lω₁ω: a sentence that belongs to
some consistency property has a model.

## Main Results

- `karp_completeness`: If φ belongs to some consistency property, then φ has a model.
- `omitting_types`: The omitting types theorem for Lω₁ω.

## References

- [Marker, "Lectures on Infinitary Model Theory", 2016]
- [Keisler-Knight, "Barwise: Infinitary Logic and Admissible Sets", 2004]
-/

universe u v

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

open FirstOrder Structure

/-- **Karp Completeness**: A sentence in a countable language that belongs to some
consistency property with equality axioms has a countable model.

This is a sentence-level consequence of the model existence theorem. -/
@[blueprint "thm:karp-completeness"
  (title := /-- Karp completeness -/)
  (statement := /-- A sentence in a countable language that belongs to some consistency
    property with equality axioms has a countable model. -/)
  (proofUses := ["thm:model-existence"])]
theorem karp_completeness [Countable (Σ l, L.Functions l)] [Countable (Σ l, L.Relations l)]
    (φ : L.Sentenceω)
    (h : ∃ C : ConsistencyPropertyEq L, {φ} ∈ C.toConsistencyProperty.sets) :
    ∃ (M : Type u) (_ : L.Structure M) (_ : Countable M), Sentenceω.Realize φ M := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨M, hStr, hCount, hModel⟩ := model_existence C {φ} hC (Set.countable_singleton φ)
  exact ⟨M, hStr, hCount, hModel φ (Set.mem_singleton φ)⟩

/-- A type (set of formulas in one free variable) is omitted by a structure M
if no element of M realizes all formulas in the type simultaneously. -/
@[blueprint "def:omits-type"
  (title := /-- Omits type -/)
  (statement := /-- A structure $M$ omits a type $p$ (a set of formulas in one free
    variable) if no element of $M$ realizes all formulas in $p$ simultaneously. -/)]
def OmitsType (M : Type*) [L.Structure M] (p : Set (L.Formulaω (Fin 1))) : Prop :=
  ∀ m : M, ∃ φ ∈ p, ¬ Formulaω.Realize φ (fun _ => m)

/-- **Omitting Types Theorem** for Lω₁ω.

Given a countable consistent theory T in a countable language and a countable collection
of types to omit (each of which is not isolated by any formula consistent with T),
there exists a countable model of T that omits all the given types.

This is a powerful generalization of the standard omitting types theorem from
first-order logic to the countable infinitary setting. -/
@[blueprint "thm:omitting-types"
  (title := /-- Omitting types -/)
  (statement := /-- Given a countable consistent theory $T$ in a countable language and
    a countable collection of non-isolated types, there exists a countable model of $T$
    that omits all the given types. -/)
  (proof := /-- Build a term model via the model existence theorem, then derive a
    contradiction for any element that would realize all formulas in an omitted type. -/)
  (uses := ["def:omits-type"])
  (proofUses := ["thm:model-existence"])]
theorem omitting_types [Countable (Σ l, L.Functions l)] [Countable (Σ l, L.Relations l)]
    (T : L.Theoryω) (_hT_countable : T.Countable)
    (Γ : Set (Set (L.Formulaω (Fin 1))))
    (hT : ∃ C : ConsistencyPropertyEq L, T ∈ C.toConsistencyProperty.sets)
    (_hΓ : Γ.Countable)
    (h_not_isolated : ∀ p ∈ Γ, ∀ (C : ConsistencyPropertyEq L)
      (φ : L.Formulaω (Fin 1)),
      T ∪ {(φ.relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)).ex} ∈ C.toConsistencyProperty.sets →
      ∃ ψ ∈ p, T ∪ {((φ.and ψ.not).relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)).ex}
        ∈ C.toConsistencyProperty.sets) :
    ∃ (M : Type u) (_ : L.Structure M) (_ : Countable M),
      Theoryω.Model T M ∧ ∀ p ∈ Γ, OmitsType (L := L) M p := by
  obtain ⟨C, hC⟩ := hT
  -- Extend T to a maximal consistent set and build the term model
  obtain ⟨S', hTS', hmax⟩ := C.toConsistencyProperty.exists_maximal T hC
  refine ⟨TermModel C S' hmax, termModelStructure, inferInstance,
    fun φ hφ => (truthLemma φ).mp (hTS' hφ), ?_⟩
  -- Show each type in Γ is omitted by the term model
  intro p hp m
  by_contra h_all
  push_neg at h_all
  -- h_all : ∀ φ ∈ p, Formulaω.Realize φ (fun _ => m)
  -- Build a NamingFunction for the term model
  have hNF : NamingFunction L (TermModel C S' hmax) :=
    ⟨Quotient.out, fun m => by rw [term_realize_eq_mk]; exact Quotient.out_eq m⟩
  -- Build the "true in model" consistency property
  let C' := trueInModelConsistencyPropertyEq (TermModel C S' hmax) hNF
  -- T is true in the term model, so T ∈ C'.sets
  have hT' : T ∈ C'.toConsistencyProperty.sets :=
    fun σ hσ => (truthLemma σ).mp (hTS' hσ)
  -- Construct φ_eq(x) := "x = name(m)" (a formula with one free variable)
  let t_m := hNF.name m
  let φ_eq : L.Formulaω (Fin 1) :=
    BoundedFormulaω.equal
      (Term.var (Sum.inl (0 : Fin 1)))
      (t_m.relabel (Sum.inl ∘ (Empty.elim : Empty → Fin 1)))
  -- Key semantic property: φ_eq at v says "v 0 = m"
  have hφ_sem : ∀ m' : TermModel C S' hmax,
      Formulaω.Realize φ_eq (fun _ : Fin 1 => m') ↔ m' = m := by
    intro m'
    simp only [φ_eq, Formulaω.Realize, BoundedFormulaω.realize_equal]
    simp only [Term.realize_var, Term.realize_relabel]
    constructor
    · intro h
      have key : (Sum.elim (fun _ : Fin 1 => m') Fin.elim0 ∘ Sum.inl ∘
          (Empty.elim : Empty → Fin 1) : Empty → _) =
          (Empty.elim : Empty → TermModel C S' hmax) :=
        funext (fun e => Empty.elim e)
      rw [key] at h; rwa [hNF.sound] at h
    · intro h; rw [h]
      have key : (Sum.elim (fun _ : Fin 1 => m) Fin.elim0 ∘ Sum.inl ∘
          (Empty.elim : Empty → Fin 1) : Empty → _) =
          (Empty.elim : Empty → TermModel C S' hmax) :=
        funext (fun e => Empty.elim e)
      rw [key]; exact (hNF.sound m).symm
  -- Helper: Fin.snoc Fin.elim0 m' = fun _ => m'
  have snoc_eq : ∀ m' : TermModel C S' hmax,
      (Fin.snoc (Fin.elim0 : Fin 0 → TermModel C S' hmax) m' : Fin 1 → _) =
      fun _ => m' :=
    fun m' => funext (fun ⟨i, hi⟩ => by
      have : i = 0 := Nat.lt_one_iff.mp hi; subst this; rfl)
  -- ∃x(φ_eq(x)) is true in the term model (witnessed by m itself)
  have h_ex_true : Sentenceω.Realize
      ((φ_eq.relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)).ex)
      (TermModel C S' hmax) := by
    simp only [Sentenceω.Realize, BoundedFormulaω.realize_ex]
    exact ⟨m, by rw [snoc_eq, BoundedFormulaω.realize_relabel_sumInr_zero]; exact (hφ_sem m).mpr rfl⟩
  -- T ∪ {∃x(φ_eq)} ∈ C'.sets
  have hT_ex : T ∪ {(φ_eq.relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)).ex}
      ∈ C'.toConsistencyProperty.sets := by
    intro σ hσ
    rcases hσ with hσT | hσeq
    · exact hT' hσT
    · rw [Set.mem_singleton_iff.mp hσeq]; exact h_ex_true
  -- Apply non-isolation to get ψ₀ ∈ p with ∃x(φ_eq ∧ ¬ψ₀) true in M
  obtain ⟨ψ₀, hψ₀_mem, hψ₀⟩ := h_not_isolated p hp C' φ_eq hT_ex
  -- Extract that ∃x(φ_eq ∧ ¬ψ₀) is true in the model
  have h_and_true : Sentenceω.Realize
      (((φ_eq.and ψ₀.not).relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)).ex)
      (TermModel C S' hmax) :=
    hψ₀ (Set.mem_union_right T rfl)
  -- Unpack: ∃ m', m' = m ∧ ¬ψ₀(m'), giving ¬ψ₀(m)
  simp only [Sentenceω.Realize, BoundedFormulaω.realize_ex] at h_and_true
  obtain ⟨m', hm'⟩ := h_and_true
  rw [snoc_eq, BoundedFormulaω.realize_relabel_sumInr_zero] at hm'
  simp only [Formulaω.Realize, BoundedFormulaω.realize_and, BoundedFormulaω.realize_not] at hm'
  obtain ⟨hm'_eq, hm'_neg⟩ := hm'
  have hm'_is_m : m' = m := (hφ_sem m').mp hm'_eq
  rw [hm'_is_m] at hm'_neg
  exact hm'_neg (h_all ψ₀ hψ₀_mem)

end Language

end FirstOrder
