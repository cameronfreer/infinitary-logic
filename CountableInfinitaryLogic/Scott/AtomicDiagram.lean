/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import CountableInfinitaryLogic.Lomega1omega.Operations

/-!
# Atomic Diagrams for Relational Languages

This file defines atomic types and atomic diagrams for relational first-order languages.
These are the building blocks for Scott formulas.

## Main Definitions

- `AtomicIdx`: An index type for atomic formulas over a relational language.
- `atomicFormula`: Builds an atomic formula from an index.
- `atomicDiagram`: The conjunction of all true/false atomic facts about a tuple.

## Implementation Notes

We restrict to relational languages (`L.IsRelational`) so that the atomic diagram of a finite
tuple is determined by equality and relation holding information.
-/

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable {M : Type w} [L.Structure M]

open FirstOrder Structure Fin

/-- Index type for atomic formulas in a relational language with `n` free variables.
Either an equality between two variables, or a relation applied to variables. -/
inductive AtomicIdx (L : Language.{u, v}) (n : ℕ) : Type max u v where
  /-- Equality between variable i and variable j. -/
  | eq (i j : Fin n) : AtomicIdx L n
  /-- Relation R applied to variables given by f. -/
  | rel {l : ℕ} (R : L.Relations l) (f : Fin l → Fin n) : AtomicIdx L n

namespace AtomicIdx

variable {n : ℕ}

instance [Countable (Σ l, L.Relations l)] : Countable (AtomicIdx L n) := by
  have h1 : Countable (Fin n × Fin n) := inferInstance
  have h2 : Countable (Σ l, L.Relations l × (Fin l → Fin n)) := by
    refine Countable.of_equiv (Σ l, L.Relations l × (Fin l → Fin n)) (Equiv.refl _)
  refine Countable.of_equiv (Fin n × Fin n ⊕ (Σ l, L.Relations l × (Fin l → Fin n))) ?_
  refine {
    toFun := fun x => match x with
      | .inl ⟨i, j⟩ => AtomicIdx.eq i j
      | .inr ⟨l, R, f⟩ => AtomicIdx.rel R f
    invFun := fun x => match x with
      | AtomicIdx.eq i j => .inl ⟨i, j⟩
      | AtomicIdx.rel R f => .inr ⟨_, R, f⟩
    left_inv := ?_
    right_inv := ?_
  }
  · intro x; cases x with
    | inl p => cases p; rfl
    | inr p => obtain ⟨_, _, _⟩ := p; rfl
  · intro x; cases x with
    | eq => rfl
    | rel => rfl

instance [Encodable (Σ l, L.Relations l)] [DecidableEq (Σ l, L.Relations l)] :
    Encodable (AtomicIdx L n) := by
  have h1 : Encodable (Fin n × Fin n) := inferInstance
  have h2 : Encodable (Σ l, L.Relations l × (Fin l → Fin n)) := by
    refine Encodable.ofEquiv (Σ l, L.Relations l × (Fin l → Fin n)) (Equiv.refl _)
  refine Encodable.ofEquiv (Fin n × Fin n ⊕ (Σ l, L.Relations l × (Fin l → Fin n))) ?_
  exact {
    toFun := fun x => match x with
      | .inl ⟨i, j⟩ => AtomicIdx.eq i j
      | .inr ⟨l, R, f⟩ => AtomicIdx.rel R f
    invFun := fun x => match x with
      | AtomicIdx.eq i j => .inl ⟨i, j⟩
      | AtomicIdx.rel R f => .inr ⟨_, R, f⟩
    left_inv := fun x => by cases x with
      | inl p => cases p; rfl
      | inr p => obtain ⟨_, _, _⟩ := p; rfl
    right_inv := fun x => by cases x with
      | eq => rfl
      | rel => rfl
  }

/-- Evaluates whether an atomic formula indexed by `idx` holds for a tuple `a`. -/
def holds (idx : AtomicIdx L n) (a : Fin n → M) : Prop :=
  match idx with
  | eq i j => a i = a j
  | rel R f => RelMap R (a ∘ f)

instance (idx : AtomicIdx L n) (a : Fin n → M) [DecidableEq M]
    [∀ l (R : L.Relations l), DecidablePred (RelMap R)] :
    Decidable (idx.holds a) :=
  match idx with
  | eq i j => inferInstanceAs (Decidable (a i = a j))
  | rel R f => inferInstanceAs (Decidable (RelMap R (a ∘ f)))

end AtomicIdx

/-- Builds an atomic formula from an index. The formula uses variables `&i` for bound variables. -/
def atomicFormula (idx : AtomicIdx L n) : L.BoundedFormula (Fin n) 0 :=
  match idx with
  | .eq i j => Term.equal (Term.var i) (Term.var j)
  | .rel R f => R.formula fun k => Term.var (f k)

/-- The atomic formula as an Lω₁ω formula. -/
def atomicFormulaω (idx : AtomicIdx L n) : L.BoundedFormulaω (Fin n) 0 :=
  (atomicFormula idx).toLω

@[simp]
theorem realize_atomicFormula (idx : AtomicIdx L n) (a : Fin n → M) :
    (atomicFormula idx).Realize a Fin.elim0 ↔ idx.holds a := by
  cases idx with
  | eq i j => simp [atomicFormula, AtomicIdx.holds, Term.equal, Term.realize]
  | rel R f => simp [atomicFormula, AtomicIdx.holds, Relations.formula, Term.realize]

@[simp]
theorem realize_atomicFormulaω (idx : AtomicIdx L n) (a : Fin n → M) :
    (atomicFormulaω idx).Realize a Fin.elim0 ↔ idx.holds a := by
  simp [atomicFormulaω, BoundedFormula.realize_toLω, realize_atomicFormula]

/-- The atomic diagram of a tuple: the conjunction over all atomic indices of either the
atomic formula or its negation, depending on whether it holds. -/
noncomputable def atomicDiagram [Countable (Σ l, L.Relations l)] (a : Fin n → M) :
    L.Formulaω (Fin n) :=
  BoundedFormulaω.einf fun idx : AtomicIdx L n =>
    if idx.holds a then atomicFormulaω idx else (atomicFormulaω idx).not

theorem realize_atomicDiagram [Countable (Σ l, L.Relations l)]
    {N : Type*} [L.Structure N] (a : Fin n → M) (b : Fin n → N) :
    (atomicDiagram a).Realize b Fin.elim0 ↔
      ∀ idx : AtomicIdx L n, idx.holds a ↔ idx.holds b := by
  simp only [atomicDiagram, BoundedFormulaω.realize_einf, Formulaω.Realize]
  constructor
  · intro h idx
    specialize h idx
    by_cases ha : idx.holds a
    · simp only [ha, ↓reduceIte, realize_atomicFormulaω] at h
      exact ⟨fun _ => h, fun _ => ha⟩
    · simp only [ha, ↓reduceIte, BoundedFormulaω.realize_not, realize_atomicFormulaω] at h
      exact ⟨fun ha' => (ha ha').elim, fun hb => (h hb).elim⟩
  · intro h idx
    by_cases ha : idx.holds a
    · simp only [ha, ↓reduceIte, realize_atomicFormulaω, (h idx).mp ha]
    · simp only [ha, ↓reduceIte, BoundedFormulaω.realize_not, realize_atomicFormulaω,
        fun hb => ha ((h idx).mpr hb), not_false_eq_true]

/-- Two tuples have the same atomic type if they satisfy exactly the same atomic formulas. -/
def SameAtomicType (a : Fin n → M) (b : Fin n → N) : Prop :=
  ∀ idx : AtomicIdx L n, idx.holds a ↔ idx.holds b

theorem sameAtomicType_iff_realize_atomicDiagram [Countable (Σ l, L.Relations l)]
    {N : Type*} [L.Structure N] (a : Fin n → M) (b : Fin n → N) :
    SameAtomicType a b ↔ (atomicDiagram a).Realize b Fin.elim0 :=
  (realize_atomicDiagram a b).symm

/-- Same atomic type is reflexive. -/
theorem SameAtomicType.refl (a : Fin n → M) : SameAtomicType a a :=
  fun _ => Iff.rfl

/-- Same atomic type is symmetric. -/
theorem SameAtomicType.symm {N : Type*} [L.Structure N]
    {a : Fin n → M} {b : Fin n → N} (h : SameAtomicType a b) :
    SameAtomicType b a :=
  fun idx => (h idx).symm

/-- Same atomic type is transitive. -/
theorem SameAtomicType.trans {N P : Type*} [L.Structure N] [L.Structure P]
    {a : Fin n → M} {b : Fin n → N} {c : Fin n → P}
    (hab : SameAtomicType a b) (hbc : SameAtomicType b c) :
    SameAtomicType a c :=
  fun idx => (hab idx).trans (hbc idx)

end Language

end FirstOrder
