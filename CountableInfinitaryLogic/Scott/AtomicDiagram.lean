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
- `SameAtomicType`: Two tuples have the same atomic type iff they satisfy the same atomics.

## Implementation Notes

We restrict to relational languages (`L.IsRelational`) so that the atomic diagram of a finite
tuple is determined by equality and relation holding information.
-/

universe u v w w'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable {M : Type w} [L.Structure M]
variable {n : ℕ}

open FirstOrder Structure Fin

/-- Index type for atomic formulas in a relational language with `n` free variables.
Either an equality between two variables, or a relation applied to variables. -/
inductive AtomicIdx (L : Language.{u, v}) (n : ℕ) : Type max u v where
  /-- Equality between variable i and variable j. -/
  | eq (i j : Fin n) : AtomicIdx L n
  /-- Relation R applied to variables given by f. -/
  | rel {l : ℕ} (R : L.Relations l) (f : Fin l → Fin n) : AtomicIdx L n

namespace AtomicIdx

/-- Countable instance for AtomicIdx. -/
instance [Countable (Σ l, L.Relations l)] : Countable (L.AtomicIdx n) := by
  haveI (l : ℕ) : Countable (L.Relations l) :=
    Function.Injective.countable (f := fun R => (⟨l, R⟩ : Σ l, L.Relations l))
      (fun _ _ h => by injection h)
  haveI : Countable (Σ l, L.Relations l × (Fin l → Fin n)) := inferInstance
  apply Countable.of_equiv (Fin n × Fin n ⊕ (Σ l, L.Relations l × (Fin l → Fin n)))
  exact {
    toFun := fun x => match x with
      | Sum.inl ⟨i, j⟩ => AtomicIdx.eq i j
      | Sum.inr ⟨l, R, f⟩ => AtomicIdx.rel R f
    invFun := fun x => match x with
      | AtomicIdx.eq i j => Sum.inl ⟨i, j⟩
      | AtomicIdx.rel R f => Sum.inr ⟨_, R, f⟩
    left_inv := fun x => by
      cases x with
      | inl p => obtain ⟨i, j⟩ := p; rfl
      | inr p => obtain ⟨l, R, f⟩ := p; rfl
    right_inv := fun x => by
      cases x with
      | eq i j => rfl
      | rel R f => rfl
  }

/-- Evaluates whether an atomic formula indexed by `idx` holds for a tuple `a`. -/
def holds (idx : L.AtomicIdx n) (a : Fin n → M) : Prop :=
  match idx with
  | eq i j => a i = a j
  | rel R f => RelMap R (a ∘ f)

end AtomicIdx

/-- Builds an atomic formula from an index. The formula uses free variables for the tuple. -/
def atomicFormula (idx : L.AtomicIdx n) : L.BoundedFormula (Fin n) 0 :=
  match idx with
  | .eq i j => Term.equal (Term.var i) (Term.var j)
  | .rel R f => R.formula fun k => Term.var (f k)

/-- The atomic formula as an Lω₁ω formula. -/
def atomicFormulaω (idx : L.AtomicIdx n) : L.BoundedFormulaω (Fin n) 0 :=
  (atomicFormula idx).toLω

omit [L.IsRelational] in
@[simp]
theorem realize_atomicFormula (idx : L.AtomicIdx n) (a : Fin n → M) :
    (atomicFormula idx).Realize a Fin.elim0 ↔ idx.holds a := by
  cases idx with
  | eq i j => simp [atomicFormula, AtomicIdx.holds, Term.equal, Term.realize]
  | rel R f =>
    simp only [atomicFormula, AtomicIdx.holds, Relations.formula, BoundedFormula.realize_rel]
    constructor <;> intro h <;> convert h using 1

omit [L.IsRelational] in
@[simp]
theorem realize_atomicFormulaω (idx : L.AtomicIdx n) (a : Fin n → M) :
    (atomicFormulaω idx).Realize a Fin.elim0 ↔ idx.holds a := by
  simp [atomicFormulaω, BoundedFormula.realize_toLω, realize_atomicFormula]

/-- The atomic diagram of a tuple: the conjunction over all atomic indices of either the
atomic formula or its negation, depending on whether it holds. -/
noncomputable def atomicDiagram [Countable (Σ l, L.Relations l)] (a : Fin n → M) :
    L.Formulaω (Fin n) := by
  classical
  haveI (l : ℕ) : Countable (L.Relations l) :=
    Function.Injective.countable (f := fun R => (⟨l, R⟩ : Σ l, L.Relations l))
      (fun _ _ h => by injection h)
  haveI : Countable (L.AtomicIdx n) := inferInstance
  haveI : Encodable (L.AtomicIdx n) := Encodable.ofCountable _
  exact BoundedFormulaω.einf fun idx : L.AtomicIdx n =>
    if idx.holds a then atomicFormulaω idx else (atomicFormulaω idx).not

/-- Two tuples have the same atomic type if they satisfy exactly the same atomic formulas. -/
def SameAtomicType {N : Type w'} [L.Structure N] (a : Fin n → M) (b : Fin n → N) : Prop :=
  ∀ idx : L.AtomicIdx n, idx.holds a ↔ idx.holds b

omit [L.IsRelational] in
/-- The correspondence between atomic diagrams and same atomic type. -/
theorem sameAtomicType_iff_realize_atomicDiagram [Countable (Σ l, L.Relations l)]
    {N : Type w'} [L.Structure N] (a : Fin n → M) (b : Fin n → N) :
    SameAtomicType (L := L) (M := M) (N := N) a b ↔
      Formulaω.Realize (atomicDiagram (L := L) (M := M) a) b := by
  classical
  simp only [atomicDiagram, Formulaω.Realize, BoundedFormulaω.realize_einf]
  constructor
  · intro h idx
    specialize h idx
    by_cases ha : idx.holds a
    · simp only [ha, ↓reduceIte, realize_atomicFormulaω] at *
      exact h.mp ha
    · simp only [ha, ↓reduceIte, BoundedFormulaω.realize_not, realize_atomicFormulaω] at *
      exact fun hb => ha (h.mpr hb)
  · intro h idx
    constructor
    · intro ha
      have := h idx
      simp only [ha, ↓reduceIte, realize_atomicFormulaω] at this
      exact this
    · intro hb
      have := h idx
      by_cases ha : idx.holds a
      · exact ha
      · simp only [ha, ↓reduceIte, BoundedFormulaω.realize_not, realize_atomicFormulaω] at this
        exact (this hb).elim

omit [L.IsRelational] in
/-- Same atomic type is reflexive. -/
@[refl]
theorem SameAtomicType.refl (a : Fin n → M) : SameAtomicType (L := L) (M := M) (N := M) a a :=
  fun _ => Iff.rfl

omit [L.IsRelational] in
/-- Same atomic type is symmetric. -/
@[symm]
theorem SameAtomicType.symm {N : Type w'} [L.Structure N]
    {a : Fin n → M} {b : Fin n → N} (h : SameAtomicType (L := L) (M := M) (N := N) a b) :
    SameAtomicType (L := L) (M := N) (N := M) b a :=
  fun idx => (h idx).symm

omit [L.IsRelational] in
/-- Same atomic type is transitive. -/
@[trans]
theorem SameAtomicType.trans {N P : Type*} [L.Structure N] [L.Structure P]
    {a : Fin n → M} {b : Fin n → N} {c : Fin n → P}
    (hab : SameAtomicType (L := L) (M := M) (N := N) a b)
    (hbc : SameAtomicType (L := L) (M := N) (N := P) b c) :
    SameAtomicType (L := L) (M := M) (N := P) a c :=
  fun idx => (hab idx).trans (hbc idx)

end Language

end FirstOrder
