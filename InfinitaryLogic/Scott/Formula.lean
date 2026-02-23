/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Scott.BackAndForth

/-!
# Scott Formulas

This file defines Scott formulas, which are Lω₁ω formulas that capture back-and-forth
equivalence at each ordinal level.

## Main Definitions

- `scottFormula`: The Scott formula for a tuple at a given ordinal level.

## Main Results

- `realize_scottFormula_iff_BFEquiv`: A tuple b satisfies the Scott formula for a at level α
  if and only if a and b are BF-equivalent at level α.

## Implementation Notes

The Scott formula at ordinal α is defined by recursion on α:
- At 0: the atomic diagram of the tuple
- At successor α + 1: the formula at α, plus forth and back conditions
- At limit λ: the conjunction over all β < λ

For the forth and back conditions, we need to quantify over elements of M, which requires
`[Countable M]` to form the countable conjunction/disjunction.

The key technical challenge is handling the variable binding correctly. When we have
a formula φ(x₀,...,xₙ) with n+1 free variables and want to existentially quantify
over the last variable, we use `relabel` to move it into a bound position.
-/

universe u v w w'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable {M : Type w} [L.Structure M]
variable [Countable (Σ l, L.Relations l)]
variable [Countable M]

-- Derive Encodable from Countable for use in einf/esup
attribute [local instance] Encodable.ofCountable

open FirstOrder Structure Fin Ordinal BoundedFormulaω

/-- Existentially quantify over the last free variable of a formula. -/
def existsLastVar {n : ℕ} (φ : L.Formulaω (Fin (n + 1))) : L.Formulaω (Fin n) :=
  (φ.relabel insertLastBound).ex

/-- Universally quantify over the last free variable of a formula. -/
def forallLastVar {n : ℕ} (φ : L.Formulaω (Fin (n + 1))) : L.Formulaω (Fin n) :=
  (φ.relabel insertLastBound).all

section Semantics

variable {N : Type w'} [L.Structure N]

/-- Maps `j : Fin k` to `⟨j.val + 1, ...⟩ : Fin (1 + k)`. Used for bound variable shifting. -/
private def Fin.succShift {k : ℕ} : Fin k → Fin (1 + k) :=
  fun j => ⟨j.val + 1, by omega⟩

/-- Helper lemma: the composition of `Sum.elim v xs` with `relabelAux insertLastBound k`
equals `Sum.elim (snoc v (xs 0)) (xs ∘ Fin.succShift)`. This is the key for proving
semantics of relabeling for formulas with k bound variables. -/
private lemma sum_elim_relabelAux_insertLastBound {k : ℕ} (v : Fin n → N) (xs : Fin (1 + k) → N) :
    Sum.elim v xs ∘ BoundedFormulaω.relabelAux insertLastBound k =
    Sum.elim (snoc v (xs 0)) (xs ∘ Fin.succShift) := by
  funext x
  cases x with
  | inl i =>
    simp only [Function.comp_apply, BoundedFormulaω.relabelAux, Sum.map_inl, Sum.elim_inl, insertLastBound]
    split_ifs with h
    · simp only [Equiv.sumAssoc_apply_inl_inl, Sum.map_inl, Sum.elim_inl, snoc, h, dite_true]; congr 1
    · simp only [Equiv.sumAssoc_apply_inl_inr, Sum.map_inr, Sum.elim_inr, finSumFinEquiv_apply_left]
      have hi : i = last n := by ext; simp only [last]; omega
      rw [hi, snoc_last]; rfl
  | inr j =>
    simp only [Function.comp_apply, BoundedFormulaω.relabelAux, Sum.map_inr, Sum.elim_inr]
    simp only [Equiv.sumAssoc_apply_inr, Sum.map_inr, Sum.elim_inr, finSumFinEquiv_apply_right, Fin.succShift]
    congr 1; ext; simp only [Fin.natAdd, id_eq]; ring

/-- Helper: composition of snoc with succShift. -/
private lemma snoc_comp_succShift_eq {k : ℕ} (xs : Fin (1 + k) → N) (y : N) :
    snoc xs y ∘ Fin.succShift = snoc (xs ∘ Fin.succShift) y := by
  funext j
  simp only [Function.comp_apply]
  cases j using lastCases with
  | last =>
    simp only [snoc_last]
    have hsuc : Fin.succShift (last k) = last (1 + k) := by ext; simp only [Fin.succShift, last]; ring
    simp only [hsuc, snoc_last]
  | cast j' =>
    simp only [snoc_castSucc]; unfold snoc
    have hlt : (Fin.succShift (castSucc j')).val < 1 + k := by simp [Fin.succShift, castSucc]; omega
    simp only [hlt, dite_true]
    have heq : castLT (Fin.succShift (castSucc j')) hlt = Fin.succShift j' := by ext; simp [castLT, Fin.succShift, castSucc]
    rw [heq]; rfl

/-- Helper: snoc xs y at position 0 equals xs at position 0. -/
private lemma snoc_zero_eq {k : ℕ} (xs : Fin (1 + k) → N) (y : N) :
    (snoc (α := fun _ => N) xs y) (0 : Fin (1 + k + 1)) = xs (0 : Fin (1 + k)) := by
  simp only [snoc]
  have h0 : (0 : Fin (1 + k + 1)).val < 1 + k := by simp only [Fin.val_zero]; omega
  simp only [h0, dite_true, castLT, cast_eq]
  have h_eq : (⟨(0 : Fin (1 + k + 1)).val, h0⟩ : Fin (1 + k)) = (0 : Fin (1 + k)) := by ext; simp only [Fin.val_zero]
  rw [h_eq]

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- The general semantics lemma for relabeling with `insertLastBound`:
    For a formula with k bound variables, relabeling shifts the last free variable
    to bound position 0, while bound variables shift up by 1.

This handles all cases including `all`, which appears in Scott formulas due to
`forallLastVar` applications at earlier stages. -/
private theorem realize_relabel_insertLastBound {n : ℕ} :
    ∀ {k : ℕ} (φ : L.BoundedFormulaω (Fin (n + 1)) k) (v : Fin n → N) (xs : Fin (1 + k) → N),
    (φ.relabel insertLastBound).Realize v xs ↔ φ.Realize (snoc v (xs 0)) (xs ∘ Fin.succShift) := by
  intro k φ
  induction φ with
  | falsum => intro v xs; simp only [relabel, realize_falsum]
  | equal t₁ t₂ => intro v xs; simp only [relabel, realize_equal, Term.realize_relabel, sum_elim_relabelAux_insertLastBound]
  | rel R ts =>
    intro v xs; simp only [relabel, realize_rel]
    have key := sum_elim_relabelAux_insertLastBound (k := _) v xs
    constructor <;> intro h <;> simp only [Term.realize_relabel, key] at h ⊢ <;> exact h
  | imp φ ψ ih_φ ih_ψ => intro v xs; simp only [relabel, realize_imp]; exact Iff.imp (ih_φ v xs) (ih_ψ v xs)
  | all φ ih =>
    intro v xs; simp only [relabel, realize_all]
    constructor <;> intro hall y
    -- Use realize_castLE_self which handles any proof of n ≤ n, not just le_refl
    · specialize hall y; rw [realize_castLE_self] at hall; rw [ih v (snoc xs y)] at hall; rw [snoc_zero_eq, snoc_comp_succShift_eq] at hall; exact hall
    · rw [realize_castLE_self, ih v (snoc xs y), snoc_zero_eq, snoc_comp_succShift_eq]; exact hall y
  | iSup φs ih => intro v xs; simp only [relabel, realize_iSup]; exact exists_congr (fun i => ih i v xs)
  | iInf φs ih => intro v xs; simp only [relabel, realize_iInf]; exact forall_congr' (fun i => ih i v xs)

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- The key semantics lemma for formulas with 0 bound variables: relabeling with `insertLastBound`
    shifts the last free variable to a bound variable position.

For `φ : L.Formulaω (Fin (n+1))` (a formula with n+1 free vars and 0 bound vars):
- `φ.relabel insertLastBound : L.BoundedFormulaω (Fin n) 1` has n free vars and 1 bound var
- When we evaluate with free var assignment `v : Fin n → N` and bound var assignment `xs : Fin 1 → N`,
  this corresponds to evaluating the original formula with `snoc v (xs 0) : Fin (n+1) → N` -/
theorem realize_relabel_insertLastBound_zero {n : ℕ} (φ : L.Formulaω (Fin (n + 1)))
    (v : Fin n → N) (xs : Fin 1 → N) :
    (φ.relabel insertLastBound).Realize v xs ↔ φ.Realize (snoc v (xs 0)) := by
  have h := realize_relabel_insertLastBound (k := 0) φ v xs
  rw [h]
  simp only [Formulaω.Realize]
  have heq : (xs ∘ Fin.succShift : Fin 0 → N) = Fin.elim0 := by ext i; exact i.elim0
  rw [heq]

/-- Helper: snoc Fin.elim0 x evaluated at 0 gives x.
    Note: We need the explicit type annotation `(α := fun _ => α)` because `snoc` is dependently typed. -/
private theorem snoc_elim0_zero {α : Type*} (x : α) :
    (snoc (α := fun _ => α) Fin.elim0 x) 0 = x := by
  simp [Fin.snoc, Fin.last]

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- Semantics of existsLastVar: existentially quantifies over the last variable.

Uses `realize_relabel_insertLastBound_zero` to show that:
- `existsLastVar φ = (φ.relabel insertLastBound).ex`
- This quantifies existentially over the last (n-th) free variable
-/
theorem realize_existsLastVar {n : ℕ} (φ : L.Formulaω (Fin (n + 1))) (v : Fin n → N) :
    (existsLastVar φ).Realize v ↔ ∃ x : N, φ.Realize (snoc v x) := by
  simp only [existsLastVar, Formulaω.Realize, realize_ex]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [realize_relabel_insertLastBound_zero, snoc_elim0_zero] at hx
    exact hx
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [realize_relabel_insertLastBound_zero, snoc_elim0_zero]
    exact hx

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- Semantics of forallLastVar: universally quantifies over the last variable. -/
theorem realize_forallLastVar {n : ℕ} (φ : L.Formulaω (Fin (n + 1))) (v : Fin n → N) :
    (forallLastVar φ).Realize v ↔ ∀ x : N, φ.Realize (snoc v x) := by
  simp only [forallLastVar, Formulaω.Realize, realize_all]
  constructor
  · intro h x
    specialize h x
    rw [realize_relabel_insertLastBound_zero, snoc_elim0_zero] at h
    exact h
  · intro h x
    rw [realize_relabel_insertLastBound_zero, snoc_elim0_zero]
    exact h x

end Semantics

/-- The Scott formula for a tuple a at ordinal level α.

At level 0: the atomic diagram of a.
At successor α + 1: formula at α ∧ (forth condition) ∧ (back condition)
At limit λ: conjunction over all β < λ.

The formula has free variables indexed by `Fin n` (representing the positions in the tuple).
Requires `[Countable M]` to quantify over elements of M in the forth/back conditions.

The definition uses `Ordinal.limitRecOn` with a motive that is constant in the ordinal
(always `(n : ℕ) → (Fin n → M) → L.Formulaω (Fin n)`), allowing uniform treatment of
tuples of different lengths in the recursion.
-/
noncomputable def scottFormula {n : ℕ} (a : Fin n → M) (α : Ordinal) : L.Formulaω (Fin n) :=
  haveI : Encodable M := Encodable.ofCountable M
  Ordinal.limitRecOn (motive := fun _ => (k : ℕ) → (Fin k → M) → L.Formulaω (Fin k)) α
    -- Zero case: atomic diagram
    (fun k a' => atomicDiagram (L := L) a')
    -- Successor case: previous formula ∧ forth ∧ back
    (fun _β ih k a' =>
      ih k a' ⊓
      einf (fun m : M => existsLastVar (ih (k + 1) (snoc a' m))) ⊓
      forallLastVar (esup (fun m : M => ih (k + 1) (snoc a' m))))
    -- Limit case: conjunction over all smaller ordinals
    -- Note: This requires {γ // γ < β} to be encodable, which holds for β < ω₁.
    -- For Scott analysis, we only use ordinals < ω₁, so this is always valid.
    -- For β ≥ ω₁, we return a trivial formula (this case is never used in practice).
    (fun _β _hβ ih k a' =>
      if h_lt : _β < Ordinal.omega 1 then
        haveI : Countable {γ // γ < _β} := by
          -- β.ToType is countable for β < ω₁
          haveI : Countable _β.ToType := by
            rw [← Cardinal.mk_le_aleph0_iff]
            rw [Cardinal.mk_toType]
            have h_card : _β.card < Cardinal.aleph 1 := Cardinal.lt_omega_iff_card_lt.mp h_lt
            have h1 : Cardinal.aleph 1 = Cardinal.aleph (Order.succ 0) := by
              congr 1; exact Ordinal.succ_zero.symm
            rw [h1, Cardinal.aleph_succ, Cardinal.aleph_zero] at h_card
            exact Order.lt_succ_iff.mp h_card
          -- Use equivalence Set.Iio β ≃ β.ToType
          exact Countable.of_equiv _β.ToType (Ordinal.ToType.mk).symm.toEquiv
        haveI : Encodable {γ // γ < _β} := Encodable.ofCountable _
        einf (fun (x : {γ // γ < _β}) => ih x.1 x.2 k a')
      else
        -- For β ≥ ω₁, return ⊤ (true). This case is never invoked for Scott analysis.
        ⊤)
    n a

omit [L.IsRelational] in
theorem scottFormula_zero {n : ℕ} (a : Fin n → M) :
    scottFormula (L := L) a 0 = atomicDiagram a := by
  simp only [scottFormula, Ordinal.limitRecOn_zero]

omit [L.IsRelational] in
theorem scottFormula_succ {n : ℕ} (a : Fin n → M) (α : Ordinal) :
    scottFormula (L := L) a (Order.succ α) =
      scottFormula a α ⊓
      einf (fun m : M => existsLastVar (scottFormula (snoc a m) α)) ⊓
      forallLastVar (esup (fun m : M => scottFormula (snoc a m) α)) := by
  haveI : Encodable M := Encodable.ofCountable M
  simp only [scottFormula, Ordinal.limitRecOn_succ]

omit [L.IsRelational] in
/-- The fundamental correspondence: a tuple b realizes the Scott formula for a at level α
if and only if a and b are BF-equivalent at level α.

**Important**: This theorem only holds for α < ω₁. For α ≥ ω₁, `scottFormula` returns ⊤
(which is always realized) while `BFEquiv` may fail, so the equivalence breaks down.
For Scott analysis of countable structures, we only use ordinals < ω₁.

The proof proceeds by ordinal induction using `limitRecOn`:
- Zero case: follows from `sameAtomicType_iff_realize_atomicDiagram`
- Successor case: uses `realize_existsLastVar` and `realize_forallLastVar`
- Limit case: uses `realize_einf`
-/
theorem realize_scottFormula_iff_BFEquiv
    {N : Type w'} [L.Structure N] {n : ℕ}
    (a : Fin n → M) (b : Fin n → N) (α : Ordinal) (hα : α < Ordinal.omega 1) :
    (scottFormula (L := L) a α).Realize b ↔ BFEquiv (L := L) α n a b := by
  induction α using Ordinal.limitRecOn generalizing n a b with
  | zero =>
    rw [scottFormula_zero, BFEquiv.zero]
    exact (sameAtomicType_iff_realize_atomicDiagram (L := L) (M := M) (N := N) a b).symm
  | succ β ih =>
    have hβ : β < Ordinal.omega 1 := lt_of_lt_of_le (Order.lt_succ β) (le_of_lt hα)
    rw [scottFormula_succ, BFEquiv.succ]
    simp only [Formulaω.realize_inf]
    constructor
    · intro ⟨⟨hbase, hforth⟩, hback⟩
      refine ⟨(ih a b hβ).mp hbase, ?_, ?_⟩
      · intro m
        rw [Formulaω.realize_einf] at hforth
        specialize hforth m
        rw [realize_existsLastVar] at hforth
        obtain ⟨n', hn'⟩ := hforth
        exact ⟨n', (ih (snoc a m) (snoc b n') hβ).mp hn'⟩
      · intro n'
        rw [realize_forallLastVar] at hback
        specialize hback n'
        rw [Formulaω.realize_esup] at hback
        obtain ⟨m, hm⟩ := hback
        exact ⟨m, (ih (snoc a m) (snoc b n') hβ).mp hm⟩
    · intro ⟨hbase, hforth, hback⟩
      refine ⟨⟨(ih a b hβ).mpr hbase, ?_⟩, ?_⟩
      · rw [Formulaω.realize_einf]
        intro m
        obtain ⟨n', hn'⟩ := hforth m
        rw [realize_existsLastVar]
        exact ⟨n', (ih (snoc a m) (snoc b n') hβ).mpr hn'⟩
      · rw [realize_forallLastVar]
        intro n'
        rw [Formulaω.realize_esup]
        obtain ⟨m, hm⟩ := hback n'
        exact ⟨m, (ih (snoc a m) (snoc b n') hβ).mpr hm⟩
  | limit β hβlimit ih =>
    rw [BFEquiv.limit β hβlimit]
    unfold scottFormula
    rw [Ordinal.limitRecOn_limit _ _ _ _ hβlimit]
    simp only [hα, dite_true]
    simp only [Formulaω.Realize, realize_einf]
    constructor
    · intro h γ hγ
      specialize h ⟨γ, hγ⟩
      have hγ' : γ < Ordinal.omega 1 := lt_trans hγ hα
      have := ih γ hγ a b hγ'
      exact this.mp h
    · intro h ⟨γ, hγ⟩
      have hγ' : γ < Ordinal.omega 1 := lt_trans hγ hα
      exact (ih γ hγ a b hγ').mpr (h γ hγ)

end Language

end FirstOrder
