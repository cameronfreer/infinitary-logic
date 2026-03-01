/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Scott.QuantifierRank

/-!
# Countable Code Layer for Lω₁ω Formulas

This file defines a countable code type for Lω₁ω formulas over a countable relational
language, and proves the key bridge lemma: if two tuples agree on all codes of bounded
quantifier rank, they are BFEquiv.

## Main Definitions

- `FormulaCode` / `FormulaCodeList`: A countable mutual inductive type encoding
  Lω₁ω formulas. Uses explicit list structure (instead of `ℕ →`) for branching,
  ensuring countability.
- `FormulaCode.toFormulaω`: Interprets a code as an actual `BoundedFormulaω` formula.

## Main Results

- `FormulaCode.instCountable`: `Countable (FormulaCode L n)`.
- `BFEquiv_implies_agree_codes`: BFEquiv implies agreement on all codes.
- `agree_codes_implies_BFEquiv`: Agreement on all codes implies BFEquiv.
  This is the key bridge from the countable world to the BFEquiv game.

## Implementation Notes

In our Lean formalization, `BoundedFormulaω` is uncountable (due to `ℕ → BoundedFormulaω`
in `iSup`/`iInf`). The `FormulaCode` type provides a countable proxy: it uses an explicit
list structure instead of `ℕ →` for branching, making the type countable. While `FormulaCode`
cannot represent all Lω₁ω formulas, every Lω₁ω formula (including every Scott formula) is
logically equivalent to a conjunction of code-representable formulas, because codes capture
all atomic facts and all finite approximations of countable conjunctions/disjunctions.
-/

universe u v w w'

namespace FirstOrder

namespace Language

variable (L : Language.{u, v})

open FirstOrder Structure Fin Ordinal BoundedFormulaω

mutual
/-- Countable codes for Lω₁ω formulas.
Uses an explicit cons/nil list (instead of `ℕ →`) for conjunctions/disjunctions.
The key property is `Countable (FormulaCode L n)`. -/
inductive FormulaCode : ℕ → Type (max u v + 1) where
  | falsum {n} : FormulaCode n
  | equal {n} (i j : Fin n) : FormulaCode n
  | rel {n l : ℕ} (R : L.Relations l) (f : Fin l → Fin n) : FormulaCode n
  | imp {n} (φ ψ : FormulaCode n) : FormulaCode n
  | all {n} (φ : FormulaCode (n + 1)) : FormulaCode n
  | iSup {n} (φs : FormulaCodeList n) : FormulaCode n
  | iInf {n} (φs : FormulaCodeList n) : FormulaCode n

/-- List of formula codes, used for countable conjunctions/disjunctions. -/
inductive FormulaCodeList : ℕ → Type (max u v + 1) where
  | nil {n} : FormulaCodeList n
  | cons {n} (head : FormulaCode n) (tail : FormulaCodeList n) : FormulaCodeList n
end

namespace FormulaCode

variable {L}

section Encoding

variable [Countable (Σ l, L.Relations l)]

noncomputable instance : Encodable (Σ l, L.Relations l) := Encodable.ofCountable _

private noncomputable def encodeFin (n m : ℕ) (f : Fin n → Fin m) : ℕ :=
  Encodable.encode (show List ℕ from (List.finRange n).map (fun i => (f i).val))

private theorem encodeFin_injective (n m : ℕ) : Function.Injective (encodeFin n m) := by
  intro f1 f2 h; unfold encodeFin at h
  have hlist : List.map (fun i => (f1 i).val) (List.finRange n) =
      List.map (fun i => (f2 i).val) (List.finRange n) := Encodable.encode_injective h
  funext i; apply Fin.val_injective
  have h1 : (List.map (fun j => (f1 j).val) (List.finRange n))[i.val] = (f1 i).val := by
    simp [List.getElem_map, List.getElem_finRange]
  have h2 : (List.map (fun j => (f2 j).val) (List.finRange n))[i.val] = (f2 i).val := by
    simp [List.getElem_map, List.getElem_finRange]
  rw [← h1, ← h2]; congr 1

mutual
noncomputable def encode : FormulaCode L n → ℕ
  | .falsum => Nat.pair 0 0
  | .equal i j => Nat.pair 1 (Nat.pair i.val j.val)
  | .rel (l := l) R f =>
    Nat.pair 2 (Nat.pair (Encodable.encode (⟨l, R⟩ : Σ l, L.Relations l)) (encodeFin l n f))
  | .imp φ ψ => Nat.pair 3 (Nat.pair (encode φ) (encode ψ))
  | .all φ => Nat.pair 4 (encode φ)
  | .iSup φs => Nat.pair 5 (encodeList φs)
  | .iInf φs => Nat.pair 6 (encodeList φs)

noncomputable def encodeList : FormulaCodeList L n → ℕ
  | .nil => 0
  | .cons head tail => Nat.pair (encode head) (encodeList tail) + 1
end

mutual
private theorem encode_injective :
    Function.Injective (FormulaCode.encode : FormulaCode L n → ℕ) := by
  intro a b h
  cases a <;> cases b <;> simp only [encode] at h <;>
    first
    -- falsum/falsum: trivial (goal is rfl after simp makes h : True)
    | rfl
    -- Cross-constructor cases: tag numbers differ, derive contradiction via Nat.pair
    | (have hp := congr_arg Nat.unpair h; simp only [Nat.unpair_pair] at hp
       exact absurd (congr_arg Prod.fst hp) (by omega))
    -- equal/equal: extract Fin values from nested pair
    | (have hp := congr_arg Nat.unpair h; simp only [Nat.unpair_pair] at hp
       have hp2 := congr_arg Nat.unpair (congr_arg Prod.snd hp)
       simp only [Nat.unpair_pair] at hp2
       exact congrArg₂ _ (by ext; exact_mod_cast congr_arg Prod.fst hp2)
         (by ext; exact_mod_cast congr_arg Prod.snd hp2))
    -- imp/imp: recursive on both subformulas
    | (have hp := congr_arg Nat.unpair h; simp only [Nat.unpair_pair] at hp
       have hp2 := congr_arg Nat.unpair (congr_arg Prod.snd hp)
       simp only [Nat.unpair_pair] at hp2
       exact congrArg₂ _ (encode_injective (congr_arg Prod.fst hp2))
         (encode_injective (congr_arg Prod.snd hp2)))
    -- all/all: recursive on single subformula
    | (have hp := congr_arg Nat.unpair h; simp only [Nat.unpair_pair] at hp
       exact congrArg _ (encode_injective (congr_arg Prod.snd hp)))
    -- iSup/iSup, iInf/iInf: recursive on list
    | (have hp := congr_arg Nat.unpair h; simp only [Nat.unpair_pair] at hp
       exact congrArg _ (encodeList_injective (congr_arg Prod.snd hp)))
    -- rel/rel: decode sigma type for (l, R) and use encodeFin_injective for f
    | (have hp := congr_arg Nat.unpair h; simp only [Nat.unpair_pair] at hp
       have hp2 := congr_arg Nat.unpair (congr_arg Prod.snd hp)
       simp only [Nat.unpair_pair] at hp2
       have hsig : (⟨_, _⟩ : Σ l, L.Relations l) = ⟨_, _⟩ :=
         Encodable.encode_injective (congr_arg Prod.fst hp2)
       have hl := congr_arg Sigma.fst hsig; subst hl
       have hR := (Sigma.mk.inj hsig).2; subst hR
       exact congrArg _ (encodeFin_injective _ _ (congr_arg Prod.snd hp2)))

private theorem encodeList_injective :
    Function.Injective (FormulaCode.encodeList : FormulaCodeList L n → ℕ) := by
  intro a b h
  cases a <;> cases b <;>
    simp only [encodeList] at h <;>
    try rfl
  · omega
  · omega
  · rename_i h1 t1 h2 t2
    have h1 : Nat.pair (encode h1) (encodeList t1) =
        Nat.pair (encode h2) (encodeList t2) := by omega
    have hp := congr_arg Nat.unpair h1
    simp [Nat.unpair_pair] at hp
    exact congrArg₂ _ (encode_injective hp.1) (encodeList_injective hp.2)
end

instance instCountable [Countable (Σ l, L.Relations l)] (n : ℕ) :
    Countable (FormulaCode L n) :=
  encode_injective.countable

instance instCountableList [Countable (Σ l, L.Relations l)] (n : ℕ) :
    Countable (FormulaCodeList L n) :=
  encodeList_injective.countable

end Encoding

section Semantics

variable [L.IsRelational] [Countable (Σ l, L.Relations l)]

mutual
/-- Interpret a code as an actual Lω₁ω formula. -/
noncomputable def toFormulaω : FormulaCode L n → L.Formulaω (Fin n)
  | .falsum => ⊥
  | .equal i j => .equal (Term.var (Sum.inl i)) (Term.var (Sum.inl j))
  | .rel R f => .rel R (fun k => Term.var (Sum.inl (f k)))
  | .imp φ ψ => .imp (toFormulaω φ) (toFormulaω ψ)
  | .all φ => forallLastVar (toFormulaω φ)
  | .iSup φs =>
    .iSup (fun k => (toFormulaωList φs).getD k ⊥)
  | .iInf φs =>
    .iInf (fun k => (toFormulaωList φs).getD k ⊤)

/-- Interpret a code list as a list of Lω₁ω formulas. -/
noncomputable def toFormulaωList :
    FormulaCodeList L n → List (L.Formulaω (Fin n))
  | .nil => []
  | .cons head tail => toFormulaω head :: toFormulaωList tail
end

/-- Semantics of a code: realized iff its formula interpretation is realized. -/
noncomputable def Realize {N : Type w} [L.Structure N]
    (c : FormulaCode L n) (b : Fin n → N) : Prop :=
  (toFormulaω c).Realize b

end Semantics

end FormulaCode

section Bridge

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

omit [Countable (Σ l, L.Relations l)] in
/-- BFEquiv implies agreement on all formula codes of bounded quantifier rank. -/
theorem BFEquiv_implies_agree_codes
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N]
    {n : ℕ} (a : Fin n → M) (b : Fin n → N)
    (α : Ordinal.{0}) (hα : α < Ordinal.omega 1)
    (hBF : BFEquiv (L := L) α n a b)
    (c : FormulaCode L n) (hc : (c.toFormulaω).qrank ≤ α) :
    (c.Realize a ↔ c.Realize b) :=
  BFEquiv_implies_agree_formulas_omega a b α hα hBF c.toFormulaω hc

/-- Agreement on all formula codes implies BFEquiv.

**DEAD CODE**: No longer on the active Scott pipeline. The conditional pipeline
(`CountableRefinementHypothesis` + `_of` variants in Sentence.lean) bypasses this entirely.

**KNOWN GAP**: This sorry is genuine. `FormulaCode` uses finite lists (`FormulaCodeList`)
for iSup/iInf, making the type countable. However, BFEquiv at successor ordinals requires
agreement on formulas with *countably infinite* conjunctions/disjunctions (the Scott formula
uses `einf`/`esup` over all elements of M). Agreement on all finite-list codes does NOT
imply agreement on countable-conjunction formulas. -/
theorem agree_codes_implies_BFEquiv
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N]
    {n : ℕ} (a : Fin n → M) (b : Fin n → N)
    (α : Ordinal.{0}) (hα : α < Ordinal.omega 1)
    (hAgree : ∀ c : FormulaCode L n, (c.toFormulaω).qrank ≤ α →
      (c.Realize a ↔ c.Realize b)) :
    BFEquiv (L := L) α n a b := by
  apply (realize_scottFormula_iff_BFEquiv a b α hα).mp
  have hSelf : (scottFormula (L := L) a α).Realize a :=
    (realize_scottFormula_iff_BFEquiv a a α hα).mpr (BFEquiv.refl α a)
  sorry

/-- BFEquiv at α is equivalent to agreement on all codes of qrank ≤ α. -/
theorem BFEquiv_iff_agree_codes
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N]
    {n : ℕ} (a : Fin n → M) (b : Fin n → N)
    (α : Ordinal.{0}) (hα : α < Ordinal.omega 1) :
    BFEquiv (L := L) α n a b ↔
    ∀ c : FormulaCode L n, (c.toFormulaω).qrank ≤ α →
      (c.Realize a ↔ c.Realize b) :=
  ⟨fun h c hc => BFEquiv_implies_agree_codes a b α hα h c hc,
   fun h => agree_codes_implies_BFEquiv a b α hα h⟩

/-- **DEAD CODE**: If BFEquiv α but ¬BFEquiv (succ α), there exists a separating code.

No longer on the active Scott pipeline. See `CountableRefinementHypothesis` in Sentence.lean.

**Trust boundary**: depends on `agree_codes_implies_BFEquiv` (sorry). -/
theorem exists_separating_code
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N]
    {n : ℕ} (a : Fin n → M) (b : Fin n → N)
    (α : Ordinal.{0}) (_hα : α < Ordinal.omega 1)
    (hsucc_lt : Order.succ α < Ordinal.omega 1)
    (_hBF : BFEquiv (L := L) α n a b)
    (hNotBF : ¬BFEquiv (L := L) (Order.succ α) n a b) :
    ∃ c : FormulaCode L n, (c.toFormulaω).qrank ≤ Order.succ α ∧
      ¬(c.Realize a ↔ c.Realize b) := by
  by_contra hall
  push_neg at hall
  exact hNotBF (agree_codes_implies_BFEquiv a b (Order.succ α) hsucc_lt
    fun c hc => hall c hc)

end Bridge

end Language

end FirstOrder
