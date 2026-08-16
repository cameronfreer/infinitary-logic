/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Karp.PotentialIso
import InfinitaryLogic.Linf.Operations
import InfinitaryLogic.Linf.QuantifierRank
import InfinitaryLogic.Linf.Theory
import Architect

/-!
# Karp's theorem: the per-node-index remnants

The theorem itself is `karp_theorem_w` in `Karp/CarrierTheorem.lean`. This file holds the
declarations against the older per-node-index syntax that still have live consumers.

## Main Results

- `BFEquiv_implies_agreeQR`: Forward direction of the Karp lemma: BF-equivalence at
  level α implies agreement on all formulas of quantifier rank ≤ α.
- `PotentialIso_implies_LinfEquivW`: the forward direction against the per-node-index
  syntax, retained for its `ScottCompletion` consumer.

## Design Notes

Karp's theorem itself lives in `Karp/CarrierTheorem.lean`, stated against the fixed-carrier
syntax. What remains here is the per-node-index material that still has consumers: the
quantifier-rank forward lemma, which `Scott/QuantifierRank.lean` and
`ModelTheory/TypePreservingBF.lean` use, and the `LinfEquivW` forward direction, which
`ModelTheory/ScottCompletion.lean` uses. Both are retained deliberately rather than ported,
because quantifier rank has no upstream target in the current pin.

## References

- [KK04]
-/

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable [Countable (Σ l, L.Relations l)]

open FirstOrder Structure Fin Ordinal

/-! ### Fin arithmetic helpers

These lemmas connect `Fin.append`, `Fin.snoc`, and `Sum.elim` and are used
throughout the structural induction in `BFEquiv_implies_agree_aux`. They
don't require the section-level `IsRelational` or `Countable` instances. -/

section FinArithmetic

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- `Sum.elim v xs` agrees with `Fin.append v xs ∘ finSumFinEquiv`. -/
private theorem sumElim_eq_append_comp {γ : Type*} {n k : ℕ}
    (v : Fin n → γ) (xs : Fin k → γ) :
    Sum.elim v xs = Fin.append v xs ∘ finSumFinEquiv := by
  exact (Fin.append_comp_sumElim (xs := v) (ys := xs)).symm

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- `Fin.snoc` distributes into `Fin.append` on the right component. -/
private theorem snoc_append_eq_append_snoc {γ : Type*} {n k : ℕ}
    (v : Fin n → γ) (xs : Fin k → γ) (x : γ) :
    Fin.snoc (Fin.append v xs) x = Fin.append v (Fin.snoc xs x) := by
  exact (Fin.append_snoc v xs x).symm

end FinArithmetic

/-! ### Atomic formula helpers

These relate `AtomicIdx` to `BoundedFormulaInfLegacy` atomic formulas. The term
lemma needs its own `[L.IsRelational]` since it asserts all terms are variables. -/

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- In a relational language, every term is a variable. -/
private theorem Term.eq_var_of_isRelational [L.IsRelational] (t : L.Term α) :
    ∃ x, t = Term.var x := by
  cases t with
  | var x => exact ⟨x, rfl⟩
  | func f => exact (IsEmpty.false f).elim

/-- Builds an L∞ω atomic formula from an `AtomicIdx`. -/
private def atomicFormulaInf (idx : L.AtomicIdx n) :
    BoundedFormulaInfLegacy.{u, v, 0, 0} L (Fin n) 0 :=
  match idx with
  | .eq i j => .equal (.var (.inl i)) (.var (.inl j))
  | .rel R f => .rel R (fun k => .var (.inl (f k)))



omit [Countable (Σ l, L.Relations l)] in
/-- The forward direction of the Karp lemma, generalized to handle bound variables.
BFEquiv at level α implies agreement on formulas of rank ≤ α. -/
private theorem BFEquiv_implies_agree_aux {M N : Type w} [L.Structure M] [L.Structure N]
    (α : Ordinal) {n k : ℕ}
    (φ : BoundedFormulaInfLegacy.{u, v, 0, 0} L (Fin n) k) (hφ : φ.qrank ≤ α)
    (v : Fin n → M) (w : Fin n → N) (xs : Fin k → M) (ys : Fin k → N)
    (hBF : BFEquiv (L := L) α (n + k) (Fin.append v xs) (Fin.append w ys)) :
    (φ.Realize v xs ↔ φ.Realize w ys) := by
  induction φ generalizing α with
  | falsum => simp
  | equal t₁ t₂ =>
    obtain ⟨x₁, rfl⟩ := Term.eq_var_of_isRelational t₁
    obtain ⟨x₂, rfl⟩ := Term.eq_var_of_isRelational t₂
    simp only [BoundedFormulaInfLegacy.realize_equal, Term.realize]
    have hSAT : SameAtomicType (L := L) (Fin.append v xs) (Fin.append w ys) :=
      (BFEquiv.zero _ _).mp (BFEquiv.monotone bot_le hBF)
    rw [sumElim_eq_append_comp v xs, sumElim_eq_append_comp w ys]
    simp only [Function.comp]
    exact hSAT (.eq (finSumFinEquiv x₁) (finSumFinEquiv x₂))
  | rel R ts =>
    simp only [BoundedFormulaInfLegacy.realize_rel]
    have hSAT : SameAtomicType (L := L) (Fin.append v xs) (Fin.append w ys) :=
      (BFEquiv.zero _ _).mp (BFEquiv.monotone bot_le hBF)
    have hvars : ∀ i, ∃ x, ts i = Term.var x := fun i => Term.eq_var_of_isRelational (ts i)
    choose ts_var hts using hvars
    have hM : (RelMap R fun i => (ts i).realize (Sum.elim v xs)) ↔
              RelMap R (Fin.append v xs ∘ (fun i => finSumFinEquiv (ts_var i))) := by
      constructor <;> intro h <;> convert h using 1 <;> ext i <;>
        simp [hts i, sumElim_eq_append_comp v xs, Function.comp]
    have hN : (RelMap R fun i => (ts i).realize (Sum.elim w ys)) ↔
              RelMap R (Fin.append w ys ∘ (fun i => finSumFinEquiv (ts_var i))) := by
      constructor <;> intro h <;> convert h using 1 <;> ext i <;>
        simp [hts i, sumElim_eq_append_comp w ys, Function.comp]
    rw [hM, hN]
    exact hSAT (.rel R (fun i => finSumFinEquiv (ts_var i)))
  | imp φ ψ ihφ ihψ =>
    simp only [BoundedFormulaInfLegacy.realize_imp, BoundedFormulaInfLegacy.qrank_imp] at hφ ⊢
    exact imp_congr
      (ihφ α (le_of_max_le_left hφ) xs ys hBF)
      (ihψ α (le_of_max_le_right hφ) xs ys hBF)
  | all φ ih =>
    simp only [BoundedFormulaInfLegacy.realize_all, BoundedFormulaInfLegacy.qrank_all] at hφ ⊢
    have hSucc : Order.succ φ.qrank ≤ α := by rwa [← Order.succ_eq_add_one] at hφ
    have hBF' := BFEquiv.monotone hSucc hBF
    constructor
    · intro hAll y
      obtain ⟨m, hm⟩ := BFEquiv.back hBF' y
      rw [snoc_append_eq_append_snoc, snoc_append_eq_append_snoc] at hm
      exact (ih φ.qrank le_rfl (Fin.snoc xs m) (Fin.snoc ys y) hm).mp (hAll m)
    · intro hAll x
      obtain ⟨y, hy⟩ := BFEquiv.forth hBF' x
      rw [snoc_append_eq_append_snoc, snoc_append_eq_append_snoc] at hy
      exact (ih φ.qrank le_rfl (Fin.snoc xs x) (Fin.snoc ys y) hy).mpr (hAll y)
  | iSup φs ih =>
    simp only [BoundedFormulaInfLegacy.realize_iSup, BoundedFormulaInfLegacy.qrank_iSup] at hφ ⊢
    exact exists_congr fun i =>
      ih i α (le_trans (Ordinal.le_iSup (fun i => (φs i).qrank) i) hφ) xs ys hBF
  | iInf φs ih =>
    simp only [BoundedFormulaInfLegacy.realize_iInf, BoundedFormulaInfLegacy.qrank_iInf] at hφ ⊢
    exact forall_congr' fun i =>
      ih i α (le_trans (Ordinal.le_iSup (fun i => (φs i).qrank) i) hφ) xs ys hBF

omit [Countable (Σ l, L.Relations l)] in
/-- **Karp Lemma, forward direction**: BF-equivalence at level α implies
agreement on all formulas of quantifier rank ≤ α.

This is a direct corollary of `BFEquiv_implies_agree_aux` with `k = 0` and
`xs = ys = Fin.elim0`. -/
theorem BFEquiv_implies_agreeQR {M N : Type w} [L.Structure M] [L.Structure N]
    (α : Ordinal) {n : ℕ} (a : Fin n → M) (b : Fin n → N)
    (h : BFEquiv (L := L) α n a b)
    (φ : BoundedFormulaInfLegacy.{u, v, 0, 0} L (Fin n) 0) (hφ : φ.qrank ≤ α) :
    (FormulaInfLegacy.Realize φ a ↔ FormulaInfLegacy.Realize φ b) := by
  have ha : Fin.append a (Fin.elim0 : Fin 0 → M) = a := by simp [Fin.append_elim0]
  have hb : Fin.append b (Fin.elim0 : Fin 0 → N) = b := by simp [Fin.append_elim0]
  exact BFEquiv_implies_agree_aux α φ hφ a b Fin.elim0 Fin.elim0 (by rwa [ha, hb])

/-! ### Karp's Theorem at universe w

This section proves Karp's theorem with `LinfEquivW` (index universe `w` matching
the structure universe). -/

section KarpW

variable {M : Type w} [L.Structure M]
variable {N : Type w} [L.Structure N]

/-! #### Infrastructure for KarpW -/

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- Bridge between `Empty` and `Fin 0` for `BoundedFormulaInfLegacy.{u,v,0,w}`. -/
private theorem sentenceInf_realize_iff_mapFreeVarsW
    {M : Type*} [L.Structure M] (φ : BoundedFormulaInfLegacy.{u, v, 0, w} L Empty 0) :
    SentenceInfLegacy.Realize φ M ↔
    FormulaInfLegacy.Realize (φ.mapFreeVars (Empty.elim : Empty → Fin 0)) (Fin.elim0 : Fin 0 → M) := by
  show φ.Realize (Empty.elim : Empty → M) Fin.elim0 ↔
       (φ.mapFreeVars Empty.elim).Realize (Fin.elim0 : Fin 0 → M) Fin.elim0
  rw [BoundedFormulaInfLegacy.realize_mapFreeVars]
  rw [comp_empty_elim Fin.elim0]

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- Bridge between `FormulaInfLegacy.Realize (Fin 0)` and `SentenceInfLegacy.Realize`
for `BoundedFormulaInfLegacy.{u,v,0,w}`. -/
private theorem formulaInf_realize_iff_mapFreeVarsW
    {M : Type*} [L.Structure M] (φ : BoundedFormulaInfLegacy.{u, v, 0, w} L (Fin 0) 0) :
    FormulaInfLegacy.Realize φ (Fin.elim0 : Fin 0 → M) ↔
    SentenceInfLegacy.Realize (φ.mapFreeVars (Fin.elim0 : Fin 0 → Empty)) M := by
  show φ.Realize (Fin.elim0 : Fin 0 → M) Fin.elim0 ↔
       (φ.mapFreeVars Fin.elim0).Realize (Empty.elim : Empty → M) Fin.elim0
  rw [BoundedFormulaInfLegacy.realize_mapFreeVars]
  rw [comp_fin_elim0 Empty.elim]

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- Builds an atomic formula from an `AtomicIdx` at universe `w`. -/
private def atomicFormulaInfW (idx : L.AtomicIdx n) :
    BoundedFormulaInfLegacy.{u, v, 0, w} L (Fin n) 0 :=
  match idx with
  | .eq i j => .equal (.var (.inl i)) (.var (.inl j))
  | .rel R f => .rel R (fun k => .var (.inl (f k)))

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
private theorem realize_atomicFormulaInfW {M : Type*} [L.Structure M]
    (idx : L.AtomicIdx n) (v : Fin n → M) :
    FormulaInfLegacy.Realize (atomicFormulaInfW (L := L) idx :
      BoundedFormulaInfLegacy.{u, v, 0, w} L (Fin n) 0) v ↔ idx.holds v := by
  cases idx with
  | eq i j =>
    simp only [atomicFormulaInfW, FormulaInfLegacy.Realize, BoundedFormulaInfLegacy.Realize, Term.realize,
      Sum.elim_inl, AtomicIdx.holds]
  | rel R f =>
    simp only [atomicFormulaInfW, FormulaInfLegacy.Realize, BoundedFormulaInfLegacy.Realize, Term.realize,
      Sum.elim_inl, AtomicIdx.holds]
    constructor <;> intro h <;> convert h using 1 <;> rfl

/-! #### Forward: PotentialIso → LinfEquivW -/

omit [Countable (Σ l, L.Relations l)] in
/-- Forward Karp at universe w, generalized to tuples. If `(a, b)` is in the PotentialIso
family, then they agree on all `BoundedFormulaInfLegacy.{u,v,0,w}` formulas.

The proof is by structural induction on the formula. The key cases:
- `all`: Use PotentialIso.forth/back to get witnesses for the universal quantifier.
- `iSup`/`iInf`: Straightforward exists_congr/forall_congr with IH. -/
private theorem PotentialIso_implies_agree_aux (P : PotentialIso L M N)
    {n k : ℕ} {a : Fin n → M} {b : Fin n → N} (hab : ⟨n, a, b⟩ ∈ P.family)
    (φ : BoundedFormulaInfLegacy.{u, v, 0, w} L (Fin n) k)
    (xs : Fin k → M) (ys : Fin k → N)
    (hext : ⟨n + k, Fin.append a xs, Fin.append b ys⟩ ∈ P.family) :
    (φ.Realize a xs ↔ φ.Realize b ys) := by
  induction φ generalizing a b with
  | falsum => simp
  | equal t₁ t₂ =>
    obtain ⟨x₁, rfl⟩ := Term.eq_var_of_isRelational t₁
    obtain ⟨x₂, rfl⟩ := Term.eq_var_of_isRelational t₂
    simp only [BoundedFormulaInfLegacy.realize_equal, Term.realize]
    have hSAT : SameAtomicType (L := L) (Fin.append a xs) (Fin.append b ys) :=
      P.compatible _ hext
    rw [sumElim_eq_append_comp a xs, sumElim_eq_append_comp b ys]
    simp only [Function.comp]
    exact hSAT (.eq (finSumFinEquiv x₁) (finSumFinEquiv x₂))
  | rel R ts =>
    simp only [BoundedFormulaInfLegacy.realize_rel]
    have hSAT : SameAtomicType (L := L) (Fin.append a xs) (Fin.append b ys) :=
      P.compatible _ hext
    have hvars : ∀ i, ∃ x, ts i = Term.var x := fun i => Term.eq_var_of_isRelational (ts i)
    choose ts_var hts using hvars
    have hM : (RelMap R fun i => (ts i).realize (Sum.elim a xs)) ↔
              RelMap R (Fin.append a xs ∘ (fun i => finSumFinEquiv (ts_var i))) := by
      constructor <;> intro h <;> convert h using 1 <;> ext i <;>
        simp [hts i, sumElim_eq_append_comp a xs, Function.comp]
    have hN : (RelMap R fun i => (ts i).realize (Sum.elim b ys)) ↔
              RelMap R (Fin.append b ys ∘ (fun i => finSumFinEquiv (ts_var i))) := by
      constructor <;> intro h <;> convert h using 1 <;> ext i <;>
        simp [hts i, sumElim_eq_append_comp b ys, Function.comp]
    rw [hM, hN]
    exact hSAT (.rel R (fun i => finSumFinEquiv (ts_var i)))
  | imp φ ψ ihφ ihψ =>
    simp only [BoundedFormulaInfLegacy.realize_imp]
    exact imp_congr (ihφ hab xs ys hext) (ihψ hab xs ys hext)
  | all φ ih =>
    simp only [BoundedFormulaInfLegacy.realize_all]
    constructor
    · intro hAll y
      obtain ⟨m, hm⟩ := P.back _ hext y
      rw [snoc_append_eq_append_snoc, snoc_append_eq_append_snoc] at hm
      exact (ih hab (Fin.snoc xs m) (Fin.snoc ys y) hm).mp (hAll m)
    · intro hAll x
      obtain ⟨y, hy⟩ := P.forth _ hext x
      rw [snoc_append_eq_append_snoc, snoc_append_eq_append_snoc] at hy
      exact (ih hab (Fin.snoc xs x) (Fin.snoc ys y) hy).mpr (hAll y)
  | iSup φs ih =>
    exact exists_congr fun i => ih i hab xs ys hext
  | iInf φs ih =>
    exact forall_congr' fun i => ih i hab xs ys hext

omit [Countable (Σ l, L.Relations l)] in
/-- Forward direction: PotentialIso implies LinfEquivW. -/
theorem PotentialIso_implies_LinfEquivW (P : PotentialIso L M N) : LinfEquivW L M N := by
  intro φ
  -- Bridge from Empty to Fin 0
  have hφ' := sentenceInf_realize_iff_mapFreeVarsW φ (M := M)
  have hφ'N := sentenceInf_realize_iff_mapFreeVarsW φ (M := N)
  rw [hφ', hφ'N]
  -- Apply the generalized agree lemma with the empty tuple
  have hext : ⟨0 + 0, Fin.append (Fin.elim0 : Fin 0 → M) Fin.elim0,
      Fin.append (Fin.elim0 : Fin 0 → N) Fin.elim0⟩ ∈ P.family := by
    simp only [Fin.eq_elim0]; exact P.empty_mem
  exact PotentialIso_implies_agree_aux P P.empty_mem _ _ _ hext

end KarpW
end Language

end FirstOrder
