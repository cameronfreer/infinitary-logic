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
# Karp's Theorem

This file proves Karp's theorem: two structures are potentially isomorphic if and only
if they are L∞ω-elementarily equivalent.

## Main Results

- `karp_theorem_w`: The canonical Karp theorem (sorry-free). For relational languages,
  potential isomorphism is equivalent to `LinfEquivW` (L∞ω-elementary equivalence with
  index types at universe `w` matching the structure universe).
- `karp_theorem_universe0`: Specialization of `karp_theorem_w` to `Type 0`, where
  `LinfEquivW` and `LinfEquiv` coincide.
- `BFEquiv_implies_agreeQR`: Forward direction of the Karp lemma (sorry-free):
  BF-equivalence at level α implies agreement on all formulas of quantifier rank ≤ α.

## Design Notes

An earlier version of this file included a backward direction `agree_implies_BFEquiv`
and an iff form `BFEquiv_iff_agreeQR` for formulas with `Type 0` index types. The
backward direction had `sorry`s due to a genuine universe obstruction: the forth/back
witnesses require `iInf` indexed by `N : Type w`, but `BoundedFormulaInf.{u,v,0,0}`
only allows `Type 0` index types. The `karp_theorem_w` pipeline (using `LinfEquivW`
with universe-`w` index types) avoids this obstruction entirely, making the old path
redundant. It was removed to eliminate 3 sorry tokens.

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

These relate `AtomicIdx` to `BoundedFormulaInf` atomic formulas. The term
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
    BoundedFormulaInf.{u, v, 0, 0} L (Fin n) 0 :=
  match idx with
  | .eq i j => .equal (.var (.inl i)) (.var (.inl j))
  | .rel R f => .rel R (fun k => .var (.inl (f k)))

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
private theorem qrank_atomicFormulaInf (idx : L.AtomicIdx n) :
    (atomicFormulaInf (L := L) idx).qrank = 0 := by
  cases idx <;> rfl

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
private theorem realize_atomicFormulaInf {M : Type*} [L.Structure M]
    (idx : L.AtomicIdx n) (v : Fin n → M) :
    FormulaInf.Realize (atomicFormulaInf (L := L) idx) v ↔ idx.holds v := by
  cases idx with
  | eq i j =>
    simp only [atomicFormulaInf, FormulaInf.Realize, BoundedFormulaInf.realize_equal,
      Term.realize, Sum.elim_inl, AtomicIdx.holds]
  | rel R f =>
    simp only [atomicFormulaInf, FormulaInf.Realize, BoundedFormulaInf.realize_rel,
      Term.realize, Sum.elim_inl, AtomicIdx.holds]
    constructor <;> intro h <;> convert h using 1

omit [Countable (Σ l, L.Relations l)] in
/-- The forward direction of the Karp lemma, generalized to handle bound variables.
BFEquiv at level α implies agreement on formulas of rank ≤ α. -/
private theorem BFEquiv_implies_agree_aux {M N : Type w} [L.Structure M] [L.Structure N]
    (α : Ordinal) {n k : ℕ}
    (φ : BoundedFormulaInf.{u, v, 0, 0} L (Fin n) k) (hφ : φ.qrank ≤ α)
    (v : Fin n → M) (w : Fin n → N) (xs : Fin k → M) (ys : Fin k → N)
    (hBF : BFEquiv (L := L) α (n + k) (Fin.append v xs) (Fin.append w ys)) :
    (φ.Realize v xs ↔ φ.Realize w ys) := by
  induction φ generalizing α with
  | falsum => simp
  | equal t₁ t₂ =>
    obtain ⟨x₁, rfl⟩ := Term.eq_var_of_isRelational t₁
    obtain ⟨x₂, rfl⟩ := Term.eq_var_of_isRelational t₂
    simp only [BoundedFormulaInf.realize_equal, Term.realize]
    have hSAT : SameAtomicType (L := L) (Fin.append v xs) (Fin.append w ys) :=
      (BFEquiv.zero _ _).mp (BFEquiv.monotone (zero_le _) hBF)
    rw [sumElim_eq_append_comp v xs, sumElim_eq_append_comp w ys]
    simp only [Function.comp]
    exact hSAT (.eq (finSumFinEquiv x₁) (finSumFinEquiv x₂))
  | rel R ts =>
    simp only [BoundedFormulaInf.realize_rel]
    have hSAT : SameAtomicType (L := L) (Fin.append v xs) (Fin.append w ys) :=
      (BFEquiv.zero _ _).mp (BFEquiv.monotone (zero_le _) hBF)
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
    simp only [BoundedFormulaInf.realize_imp, BoundedFormulaInf.qrank_imp] at hφ ⊢
    exact imp_congr
      (ihφ α (le_of_max_le_left hφ) xs ys hBF)
      (ihψ α (le_of_max_le_right hφ) xs ys hBF)
  | all φ ih =>
    simp only [BoundedFormulaInf.realize_all, BoundedFormulaInf.qrank_all] at hφ ⊢
    have hSucc : Order.succ φ.qrank ≤ α := by rwa [Ordinal.add_one_eq_succ] at hφ
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
    simp only [BoundedFormulaInf.realize_iSup, BoundedFormulaInf.qrank_iSup] at hφ ⊢
    exact exists_congr fun i =>
      ih i α (le_trans (Ordinal.le_iSup (fun i => (φs i).qrank) i) hφ) xs ys hBF
  | iInf φs ih =>
    simp only [BoundedFormulaInf.realize_iInf, BoundedFormulaInf.qrank_iInf] at hφ ⊢
    exact forall_congr' fun i =>
      ih i α (le_trans (Ordinal.le_iSup (fun i => (φs i).qrank) i) hφ) xs ys hBF

omit [Countable (Σ l, L.Relations l)] in
/-- **Karp Lemma, forward direction** (sorry-free): BF-equivalence at level α implies
agreement on all formulas of quantifier rank ≤ α.

This is a direct corollary of `BFEquiv_implies_agree_aux` with `k = 0` and
`xs = ys = Fin.elim0`. -/
theorem BFEquiv_implies_agreeQR {M N : Type w} [L.Structure M] [L.Structure N]
    (α : Ordinal) {n : ℕ} (a : Fin n → M) (b : Fin n → N)
    (h : BFEquiv (L := L) α n a b)
    (φ : BoundedFormulaInf.{u, v, 0, 0} L (Fin n) 0) (hφ : φ.qrank ≤ α) :
    (FormulaInf.Realize φ a ↔ FormulaInf.Realize φ b) := by
  have ha : Fin.append a (Fin.elim0 : Fin 0 → M) = a :=
    funext fun ⟨i, hi⟩ => by simp [Fin.append, Fin.addCases, show i < n from hi]
  have hb : Fin.append b (Fin.elim0 : Fin 0 → N) = b :=
    funext fun ⟨i, hi⟩ => by simp [Fin.append, Fin.addCases, show i < n from hi]
  exact BFEquiv_implies_agree_aux α φ hφ a b Fin.elim0 Fin.elim0 (by rwa [ha, hb])

/-! ### Karp's Theorem at universe w (sorry-free)

This section proves Karp's theorem with `LinfEquivW` (index universe `w` matching
the structure universe). Both directions are fully proved (no sorry). -/

section KarpW

variable {M : Type w} [L.Structure M]
variable {N : Type w} [L.Structure N]

/-! #### Infrastructure for KarpW -/

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- Bridge between `Empty` and `Fin 0` for `BoundedFormulaInf.{u,v,0,w}`. -/
private theorem sentenceInf_realize_iff_mapFreeVarsW
    {M : Type*} [L.Structure M] (φ : BoundedFormulaInf.{u, v, 0, w} L Empty 0) :
    SentenceInf.Realize φ M ↔
    FormulaInf.Realize (φ.mapFreeVars (Empty.elim : Empty → Fin 0)) (Fin.elim0 : Fin 0 → M) := by
  show φ.Realize (Empty.elim : Empty → M) Fin.elim0 ↔
       (φ.mapFreeVars Empty.elim).Realize (Fin.elim0 : Fin 0 → M) Fin.elim0
  rw [BoundedFormulaInf.realize_mapFreeVars]
  have h : (Fin.elim0 : Fin 0 → M) ∘ (Empty.elim : Empty → Fin 0) = (Empty.elim : Empty → M) :=
    funext fun x => x.elim
  rw [h]

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- Bridge between `FormulaInf.Realize (Fin 0)` and `SentenceInf.Realize`
for `BoundedFormulaInf.{u,v,0,w}`. -/
private theorem formulaInf_realize_iff_mapFreeVarsW
    {M : Type*} [L.Structure M] (φ : BoundedFormulaInf.{u, v, 0, w} L (Fin 0) 0) :
    FormulaInf.Realize φ (Fin.elim0 : Fin 0 → M) ↔
    SentenceInf.Realize (φ.mapFreeVars (Fin.elim0 : Fin 0 → Empty)) M := by
  show φ.Realize (Fin.elim0 : Fin 0 → M) Fin.elim0 ↔
       (φ.mapFreeVars Fin.elim0).Realize (Empty.elim : Empty → M) Fin.elim0
  rw [BoundedFormulaInf.realize_mapFreeVars]
  have h : (Empty.elim : Empty → M) ∘ (Fin.elim0 : Fin 0 → Empty) = (Fin.elim0 : Fin 0 → M) :=
    funext fun x => Fin.elim0 x
  rw [h]

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- Builds an atomic formula from an `AtomicIdx` at universe `w`. -/
private def atomicFormulaInfW (idx : L.AtomicIdx n) :
    BoundedFormulaInf.{u, v, 0, w} L (Fin n) 0 :=
  match idx with
  | .eq i j => .equal (.var (.inl i)) (.var (.inl j))
  | .rel R f => .rel R (fun k => .var (.inl (f k)))

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
private theorem realize_atomicFormulaInfW {M : Type*} [L.Structure M]
    (idx : L.AtomicIdx n) (v : Fin n → M) :
    FormulaInf.Realize (atomicFormulaInfW (L := L) idx :
      BoundedFormulaInf.{u, v, 0, w} L (Fin n) 0) v ↔ idx.holds v := by
  cases idx with
  | eq i j =>
    simp only [atomicFormulaInfW, FormulaInf.Realize, BoundedFormulaInf.Realize, Term.realize,
      Sum.elim_inl, AtomicIdx.holds]
  | rel R f =>
    simp only [atomicFormulaInfW, FormulaInf.Realize, BoundedFormulaInf.Realize, Term.realize,
      Sum.elim_inl, AtomicIdx.holds]
    constructor <;> intro h <;> convert h using 1

/-! #### Forward: PotentialIso → LinfEquivW -/

omit [Countable (Σ l, L.Relations l)] in
/-- Forward Karp at universe w, generalized to tuples. If `(a, b)` is in the PotentialIso
family, then they agree on all `BoundedFormulaInf.{u,v,0,w}` formulas.

The proof is by structural induction on the formula. The key cases:
- `all`: Use PotentialIso.forth/back to get witnesses for the universal quantifier.
- `iSup`/`iInf`: Straightforward exists_congr/forall_congr with IH. -/
private theorem PotentialIso_implies_agree_aux (P : PotentialIso L M N)
    {n k : ℕ} {a : Fin n → M} {b : Fin n → N} (hab : ⟨n, a, b⟩ ∈ P.family)
    (φ : BoundedFormulaInf.{u, v, 0, w} L (Fin n) k)
    (xs : Fin k → M) (ys : Fin k → N)
    (hext : ⟨n + k, Fin.append a xs, Fin.append b ys⟩ ∈ P.family) :
    (φ.Realize a xs ↔ φ.Realize b ys) := by
  induction φ generalizing a b with
  | falsum => simp
  | equal t₁ t₂ =>
    obtain ⟨x₁, rfl⟩ := Term.eq_var_of_isRelational t₁
    obtain ⟨x₂, rfl⟩ := Term.eq_var_of_isRelational t₂
    simp only [BoundedFormulaInf.realize_equal, Term.realize]
    have hSAT : SameAtomicType (L := L) (Fin.append a xs) (Fin.append b ys) :=
      P.compatible _ hext
    rw [sumElim_eq_append_comp a xs, sumElim_eq_append_comp b ys]
    simp only [Function.comp]
    exact hSAT (.eq (finSumFinEquiv x₁) (finSumFinEquiv x₂))
  | rel R ts =>
    simp only [BoundedFormulaInf.realize_rel]
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
    simp only [BoundedFormulaInf.realize_imp]
    exact imp_congr (ihφ hab xs ys hext) (ihψ hab xs ys hext)
  | all φ ih =>
    simp only [BoundedFormulaInf.realize_all]
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
    constructor
    · rintro ⟨i, hi⟩; exact ⟨i, (ih i hab xs ys hext).mp hi⟩
    · rintro ⟨i, hi⟩; exact ⟨i, (ih i hab xs ys hext).mpr hi⟩
  | iInf φs ih =>
    constructor
    · intro h i; exact (ih i hab xs ys hext).mp (h i)
    · intro h i; exact (ih i hab xs ys hext).mpr (h i)

omit [Countable (Σ l, L.Relations l)] in
/-- Forward direction: PotentialIso implies LinfEquivW (sorry-free). -/
theorem PotentialIso_implies_LinfEquivW (P : PotentialIso L M N) : LinfEquivW L M N := by
  intro φ
  -- Bridge from Empty to Fin 0
  have hφ' := sentenceInf_realize_iff_mapFreeVarsW φ (M := M)
  have hφ'N := sentenceInf_realize_iff_mapFreeVarsW φ (M := N)
  rw [hφ', hφ'N]
  -- Apply the generalized agree lemma with the empty tuple
  have hext : ⟨0 + 0, Fin.append (Fin.elim0 : Fin 0 → M) Fin.elim0,
      Fin.append (Fin.elim0 : Fin 0 → N) Fin.elim0⟩ ∈ P.family := by
    have ha : Fin.append (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → M) = Fin.elim0 :=
      funext fun x => Fin.elim0 x
    have hb : Fin.append (Fin.elim0 : Fin 0 → N) (Fin.elim0 : Fin 0 → N) = Fin.elim0 :=
      funext fun x => Fin.elim0 x
    simp only [ha, hb]; exact P.empty_mem
  exact PotentialIso_implies_agree_aux P P.empty_mem _ _ _ hext

/-! #### Backward: LinfEquivW → PotentialIso -/

omit [Countable (Σ l, L.Relations l)] in
/-- Backward direction: LinfEquivW implies PotentialIso (sorry-free).

The family consists of tuples `(n, a, b)` such that `a` and `b` agree on all
`BoundedFormulaInf.{u,v,0,w}` formulas with `Fin n` free variables. The forth/back
properties use a contradiction argument: if no witness exists, we can build a separating
formula using `iInf` indexed by `N : Type w` (which requires `uι = w`). -/
theorem LinfEquivW_implies_potentialIso (h : LinfEquivW L M N) :
    Nonempty (PotentialIso L M N) := by
  refine ⟨{
    family := { p | ∀ φ : BoundedFormulaInf.{u, v, 0, w} L (Fin p.1) 0,
      FormulaInf.Realize φ p.2.1 ↔ FormulaInf.Realize φ p.2.2 }
    empty_mem := ?_
    compatible := ?_
    forth := ?_
    back := ?_
  }⟩
  · -- empty_mem: from h via Empty ↔ Fin 0 bridge
    intro φ
    have hφ := formulaInf_realize_iff_mapFreeVarsW φ (M := M)
    have hφN := formulaInf_realize_iff_mapFreeVarsW φ (M := N)
    exact hφ.trans ((h _).trans hφN.symm)
  · -- compatible: atomic formulas distinguish atomic type
    intro p hp idx
    exact (realize_atomicFormulaInfW idx p.2.1).symm.trans
      ((hp _).trans (realize_atomicFormulaInfW idx p.2.2))
  · -- forth: by contradiction using iInf indexed by N : Type w
    intro ⟨n, a, b⟩ hfamily m
    simp only [Set.mem_setOf_eq] at hfamily ⊢
    by_contra h_no
    push_neg at h_no
    -- For each n' : N, choose a separating formula
    choose φ_bad h_bad using h_no
    -- For each n', get a formula true for (snoc a m) but false for (snoc b n')
    -- (or vice versa). WLOG, choose the direction.
    have h_sep : ∀ n' : N, ∃ ψ : BoundedFormulaInf.{u, v, 0, w} L (Fin (n + 1)) 0,
        FormulaInf.Realize ψ (Fin.snoc a m) ∧ ¬ FormulaInf.Realize ψ (Fin.snoc b n') := by
      intro n'
      -- h_bad n' : (Realize .. (snoc a m) ∧ ¬ Realize .. (snoc b n')) ∨
      --            (¬ Realize .. (snoc a m) ∧ Realize .. (snoc b n'))
      rcases h_bad n' with ⟨hM, hN⟩ | ⟨hM, hN⟩
      · exact ⟨φ_bad n', hM, hN⟩
      · -- Use negation: ¬Realize at (snoc a m), Realize at (snoc b n')
        refine ⟨(φ_bad n').not, (BoundedFormulaInf.realize_not _).mpr hM, fun hc => ?_⟩
        exact absurd hN ((BoundedFormulaInf.realize_not _).mp hc)
    choose ψ hψ using h_sep
    -- Build: χ := existsLastVarInf (iInf (fun n' : N => ψ n'))
    -- The iInf is indexed by N : Type w — this is why we need uι = w!
    let conj : BoundedFormulaInf.{u, v, 0, w} L (Fin (n + 1)) 0 :=
      .iInf (ι := N) ψ
    let χ : BoundedFormulaInf.{u, v, 0, w} L (Fin n) 0 :=
      BoundedFormulaInf.existsLastVarInf conj
    -- χ is true for a: witness m satisfies all ψ n'
    have hM : FormulaInf.Realize χ a := by
      rw [BoundedFormulaInf.realize_existsLastVarInf]
      refine ⟨m, ?_⟩
      show ∀ n', FormulaInf.Realize (ψ n') (Fin.snoc a m)
      exact fun n' => (hψ n').1
    -- χ is false for b: for any x, ψ (x) fails at n' = x
    have hN : ¬ FormulaInf.Realize χ b := by
      rw [BoundedFormulaInf.realize_existsLastVarInf]
      rintro ⟨x, hx⟩
      have hx' : ∀ n', FormulaInf.Realize (ψ n') (Fin.snoc b x) := hx
      exact (hψ x).2 (hx' x)
    -- Contradiction: a and b should agree on χ
    exact hN ((hfamily χ).mp hM)
  · -- back: symmetric argument
    intro ⟨n, a, b⟩ hfamily n'
    simp only [Set.mem_setOf_eq] at hfamily ⊢
    by_contra h_no
    push_neg at h_no
    choose φ_bad h_bad using h_no
    have h_sep : ∀ m : M, ∃ ψ : BoundedFormulaInf.{u, v, 0, w} L (Fin (n + 1)) 0,
        FormulaInf.Realize ψ (Fin.snoc b n') ∧ ¬ FormulaInf.Realize ψ (Fin.snoc a m) := by
      intro m
      -- h_bad m : (Realize .. (snoc a m) ∧ ¬ Realize .. (snoc b n')) ∨
      --           (¬ Realize .. (snoc a m) ∧ Realize .. (snoc b n'))
      rcases h_bad m with ⟨hM, hN⟩ | ⟨hM, hN⟩
      · -- Case: Realize (φ_bad m) (snoc a m) ∧ ¬ Realize (φ_bad m) (snoc b n')
        -- Use negation of φ_bad m: true at (snoc b n') and false at (snoc a m)
        refine ⟨(φ_bad m).not, (BoundedFormulaInf.realize_not _).mpr hN, fun hc => ?_⟩
        exact absurd hM ((BoundedFormulaInf.realize_not _).mp hc)
      · -- Case: ¬ Realize (φ_bad m) (snoc a m) ∧ Realize (φ_bad m) (snoc b n')
        exact ⟨φ_bad m, hN, hM⟩
    choose ψ hψ using h_sep
    let conj : BoundedFormulaInf.{u, v, 0, w} L (Fin (n + 1)) 0 :=
      .iInf (ι := M) ψ
    let χ : BoundedFormulaInf.{u, v, 0, w} L (Fin n) 0 :=
      BoundedFormulaInf.existsLastVarInf conj
    have hN : FormulaInf.Realize χ b := by
      rw [BoundedFormulaInf.realize_existsLastVarInf]
      refine ⟨n', ?_⟩
      show ∀ m, FormulaInf.Realize (ψ m) (Fin.snoc b n')
      exact fun m => (hψ m).1
    have hM : ¬ FormulaInf.Realize χ a := by
      rw [BoundedFormulaInf.realize_existsLastVarInf]
      rintro ⟨x, hx⟩
      have hx' : ∀ m, FormulaInf.Realize (ψ m) (Fin.snoc a x) := hx
      exact (hψ x).2 (hx' x)
    exact hM ((hfamily χ).mpr hN)

omit [Countable (Σ l, L.Relations l)] in
/-- **Karp's Theorem** (sorry-free, KK04 Theorem 1.2.1): For relational languages, two
structures are potentially isomorphic if and only if they are L∞ω-elementarily equivalent
(with index types at universe `w` matching the structure universe).

Both directions are fully proved:
- Forward: structural induction on formulas, using PotentialIso.forth/back for `all`.
- Backward: direct construction of PotentialIso family from formula agreement, using
  `iInf` indexed by `N : Type w` to build separating formulas (requires `uι = w`). -/
@[blueprint "thm:karp-theorem"
  (title := /-- Karp's theorem -/)
  (statement := /-- $M$ and $N$ admit a potential isomorphism if and only if they are
    $L_{\infty\omega}^w$-equivalent (satisfy the same $L_{\infty\omega}$ sentences
    with index types in universe $w$). -/)
  (proof := /-- Forward: a potential isomorphism witnesses agreement on all
    $L_{\infty\omega}$ sentences by induction on formula complexity. Backward: BFEquiv
    at all ordinals gives a potential isomorphism via the game-tree family. -/)
  (proofUses := ["def:potential-iso", "def:linf-equiv"])]
theorem karp_theorem_w :
    Nonempty (PotentialIso L M N) ↔ LinfEquivW L M N :=
  ⟨fun ⟨P⟩ => PotentialIso_implies_LinfEquivW P,
   LinfEquivW_implies_potentialIso⟩

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- `LinfEquivW` implies `LinfEquiv`: universe-correct equivalence implies the standard one.
This follows from `liftUI` which embeds `BoundedFormulaInf.{u,v,0,0}` into
`BoundedFormulaInf.{u,v,0,w}`. -/
theorem LinfEquivW_implies_LinfEquiv (h : LinfEquivW L M N) : LinfEquiv L M N := by
  intro φ
  -- liftUI sends φ : BoundedFormulaInf.{u,v,0,0} to BoundedFormulaInf.{u,v,0,w}
  let lφ : BoundedFormulaInf.{u, v, 0, w} L Empty 0 := BoundedFormulaInf.liftUI φ
  -- SentenceInf.Realize unfolds to Realize Empty.elim Fin.elim0
  show φ.Realize (Empty.elim : Empty → M) Fin.elim0 ↔
       φ.Realize (Empty.elim : Empty → N) Fin.elim0
  have hM : lφ.Realize (Empty.elim : Empty → M) Fin.elim0 ↔
            φ.Realize (Empty.elim : Empty → M) Fin.elim0 :=
    BoundedFormulaInf.realize_liftUI φ _ _
  have hN : lφ.Realize (Empty.elim : Empty → N) Fin.elim0 ↔
            φ.Realize (Empty.elim : Empty → N) Fin.elim0 :=
    BoundedFormulaInf.realize_liftUI φ _ _
  exact hM.symm.trans ((h lφ).trans hN)

omit [Countable (Σ l, L.Relations l)] in
/-- **Forward direction of Karp's theorem** (sorry-free): PotentialIso → LinfEquiv.

This composes `PotentialIso_implies_LinfEquivW` with `LinfEquivW_implies_LinfEquiv`
to get the standard `LinfEquiv` (with `Ordinal.{0}` index types) from a PotentialIso. -/
theorem PotentialIso_implies_LinfEquiv (P : PotentialIso L M N) : LinfEquiv L M N :=
  LinfEquivW_implies_LinfEquiv (PotentialIso_implies_LinfEquivW P)

omit [Countable (Σ l, L.Relations l)] in
/-- **Forward direction of Karp's theorem at all universes** (sorry-free):
Potential isomorphism implies L∞ω-elementary equivalence. -/
theorem karp_theorem_forward :
    Nonempty (PotentialIso L M N) → LinfEquivW L M N :=
  fun ⟨P⟩ => PotentialIso_implies_LinfEquivW P

end KarpW

omit [Countable (Σ l, L.Relations l)] in
/-- **Karp's Theorem at universe 0** (sorry-free).

This is `karp_theorem_w` specialized to `M N : Type` (i.e., `Type 0`). At universe 0,
`LinfEquivW` and `LinfEquiv` coincide (both use `BoundedFormulaInf.{u,v,0,0}`). -/
theorem karp_theorem_universe0 {M N : Type} [L.Structure M] [L.Structure N] :
    Nonempty (PotentialIso L M N) ↔ LinfEquiv L M N :=
  karp_theorem_w

end Language

end FirstOrder
