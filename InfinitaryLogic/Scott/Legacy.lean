/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Scott.Code
import InfinitaryLogic.Scott.Height
import InfinitaryLogic.Karp.Theorem
import InfinitaryLogic.Lomega1omega.Embedding
import InfinitaryLogic.Lomega1omega.Theory

/-!
# Legacy (Sorry-Tainted) Scott Pipeline

This file contains the unconditional Scott pipeline declarations that transitively depend
on `agree_codes_implies_BFEquiv` (Code.lean, genuine sorry). These declarations are
superseded by the sorry-free conditional pipeline (`_of` variants) in `Sentence.lean`,
`Height.lean`, `Rank.lean`, `CountingModels.lean`, and `CountableCorollary.lean`.

All 28 declarations here are retained for historical reference. The 3 declarations that
directly contain `sorry` are:
1. `agree_codes_implies_BFEquiv` — FormulaCode agreement does not imply BFEquiv
2. `scottRank_le_implies_stabilizesCompletely` — β > α gap
3. `scottRank_le_implies_stabilizesCompletely_of` — β > α gap (independent of Code.lean)

## Import Note

This file is NOT imported by `InfinitaryLogic.Basic`. It is compiled separately via
`InfinitaryLogic.lean` (the root module). The core library builds with zero sorry warnings.
-/

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable [Countable (Σ l, L.Relations l)]

open FirstOrder Structure Fin Ordinal BoundedFormulaω

/-! ### Code-Based Bridge (from Code.lean)

The following declarations depend on `agree_codes_implies_BFEquiv` (genuine sorry).
They are NOT used by the active conditional pipeline (`_of` variants). -/

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

/-! ### Legacy Stabilization Pipeline (from Sentence.lean)

These declarations use the Code-based bridge to establish stabilization below ω₁.
The conditional pipeline (`CountableRefinementHypothesis` + `_of` variants) provides
a sorry-free alternative. -/

/-- **Legacy (Code-based)**: The set of ordinals α < ω₁ where BFEquiv α ↔ BFEquiv (succ α)
fails for some (N, b) is countable.

**Prefer**: `CountableRefinementHypothesis` + `per_tuple_stabilization_below_omega1_of`.

**Trust boundary**: transits through `agree_codes_implies_BFEquiv` (sorry in Code.lean). -/
theorem countable_refinement_steps
    {M : Type w} [L.Structure M] [Countable M]
    (n : ℕ) (a : Fin n → M) :
    Set.Countable {α : Ordinal.{0} | α < Ordinal.omega 1 ∧
      ∃ (N : Type w) (_ : L.Structure N) (_ : Countable N) (b : Fin n → N),
        BFEquiv (L := L) α n a b ∧ ¬BFEquiv (L := L) (Order.succ α) n a b} := by
  have hSep : ∀ α : Ordinal.{0}, α ∈ ({α : Ordinal.{0} | α < Ordinal.omega 1 ∧
      ∃ (N : Type w) (_ : L.Structure N) (_ : Countable N) (b : Fin n → N),
        BFEquiv (L := L) α n a b ∧ ¬BFEquiv (L := L) (Order.succ α) n a b}) →
      ∃ c : FormulaCode L n, (c.toFormulaω).qrank = Order.succ α := by
    intro α ⟨hα_lt, N, instN, instCN, b, hBF, hNotBF⟩
    have hsucc_lt : Order.succ α < Ordinal.omega 1 :=
      Order.IsSuccLimit.succ_lt (Cardinal.isSuccLimit_omega 1) hα_lt
    letI := instN; letI := instCN
    obtain ⟨c, hc_qrank, hc_sep⟩ := exists_separating_code a b α hα_lt hsucc_lt hBF hNotBF
    refine ⟨c, le_antisymm hc_qrank (Order.succ_le_of_lt ?_)⟩
    by_contra h; push_neg at h
    exact hc_sep (BFEquiv_implies_agree_formulas_omega a b α hα_lt hBF c.toFormulaω h)
  choose f hf using hSep
  apply Countable.to_set
  exact Function.Injective.countable
    (f := fun (x : {α : Ordinal.{0} | _}) => f x.1 x.2)
    (fun ⟨α₁, hα₁⟩ ⟨α₂, hα₂⟩ heq => by
      simp only at heq
      have h1 := hf α₁ hα₁
      have h2 := hf α₂ hα₂
      rw [heq] at h1; rw [h1] at h2
      exact Subtype.ext (Order.succ_injective h2))

/-- **Legacy (Code-based)**: Per-tuple stabilization.

**Prefer**: `per_tuple_stabilization_below_omega1_of` (sorry-free conditional on
`CountableRefinementHypothesis`).

**Trust boundary**: depends on `agree_codes_implies_BFEquiv` via `countable_refinement_steps`. -/
theorem per_tuple_stabilization_below_omega1
    {M : Type w} [L.Structure M] [Countable M]
    (n : ℕ) (a : Fin n → M) :
    ∃ γ < (Ordinal.omega 1 : Ordinal.{0}),
      ∀ α, γ ≤ α → α < Ordinal.omega 1 → Order.succ α < Ordinal.omega 1 →
        ∀ (N : Type w) [L.Structure N] [Countable N] (b : Fin n → N),
          (BFEquiv (L := L) α n a b ↔ BFEquiv (L := L) (Order.succ α) n a b) := by
  by_cases hAllHold : ∀ β < (Ordinal.omega 1 : Ordinal.{0}),
      ∀ (N : Type w) (instN : L.Structure N) (instCN : Countable N) (b : Fin n → N),
        BFEquiv (L := L) β n a b
  · -- BFEquiv holds everywhere: iff trivially true
    exact ⟨0, Ordinal.omega_pos 1, fun α _ hα_lt hsucc_lt N instN instCN b =>
      ⟨fun _ => hAllHold (Order.succ α) hsucc_lt N instN instCN b, BFEquiv.of_succ⟩⟩
  · -- BFEquiv fails for some (N, b) at some level < ω₁
    push_neg at hAllHold
    obtain ⟨β₀, hβ₀_lt, N₀, instN₀, instCN₀, b₀, hβ₀_fail⟩ := hAllHold
    -- The refinement set R is countable by `countable_refinement_steps`
    have hR := countable_refinement_steps (L := L) n a
    -- R is a countable set of ordinals below ω₁
    -- If R is empty, BFEquiv never refines, so it's already stable at 0
    by_cases hRne : ({α : Ordinal.{0} | α < Ordinal.omega 1 ∧
        ∃ (N : Type w) (_ : L.Structure N) (_ : Countable N) (b : Fin n → N),
          BFEquiv (L := L) α n a b ∧ ¬BFEquiv (L := L) (Order.succ α) n a b}).Nonempty
    · -- R is nonempty: enumerate and take supremum
      haveI := hR.to_subtype
      haveI := hRne.to_subtype
      obtain ⟨enum, henum⟩ := exists_surjective_nat
        ({α : Ordinal.{0} | α < Ordinal.omega 1 ∧
          ∃ (N : Type w) (_ : L.Structure N) (_ : Countable N) (b : Fin n → N),
            BFEquiv (L := L) α n a b ∧ ¬BFEquiv (L := L) (Order.succ α) n a b})
      -- Define the sequence of ordinals
      let seq : ℕ → Ordinal.{0} := fun k => (enum k).1
      -- Each element is < ω₁
      have hseq_lt : ∀ k, seq k < Ordinal.omega 1 := fun k => (enum k).2.1
      -- The supremum is < ω₁ (by regularity)
      have hseq_lt' : ∀ k, seq k < (Cardinal.aleph 1).ord := by
        intro k; rw [Cardinal.ord_aleph]; exact hseq_lt k
      have hsup_lt := Ordinal.iSup_sequence_lt_omega_one seq hseq_lt'
      rw [Cardinal.ord_aleph] at hsup_lt
      -- Take γ = Order.succ (iSup seq)
      have hSuccSupLt : Order.succ (⨆ k, seq k) < Ordinal.omega 1 :=
        Order.IsSuccLimit.succ_lt (Cardinal.isSuccLimit_omega 1) hsup_lt
      refine ⟨Order.succ (⨆ k, seq k), hSuccSupLt, fun α hα hα_lt hsucc_lt N instN instCN b => ?_⟩
      constructor
      · intro hBF
        -- Show ¬(BFEquiv α ∧ ¬BFEquiv (succ α)): α is NOT a refinement step
        -- because α ≥ γ = succ(sup R), so α > every element of R
        by_contra hNot
        -- If BFEquiv α but ¬BFEquiv (succ α), then α ∈ R
        have hαR : α ∈ ({α : Ordinal.{0} | α < Ordinal.omega 1 ∧
            ∃ (N : Type w) (_ : L.Structure N) (_ : Countable N) (b : Fin n → N),
              BFEquiv (L := L) α n a b ∧ ¬BFEquiv (L := L) (Order.succ α) n a b}) :=
          ⟨hα_lt, N, instN, instCN, b, hBF, hNot⟩
        -- So α ≤ sup(seq)
        obtain ⟨k, hk⟩ := henum ⟨α, hαR⟩
        have hα_eq : seq k = α := congr_arg Subtype.val hk
        have hBdd : BddAbove (Set.range seq) :=
          ⟨Ordinal.omega 1, fun x ⟨k, hk⟩ => hk ▸ le_of_lt (hseq_lt k)⟩
        have hα_le_sup : α ≤ ⨆ k, seq k := hα_eq ▸ le_ciSup hBdd k
        -- But α ≥ succ(sup R) > sup R — contradiction
        exact absurd (lt_of_lt_of_le (Order.lt_succ (⨆ k, seq k)) (le_trans hα hα_le_sup))
          (lt_irrefl _)
      · exact BFEquiv.of_succ
    · -- R is empty: for all α < ω₁, BFEquiv α → BFEquiv (succ α)
      rw [Set.not_nonempty_iff_eq_empty] at hRne
      refine ⟨0, Ordinal.omega_pos 1, fun α _ hα_lt hsucc_lt N instN instCN b => ?_⟩
      constructor
      · intro hBF
        by_contra hNot
        have hmem : α ∈ ({α : Ordinal.{0} | α < Ordinal.omega 1 ∧
            ∃ (N : Type w) (_ : L.Structure N) (_ : Countable N) (b : Fin n → N),
              BFEquiv (L := L) α n a b ∧ ¬BFEquiv (L := L) (Order.succ α) n a b}) :=
          ⟨hα_lt, N, instN, instCN, b, hBF, hNot⟩
        rw [hRne] at hmem
        exact hmem.elim
      · exact BFEquiv.of_succ

/-- **Legacy (Code-based)**: Complete stabilization.

**Prefer**: `exists_complete_stabilization_of` (sorry-free conditional on
`CountableRefinementHypothesis`).

**Trust boundary**: inherits from `per_tuple_stabilization_below_omega1` →
`countable_refinement_steps` → `agree_codes_implies_BFEquiv`. -/
theorem exists_complete_stabilization (M : Type w) [L.Structure M] [Countable M] :
    ∃ α < (Ordinal.omega 1 : Ordinal.{0}), StabilizesCompletely (L := L) M α := by
  have hTuple : ∀ (t : Σ n, Fin n → M),
      ∃ γ < (Ordinal.omega 1 : Ordinal.{0}),
        ∀ α, γ ≤ α → α < Ordinal.omega 1 → Order.succ α < Ordinal.omega 1 →
          ∀ (N : Type w) [L.Structure N] [Countable N] (b : Fin t.1 → N),
            (BFEquiv (L := L) α t.1 t.2 b ↔ BFEquiv (L := L) (Order.succ α) t.1 t.2 b) :=
    fun ⟨n, a⟩ => per_tuple_stabilization_below_omega1 n a
  -- Step 2: Extract per-tuple bound ordinals
  choose boundOrd hboundOrd_lt hboundOrd_spec using hTuple
  -- Step 3: Enumerate all tuples and take supremum
  haveI : Countable (Σ n, Fin n → M) := inferInstance
  by_cases hM_nonempty : Nonempty M
  swap
  · -- M is empty: complete stabilization is trivial
    haveI : IsEmpty M := not_nonempty_iff.mp hM_nonempty
    use 1
    constructor
    · -- 1 < ω₁
      calc (1 : Ordinal) < ω := Ordinal.one_lt_omega0
        _ ≤ Ordinal.omega 1 := Ordinal.omega0_le_omega 1
    · intro n N _ _ a b
      cases n with
      | zero =>
        constructor
        · intro hBF
          -- Since M is empty: a, b are Fin.elim0.
          -- BFEquiv 1 0 means BFEquiv (succ 0), which requires
          -- back: ∀ n' : N, ∃ m : M, ... For empty M this forces N empty.
          have h1eq : (1 : Ordinal) = Order.succ 0 := by
            rw [← Ordinal.add_one_eq_succ]; simp
          rw [h1eq] at hBF ⊢
          rw [BFEquiv.succ] at hBF
          rw [BFEquiv.succ]
          refine ⟨(BFEquiv.succ 0 a b).mpr hBF, fun m => isEmptyElim m, fun n' => ?_⟩
          exact isEmptyElim (hBF.2.2 n').choose
        · exact BFEquiv.of_succ
      | succ k => exact (IsEmpty.false (a 0)).elim
  haveI : Nonempty M := hM_nonempty
  haveI : Nonempty (Σ n, Fin n → M) := ⟨⟨0, Fin.elim0⟩⟩
  obtain ⟨enumTuples, hTuples_surj⟩ := exists_surjective_nat (Σ n, Fin n → M)
  let globalStab : Ordinal.{0} := ⨆ k, boundOrd (enumTuples k) + 1
  have hGlobalLt : globalStab < Ordinal.omega 1 := by
    have hEachLt : ∀ k, boundOrd (enumTuples k) + 1 < (Cardinal.aleph 1).ord := by
      intro k; rw [Cardinal.ord_aleph]
      exact Order.IsSuccLimit.succ_lt (Cardinal.isSuccLimit_omega 1)
        (hboundOrd_lt (enumTuples k))
    have hsup := Ordinal.iSup_sequence_lt_omega_one
      (fun k => boundOrd (enumTuples k) + 1) hEachLt
    rw [Cardinal.ord_aleph] at hsup
    exact hsup
  have hSuccGlobalLt : Order.succ globalStab < Ordinal.omega 1 :=
    Order.IsSuccLimit.succ_lt (Cardinal.isSuccLimit_omega 1) hGlobalLt
  use globalStab, hGlobalLt
  intro n N _ _ a b
  obtain ⟨k, hk⟩ := hTuples_surj ⟨n, a⟩
  have hBdd : BddAbove (Set.range fun k => boundOrd (enumTuples k) + 1) :=
    ⟨Ordinal.omega 1, fun _ ⟨m, hm⟩ => hm ▸ le_of_lt
      (Order.IsSuccLimit.succ_lt (Cardinal.isSuccLimit_omega 1)
        (hboundOrd_lt (enumTuples m)))⟩
  have hk_le : boundOrd ⟨n, a⟩ + 1 ≤ globalStab := by
    have h := le_ciSup hBdd k
    simp only [hk] at h
    exact h
  have hbound_le : boundOrd ⟨n, a⟩ ≤ globalStab :=
    le_trans (Order.le_succ _) hk_le
  exact hboundOrd_spec ⟨n, a⟩ globalStab hbound_le hGlobalLt hSuccGlobalLt N b

/-! ### Unconditional Scott Sentence Theorems (from Sentence.lean)

These are the non-`_of` theorems that depend on `exists_complete_stabilization`. -/

/-- For any countable structure M in a relational countable language, there exists an ordinal
α < ω₁ such that BF-equivalence at level α (with the empty tuple) characterizes isomorphism
with M among countable structures.

**Trust boundary**: inherits sorry from `exists_complete_stabilization`. -/
theorem exists_stabilization (M : Type w) [L.Structure M] [Countable M] :
    ∃ α < (Ordinal.omega 1 : Ordinal.{0}), StabilizesAt (L := L) M α := by
  obtain ⟨α, hα_lt, hstab⟩ := exists_complete_stabilization (L := L) M
  use α, hα_lt
  intro N _ _
  constructor
  · exact BFEquiv_stabilization_implies_equiv hstab
  · intro ⟨e⟩
    show BFEquiv0 (L := L) M N α
    unfold BFEquiv0
    have h : (e : M → N) ∘ Fin.elim0 = Fin.elim0 := funext (fun i => i.elim0)
    rw [← h]
    exact equiv_implies_BFEquiv e α 0 Fin.elim0

-- Helper: stabilizationOrdinal is less than ω₁
theorem stabilizationOrdinal_lt_omega1' (M : Type w) [L.Structure M] [Countable M] :
    stabilizationOrdinal (L := L) M < Ordinal.omega 1 := by
  obtain ⟨α, hα_lt, hα_spec⟩ := exists_stabilization (L := L) M
  have h_le : stabilizationOrdinal (L := L) M ≤ α := csInf_le' hα_spec
  exact lt_of_le_of_lt h_le hα_lt

-- Helper: the characterization property holds at stabilizationOrdinal
theorem stabilizationOrdinal_stabilizes (M : Type w) [L.Structure M] [Countable M] :
    StabilizesAt (L := L) M (stabilizationOrdinal (L := L) M) := by
  obtain ⟨α, _, hα_spec⟩ := exists_stabilization (L := L) M
  have h_nonempty : {α : Ordinal.{0} | StabilizesAt (L := L) M α}.Nonempty := ⟨α, hα_spec⟩
  exact csInf_mem h_nonempty

theorem stabilizationOrdinal_spec (M : Type w) [L.Structure M] [Countable M]
    (N : Type w) [L.Structure N] [Countable N] :
    BFEquiv0 (L := L) M N (stabilizationOrdinal (L := L) M) ↔ Nonempty (M ≃[L] N) :=
  stabilizationOrdinal_stabilizes M N

theorem scottSentence_characterizes (M : Type w) [L.Structure M] [Countable M]
    (N : Type w) [L.Structure N] [Countable N] :
    (scottSentence (L := L) M).realize_as_sentence N ↔ Nonempty (M ≃[L] N) := by
  unfold scottSentence Formulaω.realize_as_sentence
  have h := realize_scottFormula_iff_BFEquiv (L := L) (M := M) (N := N)
    (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N)
    (stabilizationOrdinal (L := L) M) (stabilizationOrdinal_lt_omega1' M)
  rw [h]
  exact stabilizationOrdinal_spec M N

/-- The forward direction: if N realizes the Scott sentence of M, then M ≃[L] N. -/
theorem scottSentence_realizes_implies_equiv (M : Type w) [L.Structure M] [Countable M]
    (N : Type w) [L.Structure N] [Countable N]
    (h : (scottSentence (L := L) M).realize_as_sentence N) : Nonempty (M ≃[L] N) :=
  scottSentence_characterizes M N |>.mp h

/-- The backward direction: M itself satisfies its own Scott sentence. -/
theorem scottSentence_self (M : Type w) [L.Structure M] [Countable M] :
    (scottSentence (L := L) M).realize_as_sentence M :=
  scottSentence_characterizes M M |>.mpr ⟨Equiv.refl L M⟩

/-- Isomorphic structures satisfy each other's Scott sentences. -/
theorem scottSentence_of_equiv (M N : Type w) [L.Structure M] [L.Structure N]
    [Countable M] [Countable N] (e : M ≃[L] N) :
    (scottSentence (L := L) M).realize_as_sentence N :=
  scottSentence_characterizes M N |>.mpr ⟨e⟩

/-! ### Scott Rank Theorems (from Rank.lean) -/

theorem elementRank_lt_omega1 {M : Type w} [L.Structure M] [Countable M] (m : M) :
    elementRank (L := L) m < (Ordinal.omega 1 : Ordinal.{0}) := by
  obtain ⟨α, hα_lt, hstab⟩ := exists_complete_stabilization (L := L) M
  exact lt_of_le_of_lt (elementRank_le_completeStab hstab m) hα_lt

/-- Scott rank of a countable structure is a countable ordinal.

The proof uses that:
1. Each elementRank m ≤ α for a complete stabilization ordinal α < ω₁
2. So scottRank = ⨆ m, elementRank m + 1 ≤ α + 1 < ω₁
-/
theorem scottRank_lt_omega1 (M : Type w) [L.Structure M] [Countable M] :
    scottRank (L := L) M < (Ordinal.omega 1 : Ordinal.{0}) := by
  obtain ⟨α, hα_lt, hstab⟩ := exists_complete_stabilization (L := L) M
  unfold scottRank
  have h_limit : Order.IsSuccLimit (Ordinal.omega (1 : Ordinal.{0})) :=
    Cardinal.isSuccLimit_omega 1
  have h_bound : ∀ m : M, elementRank (L := L) m ≤ α :=
    fun m => elementRank_le_completeStab hstab m
  have h_bound' : ∀ m : M, elementRank (L := L) m + 1 ≤ α + 1 := by
    intro m
    have h := (Ordinal.add_le_add_iff_right 1).mpr (h_bound m)
    convert h using 2 <;> simp [Nat.cast_one]
  by_cases h_nonempty : Nonempty M
  · calc ⨆ m, elementRank (L := L) m + 1 ≤ α + 1 := ciSup_le h_bound'
      _ < Ordinal.omega 1 := h_limit.succ_lt hα_lt
  · haveI : IsEmpty M := not_nonempty_iff.mp h_nonempty
    have h_zero : (⨆ (m : M), elementRank (L := L) m + 1) = 0 := by
      rw [Ordinal.iSup_eq_zero_iff]
      intro m
      exact isEmptyElim m
    rw [h_zero]
    exact Ordinal.omega_pos 1

/-- **Legacy (Code-based)**: When scottRank M ≤ α, the structure M stabilizes completely at α.

**Prefer**: `scottHeight_le_implies_stabilizesCompletely_of` in Height.lean
(sorry-free conditional on `CountableRefinementHypothesis`).

**Remaining gap** (in both versions): the β > α case requires showing that the complete
stabilization ordinal ≤ scottRank M. This is independent of the Code.lean sorry
(`agree_codes_implies_BFEquiv`). -/
@[deprecated "Use `scottHeight_le_implies_stabilizesCompletely_of` from Height.lean instead"
    (since := "2026-03-01")]
theorem scottRank_le_implies_stabilizesCompletely (M : Type w) [L.Structure M] [Countable M]
    {α : Ordinal.{0}} (hα : scottRank (L := L) M ≤ α) :
    StabilizesCompletely (L := L) M α := by
  obtain ⟨β, _, hstab⟩ := exists_complete_stabilization (L := L) M
  intro n N _ _ a b
  constructor
  · intro hBFα
    by_cases hβα : β ≤ α
    · exact BFEquiv_upgrade_at_stabilization hstab (BFEquiv.monotone hβα hBFα) (Order.succ α)
        (le_trans hβα (Order.le_succ α))
    · sorry
  · exact BFEquiv.of_succ

/-- Conditional variant of `scottRank_le_implies_stabilizesCompletely`.

Uses `exists_complete_stabilization_of` (sorry-free conditional on
`CountableRefinementHypothesis`) instead of `exists_complete_stabilization`.
The β ≤ α case is identical to the original. The β > α case remains as a
separate mathematical gap (connecting per-tuple stabilization bounds with
elementRank-based scottRank), independent of the Code.lean sorry.

**Axiom status**: Depends on `CountableRefinementHypothesis` + the β ≤ scottRank M gap.
Neither dependency involves `agree_codes_implies_BFEquiv`. -/
@[deprecated "Use `scottHeight_le_implies_stabilizesCompletely_of` from Height.lean instead"
    (since := "2026-03-01")]
theorem scottRank_le_implies_stabilizesCompletely_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    (M : Type w) [L.Structure M] [Countable M]
    {α : Ordinal.{0}} (hα : scottRank (L := L) M ≤ α) :
    StabilizesCompletely (L := L) M α := by
  obtain ⟨β, _, hstab⟩ := exists_complete_stabilization_of hcount M
  intro n N _ _ a b
  constructor
  · intro hBFα
    by_cases hβα : β ≤ α
    · exact BFEquiv_upgrade_at_stabilization hstab (BFEquiv.monotone hβα hBFα) (Order.succ α)
        (le_trans hβα (Order.le_succ α))
    · sorry
  · exact BFEquiv.of_succ

/-- The stabilization ordinal is below ω₁. -/
theorem stabilizationOrdinal_lt_omega1 (M : Type w) [L.Structure M] [Countable M] :
    stabilizationOrdinal (L := L) M < Ordinal.omega 1 :=
  stabilizationOrdinal_lt_omega1' M

/-! ### Scott Height Theorems (from Height.lean) -/

/-- Scott height is less than ω₁ for countable structures. -/
theorem scottHeight_lt_omega1 (M : Type w) [L.Structure M] [Countable M] :
    scottHeight (L := L) M < Ordinal.omega 1 := by
  obtain ⟨α, hα_lt, hstab⟩ := exists_complete_stabilization (L := L) M
  have h_mem : α ∈ {α : Ordinal.{0} | ∀ {n : ℕ} (a : Fin n → M)
      (N : Type w) [L.Structure N] [Countable N] (b : Fin n → N),
      BFEquiv (L := L) α n a b → BFEquiv (L := L) (Order.succ α) n a b} := by
    intro n a N _ _ b hBF
    exact (hstab n N a b).mp hBF
  exact lt_of_le_of_lt (csInf_le ⟨0, fun _ _ => zero_le _⟩ h_mem) hα_lt

/-- At Scott height, all tuple sizes have stabilized (BFEquiv α ↔ BFEquiv (succ α)). -/
theorem scottHeight_stabilizesCompletely (M : Type w) [L.Structure M] [Countable M] :
    StabilizesCompletely (L := L) M (scottHeight (L := L) M) := by
  obtain ⟨α, _, hstab⟩ := exists_complete_stabilization (L := L) M
  intro n N _ _ a b
  constructor
  · intro hBF
    suffices h : ∀ {k : ℕ} (a' : Fin k → M) (N' : Type w) [L.Structure N']
        [Countable N'] (b' : Fin k → N'),
        BFEquiv (L := L) (scottHeight (L := L) M) k a' b' →
        BFEquiv (L := L) (Order.succ (scottHeight (L := L) M)) k a' b' from h a N b hBF
    show scottHeight (L := L) M ∈ {α : Ordinal.{0} | ∀ {n : ℕ} (a : Fin n → M)
        (N : Type w) [L.Structure N] [Countable N] (b : Fin n → N),
        BFEquiv (L := L) α n a b → BFEquiv (L := L) (Order.succ α) n a b}
    apply csInf_mem
    exact ⟨α, fun {k} a' N' _ _ b' hBF' => (hstab k N' a' b').mp hBF'⟩
  · exact BFEquiv.of_succ

/-- The canonical Scott sentence characterizes potential isomorphism. -/
theorem canonicalScottSentence_iff_potentialIso
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N] :
    (canonicalScottSentence (L := L) M).realize_as_sentence N ↔
    Nonempty (PotentialIso L M N) := by
  constructor
  · intro h
    unfold canonicalScottSentence Formulaω.realize_as_sentence at h
    rw [realize_scottFormula_iff_BFEquiv _ _ _ (scottHeight_lt_omega1 M)] at h
    have hstab := scottHeight_stabilizesCompletely (L := L) M
    exact ⟨{
      family := { p | BFEquiv (L := L) (scottHeight (L := L) M) p.1 p.2.1 p.2.2 }
      empty_mem := h
      compatible := fun p hp =>
        (BFEquiv.zero p.2.1 p.2.2).mp (BFEquiv.monotone (zero_le _) hp)
      forth := fun ⟨k, a, b⟩ hp m => by
        simp only [Set.mem_setOf_eq] at hp ⊢
        obtain ⟨n', hn'⟩ := BFEquiv.forth ((hstab k N a b).mp hp) m
        exact ⟨n', hn'⟩
      back := fun ⟨k, a, b⟩ hp n' => by
        simp only [Set.mem_setOf_eq] at hp ⊢
        obtain ⟨m, hm⟩ := BFEquiv.back ((hstab k N a b).mp hp) n'
        exact ⟨m, hm⟩
    }⟩
  · intro ⟨P⟩
    unfold canonicalScottSentence Formulaω.realize_as_sentence
    rw [realize_scottFormula_iff_BFEquiv _ _ _ (scottHeight_lt_omega1 M)]
    exact P.implies_BFEquiv_all (scottHeight (L := L) M)

/-- For countable structures, the canonical Scott sentence characterizes isomorphism. -/
theorem canonicalScottSentence_characterizes
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N] :
    (canonicalScottSentence (L := L) M).realize_as_sentence N ↔
    Nonempty (M ≃[L] N) := by
  unfold canonicalScottSentence Formulaω.realize_as_sentence
  rw [realize_scottFormula_iff_BFEquiv _ _ _ (scottHeight_lt_omega1 M)]
  constructor
  · exact BFEquiv_stabilization_implies_equiv (scottHeight_stabilizesCompletely (L := L) M)
  · intro ⟨e⟩
    have h : (e : M → N) ∘ Fin.elim0 = Fin.elim0 := funext (fun i => i.elim0)
    rw [← h]
    exact equiv_implies_BFEquiv e _ 0 Fin.elim0

/-- The canonical Scott sentence is semantically equivalent to the standard Scott sentence. -/
theorem canonicalScottSentence_equiv_scottSentence
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N] :
    (canonicalScottSentence (L := L) M).realize_as_sentence N ↔
    (scottSentence (L := L) M).realize_as_sentence N := by
  rw [canonicalScottSentence_characterizes, scottSentence_characterizes]

/-- The quantifier rank of the canonical Scott sentence is bounded. -/
theorem canonicalScottSentence_qrank
    (M : Type w) [L.Structure M] [Countable M] :
    (canonicalScottSentence (L := L) M).qrank ≤
    scottHeight (L := L) M + Ordinal.omega0 :=
  le_trans
    (scottFormula_qrank_le Fin.elim0 _ (scottHeight_lt_omega1 M))
    le_self_add

/-! ### Counting Models (from CountingModels.lean) -/

open Cardinal in
/-- When all countable models of a sentence have Scott rank bounded by α (with α < ω₁),
isomorphism between countable models is equivalent to BF-equivalence at level α.

**Status**: Inherits sorry from `per_tuple_stabilization_below_omega1` (via
`scottRank_le_implies_stabilizesCompletely`). -/
@[deprecated "Use `bounded_scottHeight_iso_eq_BFEquiv_of` instead" (since := "2026-03-01")]
theorem bounded_scottRank_iso_eq_BFEquiv
    {φ : L.Sentenceω} {α : Ordinal} (_hα : α < Ordinal.omega 1)
    (hbound : ∀ (M : Type w) [L.Structure M] [Countable M],
      Sentenceω.Realize φ M → scottRank (L := L) M ≤ α)
    {M N : Type w} [L.Structure M] [L.Structure N] [Countable M] [Countable N]
    (hM : Sentenceω.Realize φ M) (_hN : Sentenceω.Realize φ N) :
    Nonempty (M ≃[L] N) ↔
    BFEquiv (L := L) α 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) := by
  constructor
  · -- Forward: isomorphism → BFEquiv α
    intro ⟨e⟩
    have h : (e : M → N) ∘ Fin.elim0 = Fin.elim0 := funext fun i => i.elim0
    rw [← h]
    exact equiv_implies_BFEquiv e α 0 Fin.elim0
  · -- Backward: BFEquiv α → isomorphism
    intro hBF
    -- scottRank M ≤ α gives StabilizesCompletely M α
    have hstabM := scottRank_le_implies_stabilizesCompletely M (hbound M hM)
    -- Upgrade BFEquiv from α to all levels γ ≥ α
    have hAll : ∀ γ < (Ordinal.omega 1 : Ordinal.{0}),
        BFEquiv (L := L) γ 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) := by
      intro γ _
      rcases le_or_gt γ α with hγα | hαγ
      · exact BFEquiv.monotone hγα hBF
      · exact BFEquiv_upgrade_at_stabilization hstabM hBF γ hαγ.le
    exact BFEquiv_below_omega1_implies_iso hAll

/-! ### Countable Corollary (from CountableCorollary.lean) -/

/-- For countable structures in a countable relational language, Lω₁ω-elementary
equivalence implies isomorphism. -/
theorem countable_LomegaEquiv_implies_iso
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N] :
    LomegaEquiv L M N → Nonempty (M ≃[L] N) := by
  intro hEquiv
  have hM := scottSentence_self (L := L) M
  have hMω := (Formulaω.realize_toSentenceω (scottSentence (L := L) M) (M := M)).mpr hM
  have hNω := (hEquiv _).mp hMω
  have hN := (Formulaω.realize_toSentenceω (scottSentence (L := L) M) (M := N)).mp hNω
  exact (scottSentence_characterizes M N).mp hN

/-- For countable structures in a countable relational language, L∞ω-elementary
equivalence implies isomorphism. -/
theorem countable_LinfEquiv_implies_iso
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N] :
    LinfEquiv L M N → Nonempty (M ≃[L] N) := by
  intro hLinf
  apply countable_LomegaEquiv_implies_iso
  intro φ
  have h := hLinf (Sentenceω.toLinf φ)
  simp only [Sentenceω.realize_toLinf] at h
  exact h

end Language

end FirstOrder
