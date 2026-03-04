/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Scott.Sentence

/-!
# Proof of CountableRefinementHypothesis

This file proves `CountableRefinementHypothesis` and provides unconditional wrappers for
all Sentence.lean-level theorems. Together with the downstream wrappers in Rank.lean,
Height.lean, CountableCorollary.lean, and CountingModels.lean, this recovers the full
unconditional API.

## Strategy

The proof uses the "constant chain" argument:
1. Self-stabilization (`exists_complete_self_stabilization`) gives α₀ < ω₁ where the
   internal BFEquiv relation on M is frozen.
2. Under self-stabilization, forth/back witnesses chosen at level α₀ automatically work
   at all higher levels (`chain_step` + `witness_at_all_levels`).
3. By transfinite induction (`BFEquiv_of_all_finite_levels`), BFEquiv (α₀+k) for all k
   upgrades to BFEquiv ε for all ε.
4. Hence no refinement ordinals exist above γ = sup_k(α₀+k) < ω₁, and R(n,a) ⊆ [0,γ)
   is countable.

## Main Result

- `countableRefinementHypothesis` : `CountableRefinementHypothesis L`
-/

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable [Countable (Σ l, L.Relations l)]

open FirstOrder Structure Fin Ordinal BoundedFormulaω

/-! ### Main theorem: Set.Iio of countable ordinal is countable -/

/-- For any ordinal β < ω₁, the set of ordinals below β is countable. -/
theorem Set.countable_Iio_of_lt_omega1 (β : Ordinal.{0}) (hβ : β < Ordinal.omega 1) :
    Set.Countable (Set.Iio β) := by
  -- β < ω₁ means β.card < ℵ₁
  have h_card : β.card < Cardinal.aleph 1 := Cardinal.lt_omega_iff_card_lt.mp hβ
  -- Therefore β.card ≤ ℵ₀
  have h_card_le : β.card ≤ Cardinal.aleph0 := by
    have h1 : Cardinal.aleph 1 = Cardinal.aleph (Order.succ 0) := by
      congr 1; exact Ordinal.succ_zero.symm
    rw [h1, Cardinal.aleph_succ, Cardinal.aleph_zero] at h_card
    exact Order.lt_succ_iff.mp h_card
  -- β.ToType is countable since β.card ≤ ℵ₀
  haveI : Countable β.ToType := by
    rw [← Cardinal.mk_le_aleph0_iff, Cardinal.mk_toType]
    exact h_card_le
  -- Set.Iio β is in bijection with β.ToType via the Ordinal.ToType.mk map
  have h_equiv : β.ToType ≃ Set.Iio β :=
    (Ordinal.ToType.mk.toEquiv).symm
  -- Therefore Set.Iio β is countable
  exact Countable.of_equiv β.ToType h_equiv

/-! ### Helper: countable set of ordinals below ω₁ is bounded -/

/-- A countable set of ordinals below ω₁ has supremum below ω₁. -/
private theorem countable_ordinals_below_omega1_bounded
    (S : Set Ordinal.{0}) (hS : S.Countable) (hlt : ∀ x ∈ S, x < Ordinal.omega 1) :
    ∃ β < Ordinal.omega 1, ∀ x ∈ S, x < β := by
  by_cases hne : S.Nonempty
  · haveI := hS.to_subtype
    haveI := hne.to_subtype
    obtain ⟨enum, henum⟩ := exists_surjective_nat S
    let seq : ℕ → Ordinal.{0} := fun k => (enum k).1
    have hseq_lt : ∀ k, seq k < (Cardinal.aleph 1).ord := by
      intro k; rw [Cardinal.ord_aleph]; exact hlt _ (enum k).2
    have hsup_lt := Ordinal.iSup_sequence_lt_omega_one seq hseq_lt
    rw [Cardinal.ord_aleph] at hsup_lt
    have hSuccSupLt : Order.succ (⨆ k, seq k) < Ordinal.omega 1 :=
      Order.IsSuccLimit.succ_lt (Cardinal.isSuccLimit_omega 1) hsup_lt
    refine ⟨Order.succ (⨆ k, seq k), hSuccSupLt, fun x hx => ?_⟩
    obtain ⟨k, hk⟩ := henum ⟨x, hx⟩
    have hBdd : BddAbove (Set.range seq) :=
      ⟨Ordinal.omega 1, fun _ ⟨j, hj⟩ => hj ▸ le_of_lt (hlt _ (enum j).2)⟩
    calc x = seq k := (congr_arg Subtype.val hk).symm
      _ ≤ ⨆ k, seq k := le_ciSup hBdd k
      _ < Order.succ (⨆ k, seq k) := Order.lt_succ _
  · exact ⟨1, by calc (1 : Ordinal) < ω := Ordinal.one_lt_omega0
        _ ≤ Ordinal.omega 1 := Ordinal.omega0_le_omega 1,
      fun x hx => absurd ⟨x, hx⟩ hne⟩


/-! ### Key Lemma: extensions countable implies base countable -/

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- If the refinement set R(n+1, snoc a m) is countable for every m ∈ M,
then R(n, a) is countable. The proof uses `per_tuple_stabilization_from_extensions`:
countable → bounded by γ(m) < ω₁ for each m, sup_m γ(m) < ω₁ by regularity,
and then stabilization above succ(sup) bounds R(n, a). -/
private theorem extensions_countable_implies_countable
    {M : Type w} [L.Structure M] [Countable M]
    {n : ℕ} {a : Fin n → M}
    (hext : ∀ m : M, Set.Countable {ε : Ordinal.{0} | ε < Ordinal.omega 1 ∧
      ∃ (N : Type w) (_ : L.Structure N) (_ : Countable N) (b : Fin (n + 1) → N),
        BFEquiv (L := L) ε (n + 1) (Fin.snoc a m) b ∧
        ¬BFEquiv (L := L) (Order.succ ε) (n + 1) (Fin.snoc a m) b}) :
    Set.Countable {ε : Ordinal.{0} | ε < Ordinal.omega 1 ∧
      ∃ (N : Type w) (_ : L.Structure N) (_ : Countable N) (b : Fin n → N),
        BFEquiv (L := L) ε n a b ∧ ¬BFEquiv (L := L) (Order.succ ε) n a b} := by
  -- Step 1: Each extension's refinement set is bounded by some γ(m) < ω₁
  have hbounded : ∀ m : M, ∃ γ < Ordinal.omega 1,
      ∀ ε, ε < Ordinal.omega 1 → γ ≤ ε →
        ∀ (N : Type w) [L.Structure N] [Countable N] (b : Fin (n + 1) → N),
          BFEquiv (L := L) ε (n + 1) (Fin.snoc a m) b →
          BFEquiv (L := L) (Order.succ ε) (n + 1) (Fin.snoc a m) b := by
    intro m
    obtain ⟨β, hβ_lt, hβ_bound⟩ := countable_ordinals_below_omega1_bounded _ (hext m)
      (fun x hx => hx.1)
    refine ⟨β, hβ_lt, fun ε hε_lt hβε N instN instCN b hBF => ?_⟩
    by_contra hNot
    exact absurd (hβ_bound ε ⟨hε_lt, N, instN, instCN, b, hBF, hNot⟩) (not_lt.mpr hβε)
  -- Step 2: Extract γ and the stabilization iff
  choose γ hγ_lt hγ_spec using hbounded
  have hγ_iff : ∀ m, ∀ α, γ m ≤ α → α < Ordinal.omega 1 → Order.succ α < Ordinal.omega 1 →
      ∀ (N : Type w) [L.Structure N] [Countable N] (b : Fin (n + 1) → N),
        (BFEquiv (L := L) α (n + 1) (Fin.snoc a m) b ↔
         BFEquiv (L := L) (Order.succ α) (n + 1) (Fin.snoc a m) b) := by
    intro m α hα hα_lt _
    exact fun N instN instCN b => ⟨hγ_spec m α hα_lt hα N b, BFEquiv.of_succ⟩
  -- Step 3: Take S = sup_m γ(m) < ω₁
  by_cases hM : IsEmpty M
  · -- If M is empty and n > 0, `a` can't exist; if n = 0, R ⊆ {0}
    cases n with
    | succ k => exact (hM.false (a 0)).elim
    | zero =>
      -- R(0, Fin.elim0) ⊆ {0}: any ε > 0 with BFEquiv ε requires BFEquiv 1,
      -- which needs back (∀ n' : N, ∃ m : M, ...), impossible with empty M unless N empty,
      -- but then ¬BFEquiv (succ ε) also fails.
      apply Set.Countable.mono (s₂ := {(0 : Ordinal.{0})}) _ (Set.countable_singleton _)
      intro ε ⟨hε_lt, N, instN, instCN, b, hBF, hNot⟩
      simp only [Set.mem_singleton_iff]
      by_contra hε_ne
      push_neg at hε_ne
      have hε_pos : (0 : Ordinal) < ε := pos_of_ne_zero hε_ne
      -- ε > 0, so BFEquiv ε implies BFEquiv 1 = BFEquiv (succ 0)
      have hBF1 := BFEquiv.monotone (Order.succ_le_of_lt hε_pos) hBF
      -- BFEquiv (succ 0) requires back: ∀ n' : N, ∃ m : M, ...
      have hback := ((BFEquiv.succ 0 a b).mp hBF1).2.2
      -- But M is empty, so ∃ m : M is impossible if N is nonempty
      -- If N is empty, BFEquiv (succ ε) also holds, contradicting hNot
      by_cases hN : IsEmpty N
      · apply hNot; rw [BFEquiv.succ]
        exact ⟨hBF, fun m => hM.elim m, fun n' => hN.elim n'⟩
      · rw [not_isEmpty_iff] at hN
        exact hM.false (hback hN.some).choose
  · rw [not_isEmpty_iff] at hM; haveI := hM
    obtain ⟨enum, henum⟩ := exists_surjective_nat M
    let γ_seq : ℕ → Ordinal.{0} := γ ∘ enum
    have hγ_seq_lt : ∀ k, γ_seq k < (Cardinal.aleph 1).ord := by
      intro k; rw [Cardinal.ord_aleph]; exact hγ_lt (enum k)
    have hS_lt : (⨆ k, γ_seq k) < Ordinal.omega 1 := by
      rw [← Cardinal.ord_aleph]
      exact Ordinal.iSup_sequence_lt_omega_one γ_seq hγ_seq_lt
    set S := ⨆ k, γ_seq k with hS_def
    have hBdd : BddAbove (Set.range γ_seq) :=
      ⟨Ordinal.omega 1, fun _ ⟨k, hk⟩ => hk ▸ le_of_lt (hγ_lt (enum k))⟩
    have hγ_le_S : ∀ m, γ m ≤ S := by
      intro m
      obtain ⟨k, hk⟩ := henum m
      calc γ m = γ (enum k) := by rw [hk]
        _ = γ_seq k := rfl
        _ ≤ S := le_ciSup hBdd k
    have hSuccS_lt : Order.succ S < Ordinal.omega 1 :=
      Order.IsSuccLimit.succ_lt (Cardinal.isSuccLimit_omega 1) hS_lt
    -- Step 4: Apply per_tuple_stabilization_from_extensions
    have hstab := per_tuple_stabilization_from_extensions γ hγ_iff hγ_lt S hγ_le_S hS_lt
    -- Step 5: R(n, a) ⊆ [0, succ S), hence countable
    have hR_bounded : ∀ ε, ε ∈ {ε : Ordinal.{0} | ε < Ordinal.omega 1 ∧
        ∃ (N : Type w) (_ : L.Structure N) (_ : Countable N) (b : Fin n → N),
          BFEquiv (L := L) ε n a b ∧ ¬BFEquiv (L := L) (Order.succ ε) n a b} →
        ε < Order.succ S := by
      intro ε ⟨hε_lt, N, instN, instCN, b, hBF, hNot⟩
      by_contra hge
      push_neg at hge
      have hsucc_ε_lt : Order.succ ε < Ordinal.omega 1 :=
        Order.IsSuccLimit.succ_lt (Cardinal.isSuccLimit_omega 1) hε_lt
      exact hNot ((hstab ε hge hε_lt hsucc_ε_lt N b).mp hBF)
    apply Set.Countable.mono (s₂ := Set.Iio (Order.succ S))
    · exact fun ε hε => hR_bounded ε hε
    · exact Set.countable_Iio_of_lt_omega1 (Order.succ S) hSuccS_lt

/-! ### Self-stabilization to full stabilization

The key insight: `SelfStabilizesCompletely M α₀` (internal BFEquiv stabilization) implies
that the back-and-forth game cannot create new refinements above α₀ + ω, because any
forth/back witness at level α₀ already works at all higher levels (the "constant chain"
argument). This avoids the need to count external BFEquiv types directly. -/

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- Internal BFEquiv upgrade: if BFEquiv α₀ holds internally (M vs M) at self-stabilization,
it upgrades to all higher ordinals. -/
private theorem BFEquiv_self_upgrade
    {M : Type w} [L.Structure M]
    {α₀ : Ordinal.{0}} (hstab : SelfStabilizesCompletely (L := L) M α₀)
    {n : ℕ} {a a' : Fin n → M}
    (h : BFEquiv (L := L) α₀ n a a') (β : Ordinal.{0}) (hβ : α₀ ≤ β) :
    BFEquiv (L := L) β n a a' := by
  induction β using Ordinal.limitRecOn generalizing n a a' with
  | zero =>
    rwa [le_antisymm hβ (zero_le α₀)] at h
  | succ γ ih =>
    rcases hβ.lt_or_eq with hlt | heq
    · rw [Order.lt_succ_iff] at hlt
      have hγ := @ih n a a' h hlt
      rw [BFEquiv.succ]
      refine ⟨hγ, ?_, ?_⟩
      · intro m
        obtain ⟨m', hm'⟩ := BFEquiv.forth ((hstab n a a').mp h) m
        exact ⟨m', @ih (n + 1) (Fin.snoc a m) (Fin.snoc a' m') hm' hlt⟩
      · intro m'
        obtain ⟨m, hm⟩ := BFEquiv.back ((hstab n a a').mp h) m'
        exact ⟨m, @ih (n + 1) (Fin.snoc a m) (Fin.snoc a' m') hm hlt⟩
    · exact heq ▸ h
  | limit β _ ih =>
    rw [BFEquiv.limit β ‹_›]
    intro γ hγ
    rcases le_or_gt α₀ γ with hαγ | hαγ
    · exact @ih γ hγ n a a' h hαγ
    · exact BFEquiv.monotone (le_of_lt hαγ) h

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- Chain-constant step: under self-stabilization at α₀, if BFEquiv ε holds at (n+1)-tuples
and BFEquiv (succ(succ ε)) holds at n-tuples, then BFEquiv (succ ε) holds at (n+1)-tuples.

The proof uses back at level succ ε to find an M-witness mw, then self-stabilization to
show the original and new M-witnesses are equivalent at all levels ≥ α₀. -/
private theorem chain_step
    {M : Type w} [L.Structure M]
    {N : Type w} [L.Structure N] [Countable N]
    {α₀ : Ordinal.{0}} (hstab : SelfStabilizesCompletely (L := L) M α₀)
    {n : ℕ} {a : Fin n → M} {b : Fin n → N} {m : M} {m' : N}
    {ε : Ordinal.{0}} (hε : α₀ ≤ ε)
    (hBF_ext : BFEquiv (L := L) ε (n + 1) (Fin.snoc a m) (Fin.snoc b m'))
    (hBF_base : BFEquiv (L := L) (Order.succ (Order.succ ε)) n a b) :
    BFEquiv (L := L) (Order.succ ε) (n + 1) (Fin.snoc a m) (Fin.snoc b m') := by
  obtain ⟨mw, hmw⟩ := BFEquiv.back hBF_base m'
  exact BFEquiv.trans
    (BFEquiv_self_upgrade hstab
      (BFEquiv.monotone hε (BFEquiv.trans hBF_ext (BFEquiv.symm (BFEquiv.of_succ hmw))))
      (Order.succ ε) (le_of_lt (Order.lt_succ_of_le hε)))
    hmw

private theorem add_nat_succ (α : Ordinal.{0}) (k : ℕ) :
    α + ↑(k + 1) = Order.succ (α + ↑k) := by
  simp only [Order.succ_eq_add_one, Nat.cast_add, Nat.cast_one, add_assoc]

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- From a forth/back witness at level α₀, upgrade to BFEquiv (α₀+k) for all k.
Uses `chain_step` inductively: each level α₀+k upgrades to α₀+(k+1) because
self-stabilization forces the witness chain to be constant. -/
private theorem witness_at_all_levels
    {M : Type w} [L.Structure M]
    {N : Type w} [L.Structure N] [Countable N]
    {α₀ : Ordinal.{0}} (hstab : SelfStabilizesCompletely (L := L) M α₀)
    {n : ℕ} {a : Fin n → M} {b : Fin n → N} {m : M} {m' : N}
    (hbase : ∀ k : ℕ, BFEquiv (L := L) (α₀ + ↑k) n a b)
    (h0 : BFEquiv (L := L) α₀ (n + 1) (Fin.snoc a m) (Fin.snoc b m'))
    (k : ℕ) : BFEquiv (L := L) (α₀ + ↑k) (n + 1) (Fin.snoc a m) (Fin.snoc b m') := by
  induction k with
  | zero => simpa using h0
  | succ j ih =>
    rw [add_nat_succ]
    apply chain_step hstab le_self_add ih
    rw [Order.succ_eq_add_one, Order.succ_eq_add_one, add_assoc, add_assoc]
    convert hbase (j + 2) using 1; norm_cast

-- Main upgrade: from self-stabilization at α₀ and BFEquiv (α₀+k) for all k ∈ ℕ,
-- deduce BFEquiv ε for all ordinals ε. Uses transfinite induction on ε with
-- `witness_at_all_levels` to provide forth/back witnesses at successor steps.
omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
private theorem BFEquiv_of_all_finite_levels
    {M : Type w} [L.Structure M]
    {N : Type w} [L.Structure N] [Countable N]
    {α₀ : Ordinal.{0}} (hstab : SelfStabilizesCompletely (L := L) M α₀)
    {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (h : ∀ k : ℕ, BFEquiv (L := L) (α₀ + ↑k) n a b)
    (ε : Ordinal.{0}) :
    BFEquiv (L := L) ε n a b := by
  induction ε using Ordinal.limitRecOn generalizing n a b with
  | zero =>
    exact BFEquiv.monotone (zero_le α₀) (by simpa using h 0)
  | succ ε ih =>
    have hε := @ih n a b h
    have hsucc_α₀ : BFEquiv (L := L) (Order.succ α₀) n a b := by
      have := h 1; rwa [Nat.cast_one, ← Order.succ_eq_add_one] at this
    rw [BFEquiv.succ]; refine ⟨hε, ?_, ?_⟩
    · intro m
      obtain ⟨m'₀, hm'₀⟩ := BFEquiv.forth hsucc_α₀ m
      exact ⟨m'₀, @ih (n + 1) (Fin.snoc a m) (Fin.snoc b m'₀)
        (witness_at_all_levels hstab h hm'₀)⟩
    · intro m'
      obtain ⟨m₀, hm₀⟩ := BFEquiv.back hsucc_α₀ m'
      exact ⟨m₀, @ih (n + 1) (Fin.snoc a m₀) (Fin.snoc b m')
        (witness_at_all_levels hstab h hm₀)⟩
  | limit ε hε ih =>
    rw [BFEquiv.limit ε hε]
    intro δ hδ
    exact @ih δ hδ n a b h

/-! ### The Counting Lemma -/

/-- The countable refinement hypothesis holds for all countable relational languages.

For a countable structure M in a countable relational language, and any n-tuple a from M,
the set of refinement ordinals R(n, a) = {ε < ω₁ | ∃ (N, b), BFEquiv ε ∧ ¬BFEquiv (succ ε)}
is countable.

**Proof**: Self-stabilization (`exists_complete_self_stabilization`) gives α₀ < ω₁ where
internal BFEquiv on M is frozen. For any ε above γ = sup_k(α₀+k) with BFEquiv ε n a b,
the monotonicity of BFEquiv gives BFEquiv (α₀+k) for all k. The "constant chain" argument
(`witness_at_all_levels`) shows that forth/back witnesses at level α₀ work at all higher
levels (via self-stabilization + transitivity), so `BFEquiv_of_all_finite_levels` upgrades
BFEquiv to the successor. Hence no refinement ordinals exist above γ < ω₁. -/
theorem countableRefinementHypothesis : CountableRefinementHypothesis.{u, v, w} L := by
  intro M inst_struct inst_count n a
  obtain ⟨α₀, hα₀_lt, hstab⟩ := exists_complete_self_stabilization (L := L) M
  have hα_k_lt : ∀ k : ℕ, α₀ + ↑k < (Cardinal.aleph 1).ord := by
    intro k; rw [Cardinal.ord_aleph]
    induction k with
    | zero => simpa
    | succ j ih =>
      rw [Nat.cast_succ, ← add_assoc]
      exact Order.IsSuccLimit.succ_lt (Cardinal.isSuccLimit_omega 1) ih
  have hBdd : BddAbove (Set.range fun k : ℕ => α₀ + (↑k : Ordinal.{0})) :=
    ⟨(Cardinal.aleph 1).ord, fun _ ⟨k, hk⟩ => hk ▸ le_of_lt (hα_k_lt k)⟩
  set γ := ⨆ k : ℕ, (α₀ + (↑k : Ordinal.{0}))
  have hγ_lt : γ < Ordinal.omega 1 := by
    have := Ordinal.iSup_sequence_lt_omega_one _ hα_k_lt
    rwa [Cardinal.ord_aleph] at this
  apply Set.Countable.mono (s₂ := Set.Iio γ) _ (Set.countable_Iio_of_lt_omega1 γ hγ_lt)
  intro ε ⟨_, N, instN, instCN, b, hBF, hNot⟩
  simp only [Set.mem_Iio]
  by_contra hge; push_neg at hge
  exact hNot (BFEquiv_of_all_finite_levels hstab
    (fun k => BFEquiv.monotone (le_trans (le_ciSup hBdd k) hge) hBF)
    (Order.succ ε))

/-! ### Unconditional Wrappers (Sentence.lean level)

Each theorem below is a one-liner applying `countableRefinementHypothesis` to the
corresponding `_of` variant in Sentence.lean. -/

/-- The set of refinement ordinals for any tuple is countable. -/
theorem countable_refinement_steps
    {M : Type w} [L.Structure M] [Countable M]
    (n : ℕ) (a : Fin n → M) :
    Set.Countable {α : Ordinal.{0} | α < Ordinal.omega 1 ∧
      ∃ (N : Type w) (_ : L.Structure N) (_ : Countable N) (b : Fin n → N),
        BFEquiv (L := L) α n a b ∧ ¬BFEquiv (L := L) (Order.succ α) n a b} :=
  countableRefinementHypothesis M n a

/-- Per-tuple stabilization below ω₁. -/
theorem per_tuple_stabilization_below_omega1
    {M : Type w} [L.Structure M] [Countable M]
    (n : ℕ) (a : Fin n → M) :
    ∃ γ < (Ordinal.omega 1 : Ordinal.{0}),
      ∀ α, γ ≤ α → α < Ordinal.omega 1 → Order.succ α < Ordinal.omega 1 →
        ∀ (N : Type w) [L.Structure N] [Countable N] (b : Fin n → N),
          (BFEquiv (L := L) α n a b ↔ BFEquiv (L := L) (Order.succ α) n a b) :=
  per_tuple_stabilization_below_omega1_of countableRefinementHypothesis n a

/-- Complete stabilization below ω₁. -/
theorem exists_complete_stabilization (M : Type w) [L.Structure M] [Countable M] :
    ∃ α < (Ordinal.omega 1 : Ordinal.{0}), StabilizesCompletely (L := L) M α :=
  exists_complete_stabilization_of countableRefinementHypothesis M

/-- Existence of a stabilization ordinal (BFEquiv0 characterizes isomorphism). -/
theorem exists_stabilization (M : Type w) [L.Structure M] [Countable M] :
    ∃ α < (Ordinal.omega 1 : Ordinal.{0}), StabilizesAt (L := L) M α :=
  exists_stabilization_of countableRefinementHypothesis M

/-- The stabilization ordinal is below ω₁. -/
theorem stabilizationOrdinal_lt_omega1' (M : Type w) [L.Structure M] [Countable M] :
    stabilizationOrdinal (L := L) M < Ordinal.omega 1 :=
  stabilizationOrdinal_lt_omega1_of countableRefinementHypothesis M

/-- The characterization property holds at stabilizationOrdinal. -/
theorem stabilizationOrdinal_stabilizes (M : Type w) [L.Structure M] [Countable M] :
    StabilizesAt (L := L) M (stabilizationOrdinal (L := L) M) :=
  stabilizationOrdinal_stabilizes_of countableRefinementHypothesis M

/-- BFEquiv0 at stabilizationOrdinal characterizes isomorphism. -/
theorem stabilizationOrdinal_spec (M : Type w) [L.Structure M] [Countable M]
    (N : Type w) [L.Structure N] [Countable N] :
    BFEquiv0 (L := L) M N (stabilizationOrdinal (L := L) M) ↔ Nonempty (M ≃[L] N) :=
  stabilizationOrdinal_stabilizes M N

/-- The Scott sentence of M characterizes M up to isomorphism among countable structures. -/
theorem scottSentence_characterizes (M : Type w) [L.Structure M] [Countable M]
    (N : Type w) [L.Structure N] [Countable N] :
    (scottSentence (L := L) M).realize_as_sentence N ↔ Nonempty (M ≃[L] N) :=
  scottSentence_characterizes_of countableRefinementHypothesis M N

/-- If N realizes the Scott sentence of M, then M ≃[L] N. -/
theorem scottSentence_realizes_implies_equiv (M : Type w) [L.Structure M] [Countable M]
    (N : Type w) [L.Structure N] [Countable N]
    (h : (scottSentence (L := L) M).realize_as_sentence N) : Nonempty (M ≃[L] N) :=
  (scottSentence_characterizes M N).mp h

/-- M itself satisfies its own Scott sentence. -/
theorem scottSentence_self (M : Type w) [L.Structure M] [Countable M] :
    (scottSentence (L := L) M).realize_as_sentence M :=
  (scottSentence_characterizes M M).mpr ⟨Equiv.refl L M⟩

/-- Isomorphic structures satisfy each other's Scott sentences. -/
theorem scottSentence_of_equiv (M N : Type w) [L.Structure M] [L.Structure N]
    [Countable M] [Countable N] (e : M ≃[L] N) :
    (scottSentence (L := L) M).realize_as_sentence N :=
  (scottSentence_characterizes M N).mpr ⟨e⟩

end Language

end FirstOrder
