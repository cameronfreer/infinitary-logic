/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Scott.Formula
import InfinitaryLogic.Scott.Code
import InfinitaryLogic.Karp.PotentialIso
import Mathlib.ModelTheory.PartialEquiv

/-!
# Scott Sentences

This file proves the main theorem about Scott sentences: every countable structure
in a relational countable language has a Scott sentence characterizing it up to isomorphism.

## Main Definitions

- `scottSentence`: The Scott sentence of a countable structure.

## Main Results

- `scottSentence_characterizes`: A countable structure N satisfies the Scott sentence of M
  if and only if M and N are isomorphic.

## Implementation Notes

The proof proceeds by showing:
1. High enough BF-equivalence (with the empty tuple) implies `IsExtensionPair` in both directions.
2. `IsExtensionPair` in both directions between countable structures implies isomorphism
   (using mathlib's `equiv_between_cg`).
3. The Scott formula at the stabilization ordinal captures exactly this.
-/

universe u v w u'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable [Countable (Σ l, L.Relations l)]

open FirstOrder Structure Fin Ordinal BoundedFormulaω Substructure

-- We fix the ordinal universe to avoid metavariable issues
-- In practice, we typically work with Ordinal.{0}

/-! ### Helper definitions to reduce repetition -/

/-- BFEquiv at the empty tuple level. This is the key semantic predicate for Scott sentences. -/
abbrev BFEquiv0 (M : Type w) (N : Type w') [L.Structure M] [L.Structure N] (α : Ordinal) : Prop :=
  BFEquiv (L := L) α 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N)

/-- The ordinal α stabilizes for M if BFEquiv0 at level α characterizes isomorphism
with M among all countable structures of the same type. -/
def StabilizesAt (M : Type w) [L.Structure M] (α : Ordinal) : Prop :=
  ∀ (N : Type w) [L.Structure N] [Countable N], BFEquiv0 (L := L) M N α ↔ Nonempty (M ≃[L] N)

/-- BFEquiv α on n-tuples from M equals BFEquiv (succ α) for all countable N.
This captures when the BFEquiv relation has stopped distinguishing tuples at level α. -/
def StabilizesForTuples (M : Type w) [L.Structure M] (α : Ordinal) (n : ℕ) : Prop :=
  ∀ (N : Type w) [L.Structure N] [Countable N] (a : Fin n → M) (b : Fin n → N),
    BFEquiv (L := L) α n a b ↔ BFEquiv (L := L) (Order.succ α) n a b

/-- All tuple sizes stabilize at α. This is the key condition for the back-and-forth
argument to yield an isomorphism. -/
def StabilizesCompletely (M : Type w) [L.Structure M] (α : Ordinal) : Prop :=
  ∀ n : ℕ, StabilizesForTuples (L := L) M α n

/-- Strong stabilization: BFEquiv is constant for all β ≥ α.
This is a priori stronger than `StabilizesForTuples` (which only compares α to succ α),
but the two are equivalent. The strong form is more convenient for upgrading BFEquiv
to arbitrary higher ordinals. -/
def StrongStabilizesForTuples (M : Type w) [L.Structure M] (α : Ordinal) (n : ℕ) : Prop :=
  ∀ (N : Type w) [L.Structure N] [Countable N] (a : Fin n → M) (b : Fin n → N)
    (β : Ordinal), α ≤ β → (BFEquiv (L := L) α n a b ↔ BFEquiv (L := L) β n a b)

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- Strong stabilization implies weak stabilization (take β = succ α). -/
theorem StrongStabilizesForTuples.toStabilizesForTuples {M : Type w} [L.Structure M]
    {α : Ordinal} {n : ℕ} (h : StrongStabilizesForTuples (L := L) M α n) :
    StabilizesForTuples (L := L) M α n := by
  intro N _ _ a b
  exact h N a b (Order.succ α) (Order.le_succ α)

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- An isomorphism induces BF-equivalence at all ordinal levels. -/
theorem equiv_implies_BFEquiv {M N : Type w} [L.Structure M] [L.Structure N]
    (e : M ≃[L] N) (α : Ordinal) (n : ℕ) (a : Fin n → M) :
    BFEquiv (L := L) α n a (e ∘ a) := by
  induction α using Ordinal.limitRecOn generalizing n a with
  | zero =>
    rw [BFEquiv.zero]
    intro idx
    cases idx with
    | eq i j =>
      simp only [AtomicIdx.holds, Function.comp_apply]
      constructor
      · intro h; exact congrArg e h
      · intro h; exact e.injective h
    | rel R f =>
      simp only [AtomicIdx.holds]
      have hassoc : (e ∘ a) ∘ f = e ∘ (a ∘ f) := Function.comp_assoc e a f
      rw [hassoc]
      exact (e.map_rel R (a ∘ f)).symm
  | succ β ih =>
    rw [BFEquiv.succ]
    refine ⟨ih n a, ?_, ?_⟩
    · intro m
      use e m
      have : Fin.snoc (e ∘ a) (e m) = e ∘ Fin.snoc a m := by
        ext i; simp only [Fin.snoc, Function.comp_apply]
        split_ifs <;> rfl
      rw [this]
      exact ih (n + 1) (Fin.snoc a m)
    · intro n'
      use e.symm n'
      have h1 : Fin.snoc (e ∘ a) n' = e ∘ Fin.snoc a (e.symm n') := by
        ext i; simp only [Fin.snoc, Function.comp_apply]
        split_ifs with h
        · rfl
        · simp [Equiv.apply_symm_apply]
      rw [h1]
      exact ih (n + 1) (Fin.snoc a (e.symm n'))
  | limit β hβ ih =>
    rw [BFEquiv.limit β hβ]
    intro γ hγ
    exact ih γ hγ n a

/-! ### Stabilization Theory

The key insight is that for countable structures, the BFEquiv equivalence classes form
a refining sequence of partitions on tuples. Since there are only countably many tuples,
this sequence must stabilize before ω₁.

**Partition Argument**: For each α, BFEquiv α defines an equivalence relation on pairs
(a, N, b) where a is an n-tuple from M and b is an n-tuple from some countable N.
As α increases, this relation becomes finer (more distinguishing). But a decreasing
chain of partitions on a countable set has cardinality at most ω, so must stabilize
at some countable ordinal.

**Key Properties of Stabilization**:
1. If StabilizesForTuples M α n, then BFEquiv α n a b ↔ BFEquiv β n a b for all β ≥ α
2. StabilizesCompletely allows the back-and-forth to close: witnesses at level α stay at level α
3. This resolves the quantifier swap issue: we don't need ω, just any stable ordinal -/

/-! Note: StabilizesForTuples for a single tuple size n does NOT propagate to higher
ordinals without also having stabilization for (n+1)-tuples. This is because BFEquiv
at successor levels involves forth/back which creates tuples of size (n+1).

The correct approach is to use StabilizesCompletely which ensures all tuple sizes
stabilize simultaneously. See BFEquiv_upgrade_at_stabilization. -/

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- Self-stabilization: BFEquiv α on n-tuples from M vs M equals BFEquiv (succ α)
for all n. This is weaker than `StabilizesCompletely` which requires the iff
to hold for all countable N, not just M itself. -/
def SelfStabilizesCompletely (M : Type w) [L.Structure M] (α : Ordinal) : Prop :=
  ∀ (n : ℕ) (a a' : Fin n → M),
    BFEquiv (L := L) α n a a' ↔ BFEquiv (L := L) (Order.succ α) n a a'

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- At a complete stabilization ordinal, BFEquiv upgrades to all higher ordinals.
This is the key lemma that resolves the quantifier swap problem.

The proof proceeds by ordinal induction on β. The key insight is that at stabilization,
forth/back witnesses stay at level α, so we can upgrade them along with the base BFEquiv. -/
theorem BFEquiv_upgrade_at_stabilization {M N : Type w} [L.Structure M] [L.Structure N]
    [Countable N]
    {α : Ordinal} (hstab : StabilizesCompletely (L := L) M α)
    {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (h : BFEquiv (L := L) α n a b) (β : Ordinal) (hβ : α ≤ β) :
    BFEquiv (L := L) β n a b := by
  -- We prove by strong induction on β
  induction β using Ordinal.limitRecOn generalizing n a b with
  | zero =>
    -- β = 0: Since α ≤ 0, we have α = 0, so h : BFEquiv 0 n a b is exactly what we need
    have hα0 : α = 0 := le_antisymm hβ (zero_le α)
    rwa [hα0] at h
  | succ γ ih =>
    -- β = succ γ: Need to show BFEquiv (succ γ) n a b
    rw [BFEquiv.succ]
    -- Case split on whether α ≤ γ or α = succ γ
    rcases hβ.lt_or_eq with hlt | heq
    · -- α < succ γ means α ≤ γ
      rw [Order.lt_succ_iff] at hlt
      -- By IH, BFEquiv γ n a b
      have hγ : BFEquiv (L := L) γ n a b := @ih n a b h hlt
      refine ⟨hγ, ?_, ?_⟩
      · -- Forth: for each m : M, find n' : N with BFEquiv γ (n+1) (snoc a m) (snoc b n')
        intro m
        -- Use stabilization to get BFEquiv (succ α) from h
        have h_succ := (hstab n N a b).mp h
        -- From BFEquiv (succ α), get witness n' with BFEquiv α (n+1) (snoc a m) (snoc b n')
        obtain ⟨n', hn'⟩ := BFEquiv.forth h_succ m
        -- By IH (since α ≤ γ), upgrade to BFEquiv γ
        use n'
        exact @ih (n + 1) (Fin.snoc a m) (Fin.snoc b n') hn' hlt
      · -- Back: for each n' : N, find m : M with BFEquiv γ (n+1) (snoc a m) (snoc b n')
        intro n'
        have h_succ := (hstab n N a b).mp h
        obtain ⟨m, hm⟩ := BFEquiv.back h_succ n'
        use m
        exact @ih (n + 1) (Fin.snoc a m) (Fin.snoc b n') hm hlt
    · -- α = succ γ: Need to show this case works
      -- heq : α = Order.succ γ, and we've already unfolded to BFEquiv.succ goal
      -- The goal is BFEquiv γ n a b ∧ forth ∧ back
      -- From heq, h : BFEquiv (succ γ) n a b, so just use BFEquiv.succ
      subst heq
      exact (BFEquiv.succ γ a b).mp h
  | limit β hβlimit ih =>
    -- β is a limit: BFEquiv β ↔ ∀ γ < β, BFEquiv γ
    rw [BFEquiv.limit β hβlimit]
    intro γ hγ
    -- Either γ < α (use monotonicity) or α ≤ γ (use IH)
    by_cases hαγ : α ≤ γ
    · exact @ih γ hγ n a b h hαγ
    · push_neg at hαγ
      exact BFEquiv.monotone (le_of_lt hαγ) h

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- `StabilizesCompletely` implies `StrongStabilizesForTuples` for all tuple sizes.
This is the key property that allows upgrading BFEquiv to arbitrary higher ordinals.
This is essentially a restatement of `BFEquiv_upgrade_at_stabilization` in terms of
`StrongStabilizesForTuples`. -/
theorem StabilizesCompletely.toStrongStabilizesForTuples {M : Type w} [L.Structure M]
    {α : Ordinal} (hstab : StabilizesCompletely (L := L) M α) (n : ℕ) :
    StrongStabilizesForTuples (L := L) M α n := by
  intro N _ _ a b β hαβ
  constructor
  · exact fun h => BFEquiv_upgrade_at_stabilization hstab h β hαβ
  · exact BFEquiv.monotone hαβ

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- **Downward propagation**: If (n+1)-tuples have full stabilization at α, then n-tuples
have full stabilization at succ α.

The key insight: BFEquiv (succ(succ α)) n a b requires BFEquiv (succ α) n a b plus
forth/back at level succ α. The forth/back at succ α involves BFEquiv (succ α) (n+1),
which by the (n+1)-stabilization hypothesis equals BFEquiv α (n+1). But BFEquiv (succ α) n a b
already implies forth/back involving BFEquiv α (n+1) (from the succ definition). So the
additional forth/back at succ α adds no new information, giving the iff. -/
theorem StabilizesForTuples.downward_propagation
    {M : Type w} [L.Structure M]
    {α : Ordinal} {n : ℕ}
    (hstab : StabilizesForTuples (L := L) M α (n + 1)) :
    StabilizesForTuples (L := L) M (Order.succ α) n := by
  intro N _ _ a b
  constructor
  · -- Forward: BFEquiv (succ α) n a b → BFEquiv (succ(succ α)) n a b
    intro hBF
    rw [BFEquiv.succ]
    -- BFEquiv (succ(succ α)) = BFEquiv (succ α) ∧ forth(succ α) ∧ back(succ α)
    refine ⟨hBF, ?_, ?_⟩
    · -- Forth at level succ α: for each m, ∃n', BFEquiv (succ α) (n+1) (snoc a m) (snoc b n')
      intro m
      -- From hBF : BFEquiv (succ α) n a b, the succ structure gives forth at α:
      -- ∃n', BFEquiv α (n+1) (snoc a m) (snoc b n')
      obtain ⟨n', hn'⟩ := BFEquiv.forth hBF m
      use n'
      -- hn' : BFEquiv α (n+1) (snoc a m) (snoc b n')
      -- By (n+1)-stabilization: BFEquiv α (n+1) ↔ BFEquiv (succ α) (n+1)
      exact (hstab N (Fin.snoc a m) (Fin.snoc b n')).mp hn'
    · -- Back at level succ α: for each n', ∃m, BFEquiv (succ α) (n+1) (snoc a m) (snoc b n')
      intro n'
      obtain ⟨m, hm⟩ := BFEquiv.back hBF n'
      use m
      exact (hstab N (Fin.snoc a m) (Fin.snoc b n')).mp hm
  · -- Backward: BFEquiv (succ(succ α)) n a b → BFEquiv (succ α) n a b
    exact BFEquiv.of_succ

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- For countable M, there exists α < ω₁ where all tuple sizes self-stabilize
(BFEquiv α n a a' ↔ BFEquiv (succ α) n a a' for all n and all a, a' : Fin n → M).

**Proof idea**: For each triple (n, a, a'), the sequence α ↦ BFEquiv α n a a' is
antitone (by `BFEquiv.monotone`). Define the "change ordinal" as
`sInf {γ | ¬BFEquiv γ n a a'}` when this set is nonempty; this is the ordinal where
the truth value permanently drops from True to False. For α past the change ordinal,
both BFEquiv α and BFEquiv (succ α) are False, so the iff holds. If the change ordinal
does not exist (BFEquiv is True everywhere) or is ≥ ω₁, then for any α < ω₁ with
succ α < ω₁, both sides are True.

Take globalStab = sup of all change ordinals that are < ω₁ (one per triple).
By countability of the sigma type and regularity of ω₁, globalStab < ω₁.
At globalStab, for each triple, either the change ordinal is ≤ globalStab (both sides
False) or > globalStab (both sides True since succ globalStab < ω₁). -/
theorem exists_complete_self_stabilization (M : Type w) [L.Structure M] [Countable M] :
    ∃ α < (Ordinal.omega 1 : Ordinal.{0}), SelfStabilizesCompletely (L := L) M α := by
  -- For each triple (n, a, a'), define the "change ordinal":
  -- the first level where BFEquiv fails, or 0 if it never fails below ω₁.
  -- We collect an ordinal < ω₁ for each triple such that globalStab past all of them works.
  -- The key: for each triple, either BFEquiv fails at some γ < ω₁ (contribute γ to sup)
  -- or BFEquiv holds at all levels < ω₁ (contribute 0 to sup).
  -- At globalStab = sup + 1:
  --   Failing triples: change ordinal ≤ γ ≤ globalStab, so both sides False, iff holds.
  --   Non-failing triples: BFEquiv True at all < ω₁, and succ globalStab < ω₁, so both True.
  --
  -- Step 1: For each triple, extract a "bound ordinal" < ω₁
  have hTriple : ∀ (t : Σ n, (Fin n → M) × (Fin n → M)),
      ∃ γ < (Ordinal.omega 1 : Ordinal.{0}),
        ∀ α, γ ≤ α → α < Ordinal.omega 1 → Order.succ α < Ordinal.omega 1 →
          (BFEquiv (L := L) α t.1 t.2.1 t.2.2 ↔ BFEquiv (L := L) (Order.succ α) t.1 t.2.1 t.2.2) := by
    intro ⟨n, a, a'⟩
    simp only
    by_cases hFail : ∃ β < (Ordinal.omega 1 : Ordinal.{0}), ¬BFEquiv (L := L) β n a a'
    · -- BFEquiv fails at some level < ω₁
      obtain ⟨β, hβ_lt, hβ_fail⟩ := hFail
      -- The change point: first ordinal where BFEquiv fails
      set S := {δ : Ordinal.{0} | ¬BFEquiv (L := L) δ n a a'} with hS_def
      have hS_nonempty : S.Nonempty := ⟨β, hβ_fail⟩
      have hCP_mem : ¬BFEquiv (L := L) (sInf S) n a a' := csInf_mem hS_nonempty
      have hCP_le_β : sInf S ≤ β := csInf_le' hβ_fail
      use sInf S
      refine ⟨lt_of_le_of_lt hCP_le_β hβ_lt, ?_⟩
      intro α hα _ _
      -- At α ≥ changePoint, BFEquiv α is False
      have hFalse_α : ¬BFEquiv (L := L) α n a a' :=
        fun hBF => hCP_mem (BFEquiv.monotone hα hBF)
      have hFalse_succ : ¬BFEquiv (L := L) (Order.succ α) n a a' :=
        fun hBF => hFalse_α (BFEquiv.of_succ hBF)
      exact ⟨fun h => absurd h hFalse_α, fun h => absurd h hFalse_succ⟩
    · -- BFEquiv holds at all levels < ω₁
      push_neg at hFail
      use 0
      refine ⟨Ordinal.omega_pos 1, ?_⟩
      intro α _ hα_lt hsucc_lt
      exact ⟨fun _ => hFail (Order.succ α) hsucc_lt, fun _ => hFail α hα_lt⟩
  -- Step 2: Extract per-triple bound ordinals
  choose boundOrd hboundOrd_lt hboundOrd_spec using hTriple
  -- Step 3: Enumerate all triples
  haveI : Countable (Σ n, (Fin n → M) × (Fin n → M)) := inferInstance
  -- Handle empty M
  by_cases hM_nonempty : Nonempty M
  swap
  · -- M is empty: self-stabilization is trivial
    haveI : IsEmpty M := not_nonempty_iff.mp hM_nonempty
    use 0
    refine ⟨Ordinal.omega_pos 1, ?_⟩
    intro n a a'
    cases n with
    | zero =>
      constructor
      · intro h0
        rw [BFEquiv.succ]
        exact ⟨h0, fun m => isEmptyElim m, fun m' => isEmptyElim m'⟩
      · exact BFEquiv.of_succ
    | succ k => exact (IsEmpty.false (a 0)).elim
  haveI : Nonempty M := hM_nonempty
  haveI : Nonempty (Σ n, (Fin n → M) × (Fin n → M)) :=
    ⟨⟨0, Fin.elim0, Fin.elim0⟩⟩
  obtain ⟨enumTriples, hTriples_surj⟩ :=
    exists_surjective_nat (Σ n, (Fin n → M) × (Fin n → M))
  -- Step 4: Define globalStab as supremum + 1
  let globalStab : Ordinal.{0} := ⨆ k, boundOrd (enumTriples k) + 1
  -- Step 5: Show globalStab < ω₁
  have hGlobalLt : globalStab < Ordinal.omega 1 := by
    have hEachLt : ∀ k, boundOrd (enumTriples k) + 1 < (Cardinal.aleph 1).ord := by
      intro k; rw [Cardinal.ord_aleph]
      exact Order.IsSuccLimit.succ_lt (Cardinal.isSuccLimit_omega 1)
        (hboundOrd_lt (enumTriples k))
    have hsup := Ordinal.iSup_sequence_lt_omega_one
      (fun k => boundOrd (enumTriples k) + 1) hEachLt
    rw [Cardinal.ord_aleph] at hsup
    exact hsup
  -- Step 6: succ globalStab < ω₁ (since ω₁ is a limit ordinal)
  have hSuccGlobalLt : Order.succ globalStab < Ordinal.omega 1 :=
    Order.IsSuccLimit.succ_lt (Cardinal.isSuccLimit_omega 1) hGlobalLt
  -- Step 7: Show globalStab satisfies SelfStabilizesCompletely
  use globalStab, hGlobalLt
  intro n a a'
  -- Get the triple's index
  obtain ⟨k, hk⟩ := hTriples_surj ⟨n, a, a'⟩
  -- boundOrd for this triple
  have hBdd : BddAbove (Set.range fun k => boundOrd (enumTriples k) + 1) :=
    ⟨Ordinal.omega 1, fun _ ⟨m, hm⟩ => hm ▸ le_of_lt
      (Order.IsSuccLimit.succ_lt (Cardinal.isSuccLimit_omega 1)
        (hboundOrd_lt (enumTriples m)))⟩
  have hk_le : boundOrd ⟨n, a, a'⟩ + 1 ≤ globalStab := by
    have h := le_ciSup hBdd k
    simp only [hk] at h
    exact h
  have hbound_le : boundOrd ⟨n, a, a'⟩ ≤ globalStab :=
    le_trans (Order.le_succ _) hk_le
  exact hboundOrd_spec ⟨n, a, a'⟩ globalStab hbound_le hGlobalLt hSuccGlobalLt

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- For countable M and N, BFEquiv at all ordinals below ω₁ implies BFEquiv at all ordinals.

The key step uses a sup + regularity argument: for FORTH (or BACK) at any ordinal β,
we need to find a witness n' (or m). By contradiction: if no witness works, each candidate
fails at some ordinal α_{candidate} < ω₁. Taking the sup over a countable enumeration
(which is < ω₁ by regularity since cof(ω₁) = ω₁ > ω) gives a level where the
forth/back condition does produce a witness, contradicting the assumed failure.

The enumeration via `exists_surjective_nat` avoids universe issues (both M and N may live
in arbitrary universes, but ℕ → Ordinal.{0} can always be bounded by `iSup_sequence_lt_omega_one`). -/
private theorem BFEquiv_all_countable_ordinals_implies_all
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N]
    {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (h : ∀ α < (Ordinal.omega 1 : Ordinal.{0}), BFEquiv (L := L) α n a b) :
    ∀ α : Ordinal.{0}, BFEquiv (L := L) α n a b := by
  intro α
  induction α using Ordinal.limitRecOn generalizing n a b with
  | zero => exact h 0 (Ordinal.omega_pos 1)
  | succ β ih =>
    rw [BFEquiv.succ]
    have hβ : BFEquiv (L := L) β n a b := ih (fun γ hγ => h γ hγ)
    refine ⟨hβ, ?_, ?_⟩
    · -- Forth: for each m : M, ∃ n' : N, BFEquiv β (n+1) (snoc a m) (snoc b n')
      intro m
      by_contra h_no
      push_neg at h_no
      -- If N is empty, BFEquiv at succ level requires forth, giving ∃ n' : N which is False
      by_cases hN : IsEmpty N
      · have hsucc0_lt : Order.succ 0 < Ordinal.omega 1 :=
          Order.IsSuccLimit.succ_lt (Cardinal.isSuccLimit_omega 1) (Ordinal.omega_pos 1)
        exact hN.false (BFEquiv.forth (h _ hsucc0_lt) m).choose
      · -- N nonempty: use enumeration
        rw [not_isEmpty_iff] at hN; haveI := hN
        have hnfail : ∀ n' : N, ∃ γ < (Ordinal.omega 1 : Ordinal.{0}),
            ¬BFEquiv (L := L) γ (n + 1) (Fin.snoc a m) (Fin.snoc b n') := by
          intro n'
          by_contra hall
          push_neg at hall
          exact h_no n' (ih (fun γ hγ => hall γ hγ))
        choose αbad hαbad_lt hαbad_fail using hnfail
        obtain ⟨enum, henum⟩ := exists_surjective_nat N
        let αbad_seq : ℕ → Ordinal.{0} := αbad ∘ enum
        have hαbad_seq_lt : ∀ k, αbad_seq k < (Cardinal.aleph 1).ord := by
          intro k; rw [Cardinal.ord_aleph]; exact hαbad_lt (enum k)
        have hS_lt : (⨆ k, αbad_seq k) < Ordinal.omega 1 := by
          rw [← Cardinal.ord_aleph]
          exact Ordinal.iSup_sequence_lt_omega_one αbad_seq hαbad_seq_lt
        have hbdd_seq : BddAbove (Set.range αbad_seq) :=
          ⟨Ordinal.omega 1, fun _ ⟨k, hk⟩ => hk ▸ le_of_lt (hαbad_lt (enum k))⟩
        have hle_sup : ∀ n' : N, αbad n' ≤ ⨆ k, αbad_seq k := by
          intro n'
          obtain ⟨k, hk⟩ := henum n'
          calc αbad n' = αbad (enum k) := by rw [hk]
            _ = αbad_seq k := rfl
            _ ≤ ⨆ k, αbad_seq k := le_ciSup hbdd_seq k
        set S := ⨆ k, αbad_seq k
        have hsucc_lt : Order.succ S < Ordinal.omega 1 :=
          Order.IsSuccLimit.succ_lt (Cardinal.isSuccLimit_omega 1) hS_lt
        have hBF_succ : BFEquiv (L := L) (Order.succ S) n a b := h _ hsucc_lt
        obtain ⟨n'₀, hn'₀⟩ := BFEquiv.forth hBF_succ m
        exact hαbad_fail n'₀ (BFEquiv.monotone (hle_sup n'₀) hn'₀)
    · -- Back: for each n' : N, ∃ m : M, BFEquiv β (n+1) (snoc a m) (snoc b n')
      intro n'
      by_contra h_no
      push_neg at h_no
      -- If M is empty, back at succ level gives m : M, contradicting emptiness
      by_cases hM : IsEmpty M
      · have hsucc0_lt : Order.succ 0 < Ordinal.omega 1 :=
          Order.IsSuccLimit.succ_lt (Cardinal.isSuccLimit_omega 1) (Ordinal.omega_pos 1)
        exact hM.false (BFEquiv.back (h _ hsucc0_lt) n').choose
      · -- M nonempty: use enumeration
        rw [not_isEmpty_iff] at hM; haveI := hM
        have hmfail : ∀ m : M, ∃ γ < (Ordinal.omega 1 : Ordinal.{0}),
            ¬BFEquiv (L := L) γ (n + 1) (Fin.snoc a m) (Fin.snoc b n') := by
          intro m
          by_contra hall
          push_neg at hall
          exact h_no m (ih (fun γ hγ => hall γ hγ))
        choose αbad hαbad_lt hαbad_fail using hmfail
        obtain ⟨enum, henum⟩ := exists_surjective_nat M
        let αbad_seq : ℕ → Ordinal.{0} := αbad ∘ enum
        have hαbad_seq_lt : ∀ k, αbad_seq k < (Cardinal.aleph 1).ord := by
          intro k; rw [Cardinal.ord_aleph]; exact hαbad_lt (enum k)
        have hS_lt : (⨆ k, αbad_seq k) < Ordinal.omega 1 := by
          rw [← Cardinal.ord_aleph]
          exact Ordinal.iSup_sequence_lt_omega_one αbad_seq hαbad_seq_lt
        have hbdd_seq : BddAbove (Set.range αbad_seq) :=
          ⟨Ordinal.omega 1, fun _ ⟨k, hk⟩ => hk ▸ le_of_lt (hαbad_lt (enum k))⟩
        have hle_sup : ∀ m : M, αbad m ≤ ⨆ k, αbad_seq k := by
          intro m
          obtain ⟨k, hk⟩ := henum m
          calc αbad m = αbad (enum k) := by rw [hk]
            _ = αbad_seq k := rfl
            _ ≤ ⨆ k, αbad_seq k := le_ciSup hbdd_seq k
        set S := ⨆ k, αbad_seq k
        have hsucc_lt : Order.succ S < Ordinal.omega 1 :=
          Order.IsSuccLimit.succ_lt (Cardinal.isSuccLimit_omega 1) hS_lt
        have hBF_succ : BFEquiv (L := L) (Order.succ S) n a b := h _ hsucc_lt
        obtain ⟨m₀, hm₀⟩ := BFEquiv.back hBF_succ n'
        exact hαbad_fail m₀ (BFEquiv.monotone (hle_sup m₀) hm₀)
  | limit β hβlimit ih =>
    rw [BFEquiv.limit β hβlimit]
    intro γ hγ
    exact ih γ hγ (fun δ hδ => h δ hδ)

/-! ### Countable intersection and BFEquiv-to-PotentialIso lemmas -/

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- A decreasing ω₁-chain of nonempty subsets of a countable type has nonempty intersection.

More precisely: if `S : Ordinal → Set X` where `X` is countable, `S` is antitone
(S α ⊇ S β for α ≤ β), and each `S α` is nonempty for `α < ω₁`, then
`⋂ α < ω₁, S α` is nonempty.

**Proof**: For each `x ∈ S 0`, define `d(x) = sInf {α | x ∉ S α}` (the "departure ordinal").
If all `d(x) < ω₁`, then `sup {d(x)} < ω₁` by regularity of ω₁ and countability of X.
Let `γ = sup {d(x)}`. Then `S γ = ∅` (every element has departed), contradicting nonemptiness.
So some `x` has `d(x) ≥ ω₁`, meaning `x ∈ S α` for all `α < ω₁`. -/
theorem nonempty_iInter_of_antitone_of_nonempty {X : Type*} [Countable X]
    (S : Ordinal.{0} → Set X) (hAnti : Antitone S)
    (hNonempty : ∀ α < (Ordinal.omega 1 : Ordinal.{0}), (S α).Nonempty) :
    (⋂ α ∈ Set.Iio (Ordinal.omega 1 : Ordinal.{0}), S α).Nonempty := by
  classical
  -- For each x, define d(x) = sInf {α | x ∉ S α} (possibly = 0 if x ∉ S 0)
  -- If d(x) ≥ ω₁ for some x, then x ∈ S α for all α < ω₁ and we're done.
  by_contra hEmpty
  rw [Set.not_nonempty_iff_eq_empty] at hEmpty
  -- Every x eventually departs: for every x ∈ S 0, ∃ α < ω₁ with x ∉ S α
  have hAllDepart : ∀ x ∈ S 0, ∃ α < (Ordinal.omega 1 : Ordinal.{0}), x ∉ S α := by
    intro x hx0
    by_contra hall
    push_neg at hall
    -- x ∈ S α for all α < ω₁
    have hxmem : x ∈ ⋂ α ∈ Set.Iio (Ordinal.omega 1 : Ordinal.{0}), S α := by
      simp only [Set.mem_iInter, Set.mem_Iio]
      exact fun α hα => hall α hα
    rw [hEmpty] at hxmem
    exact hxmem
  -- For each x ∈ S 0, choose a departure ordinal < ω₁
  have hS0nonempty : (S 0).Nonempty := hNonempty 0 (Ordinal.omega_pos 1)
  -- Get departure ordinals for ALL elements (set to 0 for x ∉ S 0)
  let depart : X → Ordinal.{0} := fun x =>
    if hx : x ∈ S 0 then (hAllDepart x hx).choose else 0
  have hdepart_lt : ∀ x ∈ S 0, depart x < Ordinal.omega 1 := by
    intro x hx
    simp only [depart]
    rw [dif_pos hx]
    exact (hAllDepart x hx).choose_spec.1
  have hdepart_spec : ∀ x ∈ S 0, x ∉ S (depart x) := by
    intro x hx
    simp only [depart]
    rw [dif_pos hx]
    exact (hAllDepart x hx).choose_spec.2
  -- Enumerate X (or rather S 0)
  -- Take sup of departure ordinals over all of X
  -- Enumerate X via ℕ to use iSup_sequence_lt_omega_one
  by_cases hX : IsEmpty X
  · -- If X is empty, S 0 = ∅, contradicting nonemptiness
    exact absurd (hNonempty 0 (Ordinal.omega_pos 1)) (by
      rw [Set.not_nonempty_iff_eq_empty, Set.eq_empty_iff_forall_notMem]
      intro x; exact hX.elim x)
  rw [not_isEmpty_iff] at hX; haveI := hX
  obtain ⟨enum, henum⟩ := exists_surjective_nat X
  -- Compose depart with enum to get ℕ → Ordinal.{0}
  let depart_seq : ℕ → Ordinal.{0} := depart ∘ enum
  have hdepart_seq_lt : ∀ k, depart_seq k < (Cardinal.aleph 1).ord := by
    intro k
    rw [Cardinal.ord_aleph]
    by_cases hx : enum k ∈ S 0
    · exact hdepart_lt (enum k) hx
    · show depart (enum k) < _
      simp only [depart]
      rw [dif_neg hx]
      exact Ordinal.omega_pos 1
  have hSup_lt : (⨆ k, depart_seq k) < Ordinal.omega 1 := by
    rw [← Cardinal.ord_aleph]
    exact Ordinal.iSup_sequence_lt_omega_one depart_seq hdepart_seq_lt
  have hBdd_seq : BddAbove (Set.range depart_seq) :=
    ⟨Ordinal.omega 1, fun _ ⟨k, hk⟩ => hk ▸ le_of_lt
      (by rw [Cardinal.ord_aleph] at hdepart_seq_lt; exact hdepart_seq_lt k)⟩
  have hle_sup : ∀ x : X, depart x ≤ ⨆ k, depart_seq k := by
    intro x
    obtain ⟨k, hk⟩ := henum x
    calc depart x = depart (enum k) := by rw [hk]
      _ = depart_seq k := rfl
      _ ≤ ⨆ k, depart_seq k := le_ciSup hBdd_seq k
  -- S (iSup depart_seq) is nonempty
  obtain ⟨x, hx⟩ := hNonempty (⨆ k, depart_seq k) hSup_lt
  -- x ∈ S (iSup depart_seq) ⊆ S 0
  have hx0 : x ∈ S 0 := hAnti (zero_le _) hx
  -- But depart x ≤ iSup depart_seq, so S (iSup ...) ⊆ S (depart x)
  -- And x ∉ S (depart x), contradiction
  exact hdepart_spec x hx0 (hAnti (hle_sup x) hx)

omit [Countable (Σ l, L.Relations l)] in
/-- If two countable structures are BF-equivalent at all ordinal levels below ω₁
(for the empty tuple), then there exists a potential isomorphism between them,
and hence they are isomorphic.

**Proof**: Define the family
`F = {(k, a, b) | ∀ α < ω₁, BFEquiv α k a b}`.
This family contains the empty tuple (by hypothesis) and is compatible (BFEquiv 0 gives
SameAtomicType). For the forth property: given (k, a, b) ∈ F and m : M, for each α < ω₁,
from BFEquiv (succ α) k a b (since succ α < ω₁ by regularity), BFEquiv.forth gives
n'_α with BFEquiv α (k+1) (snoc a m) (snoc b n'_α). The sets
`S_α = {n' ∈ N | BFEquiv α (k+1) (snoc a m) (snoc b n')}` form a decreasing chain
(by BFEquiv.monotone) of nonempty subsets of the countable type N.
By `nonempty_iInter_of_antitone_of_nonempty`, ∃ n' in the intersection, giving
BFEquiv α (k+1) (snoc a m) (snoc b n') for all α < ω₁. The back property is symmetric.

The result then follows from `PotentialIso.countable_toEquiv`. -/
theorem BFEquiv_below_omega1_implies_potentialIso
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N]
    (h : ∀ α < (Ordinal.omega 1 : Ordinal.{0}),
      BFEquiv (L := L) α 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N)) :
    Nonempty (PotentialIso L M N) := by
  -- Define the family: tuples that are BF-equivalent at ALL levels < ω₁
  let F : Set (Σ n : ℕ, (Fin n → M) × (Fin n → N)) :=
    { p | ∀ α < (Ordinal.omega 1 : Ordinal.{0}), BFEquiv (L := L) α p.1 p.2.1 p.2.2 }
  -- empty_mem: by hypothesis
  have hempty : ⟨0, Fin.elim0, Fin.elim0⟩ ∈ F := h
  -- compatible: BFEquiv 0 gives SameAtomicType
  have hcompat : ∀ p ∈ F, SameAtomicType (L := L) p.2.1 p.2.2 := by
    intro p hp
    exact (BFEquiv.zero p.2.1 p.2.2).mp (hp 0 (Ordinal.omega_pos 1))
  -- forth: use the countable intersection lemma
  have hforth : ∀ p ∈ F, ∀ m : M, ∃ n' : N,
      ⟨p.1 + 1, Fin.snoc p.2.1 m, Fin.snoc p.2.2 n'⟩ ∈ F := by
    intro ⟨k, a, b⟩ hp m
    simp only [Set.mem_setOf_eq, F] at hp ⊢
    -- For each α < ω₁, succ α < ω₁ (ω₁ is a limit), so BFEquiv (succ α) k a b holds.
    -- By forth, ∃ n'_α with BFEquiv α (k+1) (snoc a m) (snoc b n'_α).
    -- Define S_α = {n' | BFEquiv α (k+1) (snoc a m) (snoc b n')}
    let S : Ordinal.{0} → Set N := fun α =>
      { n' | BFEquiv (L := L) α (k + 1) (Fin.snoc a m) (Fin.snoc b n') }
    -- S is antitone
    have hAnti : Antitone S := by
      intro α β hαβ n' hn'
      simp only [Set.mem_setOf_eq, S] at hn' ⊢
      exact BFEquiv.monotone hαβ hn'
    -- Each S α is nonempty for α < ω₁
    have hNonempty : ∀ α < (Ordinal.omega 1 : Ordinal.{0}), (S α).Nonempty := by
      intro α hα
      have hsucc_lt : Order.succ α < Ordinal.omega 1 :=
        Order.IsSuccLimit.succ_lt (Cardinal.isSuccLimit_omega 1) hα
      obtain ⟨n', hn'⟩ := BFEquiv.forth (hp (Order.succ α) hsucc_lt) m
      exact ⟨n', hn'⟩
    -- By countable intersection lemma
    obtain ⟨n', hn'⟩ := nonempty_iInter_of_antitone_of_nonempty S hAnti hNonempty
    simp only [Set.mem_iInter, Set.mem_Iio, Set.mem_setOf_eq, S] at hn'
    exact ⟨n', hn'⟩
  -- back: symmetric argument
  have hback : ∀ p ∈ F, ∀ n' : N, ∃ m : M,
      ⟨p.1 + 1, Fin.snoc p.2.1 m, Fin.snoc p.2.2 n'⟩ ∈ F := by
    intro ⟨k, a, b⟩ hp n'
    simp only [Set.mem_setOf_eq, F] at hp ⊢
    let S : Ordinal.{0} → Set M := fun α =>
      { m | BFEquiv (L := L) α (k + 1) (Fin.snoc a m) (Fin.snoc b n') }
    have hAnti : Antitone S := by
      intro α β hαβ m hm
      simp only [Set.mem_setOf_eq, S] at hm ⊢
      exact BFEquiv.monotone hαβ hm
    have hNonempty : ∀ α < (Ordinal.omega 1 : Ordinal.{0}), (S α).Nonempty := by
      intro α hα
      have hsucc_lt : Order.succ α < Ordinal.omega 1 :=
        Order.IsSuccLimit.succ_lt (Cardinal.isSuccLimit_omega 1) hα
      obtain ⟨m, hm⟩ := BFEquiv.back (hp (Order.succ α) hsucc_lt) n'
      exact ⟨m, hm⟩
    obtain ⟨m, hm⟩ := nonempty_iInter_of_antitone_of_nonempty S hAnti hNonempty
    simp only [Set.mem_iInter, Set.mem_Iio, Set.mem_setOf_eq, S] at hm
    exact ⟨m, hm⟩
  exact ⟨PotentialIso.mk F hempty hcompat hforth hback⟩

omit [Countable (Σ l, L.Relations l)] in
/-- Corollary: If BFEquiv at all levels below ω₁ for empty tuples between countable structures,
then they are isomorphic. Combines `BFEquiv_below_omega1_implies_potentialIso` with
`PotentialIso.countable_toEquiv`. -/
theorem BFEquiv_below_omega1_implies_iso
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N]
    (h : ∀ α < (Ordinal.omega 1 : Ordinal.{0}),
      BFEquiv (L := L) α 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N)) :
    Nonempty (M ≃[L] N) := by
  obtain ⟨P⟩ := BFEquiv_below_omega1_implies_potentialIso (L := L) h
  exact P.countable_toEquiv

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- Strong stabilization from the extension iff: if the iff holds at all `α ≥ γ` for a
specific (n+1)-tuple, then BFEquiv at `γ` implies BFEquiv at all higher levels. -/
private theorem BFEquiv_upgrade_from_iff
    {M : Type w} [L.Structure M]
    {N : Type w} [L.Structure N] [Countable N]
    {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (γ : Ordinal.{0}) (_hγ_lt : γ < Ordinal.omega 1)
    (hiff : ∀ α, γ ≤ α → α < Ordinal.omega 1 → Order.succ α < Ordinal.omega 1 →
        (BFEquiv (L := L) α n a b ↔ BFEquiv (L := L) (Order.succ α) n a b))
    (hBF : BFEquiv (L := L) γ n a b) :
    ∀ β, γ ≤ β → β < Ordinal.omega 1 → BFEquiv (L := L) β n a b := by
  intro β hβ_ge hβ_lt
  induction β using Ordinal.limitRecOn with
  | zero => exact BFEquiv.monotone (zero_le _) hBF
  | succ δ ih =>
    rcases hβ_ge.lt_or_eq with hlt | heq
    · rw [Order.lt_succ_iff] at hlt
      have hδ_lt := lt_of_lt_of_le (Order.lt_succ δ) (le_of_lt hβ_lt)
      exact (hiff δ hlt hδ_lt hβ_lt).mp (ih hlt hδ_lt)
    · rw [← heq]; exact hBF
  | limit lim hlim ih =>
    rw [BFEquiv.limit lim hlim]
    intro δ hδ
    by_cases hge : γ ≤ δ
    · exact ih δ hδ hge (lt_trans hδ hβ_lt)
    · push_neg at hge
      exact BFEquiv.monotone (le_of_lt hge) hBF

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- Per-tuple stabilization from extensions: if each (n+1)-extension `(Fin.snoc a m)` has
a stabilization bound `γ m` (the iff `BFEquiv α ↔ BFEquiv (succ α)` holds for all `α ≥ γ m`
and all countable `(N, b)`), then `(n, a)` itself has a stabilization bound at
`Order.succ S` where `S = sup_m (γ m)`.

The key insight: at the (n+1)-level, the extension iff gives strong stabilization
(BFEquiv constant past `γ m`). So the forth/back witness sets stabilize: for `β ≥ γ m`,
the set of valid witnesses is the same as at `γ m`. This handles both successor `α`
(witnesses from forth/back at `δ ≥ S`) and limit `α` (intersection of stabilized sets). -/
private theorem per_tuple_stabilization_from_extensions
    {M : Type w} [L.Structure M]
    {n : ℕ} {a : Fin n → M}
    (γ : M → Ordinal.{0})
    (hγ : ∀ m, ∀ α, γ m ≤ α → α < Ordinal.omega 1 → Order.succ α < Ordinal.omega 1 →
      ∀ (N : Type w) [L.Structure N] [Countable N] (b : Fin (n + 1) → N),
        (BFEquiv (L := L) α (n + 1) (Fin.snoc a m) b ↔
         BFEquiv (L := L) (Order.succ α) (n + 1) (Fin.snoc a m) b))
    (hγ_lt : ∀ m, γ m < Ordinal.omega 1)
    (S : Ordinal.{0}) (hS : ∀ m, γ m ≤ S)
    (_hS_lt : S < Ordinal.omega 1) :
    ∀ α, Order.succ S ≤ α → α < Ordinal.omega 1 → Order.succ α < Ordinal.omega 1 →
      ∀ (N : Type w) [L.Structure N] [Countable N] (b : Fin n → N),
        (BFEquiv (L := L) α n a b ↔ BFEquiv (L := L) (Order.succ α) n a b) := by
  -- Helper: the extension iff for (snoc a m) gives strong stabilization:
  -- BFEquiv (γ m) (n+1) (snoc a m) c implies BFEquiv β (n+1) (snoc a m) c for all β ≥ γ m.
  have hstrong : ∀ (m : M) (N' : Type w) [L.Structure N'] [Countable N']
      (c : Fin (n + 1) → N'),
      BFEquiv (L := L) (γ m) (n + 1) (Fin.snoc a m) c →
      ∀ β, γ m ≤ β → β < Ordinal.omega 1 →
        BFEquiv (L := L) β (n + 1) (Fin.snoc a m) c := by
    intro m N' _ _ c hc β hβ hβ_lt
    exact BFEquiv_upgrade_from_iff (γ m) (hγ_lt m)
      (fun α hα hα_lt hsucc_lt => hγ m α hα hα_lt hsucc_lt N' c) hc β hβ hβ_lt
  intro α hα_ge hα_lt hsucc_lt N instN instCN b
  constructor
  · -- Forward: BFEquiv α n a b → BFEquiv (succ α) n a b
    intro hBF
    rw [BFEquiv.succ]
    refine ⟨hBF, ?_, ?_⟩
    · -- Forth at α: for m, ∃ n', BFEquiv α (n+1) (snoc a m) (snoc b n')
      intro m
      -- Get a witness from a level below α where we have BFEquiv (succ _)
      -- BFEquiv (succ S) n a b holds (since succ S ≤ α, monotonicity)
      have hBF_succS : BFEquiv (L := L) (Order.succ S) n a b :=
        BFEquiv.monotone hα_ge hBF
      -- Forth at S gives n' with BFEquiv S (n+1) (snoc a m) (snoc b n')
      obtain ⟨n', hn'⟩ := BFEquiv.forth hBF_succS m
      -- Since S ≥ γ m: strong stabilization upgrades to BFEquiv α (n+1)
      exact ⟨n', hstrong m N (Fin.snoc b n')
        (BFEquiv.monotone (hS m) hn') α (le_trans (hS m) (Order.le_succ S |>.trans hα_ge))
        hα_lt⟩
    · -- Back at α: for n', ∃ m, BFEquiv α (n+1) (snoc a m) (snoc b n')
      intro n'
      have hBF_succS : BFEquiv (L := L) (Order.succ S) n a b :=
        BFEquiv.monotone hα_ge hBF
      obtain ⟨m₀, hm₀⟩ := BFEquiv.back hBF_succS n'
      exact ⟨m₀, hstrong m₀ N (Fin.snoc b n')
        (BFEquiv.monotone (hS m₀) hm₀) α
        (le_trans (hS m₀) (Order.le_succ S |>.trans hα_ge)) hα_lt⟩
  · exact BFEquiv.of_succ

/-! ### Refinement Descent Lemmas

These lemmas decompose refinement failures at n-tuples into refinement failures at
(n+1)-tuples at strictly smaller ordinals. They are the key infrastructure for proving
`per_tuple_stabilization_below_omega1` without relying on the `FormulaCode` bridge. -/

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- At a successor refinement ordinal `succ δ`, the failure of `BFEquiv (succ(succ δ))`
(while `BFEquiv (succ δ)` holds) produces a refinement at the (n+1)-tuple level at ordinal δ.

The proof is by contradiction: if every (n+1)-extension with `BFEquiv δ` also satisfies
`BFEquiv (succ δ)`, then we can rebuild `BFEquiv (succ(succ δ))` from the forth/back
witnesses at level δ (which come from `BFEquiv (succ δ)`), contradicting the hypothesis. -/
theorem refinement_descent_succ
    {M : Type w} [L.Structure M] {N : Type w'} [L.Structure N]
    {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    {δ : Ordinal}
    (hBF : BFEquiv (L := L) (Order.succ δ) n a b)
    (hNotBF : ¬BFEquiv (L := L) (Order.succ (Order.succ δ)) n a b) :
    ∃ m : M, ∃ n' : N,
      BFEquiv (L := L) δ (n + 1) (Fin.snoc a m) (Fin.snoc b n') ∧
      ¬BFEquiv (L := L) (Order.succ δ) (n + 1) (Fin.snoc a m) (Fin.snoc b n') := by
  by_contra h
  push_neg at h
  apply hNotBF
  rw [BFEquiv.succ]
  refine ⟨hBF, ?_, ?_⟩
  · intro m
    obtain ⟨n', hn'⟩ := BFEquiv.forth hBF m
    exact ⟨n', h m n' hn'⟩
  · intro n'
    obtain ⟨m, hm⟩ := BFEquiv.back hBF n'
    exact ⟨m, h m n' hm⟩

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- If BFEquiv holds at δ but fails at α (with δ < α), there exists a refinement
ordinal ε ∈ [δ, α) where BFEquiv ε holds but BFEquiv (succ ε) fails.

This follows from well-foundedness of ordinals: the first failure ordinal above δ
must be a successor (limits can't be first failures, since BFEquiv at a limit is the
conjunction of all lower levels). -/
theorem exists_refinement_between
    {M : Type w} [L.Structure M] {N : Type w'} [L.Structure N]
    {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    {δ α : Ordinal}
    (hδα : δ < α)
    (hBFδ : BFEquiv (L := L) δ n a b)
    (hNotBFα : ¬BFEquiv (L := L) α n a b) :
    ∃ ε, δ ≤ ε ∧ ε < α ∧
      BFEquiv (L := L) ε n a b ∧
      ¬BFEquiv (L := L) (Order.succ ε) n a b := by
  set S := Set.Ioi δ ∩ {γ | ¬BFEquiv (L := L) γ n a b}
  have hne : S.Nonempty := ⟨α, hδα, hNotBFα⟩
  set β := sInf S with hβ_def
  have hβ_mem : β ∈ S := csInf_mem hne
  have hβ_gt_δ : δ < β := hβ_mem.1
  have hβ_fail : ¬BFEquiv (L := L) β n a b := hβ_mem.2
  have hβ_le_α : β ≤ α :=
    csInf_le (OrderBot.bddBelow S) (Set.mem_inter hδα hNotBFα)
  have hβ_min : ∀ γ, δ < γ → γ < β → BFEquiv (L := L) γ n a b := by
    intro γ hγδ hγβ
    by_contra h
    exact not_lt.mpr (csInf_le (OrderBot.bddBelow S) (Set.mem_inter hγδ h)) hγβ
  by_cases hβ_sl : Order.IsSuccLimit β
  · exact absurd ((BFEquiv.limit β hβ_sl a b).mpr fun γ hγ =>
      (le_or_gt γ δ).elim (fun h => BFEquiv.monotone h hBFδ) (fun h => hβ_min γ h hγ)) hβ_fail
  · have hβ_notMin : ¬IsMin β := not_isMin_of_lt (lt_of_le_of_lt bot_le hβ_gt_δ)
    have : ¬Order.IsSuccPrelimit β := fun h => hβ_sl ⟨hβ_notMin, h⟩
    rw [Order.not_isSuccPrelimit_iff] at this
    obtain ⟨ε, _, hεβ⟩ := this
    have hBFε : BFEquiv (L := L) ε n a b :=
      (le_or_gt ε δ).elim (fun h => BFEquiv.monotone h hBFδ)
        (fun h => hβ_min ε h (hεβ ▸ Order.lt_succ ε))
    refine ⟨ε, ?_, ?_, hBFε, ?_⟩
    · exact Order.lt_succ_iff.mp (hεβ ▸ hβ_gt_δ)
    · calc ε < Order.succ ε := Order.lt_succ ε
        _ = β := hεβ
        _ ≤ α := hβ_le_α
    · rw [show (Order.succ ε) = β from hεβ]; exact hβ_fail

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- At a limit refinement ordinal α (BFEquiv α holds but BFEquiv (succ α) fails),
the forth/back failure at level α generates refinement ordinals below α for extensions.

The proof decomposes ¬BFEquiv (succ α) into forth or back failure at level α, then uses
`exists_refinement_between` to find a successor refinement ordinal for the extension. -/
theorem refinement_descent_limit
    {M : Type w} [L.Structure M] {N : Type w'} [L.Structure N]
    {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    {α : Ordinal} (hα_limit : Order.IsSuccLimit α)
    (hBF : BFEquiv (L := L) α n a b)
    (hNotBF : ¬BFEquiv (L := L) (Order.succ α) n a b) :
    ∃ m : M, ∃ n' : N, ∃ ε < α,
      BFEquiv (L := L) ε (n + 1) (Fin.snoc a m) (Fin.snoc b n') ∧
      ¬BFEquiv (L := L) (Order.succ ε) (n + 1) (Fin.snoc a m) (Fin.snoc b n') := by
  rw [BFEquiv.succ] at hNotBF
  have hFB : ¬((∀ m : M, ∃ n' : N,
      BFEquiv (L := L) α (n + 1) (Fin.snoc a m) (Fin.snoc b n')) ∧
      (∀ n' : N, ∃ m : M,
      BFEquiv (L := L) α (n + 1) (Fin.snoc a m) (Fin.snoc b n'))) := by
    intro ⟨hf, hb⟩; exact hNotBF ⟨hBF, hf, hb⟩
  rw [not_and_or] at hFB
  have hα_pos : (0 : Ordinal) < α := hα_limit.bot_lt
  have hBFsucc0 : BFEquiv (L := L) (Order.succ 0) n a b :=
    BFEquiv.monotone (Order.succ_le_of_lt hα_pos) hBF
  rcases hFB with hNotForth | hNotBack
  · -- Forth fails: ∃ m₀, ∀ n', ¬BFEquiv α (n+1) (snoc a m₀) (snoc b n')
    push_neg at hNotForth
    obtain ⟨m₀, hm₀⟩ := hNotForth
    obtain ⟨n'₀, hn'₀⟩ := BFEquiv.forth hBFsucc0 m₀
    obtain ⟨ε, _, hε_lt, hBFε, hNotBFε⟩ :=
      exists_refinement_between hα_pos hn'₀ (hm₀ n'₀)
    exact ⟨m₀, n'₀, ε, hε_lt, hBFε, hNotBFε⟩
  · -- Back fails: ∃ n'₀, ∀ m, ¬BFEquiv α (n+1) (snoc a m) (snoc b n'₀)
    push_neg at hNotBack
    obtain ⟨n'₀, hn'₀⟩ := hNotBack
    obtain ⟨m₀, hm₀⟩ := BFEquiv.back hBFsucc0 n'₀
    obtain ⟨ε, _, hε_lt, hBFε, hNotBFε⟩ :=
      exists_refinement_between hα_pos hm₀ (hn'₀ m₀)
    exact ⟨m₀, n'₀, ε, hε_lt, hBFε, hNotBFε⟩

/-! ### Infrastructure for proving `per_tuple_stabilization_below_omega1` (Code-based approach)

The formula-type counting approach: `BFEquiv_iff_agree_formulas_omega` reduces BFEquiv
at level α to agreement on all Lω₁ω formulas of quantifier rank ≤ α. The `FormulaCode`
type (from `Scott.Code`) provides a countable proxy for these formulas. Each refinement
step (α → α+1) is witnessed by a separating code, and since codes are countable, the
total number of refinement steps is countable, giving stabilization below ω₁. -/

/-- The set of ordinals α < ω₁ where BFEquiv α ↔ BFEquiv (succ α) fails for some (N, b)
is countable. This is the direct ingredient for `per_tuple_stabilization_below_omega1`:
a countable set of ordinals below ω₁ has supremum below ω₁.

Each refinement step α has a separating code c ∈ FormulaCode L n with qrank(c) = succ α.
The map α ↦ c is injective (different α give different qranks), giving an injection
into a countable type.

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

/-- Per-tuple stabilization: for any tuple (n, a) from a countable structure M,
there exists γ < ω₁ such that for all α ≥ γ (with α, succ α < ω₁), the BFEquiv iff
holds uniformly for all countable structures N and tuples b.

This is the **sole assumption** blocking the Scott analysis pipeline. All downstream
results (`exists_complete_stabilization`, `scottRank_le_implies_stabilizesCompletely`,
`scottHeight_lt_omega1`, `scottSentence_characterizes`, etc.) are sorry-free in their
own proofs and depend only on this theorem.

**Trust boundary**: depends on `agree_codes_implies_BFEquiv` via `countable_refinement_steps`.

**Proof strategy**: The standard textbook proof (Marker, Keisler-Knight) uses a
*counting types* argument: for fixed (M, a), the "α-type" is the partition of countable
(N, b) pairs into BFEquiv-true and BFEquiv-false. As α increases, the partition refines
monotonically (elements only move from true to false). Each (N, b) has a unique "first
failure ordinal" β(N,b) which is always 0 or a successor (BFEquiv at limits is the
conjunction of all lower levels). The key is showing sup{β(N,b)} < ω₁, which requires
bounding the number of *distinct* first-failure ordinals.

**Viable approaches**:
(a) Use `BFEquiv_iff_agree_formulas_omega` to reduce BFEquiv types to Lω₁ω formula types.
    Since formulas at each quantifier rank over a countable signature are countable, the
    number of distinct formula-types is countable, giving the bound. See
    `countable_first_failure_ordinals` and `countable_refinement_steps` below.
(b) A direct counting-types argument on the game-theoretic BFEquiv, showing the quotient
    of countable (N, b) by BFEquiv-equivalence is countable at each level. -/
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

/-- For countable M, there exists α < ω₁ where all tuples stabilize completely:
`BFEquiv α n a b ↔ BFEquiv (succ α) n a b` for ALL countable N and tuples b.

This is a standard result in infinitary model theory (see Marker, "Lectures on
Infinitary Model Theory", or Keisler-Knight §1.3). The key point is that for countable
structures, the BFEquiv refinement chain must stabilize at a countable ordinal.

**Important**: Self-stabilization (`SelfStabilizesCompletely`) does NOT imply full
stabilization (`StabilizesCompletely`). See docstring on
`per_tuple_stabilization_below_omega1` for the per-tuple argument.

**Status**: sorry-free; depends on `per_tuple_stabilization_below_omega1` (Tier 1). -/
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

omit [Countable (Σ l, L.Relations l)] in
/-- At a complete stabilization ordinal, BFEquiv0 implies isomorphism for countable structures.
This is the corrected version of BFEquiv_omega_implies_equiv. -/
theorem BFEquiv_stabilization_implies_equiv {M N : Type w} [L.Structure M] [L.Structure N]
    [Countable M] [Countable N]
    {α : Ordinal} (hstab : StabilizesCompletely (L := L) M α)
    (h : BFEquiv (L := L) α 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N)) :
    Nonempty (M ≃[L] N) := by
  -- Construct PotentialIso from stabilization: the family of tuples with BFEquiv α
  -- At stabilization, BFEquiv α ↔ BFEquiv (succ α), so forth/back witnesses stay at level α
  exact (PotentialIso.mk
    { p | BFEquiv (L := L) α p.1 p.2.1 p.2.2 }
    h
    (fun p hp => (BFEquiv.zero p.2.1 p.2.2).mp (BFEquiv.monotone (zero_le _) hp))
    (fun ⟨k, a, b⟩ hp m => by
      simp only [Set.mem_setOf_eq] at hp ⊢
      exact BFEquiv.forth ((hstab k N a b).mp hp) m)
    (fun ⟨k, a, b⟩ hp n' => by
      simp only [Set.mem_setOf_eq] at hp ⊢
      exact BFEquiv.back ((hstab k N a b).mp hp) n')
  ).countable_toEquiv

/-- For any countable structure M in a relational countable language, there exists an ordinal
α < ω₁ such that BF-equivalence at level α (with the empty tuple) characterizes isomorphism
with M among countable structures.

**Proof approach**: We use the complete stabilization ordinal from `exists_complete_stabilization`.
At a complete stabilization ordinal α:
- The BFEquiv relation has stopped refining: BFEquiv α ↔ BFEquiv (succ α) for all tuple sizes
- This allows the back-and-forth to close: witnesses at level α stay at level α
- The standard argument then produces an isomorphism

**Historical note**: An earlier version claimed ω always works, but this is false without
the stabilization property. The counterexample is algebraically closed fields of different
transcendence degrees: they satisfy BFEquiv ω but are not isomorphic.
-/
theorem exists_stabilization (M : Type w) [L.Structure M] [Countable M] :
    ∃ α < (Ordinal.omega 1 : Ordinal.{0}), StabilizesAt (L := L) M α := by
  -- Get the complete stabilization ordinal.
  -- **Countability is essential**: uncountable structures may not stabilize below ω₁.
  -- The argument uses that M^n is countable, so the sequence of BFEquiv partitions
  -- can refine at most countably many times, hence must stabilize at some α < ω₁.
  obtain ⟨α, hα_lt, hstab⟩ := exists_complete_stabilization (L := L) M
  use α, hα_lt
  -- Show that at complete stabilization, BFEquiv0 ↔ isomorphism
  intro N _ _
  constructor
  · -- Forward: BFEquiv α 0 [] [] → isomorphism
    exact BFEquiv_stabilization_implies_equiv hstab
  · -- Backward: isomorphism → BFEquiv α 0 [] []
    intro ⟨e⟩
    show BFEquiv0 (L := L) M N α
    unfold BFEquiv0
    have h : (e : M → N) ∘ Fin.elim0 = Fin.elim0 := funext (fun i => i.elim0)
    rw [← h]
    exact equiv_implies_BFEquiv e α 0 Fin.elim0

/-- The stabilization ordinal for a structure M: the least ordinal where the Scott analysis
stabilizes. We fix the ordinal universe to 0 for consistency with our BFEquiv definitions. -/
noncomputable def stabilizationOrdinal (M : Type w) [L.Structure M] [Countable M] :
    Ordinal.{0} :=
  sInf {α : Ordinal.{0} | StabilizesAt (L := L) M α}

/-- The Scott sentence of a countable structure M in a relational countable language.

A sentence is a formula with no free variables, which corresponds to `Formulaω (Fin 0)`
since `Fin 0` is empty. -/
noncomputable def scottSentence (M : Type w) [L.Structure M] [Countable M] : L.Formulaω (Fin 0) :=
  scottFormula (L := L) (M := M) (n := 0) Fin.elim0
    (stabilizationOrdinal (L := L) M)

/-- Realize a formula with no free variables as a sentence in a structure. -/
def Formulaω.realize_as_sentence (φ : L.Formulaω (Fin 0)) (N : Type w) [L.Structure N] : Prop :=
  φ.Realize (Fin.elim0 : Fin 0 → N)

/-- The main theorem: a countable structure N satisfies the Scott sentence of M
if and only if M and N are isomorphic.

The proof uses:
1. `scottSentence` is defined as `scottFormula Fin.elim0 (stabilizationOrdinal M)`
2. `realize_scottFormula_iff_BFEquiv` converts Scott formula realization to BFEquiv
3. `exists_stabilization` shows that BFEquiv at the stabilization ordinal characterizes isomorphism
-/
-- Helper: stabilizationOrdinal is less than ω₁
theorem stabilizationOrdinal_lt_omega1' (M : Type w) [L.Structure M] [Countable M] :
    stabilizationOrdinal (L := L) M < Ordinal.omega 1 := by
  -- The infimum of a non-empty set of ordinals bounded by ω₁ is < ω₁
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
  -- Use realize_scottFormula_iff_BFEquiv
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

end Language

end FirstOrder
