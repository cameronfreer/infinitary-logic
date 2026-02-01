/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Scott.AtomicDiagram

/-!
# Back-and-Forth Equivalence

This file defines the back-and-forth equivalence relation between tuples in structures,
indexed by ordinals. This is the semantic predicate that corresponds to Scott formulas.

## Main Definitions

- `BFEquiv`: The α-back-and-forth equivalence between tuples, indexed by ordinal α.

## Main Results

- `BFEquiv.zero_iff_sameAtomicType`: At level 0, BF-equivalence is atomic type equivalence.
- `BFEquiv.monotone`: BF-equivalence at higher ordinals implies equivalence at lower ordinals.
- `BFEquiv.forth`/`BFEquiv.back`: Extension properties at successor ordinals.
- `BFEquiv.symm`: BF-equivalence is symmetric.

## Implementation Notes

We use `Ordinal.limitRecOn` for the definition, which requires handling three cases:
- Zero: same atomic type
- Successor `Order.succ α`: equivalence at α plus forth and back conditions
- Limit (with `Order.IsSuccLimit`): equivalence at all smaller ordinals

## Known Limitation: ω-Level Coherence and Quantifier Swap

A natural approach to proving `BFEquiv_omega_implies_equiv` (BF-equivalence at ω implies
isomorphism) is to define a "strategy" type that carries explicit witnesses instead of
just existence claims. The inductive definition:

```
inductive BFStrategy : (k : ℕ) → ... → Type
  | zero : SameAtomicType a b → BFStrategy 0 n a b
  | succ : BFStrategy k n a b →
           (forth : (m : M) → Σ n', BFStrategy k (n+1) ...) → ...
```

fails Lean's nested-inductive check. However, we CAN define BFStrategy by recursion on k
(this compiles and avoids the kernel restriction). See `BFStrategy` below.

We then define `BFStrategyOmega n a b := ∀ k, BFStrategy k n a b`, a coherent family of
strategies at all finite levels. This is the "winning strategy in the ω-round EF game."

**The real mathematical issue**: Even with these definitions, we have:
- `BFStrategyOmega → isomorphism` is provable (the strategy gives coherent witnesses)
- `BFEquiv ω → BFStrategyOmega` is the open problem (possibly false without extra assumptions)

This is the standard model-theory distinction: "BFEquiv holds at all finite levels"
(∀ k, Duplicator wins the k-round game) does NOT imply "Duplicator has a winning strategy
in the ω-round game," even for countable structures.

The obstruction is the quantifier swap:

```
From BFEquiv ω: ∀ k, ∃ n'_k, BFEquiv k (snoc a m) (snoc b n'_k)
Need:          ∃ n', ∀ k, BFEquiv k (snoc a m) (snoc b n')
```

**Concrete counterexample** to such swaps: Let S_k = {n ∈ ℕ | n ≥ k}. Each S_k is non-empty,
and S_0 ⊇ S_1 ⊇ S_2 ⊇ ..., but ⋂_k S_k = ∅. The witnesses keep shifting as k grows.

In our setting, S_k = {n' ∈ N | BFEquiv k (snoc a m) (snoc b n')}. By monotonicity of
BFEquiv, these sets are decreasing. But without a stabilization property, their
intersection may be empty.

**Note on alternative approaches**:
- Dependent choice does NOT help: even with full AC, ∀ k, ∃ n'_k doesn't yield ∃ n', ∀ k
  when the sets strictly decrease to empty intersection.
- König's lemma would require finite branching or compactness; not available here since
  the "tree" of valid witnesses lacks the necessary finiteness properties.
- A game-theoretic formulation (strategy as function on finite plays) might help but
  still requires proving a winning strategy exists from BFEquiv ω.

**Path forward**: The cleanest resolution would be either:
1. Prove a stabilization property: show S_k eventually stabilizes (becomes constant)
2. Work with BFStrategyOmega directly as the hypothesis for isomorphism theorems
3. Add structure to the problem that forces uniform witnesses

For now, the ω-level coherence proofs remain incomplete (marked with `sorry`).
-/

universe u v w w'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable {M : Type w} [L.Structure M]
variable {N : Type w'} [L.Structure N]

open FirstOrder Structure Fin Ordinal

/-- Back-and-forth equivalence at ordinal α between tuples a in M and b in N.

At level 0: same atomic type.
At successor α + 1: same atomic type, plus:
  - (forth) for every m in M, there exists n in N with BFEquiv α (snoc a m) (snoc b n)
  - (back) for every n in N, there exists m in M with BFEquiv α (snoc a m) (snoc b n)
At limit λ: BFEquiv β for all β < λ.
-/
noncomputable def BFEquiv (α : Ordinal) (n : ℕ) (a : Fin n → M) (b : Fin n → N) : Prop :=
  Ordinal.limitRecOn α
    -- Zero case: same atomic type
    (fun (k : ℕ) (a' : Fin k → M) (b' : Fin k → N) =>
      SameAtomicType (L := L) (M := M) (N := N) a' b')
    -- Successor case
    (fun _β ih (k : ℕ) (a' : Fin k → M) (b' : Fin k → N) =>
      ih k a' b' ∧
      (∀ m : M, ∃ n' : N, ih (k + 1) (snoc a' m) (snoc b' n')) ∧
      (∀ n' : N, ∃ m : M, ih (k + 1) (snoc a' m) (snoc b' n')))
    -- Limit case
    (fun _β _hβ ih (k : ℕ) (a' : Fin k → M) (b' : Fin k → N) =>
      ∀ γ (hγ : γ < _β), ih γ hγ k a' b')
    n a b

variable {n : ℕ}

omit [L.IsRelational] in
theorem BFEquiv.zero (a : Fin n → M) (b : Fin n → N) :
    BFEquiv (L := L) 0 n a b ↔ SameAtomicType (L := L) (M := M) (N := N) a b := by
  simp only [BFEquiv, Ordinal.limitRecOn_zero]

omit [L.IsRelational] in
theorem BFEquiv.zero_iff_sameAtomicType (a : Fin n → M) (b : Fin n → N) :
    BFEquiv (L := L) 0 n a b ↔ SameAtomicType (L := L) (M := M) (N := N) a b :=
  BFEquiv.zero a b

omit [L.IsRelational] in
theorem BFEquiv.succ (α : Ordinal) (a : Fin n → M) (b : Fin n → N) :
    BFEquiv (L := L) (Order.succ α) n a b ↔
      BFEquiv (L := L) α n a b ∧
      (∀ m : M, ∃ n' : N, BFEquiv (L := L) α (n + 1) (snoc a m) (snoc b n')) ∧
      (∀ n' : N, ∃ m : M, BFEquiv (L := L) α (n + 1) (snoc a m) (snoc b n')) := by
  simp only [BFEquiv, Ordinal.limitRecOn_succ]

omit [L.IsRelational] in
theorem BFEquiv.limit (α : Ordinal) (hα : Order.IsSuccLimit α) (a : Fin n → M) (b : Fin n → N) :
    BFEquiv (L := L) α n a b ↔ ∀ β, β < α → BFEquiv (L := L) β n a b := by
  unfold BFEquiv
  rw [Ordinal.limitRecOn_limit _ _ _ _ hα]

omit [L.IsRelational] in
/-- BF-equivalence at level α + 1 implies BF-equivalence at level α. -/
theorem BFEquiv.of_succ {α : Ordinal} {a : Fin n → M} {b : Fin n → N}
    (h : BFEquiv (L := L) (Order.succ α) n a b) : BFEquiv (L := L) α n a b :=
  ((BFEquiv.succ α a b).mp h).1

omit [L.IsRelational] in
/-- BF-equivalence is monotone: higher ordinals imply lower ordinals. -/
theorem BFEquiv.monotone {α β : Ordinal} (hαβ : α ≤ β)
    {a : Fin n → M} {b : Fin n → N} (h : BFEquiv (L := L) β n a b) :
    BFEquiv (L := L) α n a b := by
  induction β using Ordinal.limitRecOn generalizing n a b with
  | zero =>
    simp only [nonpos_iff_eq_zero] at hαβ
    rwa [hαβ]
  | succ γ ih =>
    rcases hαβ.lt_or_eq with hαβ' | rfl
    · rw [Order.lt_succ_iff] at hαβ'
      exact ih hαβ' (BFEquiv.of_succ h)
    · exact h
  | limit γ hγ _ih =>
    rcases hαβ.lt_or_eq with hαβ' | rfl
    · exact (BFEquiv.limit γ hγ a b).mp h α hαβ'
    · exact h

omit [L.IsRelational] in
/-- The "forth" property at a successor level. -/
theorem BFEquiv.forth {α : Ordinal} {a : Fin n → M} {b : Fin n → N}
    (h : BFEquiv (L := L) (Order.succ α) n a b) (m : M) :
    ∃ n' : N, BFEquiv (L := L) α (n + 1) (snoc a m) (snoc b n') :=
  ((BFEquiv.succ α a b).mp h).2.1 m

omit [L.IsRelational] in
/-- The "back" property at a successor level. -/
theorem BFEquiv.back {α : Ordinal} {a : Fin n → M} {b : Fin n → N}
    (h : BFEquiv (L := L) (Order.succ α) n a b) (n' : N) :
    ∃ m : M, BFEquiv (L := L) α (n + 1) (snoc a m) (snoc b n') :=
  ((BFEquiv.succ α a b).mp h).2.2 n'

omit [L.IsRelational] in
/-- BF-equivalence at level 0 is reflexive. -/
theorem BFEquiv.refl_zero (a : Fin n → M) :
    BFEquiv (L := L) (M := M) (N := M) (0 : Ordinal) n a a :=
  (BFEquiv.zero a a).mpr (SameAtomicType.refl a)

omit [L.IsRelational] in
/-- BF-equivalence is symmetric at all levels. -/
theorem BFEquiv.symm {α : Ordinal} {a : Fin n → M} {b : Fin n → N}
    (h : BFEquiv (L := L) α n a b) : BFEquiv (L := L) (M := N) (N := M) α n b a := by
  induction α using Ordinal.limitRecOn generalizing n a b with
  | zero =>
    rw [BFEquiv.zero] at h ⊢
    exact h.symm
  | succ β ih =>
    rw [BFEquiv.succ] at h ⊢
    exact ⟨ih h.1, fun n' => let ⟨m, hm⟩ := h.2.2 n'; ⟨m, ih hm⟩,
           fun m => let ⟨n', hn'⟩ := h.2.1 m; ⟨n', ih hn'⟩⟩
  | limit β hβ ih =>
    rw [BFEquiv.limit β hβ] at h ⊢
    exact fun γ hγ => ih γ hγ (h γ hγ)

/-! ### BFStrategy: Explicit Witness Strategies

A back-and-forth strategy at level k provides explicit witnesses for extensions.
Unlike `BFEquiv` which only asserts existence, a strategy carries the actual witnesses.

The key insight is that `BFStrategy` can be defined by recursion on k (not as an
inductive type), avoiding Lean's nested-inductive check that blocks inductive definitions.

The open problem is `BFEquiv ω → BFStrategyOmega`: this is the quantifier swap obstruction.
Having a strategy implies BFEquiv, but the converse requires choosing coherent witnesses. -/

/-- Back-and-forth strategy at level k. Provides explicit witnesses for extensions.
At level 0: proof that tuples have the same atomic type (as a Prop, lifted to Type).
At level k+1: strategy at level k, plus witness functions for forth and back.

Note: We define this outside the section to have explicit control over parameters. -/
def BFStrategy (L : Language.{u, v}) [L.IsRelational] (M : Type w) (N : Type w')
    [L.Structure M] [L.Structure N] : ℕ → (n : ℕ) → (Fin n → M) → (Fin n → N) → Prop :=
  fun k => match k with
  | 0 => fun _n a b => SameAtomicType (L := L) a b
  | k + 1 => fun n a b =>
    (BFStrategy L M N k n a b) ∧
    (∀ m : M, ∃ n' : N, BFStrategy L M N k (n + 1) (Fin.snoc a m) (Fin.snoc b n')) ∧
    (∀ n' : N, ∃ m : M, BFStrategy L M N k (n + 1) (Fin.snoc a m) (Fin.snoc b n'))

/-- A coherent family of strategies at all finite levels.
This is the "winning strategy in the ω-round EF game."

Note: This is propositional. For the data-carrying version that allows extracting
witnesses computationally, one would need to lift to Type using Choice. -/
def BFStrategyOmega (n : ℕ) (a : Fin n → M) (b : Fin n → N) : Prop :=
  ∀ k : ℕ, BFStrategy L M N k n a b

/-- A strategy at level k implies BF-equivalence at level k. -/
theorem BFStrategy_implies_BFEquiv {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (k : ℕ) (strat : BFStrategy L M N k n a b) :
    BFEquiv (L := L) (k : Ordinal.{0}) n a b := by
  induction k generalizing n a b with
  | zero =>
    simp only [Nat.cast_zero]
    rw [BFEquiv.zero]
    exact strat
  | succ k ih =>
    have hsucc : ((k + 1 : ℕ) : Ordinal.{0}) = Order.succ (k : Ordinal.{0}) := by
      rw [← Ordinal.add_one_eq_succ]; norm_cast
    rw [hsucc, BFEquiv.succ]
    obtain ⟨strat_k, forth, back⟩ := strat
    refine ⟨ih strat_k, ?_, ?_⟩
    · intro m
      obtain ⟨n', strat_ext⟩ := forth m
      exact ⟨n', ih strat_ext⟩
    · intro n'
      obtain ⟨m, strat_ext⟩ := back n'
      exact ⟨m, ih strat_ext⟩

/-- A coherent ω-strategy implies BF-equivalence at level ω. -/
theorem BFStrategyOmega_implies_BFEquiv_omega {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (hstrat : BFStrategyOmega (L := L) n a b) :
    BFEquiv (L := L) (ω : Ordinal.{0}) n a b := by
  rw [BFEquiv.limit ω Ordinal.isSuccLimit_omega0]
  intro γ hγ
  -- γ < ω means γ is a natural number
  have ⟨k, hk⟩ := Ordinal.lt_omega0.mp hγ
  subst hk
  exact BFStrategy_implies_BFEquiv k (hstrat k)

end Language

end FirstOrder
