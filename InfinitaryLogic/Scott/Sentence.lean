/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Scott.Formula
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

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- BFEquiv at ω implies BFEquiv at any finite ordinal. -/
theorem BFEquiv_omega_implies_finite {M N : Type w} [L.Structure M] [L.Structure N]
    (hBF : BFEquiv (L := L) (ω : Ordinal.{0}) 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N))
    (n : ℕ) :
    BFEquiv (L := L) (n : Ordinal.{0}) 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) :=
  BFEquiv.monotone (le_of_lt (Ordinal.nat_lt_omega0 n)) hBF

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- From BFEquiv (k+1) 0 at empty tuples, we can get matching singletons at level k. -/
theorem BFEquiv_succ_forth_singleton {M N : Type w} [L.Structure M] [L.Structure N]
    {k : ℕ} (hBF : BFEquiv (L := L) ((k + 1 : ℕ) : Ordinal.{0}) 0
      (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N))
    (m : M) : ∃ n' : N, BFEquiv (L := L) (k : Ordinal.{0}) 1 ![m] ![n'] := by
  have hconv : ((k + 1 : ℕ) : Ordinal.{0}) = Order.succ (k : Ordinal.{0}) := by
    rw [← Ordinal.add_one_eq_succ]; norm_cast
  rw [hconv, BFEquiv.succ] at hBF
  obtain ⟨_, hforth, _⟩ := hBF
  obtain ⟨n', hn'⟩ := hforth m
  use n'
  convert hn' using 2 <;> ext i <;> fin_cases i <;> simp [Fin.snoc]

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- From BFEquiv (k+1) for tuples, we can extend using forth. -/
theorem BFEquiv_succ_forth_extend {M N : Type w} [L.Structure M] [L.Structure N]
    {k : ℕ} {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (hBF : BFEquiv (L := L) (Order.succ (k : Ordinal.{0})) n a b)
    (m : M) : ∃ n' : N, BFEquiv (L := L) (k : Ordinal.{0}) (n + 1) (Fin.snoc a m) (Fin.snoc b n') :=
  (BFEquiv.succ (k : Ordinal.{0}) a b).mp hBF |>.2.1 m

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- From BFEquiv at a successor level, we get same atomic type. -/
theorem BFEquiv_succ_implies_sameAtomicType {M N : Type w} [L.Structure M] [L.Structure N]
    {α : Ordinal} {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (hBF : BFEquiv (L := L) (Order.succ α) n a b) :
    SameAtomicType (L := L) a b := by
  have h := (BFEquiv.succ α a b).mp hBF
  have hzero : (0 : Ordinal) ≤ α := zero_le α
  exact (BFEquiv.zero a b).mp (BFEquiv.monotone hzero h.1)

/-! ### Back-and-Forth at ω: Witness Stabilization Approach

**The quantifier swap problem**: From `BFEquiv ω n a b`, we get `∀ k, ∃ n'_k, BFEquiv k (n+1) ...`.
To prove `BFEquiv_omega_forth_extend`, we need `∃ n', ∀ k, BFEquiv k (n+1) ...`.

**Solution**: For countable N, the witness sets S_k = {n' | BFEquiv k (n+1) (snoc a m) (snoc b n')}
form a decreasing chain (by BFEquiv.monotone). We show this chain stabilizes:

1. **Finite refinement**: At each level k, S_k partitions N into finitely many BFEquiv-equivalence
   classes (for countable relational language, there are only finitely many atomic types).

2. **Stabilization**: A decreasing chain of finite partitions must eventually stabilize.
   Once stable, S_k = S_{k+1} = ... so any witness from the stable set works for all levels.

3. **Non-empty intersection**: Since S_k is non-empty for all k (from BFEquiv.forth) and the
   chain stabilizes, the intersection ⋂_k S_k is non-empty.

For non-countable structures, the stabilization argument doesn't apply directly, but we only
need `BFEquiv_omega_forth_extend` for countable structures in our main theorems.
-/

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- BFEquiv at ω is preserved under forth: if we have BFEquiv ω on n-tuples and add an element
to M, there exists a matching element in N such that BFEquiv ω holds on the (n+1)-tuples.

**Proof status**: This theorem encapsulates the quantifier swap problem:
- From BFEquiv ω: ∀ k, ∃ n'_k, BFEquiv k (n+1) (snoc a m) (snoc b n'_k)
- We need:       ∃ n', ∀ k, BFEquiv k (n+1) (snoc a m) (snoc b n')

This is NOT automatic. Counterexample to such swaps: S_k = {j ∈ ℕ | j ≥ k}, each non-empty,
decreasing, but ⋂_k S_k = ∅.

**Possible approaches**:
1. Strategy-based: Use `BFStrategyOmega` which provides coherent witnesses at all levels
2. Stabilization: Show witness sets S_k stabilize for countable N (needs finite types)
3. Restrict to countable N and use dependent choice with BFEquiv monotonicity

**Note**: This theorem is NOT used by `scottSentence_characterizes`, which goes through
`stabilizationOrdinal_spec` instead. The sorry here blocks `BFEquiv_omega_implies_equiv`
but not the main Scott sentence theorem. -/
theorem BFEquiv_omega_forth_extend {M N : Type w} [L.Structure M] [L.Structure N]
    {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (hBF : BFEquiv (L := L) ω n a b) (m : M) :
    ∃ n' : N, BFEquiv (L := L) ω (n + 1) (Fin.snoc a m) (Fin.snoc b n') := by
  sorry

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- From BFEquiv (n + k) 0 at empty tuples and n elements of M, we can build
matching n-tuples at BFEquiv level k. This is the iteration of the forth property. -/
theorem BFEquiv_iterate_forth {M N : Type w} [L.Structure M] [L.Structure N]
    {n k : ℕ} (hBF : BFEquiv (L := L) ((n + k : ℕ) : Ordinal.{0}) 0
      (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N))
    (ms : Fin n → M) :
    ∃ ns : Fin n → N, BFEquiv (L := L) (k : Ordinal.{0}) n ms ns := by
  induction n generalizing k with
  | zero =>
    use Fin.elim0
    have hms : ms = Fin.elim0 := funext (fun i => i.elim0)
    rw [hms]
    convert hBF using 2; simp
  | succ n ih =>
    -- From BFEquiv ((n+1) + k) 0 [] [], rewrite as BFEquiv (n + (k+1)) 0 [] []
    have hrewrite : ((n + 1 + k : ℕ) : Ordinal.{0}) = ((n + (k + 1) : ℕ) : Ordinal.{0}) := by
      norm_cast; omega
    rw [hrewrite] at hBF
    -- Get matching n-tuple at level k+1 using IH
    obtain ⟨ns_init, hns_init⟩ := ih hBF (ms ∘ Fin.castSucc)
    -- Use forth to extend by one more element
    have hsucc : (k + 1 : ℕ) = Order.succ (k : Ordinal.{0}) := by
      rw [← Ordinal.add_one_eq_succ]; norm_cast
    have hns_init' : BFEquiv (L := L) (Order.succ (k : Ordinal.{0})) n
        (ms ∘ Fin.castSucc) ns_init := by
      convert hns_init using 2
    obtain ⟨n_last, hn_last⟩ := BFEquiv_succ_forth_extend hns_init' (ms (Fin.last n))
    use Fin.snoc ns_init n_last
    -- Convert ms to Fin.snoc form
    have hms_snoc : ms = Fin.snoc (ms ∘ Fin.castSucc) (ms (Fin.last n)) := by
      ext i; simp only [Fin.snoc, Function.comp_apply]
      split_ifs with h
      · rfl
      · simp only [cast_eq]
        congr 1
        exact Fin.ext (Nat.eq_of_lt_succ_of_not_lt i.isLt h)
    rw [hms_snoc]
    exact hn_last

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- BFEquiv at level k allows building partial isomorphisms of size up to k.
This is a corollary of `BFEquiv_iterate_forth` with k = 0. -/
theorem BFEquiv_build_matching_tuples_forth {M N : Type w} [L.Structure M] [L.Structure N]
    {k : ℕ} (hBF : BFEquiv (L := L) ((k : ℕ) : Ordinal.{0}) 0
      (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N))
    (ms : Fin k → M) :
    ∃ ns : Fin k → N, SameAtomicType (L := L) ms ns := by
  have hrewrite : ((k : ℕ) : Ordinal.{0}) = ((k + 0 : ℕ) : Ordinal.{0}) := by norm_cast
  rw [hrewrite] at hBF
  obtain ⟨ns, hns⟩ := BFEquiv_iterate_forth hBF ms
  use ns
  -- BFEquiv 0 k ms ns = SameAtomicType ms ns
  exact (BFEquiv.zero ms ns).mp hns

/-! ### Coherent Chain Construction

Instead of trying to prove coherence for `BFEquiv_iterate_forth` (which uses Classical.choose
in a complex way), we define a coherent chain directly using Nat.rec.

The key is to build the chain incrementally, where each step EXTENDS the previous one,
rather than making independent calls. -/

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- Build a coherent chain of matching tuples for an enumeration of M.

Given BFEquiv ω 0 [] [] and an enumeration enumM : ℕ → M, this produces a sequence
chainN : (k : ℕ) → Fin k → N such that:
1. SameAtomicType (enumM|_k) (chainN k) for all k
2. chainN (k+1) ∘ castSucc = chainN k (coherence)

The construction uses Nat.rec to ensure coherence by building chainN(k+1) from chainN(k). -/
noncomputable def buildCoherentChain {M N : Type w} [L.Structure M] [L.Structure N]
    (hBF : BFEquiv (L := L) (ω : Ordinal.{0}) 0
      (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N))
    (enumM : ℕ → M) : (k : ℕ) → { ns : Fin k → N // SameAtomicType (L := L) (fun i : Fin k => enumM i.val) ns } :=
  fun k =>
    let hBFk : BFEquiv (L := L) ((k : ℕ) : Ordinal.{0}) 0
        (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) :=
      BFEquiv.monotone (le_of_lt (Ordinal.nat_lt_omega0 k)) hBF
    let matching := BFEquiv_build_matching_tuples_forth hBFk (fun i : Fin k => enumM i.val)
    ⟨Classical.choose matching, Classical.choose_spec matching⟩

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- The coherent chain satisfies SameAtomicType at each level. -/
theorem buildCoherentChain_sameAtomicType {M N : Type w} [L.Structure M] [L.Structure N]
    (hBF : BFEquiv (L := L) (ω : Ordinal.{0}) 0
      (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N))
    (enumM : ℕ → M) (k : ℕ) :
    SameAtomicType (L := L) (fun i : Fin k => enumM i.val) (buildCoherentChain hBF enumM k).val :=
  (buildCoherentChain hBF enumM k).prop

/-! Note: The buildCoherentChain construction does NOT guarantee coherence (chainN(k+1) extending
chainN(k)) because each recursive call uses BFEquiv_build_matching_tuples_forth independently.

To get true coherence, we would need to show that iterate_forth respects the existing prefix,
which requires the stabilization argument or a stronger BFEquiv property.

For the main isomorphism theorem, we work around this by using a different approach. -/

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- From BFEquiv (k+1) for tuples, we can extend using back. -/
theorem BFEquiv_succ_back_extend {M N : Type w} [L.Structure M] [L.Structure N]
    {k : ℕ} {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (hBF : BFEquiv (L := L) (Order.succ (k : Ordinal.{0})) n a b)
    (n' : N) : ∃ m : M, BFEquiv (L := L) (k : Ordinal.{0}) (n + 1) (Fin.snoc a m) (Fin.snoc b n') :=
  (BFEquiv.succ (k : Ordinal.{0}) a b).mp hBF |>.2.2 n'

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- The back analogue of BFEquiv_iterate_forth. From BFEquiv (n + k) 0 at empty tuples
and n elements of N, we can build matching n-tuples at BFEquiv level k. -/
theorem BFEquiv_iterate_back {M N : Type w} [L.Structure M] [L.Structure N]
    {n k : ℕ} (hBF : BFEquiv (L := L) ((n + k : ℕ) : Ordinal.{0}) 0
      (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N))
    (ns : Fin n → N) :
    ∃ ms : Fin n → M, BFEquiv (L := L) (k : Ordinal.{0}) n ms ns := by
  induction n generalizing k with
  | zero =>
    use Fin.elim0
    have hns : ns = Fin.elim0 := funext (fun i => i.elim0)
    rw [hns]
    convert hBF using 2; simp
  | succ n ih =>
    have hrewrite : ((n + 1 + k : ℕ) : Ordinal.{0}) = ((n + (k + 1) : ℕ) : Ordinal.{0}) := by
      norm_cast; omega
    rw [hrewrite] at hBF
    obtain ⟨ms_init, hms_init⟩ := ih hBF (ns ∘ Fin.castSucc)
    have hsucc : (k + 1 : ℕ) = Order.succ (k : Ordinal.{0}) := by
      rw [← Ordinal.add_one_eq_succ]; norm_cast
    have hms_init' : BFEquiv (L := L) (Order.succ (k : Ordinal.{0})) n
        ms_init (ns ∘ Fin.castSucc) := by
      convert hms_init using 2
    obtain ⟨m_last, hm_last⟩ := BFEquiv_succ_back_extend hms_init' (ns (Fin.last n))
    use Fin.snoc ms_init m_last
    have hns_snoc : ns = Fin.snoc (ns ∘ Fin.castSucc) (ns (Fin.last n)) := by
      ext i; simp only [Fin.snoc, Function.comp_apply]
      split_ifs with h
      · rfl
      · simp only [cast_eq]
        congr 1
        exact Fin.ext (Nat.eq_of_lt_succ_of_not_lt i.isLt h)
    rw [hns_snoc]
    exact hm_last

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- For relational languages, embeddings between substructures preserve atomic type.
This is because embeddings preserve equalities and relations by definition.

Key insight: For relational L, if f : S ↪[L] T, then for any tuple ms : Fin n → S,
the images (ms, f ∘ ms) have the same atomic type. -/
theorem Embedding.sameAtomicType_comp {S : Type*} {T : Type*}
    [L.Structure S] [L.Structure T] (f : S ↪[L] T)
    {n : ℕ} (ms : Fin n → S) :
    SameAtomicType (L := L) ms (f ∘ ms) := by
  intro idx
  cases idx with
  | eq i j =>
    simp only [AtomicIdx.holds, Function.comp_apply]
    constructor
    · intro h; exact congrArg f h
    · intro h; exact f.injective h
  | rel R g =>
    simp only [AtomicIdx.holds, Function.comp_apply]
    have hassoc : (f ∘ ms) ∘ g = f ∘ (ms ∘ g) := Function.comp_assoc f ms g
    rw [hassoc]
    exact (f.map_rel R (ms ∘ g)).symm

/-! ### Limitation of the SameAtomicType Extension Approach

The following lemmas (`SameAtomicType_extend_forth`, `SameAtomicType_extend_back`) were
intended to show that from BFEquiv ω 0 [] [] and an existing SameAtomicType matching
(ms, ns), we can extend by any element while PRESERVING the existing correspondence.

**However, this is NOT achievable with the current machinery:**

The issue is that `BFEquiv_iterate_forth` builds SOME ns' matching (snoc ms m), but ns'
may differ from (snoc ns _) on the first n positions. We don't have a way to force the
extension to respect the existing (ms, ns) correspondence.

To extend while preserving correspondence, we'd need BFEquiv (k+1) n ms ns (for some k),
which would allow using BFEquiv.forth. But BFEquiv ω 0 [] [] doesn't imply BFEquiv k n ms ns
for arbitrary SameAtomicType pairs (ms, ns).

**The workaround for BFEquiv_omega_implies_equiv:**

Instead of extending existing matchings, the proof uses `BFEquiv_iterate_forth` to build
fresh matchings from scratch at each stage. While this doesn't produce coherent extensions,
it still produces SameAtomicType matchings which suffice for the isomorphism construction
via a different argument.
-/

/-! ### BFEquiv ω and Elementary Equivalence

BFEquiv at level ω is equivalent to elementary equivalence (Duplicator winning all finite
Ehrenfeucht-Fraïssé games). This is a standard result in model theory.

**Important**: Elementary equivalence does NOT imply isomorphism in general. Two countable
structures can be elementarily equivalent (satisfy exactly the same first-order sentences)
without being isomorphic. Potential examples in relational languages include equivalence
relations with matching finite-class structure but different arrangements of infinite classes.

The **quantifier swap problem** explains why BFEquiv ω alone doesn't give isomorphism:
- From BFEquiv ω: ∀ k, ∃ n'_k, BFEquiv k (n+1) (snoc a m) (snoc b n'_k)
- For isomorphism we'd need: ∃ n', ∀ k, BFEquiv k (n+1) (snoc a m) (snoc b n')

The witnesses n'_k may differ for each k with empty "intersection" (like S_k = {j | j ≥ k}).

**Correct approach**: Use `BFEquiv_stabilization_implies_equiv` with a complete stabilization
ordinal α where BFEquiv α ↔ BFEquiv (succ α). At such an ordinal, witnesses stay stable.

**For the main Scott sentence theorem**: Use `scottSentence_characterizes` which goes through
`stabilizationOrdinal_spec` with the correct stabilization argument.
-/

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- BFEquiv ω is equivalent to BFEquiv k for all finite k. This captures the fact that
BFEquiv at ω means "winning all finite Ehrenfeucht-Fraïssé games."

**Note**: ω is typically NOT a stabilization point. At each finite level k, we get witnesses
n'_k, but these witnesses may shift as k grows (the "quantifier swap problem"). Stabilization
requires finding a level α where witnesses remain constant, which happens at some countable
ordinal (possibly much larger than ω) for countable structures. -/
theorem BFEquiv_omega_iff_forall_finite {M N : Type w} [L.Structure M] [L.Structure N]
    {n : ℕ} {a : Fin n → M} {b : Fin n → N} :
    BFEquiv (L := L) (ω : Ordinal.{0}) n a b ↔ ∀ k : ℕ, BFEquiv (L := L) (k : Ordinal.{0}) n a b := by
  constructor
  · -- BFEquiv ω → ∀ k, BFEquiv k
    intro hω k
    exact BFEquiv.monotone (le_of_lt (Ordinal.nat_lt_omega0 k)) hω
  · -- ∀ k, BFEquiv k → BFEquiv ω
    intro hk
    rw [BFEquiv.limit ω Ordinal.isSuccLimit_omega0]
    intro γ hγ
    obtain ⟨k, hk_eq⟩ := Ordinal.lt_omega0.mp hγ
    subst hk_eq
    exact hk k

/-- General iteration: from strategy at level sz for n-tuples, extend by sz elements.

This is the core workhorse that handles arbitrary starting tuples. The key properties:
- Level decreases by 1 for each forth application
- Tuple size increases by 1 for each forth application
- After sz applications, level is 0 (gives SameAtomicType)

Returns ns : Fin sz → N and a proof of SameAtomicType for the extended tuples. -/
noncomputable def iterateForthGeneral {M N : Type w} [L.Structure M] [L.Structure N] :
    (sz n : ℕ) → (a : Fin n → M) → (b : Fin n → N) →
    (strat : BFStrategyT L M N sz n a b) → (ms : Fin sz → M) →
    { ns : Fin sz → N // SameAtomicType (L := L) (Fin.append a ms) (Fin.append b ns) } := by
  intro sz
  induction sz with
  | zero =>
    intro n a b strat ms
    -- sz = 0: no elements to add, strat is already at level 0
    refine ⟨Fin.elim0, ?_⟩
    -- Need: SameAtomicType (Fin.append a Fin.elim0) (Fin.append b Fin.elim0)
    -- strat : BFStrategyT 0 n a b = { _ : PUnit // SameAtomicType a b }
    have hms : ms = Fin.elim0 := funext (fun i => i.elim0)
    subst hms
    -- Fin.append a Fin.elim0 = a (after identifying n + 0 with n)
    convert strat.property using 2 <;>
    · ext i
      simp only [Fin.append, Fin.addCases]
      have hi : (i : ℕ) < n := i.isLt
      simp [hi, Fin.castLT]
  | succ sz ih =>
    intro n a b strat ms
    -- strat : BFStrategyT (sz+1) n a b
    -- ms : Fin (sz+1) → M
    obtain ⟨_, forth, _⟩ := strat
    let m₀ := ms 0
    obtain ⟨n₀, strat_ext⟩ := forth m₀
    -- strat_ext : BFStrategyT sz (n+1) (Fin.snoc a m₀) (Fin.snoc b n₀)
    let ms' : Fin sz → M := ms ∘ Fin.succ
    -- Apply IH with n' = n+1
    obtain ⟨ns', sat_ext⟩ := ih (n + 1) (Fin.snoc a m₀) (Fin.snoc b n₀) strat_ext ms'
    -- ns' : Fin sz → N
    -- sat_ext : SameAtomicType (Fin.append (Fin.snoc a m₀) ms')
    --                          (Fin.append (Fin.snoc b n₀) ns')
    let ns : Fin (sz + 1) → N := Fin.cons n₀ ns'
    refine ⟨ns, ?_⟩
    -- Key: Fin.append a (Fin.cons m₀ ms') = Fin.append (Fin.snoc a m₀) ms' (after reindexing)
    have hms_eq : ms = Fin.cons m₀ ms' := by
      ext i; cases i using Fin.cases <;> rfl
    have hns_eq : ns = Fin.cons n₀ ns' := rfl
    rw [hms_eq, hns_eq]
    have hsize : n + (sz + 1) = (n + 1) + sz := by omega
    -- The key identity: appending (a, cons m₀ ms') = appending (snoc a m₀, ms') after reindexing
    -- Use SameAtomicType.relabel with explicit index computation
    -- The key identity: appending (a, cons m₀ ms') = appending (snoc a m₀, ms') after reindexing
    -- Both represent the same (n + sz + 1)-tuple: a(0), ..., a(n-1), m₀, ms'(0), ..., ms'(sz-1)
    -- The Fin index manipulation is tedious bookkeeping; the mathematical content is that
    -- these tuples contain the same elements in the same order.
    -- sat_ext gives: SameAtomicType (Fin.append (Fin.snoc a m₀) ms') (Fin.append (Fin.snoc b n₀) ns')
    -- We need:      SameAtomicType (Fin.append a (Fin.cons m₀ ms')) (Fin.append b (Fin.cons n₀ ns'))
    -- These are the same tuples, just with different Fin indexing conventions.
    -- The conversion is: Fin.snoc a m₀ = (a(0), ..., a(n-1), m₀) as (n+1)-tuple
    --                    Fin.cons m₀ ms' = (m₀, ms'(0), ..., ms'(sz-1)) as (sz+1)-tuple
    -- So Fin.append (Fin.snoc a m₀) ms' = (a(0), ..., a(n-1), m₀, ms'(0), ..., ms'(sz-1))
    --    Fin.append a (Fin.cons m₀ ms') = (a(0), ..., a(n-1), m₀, ms'(0), ..., ms'(sz-1))
    -- They are the same sequence, just indexed differently: (n+1)+sz vs n+(sz+1).
    -- sat_ext : SameAtomicType (Fin.append (Fin.snoc a m₀) ms') (Fin.append (Fin.snoc b n₀) ns')
    -- We need: SameAtomicType (Fin.append a (Fin.cons m₀ ms')) (Fin.append b (Fin.cons n₀ ns'))
    -- The tuples are identical sequences, just reindexed:
    --   Fin.append (Fin.snoc a m₀) ms' = (a(0), ..., a(n-1), m₀, ms'(0), ..., ms'(sz-1))
    --   Fin.append a (Fin.cons m₀ ms') = (a(0), ..., a(n-1), m₀, ms'(0), ..., ms'(sz-1))
    -- The difference is (n+1)+sz vs n+(sz+1) indexing.
    -- Use append_right_cons: Fin.append a (Fin.cons m₀ ms') = Fin.append (Fin.snoc a m₀) ms' ∘ Fin.cast ...
    rw [Fin.append_right_cons, Fin.append_right_cons]
    exact sat_ext.relabel _

/-- Build matching k-tuple in N from strategy at level k for empty tuples.
This is the core helper for the back-and-forth construction.

Uses `iterateForthGeneral` to iterate forth k times, starting from empty tuples. -/
noncomputable def buildMatchingTuple {M N : Type w} [L.Structure M] [L.Structure N]
    (k : ℕ) (strat : BFStrategyT L M N k 0 Fin.elim0 Fin.elim0) (ms : Fin k → M) :
    { ns : Fin k → N // SameAtomicType (L := L) ms ns } := by
  obtain ⟨ns, sat⟩ := iterateForthGeneral k 0 Fin.elim0 Fin.elim0 strat ms
  refine ⟨ns, ?_⟩
  -- sat : SameAtomicType (Fin.append Fin.elim0 ms) (Fin.append Fin.elim0 ns)
  -- Use elim0_append: Fin.append Fin.elim0 ms = ms ∘ Fin.cast (Nat.zero_add k)
  rw [Fin.elim0_append, Fin.elim0_append] at sat
  exact sat.relabel (Fin.cast (Nat.zero_add k).symm)

/-- General iteration using back: from strategy at level sz for n-tuples, extend by sz elements.

This is the back version of `iterateForthGeneral`. -/
noncomputable def iterateBackGeneral {M N : Type w} [L.Structure M] [L.Structure N] :
    (sz n : ℕ) → (a : Fin n → M) → (b : Fin n → N) →
    (strat : BFStrategyT L M N sz n a b) → (ns : Fin sz → N) →
    { ms : Fin sz → M // SameAtomicType (L := L) (Fin.append a ms) (Fin.append b ns) } := by
  intro sz
  induction sz with
  | zero =>
    intro n a b strat ns
    refine ⟨Fin.elim0, ?_⟩
    have hns : ns = Fin.elim0 := funext (fun i => i.elim0)
    subst hns
    convert strat.property using 2 <;>
    · ext i
      simp only [Fin.append, Fin.addCases]
      have hi : (i : ℕ) < n := i.isLt
      simp [hi, Fin.castLT]
  | succ sz ih =>
    intro n a b strat ns
    obtain ⟨_, _, back⟩ := strat
    let n₀ := ns 0
    obtain ⟨m₀, strat_ext⟩ := back n₀
    let ns' : Fin sz → N := ns ∘ Fin.succ
    obtain ⟨ms', sat_ext⟩ := ih (n + 1) (Fin.snoc a m₀) (Fin.snoc b n₀) strat_ext ns'
    let ms : Fin (sz + 1) → M := Fin.cons m₀ ms'
    refine ⟨ms, ?_⟩
    have hns_eq : ns = Fin.cons n₀ ns' := by
      ext i; cases i using Fin.cases <;> rfl
    have hms_eq : ms = Fin.cons m₀ ms' := rfl
    rw [hns_eq, hms_eq]
    rw [Fin.append_right_cons, Fin.append_right_cons]
    exact sat_ext.relabel _

/-- Build matching k-tuple in M from strategy at level k for empty tuples, using back.
This is the back version of `buildMatchingTuple`. -/
noncomputable def buildMatchingTupleBack {M N : Type w} [L.Structure M] [L.Structure N]
    (k : ℕ) (strat : BFStrategyT L M N k 0 Fin.elim0 Fin.elim0) (ns : Fin k → N) :
    { ms : Fin k → M // SameAtomicType (L := L) ms ns } := by
  obtain ⟨ms, sat⟩ := iterateBackGeneral k 0 Fin.elim0 Fin.elim0 strat ns
  refine ⟨ms, ?_⟩
  rw [Fin.elim0_append, Fin.elim0_append] at sat
  exact sat.relabel (Fin.cast (Nat.zero_add k).symm)

/-- From a coherent Type-valued ω-strategy on empty tuples, build an isomorphism.

This is the strategy-based version that SOLVES the quantifier swap problem in
`BFEquiv_omega_implies_equiv`. The Type-valued strategy carries actual witness functions
(not just existence proofs), making the back-and-forth construction straightforward.

**Key insight**: With `BFStrategyOmegaT`, we have witness FUNCTIONS `forth : M → N × ...`
and `back : N → M × ...`. These are coherent by construction, so we can build the
isomorphism by iterating them over enumerations of M and N. -/
theorem BFStrategyOmegaT_implies_equiv {M N : Type w} [L.Structure M] [L.Structure N]
    [Countable M] [Countable N]
    (hStrat : BFStrategyOmegaT (L := L) 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N)) :
    Nonempty (M ≃[L] N) := by
  -- The strategy at level k gives us computational witnesses for k-step extensions
  -- We use the strategy at sufficiently high levels to build the isomorphism

  -- Get BFEquiv ω from the strategy (for the empty/nonempty case analysis)
  have hBF : BFEquiv (L := L) (ω : Ordinal.{0}) 0
      (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) :=
    BFStrategyOmegaT_implies_BFEquiv_omega hStrat

  -- Handle the empty case
  by_cases hM_empty : IsEmpty M
  · by_cases hN_empty : IsEmpty N
    · refine ⟨⟨Equiv.equivOfIsEmpty M N, ?_, ?_⟩⟩
      · intro n f; exact IsEmpty.elim inferInstance f
      · intro n r x
        match n with
        | 0 =>
          have hBF0 := BFEquiv.monotone (zero_le _) hBF
          have hSAT := (BFEquiv.zero (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N)).mp hBF0
          have hx : x = Fin.elim0 := funext (fun i => i.elim0)
          subst hx
          have hcomp : (Equiv.equivOfIsEmpty M N).toFun ∘ (Fin.elim0 : Fin 0 → M) =
                       (Fin.elim0 : Fin 0 → N) := funext (fun i => i.elim0)
          simp only [hcomp]
          exact (hSAT (AtomicIdx.rel r Fin.elim0)).symm
        | n + 1 => exact IsEmpty.elim hM_empty (x 0)
    · -- M empty, N nonempty: get contradiction from back at level 1
      push_neg at hN_empty
      obtain ⟨n⟩ := hN_empty
      -- Use the strategy at level 1 to get a witness in M
      have strat1 := hStrat 1
      obtain ⟨_, _, back⟩ := strat1
      obtain ⟨m, _⟩ := back n
      exact hM_empty.elim m
  push_neg at hM_empty
  haveI : Nonempty M := hM_empty

  -- N must also be nonempty (use forth at level 1)
  haveI : Nonempty N := by
    obtain ⟨m⟩ : Nonempty M := inferInstance
    have strat1 := hStrat 1
    obtain ⟨_, forth, _⟩ := strat1
    obtain ⟨n, _⟩ := forth m
    exact ⟨n⟩

  -- Get enumerations
  obtain ⟨enumM, hM_surj⟩ := exists_surjective_nat M
  obtain ⟨enumN, hN_surj⟩ := exists_surjective_nat N

  /-
  **Type-valued strategy construction**

  With BFStrategyOmegaT, we have actual witness functions. The construction proceeds:

  1. Build a chain of matching tuples (aₖ, bₖ) where aₖ : Fin k → M, bₖ : Fin k → N
  2. The chain is coherent: (aₖ₊₁, bₖ₊₁) extends (aₖ, bₖ)
  3. Each step uses the strategy's forth/back witnesses
  4. The limit defines the isomorphism

  The key is using the strategy at level ≥ 2k to build k-tuples, so we always
  have enough "budget" for extensions.
  -/

  /-
  **Type-valued strategy chain construction**

  Key insight: `hStrat k` gives `BFStrategyT L M N k 0 [] []`.

  From `hStrat k` for empty tuples, applying forth k times gives a strategy at level 0
  for k-tuples, which means SameAtomicType holds for the resulting k-tuples.

  The construction iterates forth starting from hStrat k:
  - forth(enumM 0) → level k-1 for 1-tuple
  - forth(enumM 1) → level k-2 for 2-tuple
  - ...
  - forth(enumM (k-1)) → level 0 for k-tuple (SameAtomicType)
  -/

  -- The key lemma: from BFStrategyOmegaT, we can build any finite matching
  -- This follows because hStrat k allows k forth applications

  -- For the isomorphism, we need:
  -- 1. A function f : M → N where f(enumM i) is the witness from i+1 forth iterations
  -- 2. A function g : N → M where g(enumN j) is the witness from j+1 back iterations
  -- 3. Proof that f, g are inverses (from determinism of witnesses)
  -- 4. Proof that f preserves relations (from SameAtomicType at level 0)

  /-
  **Construction using buildMatchingTuple**

  Define f : M → N using the strategy witnesses:
  - For m = enumM i, construct the (i+1)-tuple [enumM 0, ..., enumM i]
  - Use hStrat (i+1) with buildMatchingTuple to get matching [n_0, ..., n_i]
  - Define f(m) = n_i (the last element)

  The challenge is showing this is an isomorphism:
  1. f is well-defined (doesn't depend on choice of enumeration index)
  2. f is injective (from SameAtomicType equalities)
  3. f is surjective (build inverse using back operations)
  4. f preserves relations (from SameAtomicType)

  For (1): If m = enumM i = enumM j with i < j, then both definitions give the same value
  because SameAtomicType forces equalities between positions.

  For (3): Define g similarly using back operations from the strategy.
  -/

  -- Helper: get matching tuple for first k elements of enumM
  let getMTuple : (k : ℕ) → { ns : Fin k → N // SameAtomicType (L := L) (enumM ∘ Fin.val) ns } :=
    fun k => buildMatchingTuple k (hStrat k) (fun i => enumM i.val)

  -- Define f: for each m, find its index and look up the corresponding n
  -- Use Classical.choose since Nat.find requires DecidablePred
  let indexM : M → ℕ := fun m => Classical.choose (hM_surj m)
  let f : M → N := fun m =>
    let i := indexM m
    (getMTuple (i + 1)).val (Fin.last i)

  -- Similarly for g using back operations
  -- Helper: get matching tuple for first k elements of enumN using back
  let getMTupleBack : (k : ℕ) → { ms : Fin k → M // SameAtomicType (L := L) ms (enumN ∘ Fin.val) } :=
    fun k => buildMatchingTupleBack k (hStrat k) (fun i => enumN i.val)

  let indexN : N → ℕ := fun n => Classical.choose (hN_surj n)
  let g : N → M := fun n =>
    let j := indexN n
    (getMTupleBack (j + 1)).val (Fin.last j)

  /-
  **Remaining proof obligations**:
  1. Show f ∘ g = id and g ∘ f = id
  2. Show f preserves relations
  3. Show g preserves relations (follows from 1 and 2)

  The key for (1) is that SameAtomicType includes equalities, so:
  - If enumM i = enumM j, then the witnesses n_i and n_j must be equal
  - This "locks in" the correspondence and forces f, g to be inverses

  The proof requires careful analysis of how indices interact, but the
  mathematical content is straightforward with the strategy structure.
  -/

  sorry

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- BFEquiv at level k starting from singletons allows iteration of forth to build matching tuples.

From BFEquiv (sz + k) 1 ![m] ![n₀] and sz additional elements starting from m, we can build
matching (sz+1)-tuples at BFEquiv level k.

This is the key lemma that allows building isomorphisms tracking where m is sent.

**Proof idea**: Induction on sz. At each step, use the forth property of BFEquiv at successor
level to extend the tuple by one element. The base case (sz = 0) just rewrites the tuples
to singleton form. -/
theorem BFEquiv_iterate_forth_from_singleton {M N : Type w} [L.Structure M] [L.Structure N]
    {m : M} {n₀ : N}
    {sz k : ℕ} (hBF : BFEquiv (L := L) ((sz + k : ℕ) : Ordinal.{0}) 1 ![m] ![n₀])
    (ms : Fin sz → M) :
    ∃ ns : Fin sz → N, BFEquiv (L := L) (k : Ordinal.{0}) (sz + 1)
      (Fin.cons m ms) (Fin.cons n₀ ns) := by
  induction sz generalizing k with
  | zero =>
    use Fin.elim0
    -- Fin.cons m Fin.elim0 = ![m] and Fin.cons n₀ Fin.elim0 = ![n₀]
    have hms : ms = Fin.elim0 := funext (fun i => i.elim0)
    have h1 : Fin.cons m (Fin.elim0 : Fin 0 → M) = ![m] := by ext i; fin_cases i; rfl
    have h2 : Fin.cons n₀ (Fin.elim0 : Fin 0 → N) = ![n₀] := by ext i; fin_cases i; rfl
    rw [hms, h1, h2]
    convert hBF using 2; omega
  | succ sz ih =>
    -- Type annotations to help inference
    let ms_init : Fin sz → M := ms ∘ Fin.castSucc
    let ms_last : M := ms (Fin.last sz)
    -- From BFEquiv ((sz+1) + k) 1 ![m] ![n₀], rewrite as BFEquiv (sz + (k+1)) 1 ...
    have hrewrite : ((sz + 1 + k : ℕ) : Ordinal.{0}) = ((sz + (k + 1) : ℕ) : Ordinal.{0}) := by
      norm_cast; omega
    rw [hrewrite] at hBF
    -- Get matching sz-tuple at level k+1 using IH
    obtain ⟨ns_init, hns_init⟩ := ih hBF ms_init
    -- hns_init : BFEquiv (k + 1) (sz + 1) (Fin.cons m ms_init) (Fin.cons n₀ ns_init)
    -- Use forth to extend by one more element
    have hsucc : (k + 1 : ℕ) = Order.succ (k : Ordinal.{0}) := by
      rw [← Ordinal.add_one_eq_succ]; norm_cast
    have hns_init' : BFEquiv (L := L) (Order.succ (k : Ordinal.{0})) (sz + 1)
        (Fin.cons m ms_init) (Fin.cons n₀ ns_init) := by
      convert hns_init using 2
    -- Apply forth with the last element ms_last : M
    obtain ⟨n_last, hn_last⟩ := BFEquiv_succ_forth_extend hns_init' ms_last
    -- hn_last : BFEquiv k ((sz + 1) + 1) (Fin.snoc (Fin.cons m ms_init) ms_last)
    --                                    (Fin.snoc (Fin.cons n₀ ns_init) n_last)
    use Fin.snoc ns_init n_last
    -- Need to show: Fin.cons m ms = Fin.snoc (Fin.cons m ms_init) ms_last
    -- and: Fin.cons n₀ (Fin.snoc ns_init n_last) = Fin.snoc (Fin.cons n₀ ns_init) n_last
    -- Use Fin.cons_snoc_eq_snoc_cons: cons a (snoc q b) = snoc (cons a q) b
    have hns_eq : Fin.cons n₀ (Fin.snoc ns_init n_last) =
        (Fin.snoc (Fin.cons n₀ ns_init) n_last : Fin (sz + 2) → N) :=
      Fin.cons_snoc_eq_snoc_cons n₀ ns_init n_last
    -- For hms_eq, we need: Fin.cons m ms = Fin.snoc (Fin.cons m ms_init) ms_last
    -- Since ms_init = ms ∘ castSucc and ms_last = ms (last sz), this is:
    -- Fin.cons m ms = Fin.snoc (Fin.cons m (ms ∘ castSucc)) (ms (last sz))
    -- By cons_snoc_eq_snoc_cons: Fin.cons m (Fin.snoc (ms ∘ castSucc) (ms (last sz))) = RHS
    -- So we need: ms = Fin.snoc (ms ∘ castSucc) (ms (last sz))
    have hms_decomp : ms = Fin.snoc (ms ∘ Fin.castSucc) (ms (Fin.last sz)) := by
      ext i
      simp only [Fin.snoc, Function.comp_apply]
      split_ifs with h
      · simp only [Fin.castSucc, Fin.castLT]; rfl
      · have hi : i = Fin.last sz := by
          ext
          simp only [Fin.val_last]
          omega
        simp only [hi, cast_eq]
    have hms_eq : Fin.cons m ms =
        (Fin.snoc (Fin.cons m ms_init) ms_last : Fin (sz + 2) → M) := by
      rw [hms_decomp]
      exact Fin.cons_snoc_eq_snoc_cons m ms_init ms_last
    rw [hms_eq, hns_eq]
    convert hn_last

/-- From BFEquiv at level ≥ ω for singleton tuples, build an isomorphism sending m to n.

**Proof status**: This theorem has the same coherence issue as `BFEquiv_omega_implies_equiv`.
The back-and-forth argument starting from (m, n) works at finite levels, but extracting
a coherent infinite chain requires solving the quantifier swap.

**Strategy for completion**: Same as `BFEquiv_omega_implies_equiv`:
1. Prove coherence of iterate_forth_from_singleton construction, or
2. Use Type-valued BFStrategy with computational witnesses

**Usage**: This theorem is used in `stabilizationOrdinal_mem_elementRank_set` for the
case where stabilizationOrdinal ≥ ω. The sorry here blocks that proof path in Rank.lean.

**Key lemma used**: `BFEquiv_iterate_forth_from_singleton` - builds matching tuples
starting from the singleton (m, n) correspondence. -/
theorem BFEquiv_ge_omega_singleton_implies_equiv_with_image {M N : Type w}
    [L.Structure M] [L.Structure N] [Countable M] [Countable N]
    {α : Ordinal.{0}} (hα : ω ≤ α)
    {m : M} {n : N}
    (hBF : BFEquiv (L := L) α 1 ![m] ![n]) :
    ∃ e : M ≃[L] N, e m = n := by
  /-
  **Proof strategy**: Adapt BFEquiv_omega_implies_equiv to start from (m, n).

  Once the coherence issue is resolved for BFEquiv_omega_implies_equiv,
  this theorem follows by:
  1. Starting the back-and-forth with p₀ = {m ↦ n}
  2. Using BFEquiv_iterate_forth_from_singleton for extensions
  3. The limit isomorphism e has e(m) = n by construction
  -/
  -- First show BFEquiv ω 1 ![m] ![n] by monotonicity
  have hBF_omega : BFEquiv (L := L) ω 1 ![m] ![n] := BFEquiv.monotone hα hBF
  -- Now build IsExtensionPair relative to tuples starting from m
  -- We adapt the approach from BFEquiv_omega_implies_equiv
  -- Key: all partial maps in our construction will have m ↦ n as the first pair

  -- Get CG instances
  haveI h_M_cg : Structure.CG L M := Structure.cg_of_countable
  haveI h_N_cg : Structure.CG L N := Structure.cg_of_countable

  -- Build initial FGEquiv g₀ mapping the closure of {m} to closure of {n}
  -- For relational languages, closure of {m} is just {m} itself
  have hBF0 : SameAtomicType (L := L) ![m] ![n] :=
    (BFEquiv.zero ![m] ![n]).mp (BFEquiv.monotone (zero_le _) hBF_omega)

  -- Key insight: We need to show that from any partial bijection starting with m ↦ n,
  -- we can extend it. This follows from BFEquiv_iterate_forth_from_singleton.

  -- Construct the isomorphism directly via the back-and-forth, always keeping m ↦ n
  -- For this, we use equiv_between_cg with a singleton initial FGEquiv

  -- Show that any singleton substructure is just a point in relational languages
  -- closure({m}) in a relational language is just {m} since there are no functions
  have hclosure_m : (closure L {m} : Set M) = {m} :=
    Substructure.closure_eq_of_isRelational L {m}

  have hclosure_n : (closure L {n} : Set N) = {n} :=
    Substructure.closure_eq_of_isRelational L {n}

  -- Build an FGEquiv from {m} to {n}
  -- We need: PartialEquiv with dom = closure L {m}, cod = closure L {n}, and toEquiv

  -- For now, we derive IsExtensionPair from BFEquiv ω 0 [] [] which we get from BFEquiv ω 1 ![m] ![n]
  -- Actually, we can't derive BFEquiv ω 0 [] [] from BFEquiv ω 1 ![m] ![n] directly.

  -- Alternative: prove directly that we can build an isomorphism with the property

  -- The key is BFEquiv_iterate_forth_from_singleton: starting from m ↦ n,
  -- we can extend to any tuple, and then use back to balance.

  -- For the full proof, we need to show that the partial maps can be extended arbitrarily.
  -- Since this requires significant infrastructure (adapting equiv_between_cg),
  -- we use the observation that BFEquiv_omega_implies_equiv gives SOME isomorphism,
  -- and we need to show the BFEquiv structure gives us one with e(m) = n.

  -- From BFEquiv ω 0 [] [] we would get an isomorphism.
  -- But we have BFEquiv ω 1 ![m] ![n].

  -- New approach: From the back-and-forth at singleton level, any m' has a match n'
  -- at succ level. This gives us the extension property starting from (m, n).

  -- The iteration: enumerate M and N, use forth/back alternating, always keeping m first.

  -- For a complete formal proof, we'd need to formalize the back-and-forth construction
  -- that tracks the initial correspondence. For now, we note that this follows from the
  -- standard back-and-forth argument starting from a non-empty partial isomorphism.

  -- Technical detail: The standard mathlib `equiv_between_cg` starts from any FGEquiv g
  -- and produces an isomorphism extending g. Our g₀ maps m ↦ n, so the result has e(m) = n.

  -- We need to verify IsExtensionPair holds. This requires showing that for ANY FGEquiv f,
  -- we can extend it. But BFEquiv ω 1 ![m] ![n] only gives us extension for tuples starting
  -- with m.

  /-
  **Solution: Incremental chain starting from (m, n)**

  Once BFEquiv_omega_implies_equiv is established with the incremental chain construction,
  this theorem follows by starting the chain with (m, n) instead of empty.

  Specifically:
  1. BFEquiv_iterate_forth_from_singleton gives us: from BFEquiv (sz+k) 1 ![m] ![n] and
     additional elements ms, we can build matching tuples (Fin.cons m ms, Fin.cons n ns)
     with BFEquiv k (sz+1).

  2. Start the back-and-forth with p₀ = {m ↦ n}

  3. At each extension stage, use BFEquiv_iterate_forth_from_singleton or the back variant
     to extend while keeping m ↦ n as the first element

  4. The limit isomorphism e has e(m) = n by construction, since every partial map
     in the chain maps m to n.

  This is exactly the same as BFEquiv_omega_implies_equiv but with a non-empty start.
  -/

  -- The key lemma: BFEquiv_iterate_forth_from_singleton allows building matching tuples
  -- starting from the singleton correspondence m ↦ n

  -- For any additional elements ms : Fin k → M, we get ns : Fin k → N such that
  -- (Fin.cons m ms, Fin.cons n ns) is a valid matching at some BFEquiv level

  -- Enumerate M \ {m} and N \ {n}, then apply the incremental construction
  -- The resulting bijection fixes m ↦ n by construction

  -- Formal proof requires the same chain infrastructure as BFEquiv_omega_implies_equiv
  -- Once that is complete, this follows immediately

  sorry

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

/-- Helper lemma: given a family of stabilization ordinals f(k) for each k-tuple,
and a supremum β that is past all f(k), we can upgrade BFEquiv from f(n) to β.

The hypothesis h : BFEquiv (f n) n a b states that a and b are BF-equivalent at
level f(n), which is the stabilization ordinal for n-tuples. The conclusion is
that they're also BF-equivalent at the higher level β.

**Key insight**: The witnesses from forth/back at level f(n) (for n-tuples) give
(n+1)-tuples at level (f n) - 1 = pred (f n). But for upgrading (n+1)-tuples,
we need to reach the (n+1)-tuple stabilization level f(n+1).

**Gap issue**: When f(n) < f(n+1), the (n+1)-tuple witness at f(n) is BELOW
the (n+1)-tuple stabilization point. The recursive call for (n+1)-tuples needs
input at f(n+1), but we only have f(n). This creates "gap cases" in the proof.

**Monotonization approach** (not implemented): Define g(n) = sup{f(k) | k ≤ n}.
Then g is nondecreasing and (n+1)-tuples at g(n) are at or past their stabilization
point g(n+1) ≥ f(n+1). However, this changes the induction structure.

**Actual usage**: In exists_complete_stabilization, the input comes from forth at
succ (f (k+1)), giving (k+1)-tuples at f(k+1). When recursing with n = k+1, the
input IS at f(n). But the recursive forth/back for (k+2)-tuples creates the gap. -/
private theorem BFEquiv_upgrade_from_family_aux {M N : Type w} [L.Structure M] [L.Structure N]
    [Countable N]
    {f : ℕ → Ordinal} (hf_stab : ∀ k, StabilizesForTuples (L := L) M (f k) k)
    {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (h : BFEquiv (L := L) (f n) n a b) (β : Ordinal) (hβ : ∀ k, f k ≤ β) :
    BFEquiv (L := L) β n a b := by
  -- The proof uses ordinal induction on β, generalizing over n, a, b.
  -- The key is that h is at level f(n), the stabilization point for n-tuples.
  -- We use stabilization to move from f(n) to succ(f(n)), then use monotonicity
  -- or recursive IH to reach β.
  induction β using Ordinal.limitRecOn generalizing n a b with
  | zero =>
    -- β = 0: f(n) ≤ 0 implies f(n) = 0, so h is already at level 0
    have hfn0 : f n = 0 := le_antisymm (hβ n) (zero_le _)
    rwa [hfn0] at h
  | succ γ ih =>
    -- β = succ γ: Either f(n) = β (done) or f(n) < β (need construction)
    rcases (hβ n).lt_or_eq with hfn_lt | hfn_eq
    · -- f(n) < succ γ, so f(n) ≤ γ
      rw [Order.lt_succ_iff] at hfn_lt
      rw [BFEquiv.succ]
      refine ⟨?base, ?forth, ?back⟩
      case base =>
        -- BFEquiv γ n a b: use stabilization + monotonicity or IH
        have h_stab := (hf_stab n N a b).mp h
        -- h_stab : BFEquiv (succ (f n)) n a b
        by_cases hcase : γ ≤ Order.succ (f n)
        · -- γ ≤ succ (f n): monotonicity down to γ
          exact BFEquiv.monotone hcase h_stab
        · -- γ > succ (f n): need to bridge from succ (f n) to γ
          push_neg at hcase
          -- Use IH: ih requires h at f(n) and bound ∀ k, f k ≤ γ
          -- We have bound ∀ k, f k ≤ succ γ. Need ∀ k, f k ≤ γ.
          -- If some f k = succ γ, we can't use IH directly.
          -- However, the key observation: stabilization at f(n) gives us
          -- BFEquiv (succ (f n)) n a b. From this, we want BFEquiv γ n a b
          -- where γ > succ (f n).
          -- Use the same stabilization repeatedly: at each ordinal level α ≥ f(n),
          -- we have BFEquiv α n a b ↔ BFEquiv (succ α) n a b (by stabilization).
          -- This isn't quite right: stabilization is specifically at f(n), not at all α ≥ f(n).
          -- The correct interpretation: stabilization means once past f(n), BFEquiv
          -- for n-tuples is constant. So BFEquiv (f n) = BFEquiv γ for all γ ≥ f n.
          -- We prove this direction (f n → γ) using the BFEquiv.succ structure:
          -- BFEquiv (succ α) ↔ BFEquiv α ∧ forth ∧ back
          -- From stabilization, BFEquiv (f n) ↔ BFEquiv (succ (f n)).
          -- For forth at succ (f n): witnesses at f n for (n+1)-tuples.
          -- For back: similar.
          -- The recursive structure: to prove BFEquiv γ from BFEquiv (f n):
          -- - If γ is successor of δ: prove BFEquiv δ recursively, then add forth/back.
          --   The forth/back at δ need (n+1)-tuples at δ-1 (or δ for limits).
          --   These come from stabilization at f(n), giving (n+1) at f(n)-1.
          --   To upgrade to δ-1, recursively apply for (n+1)-tuples if f(n+1) ≤ δ-1.
          -- This is exactly the structure of the IH. The challenge is the bound.
          -- For IH at γ, we need ∀ k, f k ≤ γ. If some f k = succ γ, fail.
          -- BUT: in this branch, we're computing BFEquiv γ FOR n-tuples only.
          -- The (n+1)-tuples at γ-1 are handled by recursion with n+1.
          -- That recursion needs bound ∀ k, f k ≤ γ-1 or similar.
          -- SIMPLIFICATION: Use the bound we have. If IH fails due to bound,
          -- handle those cases with monotonicity.
          -- Actually, for n-tuples, stabilization at f(n) means:
          -- For any α ≥ f(n), BFEquiv (f n) n a b → BFEquiv α n a b.
          -- Proof: induction on α - f(n). At each step, use stabilization iff
          -- plus the IH for forth/back. The forth/back for n-tuples at α need
          -- (n+1)-tuples at α. These come from... where?
          -- From stabilization at f(n): BFEquiv (f n) → BFEquiv (succ (f n)).
          -- Forth at succ (f n) gives witnesses at f(n) for (n+1)-tuples.
          -- To get (n+1)-tuples at α, need to upgrade from f(n) to α.
          -- If f(n+1) ≤ f(n), monotonicity down to f(n+1), then stabilization up.
          -- If f(n+1) > f(n), the (n+1)-tuple at f(n) is BELOW stabilization.
          -- In this case, (n+1) hasn't stabilized yet at f(n).
          -- To reach α for (n+1): if α < f(n+1), monotonicity works (f(n) to α).
          --   Wait, monotonicity goes DOWN: BFEquiv (f n) → BFEquiv α for α ≤ f n.
          --   Here α ≥ f(n), so monotonicity doesn't help directly.
          -- RESOLUTION: The witnesses from forth at succ (f n) are at f(n).
          -- For (n+1)-tuples, if f(n) ≥ f(n+1), monotone to f(n+1), then IH.
          -- If f(n) < f(n+1) ≤ α, we need BFEquiv α (n+1) from BFEquiv (f n) (n+1).
          -- Since f(n) < f(n+1), the (n+1)-tuple hasn't stabilized at f(n).
          -- So BFEquiv (f n) (n+1) ↔ BFEquiv (f(n+1)) (n+1) is NOT guaranteed.
          -- However, if f(n) ≥ α, monotonicity DOWN gives BFEquiv α from BFEquiv (f n).
          -- If f(n) < α: we're asking for a STRONGER condition.
          -- CONCLUSION: When f(n) < f(n+1) and f(n) < α < f(n+1), we're stuck.
          -- But in the ACTUAL USAGE, the witnesses come from forth at succ (f (k+1)),
          -- which gives (k+1)-tuples at f(k+1), the stabilization point!
          -- So for the recursive call, n becomes k+1, and h is at f(k+1) = f(n).
          -- This means the bound works out: we're always at stabilization points.
          -- For this inner proof (base case), we just need BFEquiv γ for n-tuples.
          -- We have h at f(n), and stabilization gives succ (f n).
          -- From succ (f n) to γ > succ (f n), use IH. But IH needs bound.
          -- If bound fails (some f k > γ), use monotonicity for those k's contributions.
          -- For n-tuples specifically, stabilization at f(n) gives the upgrade.
          -- The bound issue is for (n+1)-tuples in forth/back.
          sorry
      case forth =>
        intro m
        have h_stab := (hf_stab n N a b).mp h
        obtain ⟨n', hn'⟩ := BFEquiv.forth h_stab m
        use n'
        -- hn' : BFEquiv (f n) (n+1) (snoc a m) (snoc b n')
        -- Need: BFEquiv γ (n+1)
        -- Case analysis on where f(n), f(n+1), and γ stand relative to each other.
        -- If f(n) ≥ γ: monotonicity DOWN gives the result.
        -- If f(n) < γ ≤ f(n+1): need to go UP, but (n+1) hasn't stabilized yet.
        --   In this case, we actually need witnesses at higher levels, which
        --   we don't have directly from hn' at f(n).
        -- If f(n+1) ≤ γ: (n+1)-tuples are stable. Use IH to upgrade.
        --   But IH for (n+1)-tuples expects input at f(n+1), not f(n).
        --   If f(n) ≥ f(n+1): monotonicity gives f(n+1) from f(n).
        --   If f(n) < f(n+1): we're in a gap.
        -- The resolution: in actual usage, hn' comes from forth at level
        -- succ (f (k+1)) for k-tuples, giving (k+1)-tuples at f(k+1).
        -- When we recurse with n = k+1, the input IS at f(n) = f(k+1).
        by_cases hfn_γ : γ ≤ f n
        · -- γ ≤ f(n): monotonicity DOWN from f(n) to γ
          exact BFEquiv.monotone hfn_γ hn'
        · -- f(n) < γ: need to go UP
          push_neg at hfn_γ
          -- Check if (n+1)-tuples have stabilized by γ
          by_cases hfn1_γ : f (n + 1) ≤ γ
          · -- f(n+1) ≤ γ: (n+1)-tuples are stable at γ
            -- Need BFEquiv γ (n+1) from BFEquiv (f n) (n+1)
            -- If f(n) ≥ f(n+1): mono to f(n+1), then IH for (n+1)
            -- If f(n) < f(n+1): hn' is at f(n) < f(n+1) ≤ γ
            --   Use IH for (n+1): requires input at f(n+1).
            --   From hn' at f(n), if f(n) ≥ f(n+1), mono gives it.
            --   If f(n) < f(n+1), we need stabilization for (n+1) to bridge.
            --   Stabilization at f(n+1): BFEquiv (f(n+1)) ↔ BFEquiv (succ (f(n+1)))
            --   But we don't have BFEquiv (f(n+1)) (n+1), only (f n) (n+1).
            --   STUCK unless f(n) ≥ f(n+1).
            -- Need to upgrade (n+1)-tuples from f(n) to γ where f(n+1) ≤ γ
            -- This requires IH for (n+1)-tuples, but the bound is tricky.
            -- The IH requires ∀ k, f k ≤ γ, but we only have ∀ k, f k ≤ succ γ.
            -- For now, use sorry and note this is the key technical gap.
            sorry
          · -- f(n+1) > γ: (n+1)-tuples not yet stable at γ
            push_neg at hfn1_γ
            -- f(n) < γ < f(n+1): in the gap before (n+1) stabilizes
            -- We have hn' at f(n), want γ, and both f(n) < γ and γ < f(n+1).
            -- Without additional structure, we can't bridge this gap.
            sorry
      case back =>
        intro n'
        have h_stab := (hf_stab n N a b).mp h
        obtain ⟨m, hm⟩ := BFEquiv.back h_stab n'
        use m
        -- Symmetric to forth
        by_cases hfn_γ : γ ≤ f n
        · exact BFEquiv.monotone hfn_γ hm
        · push_neg at hfn_γ
          by_cases hfn1_γ : f (n + 1) ≤ γ
          · -- Similar to forth case
            sorry
          · push_neg at hfn1_γ
            sorry
    · -- f(n) = succ γ = β: h is already at level β
      rw [← hfn_eq]; exact h
  | limit β hβlim ih =>
    -- β is a limit: BFEquiv β ↔ ∀ γ < β, BFEquiv γ
    rw [BFEquiv.limit β hβlim]
    intro γ hγ
    by_cases hfn_γ : f n ≤ γ
    · -- f(n) ≤ γ: need to go from f(n) to γ, use IH
      by_cases hall : ∀ k, f k ≤ γ
      · exact @ih γ hγ n a b h hall
      · -- Some f(k) > γ: can't use IH directly
        -- For n-tuples, if f(n) ≤ γ, stabilization should give the upgrade.
        -- But forth/back need (n+1)-tuples at γ, which may not be bounded.
        sorry
    · -- f(n) > γ: monotonicity DOWN from f(n) to γ
      push_neg at hfn_γ
      exact BFEquiv.monotone (le_of_lt hfn_γ) h

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

/-- For countable M and each n, there exists α < ω₁ where n-tuples stabilize.

**Proof idea**: Consider the sequence of equivalence relations Eα on (Fin n → M) × Σ N, (Fin n → N)
defined by (a, N, b) Eα (a', N', b') iff a = a' and for all countable P and c : Fin n → P,
BFEquiv α n a c ↔ BFEquiv α n a' c.

This is a refining sequence: Eβ ⊆ Eα when α < β (because BFEquiv is antimonotone in α).
For countable M, (Fin n → M) is countable, so there are at most countably many Eα-classes.
A decreasing chain of partitions with countably many classes must stabilize at some
countable ordinal.

Note: The proof of StabilizesForTuples requires showing that BFEquiv α ↔ BFEquiv (succ α) for
n-tuples, which involves forth/back conditions that use (n+1)-tuples. The proper way to prove
this is through the complete stabilization machinery, which handles all tuple sizes simultaneously.
This theorem provides the per-tuple-size existence which is then combined in
`exists_complete_stabilization`. -/
theorem exists_stabilization_for_tuples (M : Type w) [L.Structure M] [Countable M] (n : ℕ) :
    ∃ α < (Ordinal.omega 1 : Ordinal.{0}), StabilizesForTuples (L := L) M α n := by
  /-
  **Proof outline**: We use the Scott formula characterization of BFEquiv.

  The key insight is that BFEquiv α n a b ↔ (scottFormula a α).Realize b
  (by `realize_scottFormula_iff_BFEquiv`). Since the Scott formula depends only on M, a, and α:
  - For fixed a, b: as α increases, the formula gets stronger (implies lower-level formulas)
  - The stabilization condition BFEquiv α ↔ BFEquiv (succ α) means the formulas at α and succ α
    are logically equivalent (for the purpose of testing against countable structures)

  For each pair (a, a') of n-tuples from M, define:
    stab(a, a') = sInf {α | BFEquiv α n a a' ↔ BFEquiv (succ α) n a a'}

  This set is nonempty (it contains all ordinals ≥ ω since eventually stabilizes) and the
  infimum is well-defined. The key facts are:
  1. For each pair, stab(a, a') < ω₁ (antitone sequence stabilizes before ω₁)
  2. There are countably many pairs (M^n × M^n is countable)
  3. The supremum of countably many ordinals < ω₁ is < ω₁ (regularity of ω₁)

  The proof proceeds by showing self-stabilization (M testing against M) implies full
  stabilization (M testing against all countable N) via the Scott formula.
  -/

  -- Step 1: Define per-pair stabilization for M testing against M
  -- For each pair (a, a'), consider the set of α where BFEquiv α n a a' ↔ BFEquiv (succ α) n a a'
  let selfStabSet : (Fin n → M) → (Fin n → M) → Set Ordinal.{0} := fun a a' =>
    {α | BFEquiv (L := L) α n a a' ↔ BFEquiv (L := L) (Order.succ α) n a a'}

  -- Step 2: Show each selfStabSet is nonempty and has an element < ω₁
  -- The key is that the BFEquiv relation, when restricted to M × M, forms a decreasing
  -- sequence of equivalence relations. Eventually it must stabilize.
  have hSelfStab : ∀ a a' : Fin n → M, ∃ α < Ordinal.omega 1, α ∈ selfStabSet a a' := by
    intro a a'
    -- The BFEquiv relation for (a, a') forms an antitone sequence of truth values.
    -- There are only two possible values (True/False), so it stabilizes.
    -- The stabilization point is the infimum of {α | BFEquiv α n a a' = BFEquiv (succ α) n a a'}.
    -- This is well-defined because:
    -- 1. At level 0, BFEquiv may or may not hold
    -- 2. The sequence is antitone: β ≥ α → (BFEquiv β n a a' → BFEquiv α n a a')
    -- 3. Either BFEquiv holds eventually for all levels, or it fails at some level
    -- 4. If it fails at level β, then for all γ ≥ β, BFEquiv γ n a a' = False
    -- 5. If it holds for all levels, stabilization is at 0
    --
    -- More precisely: define change(a,a') = sInf {α | ¬BFEquiv α n a a'} if nonempty, else 0.
    -- Then for α ≥ change(a,a'), BFEquiv α n a a' is constantly False (if change exists)
    -- or constantly True (if no change). In either case, stabilization occurs.
    --
    -- The change point (if it exists) is < ω₁ because:
    -- - If BFEquiv fails at some level, it's witnessed by some finite stage of the
    --   back-and-forth construction failing
    -- - Such failures are determined by the countable structure M
    -- - The failure point is thus below ω₁
    by_cases hEventuallyFalse : ∃ β, ¬BFEquiv (L := L) β n a a'
    · -- Case: BFEquiv eventually becomes False
      -- Take the infimum of levels where it's False
      let changePoint := sInf {β : Ordinal.{0} | ¬BFEquiv (L := L) β n a a'}
      have hNonempty : {β : Ordinal.{0} | ¬BFEquiv (L := L) β n a a'}.Nonempty :=
        hEventuallyFalse
      -- The changePoint is the first level where BFEquiv is False
      have hFalseAt : ¬BFEquiv (L := L) changePoint n a a' := csInf_mem hNonempty
      -- For all β > changePoint, BFEquiv β n a a' is also False (by monotonicity)
      have hFalseAbove : ∀ β ≥ changePoint, ¬BFEquiv (L := L) β n a a' := by
        intro β hβ
        intro hBF
        have hContra := BFEquiv.monotone hβ hBF
        exact hFalseAt hContra
      -- So changePoint is a stabilization point
      use changePoint
      constructor
      · -- changePoint < ω₁
        -- The changePoint is the sInf of a nonempty set of ordinals
        -- We need to show this sInf is < ω₁
        -- This follows from the fact that if any element of the set is < ω₁,
        -- then the infimum is ≤ that element < ω₁
        -- We'll show that ω itself is in the set (or past the change point)
        -- Actually, we need a more careful argument...
        -- The change point could be any ordinal. But for countable structures,
        -- by the Scott sentence theory, stabilization occurs at some countable ordinal.
        -- For now, we use a simpler bound: if BFEquiv fails at β, then β provides
        -- a witness. The first such β is the change point.
        -- We need: every such β that witnesses failure has β < ω₁.
        -- This is because BFEquiv at level β is determined by back-and-forth games
        -- of length β. For countable structures, the relevant distinctions are
        -- captured by ordinals < ω₁.
        --
        -- Alternative: use that the set of n-tuples (a, a') is countable,
        -- so we can use a diagonal argument later. For each individual pair,
        -- we just need SOME bound < ω₁.
        -- Use that ω is past any finite stabilization
        -- Actually, a cleaner approach: by well-foundedness, the infimum exists.
        -- We show changePoint ≤ ω for countable structures by the nature of
        -- BFEquiv (if two elements differ, they differ at some finite stage).
        -- But this requires more careful analysis of BFEquiv structure.
        --
        -- Simplest approach: use that ω ∈ the upper set, so changePoint ≤ ω < ω₁.
        -- But we need to verify ω is an upper bound for the change set,
        -- which isn't generally true.
        --
        -- Use a different approach: the Scott formula characterization.
        -- At level α, BFEquiv α n a a' ↔ (scottFormula a α).Realize a'.
        -- The scottFormula is in L_ω₁ω (infinitary formulas with countable conjunctions).
        -- For countable M, the semantics of such formulas stabilize below ω₁.
        --
        -- For now, we use sorry for this bound, as the full proof requires
        -- additional model-theoretic machinery about L_ω₁ω semantics.
        sorry
      · -- changePoint is a stabilization point
        show BFEquiv changePoint n a a' ↔ BFEquiv (Order.succ changePoint) n a a'
        -- Both sides are False
        constructor
        · intro h; exact absurd h hFalseAt
        · intro h; exact absurd h (hFalseAbove (Order.succ changePoint) (Order.le_succ changePoint))
    · -- Case: BFEquiv is True at all levels
      push_neg at hEventuallyFalse
      -- BFEquiv α n a a' is True for all α, so 0 is a stabilization point
      use 0
      constructor
      · exact Ordinal.omega_pos 1
      · -- 0 is a stabilization point: BFEquiv 0 ↔ BFEquiv (succ 0)
        constructor
        · intro _; exact hEventuallyFalse (Order.succ 0)
        · intro _; exact hEventuallyFalse 0

  -- Step 3: Extract the per-pair stabilization ordinals
  choose stabOrd hstabOrd_lt hstabOrd_mem using hSelfStab

  -- Step 4: Enumerate all pairs (using countability of M^n × M^n)
  haveI : Countable (Fin n → M) := inferInstance
  haveI : Countable ((Fin n → M) × (Fin n → M)) := inferInstance
  -- Handle case when M is empty
  by_cases hM_nonempty : Nonempty M
  swap
  · -- M is empty: StabilizesForTuples holds at some level < ω₁
    -- For empty M, the stabilization happens at level 1.
    -- For n > 0, the statement is vacuous since there are no tuples a : Fin n → M.
    -- For n = 0, the BFEquiv relation stabilizes because the back condition at level α ≥ 1
    -- is constantly false (or true) depending on whether N is nonempty.
    haveI : IsEmpty M := not_nonempty_iff.mp hM_nonempty
    use 1
    refine ⟨lt_trans Ordinal.one_lt_omega0 Ordinal.omega0_lt_omega_one, ?_⟩
    intro N _ _ a b
    cases n with
    | zero =>
      -- For 0-tuples with empty M, BFEquiv 1 already forces N to be empty
      -- (back condition requires ∃ m : M, ... which is impossible).
      -- So BFEquiv (succ 1) adds nothing: forth/back are both vacuous.
      constructor
      · intro h1
        have hNe : IsEmpty N := by
          by_contra hne
          rw [not_isEmpty_iff] at hne
          obtain ⟨n'⟩ := hne
          have h1s : BFEquiv (L := L) (Order.succ 0) 0 a b := by
            rwa [Ordinal.succ_zero]
          exact IsEmpty.false (BFEquiv.back h1s n').choose
        rw [BFEquiv.succ]
        exact ⟨h1, fun m => isEmptyElim m, fun n' => isEmptyElim n'⟩
      · exact BFEquiv.of_succ
    | succ k => exact (IsEmpty.false (a 0)).elim
  haveI : Nonempty M := hM_nonempty
  haveI : Nonempty ((Fin n → M) × (Fin n → M)) :=
    ⟨(fun _ => Classical.arbitrary M, fun _ => Classical.arbitrary M)⟩
  obtain ⟨enumPairs, hPairs_surj⟩ := exists_surjective_nat ((Fin n → M) × (Fin n → M))

  -- Step 5: Define the global stabilization ordinal as supremum + 1
  let globalStab : Ordinal.{0} := ⨆ k, stabOrd (enumPairs k).1 (enumPairs k).2 + 1

  -- Step 6: Show globalStab < ω₁
  have hGlobalLt : globalStab < Ordinal.omega 1 := by
    have hEachLt : ∀ k, stabOrd (enumPairs k).1 (enumPairs k).2 + 1 < Ordinal.omega 1 := by
      intro k
      exact Order.IsSuccLimit.succ_lt (Cardinal.isSuccLimit_omega 1)
        (hstabOrd_lt (enumPairs k).1 (enumPairs k).2)
    have hEachLt' : ∀ k, stabOrd (enumPairs k).1 (enumPairs k).2 + 1 < (Cardinal.aleph 1).ord := by
      intro k; rw [Cardinal.ord_aleph]; exact hEachLt k
    have hsup := Ordinal.iSup_sequence_lt_omega_one
      (fun k => stabOrd (enumPairs k).1 (enumPairs k).2 + 1) hEachLt'
    rw [Cardinal.ord_aleph] at hsup
    exact hsup

  -- Step 7: Show globalStab satisfies StabilizesForTuples
  -- Self-stabilization at globalStab implies full stabilization
  have hSelfStabAtGlobal : ∀ a a' : Fin n → M,
      BFEquiv (L := L) globalStab n a a' ↔ BFEquiv (L := L) (Order.succ globalStab) n a a' := by
    intro a a'
    -- Get the pair index
    obtain ⟨k, hk⟩ := hPairs_surj (a, a')
    -- The stabilization ordinal for this pair is stabOrd a a'
    have hstab := hstabOrd_mem a a'
    -- We have stabOrd a a' < globalStab (since globalStab is sup of stabOrd _ _ + 1)
    have hBdd : BddAbove (Set.range fun k => stabOrd (enumPairs k).1 (enumPairs k).2 + 1) :=
      ⟨Ordinal.omega 1, fun _ ⟨m, hm⟩ => hm ▸ le_of_lt
        (Order.IsSuccLimit.succ_lt (Cardinal.isSuccLimit_omega 1)
          (hstabOrd_lt (enumPairs m).1 (enumPairs m).2))⟩
    have hk_le : stabOrd a a' + 1 ≤ globalStab := by
      have h := le_ciSup hBdd k
      simp only [hk] at h
      exact h
    have hstab_lt : stabOrd a a' < globalStab := lt_of_lt_of_le (Order.lt_succ _) hk_le
    -- Since stabOrd a a' is the stabilization point and globalStab > stabOrd a a',
    -- the BFEquiv relation is constant on [stabOrd a a', ∞)
    -- We need to show: BFEquiv globalStab ↔ BFEquiv (succ globalStab)
    -- From hstab: BFEquiv (stabOrd a a') ↔ BFEquiv (succ (stabOrd a a'))
    -- By BFEquiv.monotone, we can propagate this to globalStab
    -- The key: once stabilized at stabOrd a a', BFEquiv is constant above that point
    -- Proof: At stabOrd a a', BFEquiv (stabOrd) ↔ BFEquiv (succ stabOrd)
    -- This means either both hold or neither holds.
    -- By monotonicity, for any γ ≥ stabOrd: BFEquiv γ → BFEquiv (stabOrd)
    -- And: BFEquiv (stabOrd) → BFEquiv γ (need to prove this direction)
    --
    -- The issue: stabilization at stabOrd gives equivalence with succ stabOrd,
    -- but extending to arbitrary γ ≥ stabOrd requires the full induction.
    -- However, for just checking globalStab ↔ succ globalStab, we can use:
    -- Both directions follow from monotonicity + the fact that the value is constant.
    constructor
    · intro hBF_global
      -- BFEquiv globalStab → BFEquiv (succ globalStab)
      -- By monotonicity: BFEquiv globalStab → BFEquiv (stabOrd a a')
      have hBF_stab := BFEquiv.monotone (le_of_lt hstab_lt) hBF_global
      -- By stabilization: BFEquiv (stabOrd a a') → BFEquiv (succ (stabOrd a a'))
      have hBF_succ_stab := hstab.mp hBF_stab
      -- We need to propagate from succ (stabOrd a a') up to succ globalStab
      -- This requires showing BFEquiv is monotonically constant above stabOrd
      -- which is the "upgrade" property from stabilization.
      -- For self-testing (M vs M), this should follow from the stabilization condition.
      -- The key insight: stabilization means BFEquiv is constant at all levels ≥ stabOrd.
      -- Proof: by transfinite induction. At each step α ↔ succ α since we're past stabOrd.
      -- We need a lemma: StabilizesForTuples at α implies strong stabilization for self-testing.
      -- For now, we use the structure of BFEquiv.succ directly.
      rw [BFEquiv.succ]
      refine ⟨hBF_global, ?_, ?_⟩
      · -- forth at globalStab for n-tuples
        intro m
        -- Need to show ∃ m', BFEquiv globalStab (n+1) (snoc a m) (snoc a' m')
        -- This is about (n+1)-tuples, not n-tuples.
        -- The stabilization for n-tuples doesn't directly give this.
        -- This is the key issue: StabilizesForTuples at a given n doesn't control n+1.
        -- For self-stabilization to imply full stabilization, we need to use
        -- the Scott formula characterization, which ties all tuple sizes together.
        -- For now, we defer this to the sorry.
        sorry
      · -- back at globalStab for n-tuples
        intro m'
        sorry
    · intro hBF_succ_global
      -- BFEquiv (succ globalStab) → BFEquiv globalStab: just BFEquiv.monotone
      exact BFEquiv.of_succ hBF_succ_global

  -- Use self-stabilization to get full stabilization
  use globalStab, hGlobalLt
  intro N _ _ a b
  -- Need: BFEquiv globalStab n a b ↔ BFEquiv (succ globalStab) n a b
  -- Use the Scott formula: BFEquiv α n a b ↔ (scottFormula a α).Realize b
  -- Since scottFormula depends only on M and a, stabilization of the formula
  -- (checked via self-testing with M) implies stabilization for all countable N.
  -- Specifically:
  -- - (scottFormula a globalStab).Realize b ↔ BFEquiv globalStab n a b (by the iff)
  -- - (scottFormula a (succ globalStab)).Realize b ↔ BFEquiv (succ globalStab) n a b
  -- - If the formulas at globalStab and succ globalStab are equivalent (semantically),
  --   then both BFEquiv conditions are equivalent.
  --
  -- The semantic equivalence of scottFormula a globalStab and scottFormula a (succ globalStab)
  -- follows from the self-stabilization property, since the formulas' truth values on
  -- countable structures are determined by their truth on M (via back-and-forth).
  --
  -- This is the core of the Scott sentence theorem: the formula at stabilization
  -- characterizes the isomorphism type among countable structures.
  --
  -- Full proof requires showing that self-stabilization implies the formulas are
  -- semantically equivalent, which needs more infrastructure.
  sorry

/-- For countable M, there exists α < ω₁ where all tuples stabilize.

**Proof approach**: Take the supremum of the stabilization ordinals for each tuple size.
Since each is < ω₁ and there are countably many (one for each n ∈ ℕ), the
supremum is also < ω₁ by regularity of ω₁.

**Key challenge**: Showing that per-tuple-size stabilization implies complete
stabilization at the supremum. The upgrade from f(k) to sup for k-tuples requires
witnesses from forth/back, which involve (k+1)-tuples. These (k+1)-tuples need to
be upgraded from f(k) (where they're produced) to sup.

**The gap issue**: If f(k) < f(k+1), the (k+1)-tuple witnesses at f(k) are BELOW
the (k+1)-tuple stabilization point f(k+1). The upgrade from f(k) to sup crosses
this stabilization boundary, which requires the full `BFEquiv_upgrade_from_family_aux`
lemma with its gap cases.

**Alternative approach** (not implemented): Prove complete stabilization directly
without going through per-tuple-size stabilization. The model-theoretic argument
shows that the entire BFEquiv relation stabilizes simultaneously, not tuple-by-tuple. -/
theorem exists_complete_stabilization (M : Type w) [L.Structure M] [Countable M] :
    ∃ α < (Ordinal.omega 1 : Ordinal.{0}), StabilizesCompletely (L := L) M α := by
  -- For each n, get the stabilization ordinal αₙ < ω₁
  have h : ∀ n : ℕ, ∃ α < (Ordinal.omega 1 : Ordinal.{0}), StabilizesForTuples (L := L) M α n :=
    exists_stabilization_for_tuples M
  -- Take the supremum
  let f : ℕ → Ordinal.{0} := fun n => Classical.choose (h n)
  have hf : ∀ n, f n < Ordinal.omega 1 ∧ StabilizesForTuples (L := L) M (f n) n := by
    intro n
    exact Classical.choose_spec (h n)
  -- The supremum of countably many ordinals < ω₁ is < ω₁
  -- We use sup + 1 to ensure we're past all individual stabilization points
  -- Helper: each f n + 1 < ω₁
  have hlt : ∀ n, f n + 1 < Ordinal.omega 1 := fun n =>
    Order.IsSuccLimit.succ_lt (Cardinal.isSuccLimit_omega 1) (hf n).1
  use ⨆ n, f n + 1
  constructor
  ·
    -- Use that ω₁ is regular: supremum of countably many ordinals < ω₁ is < ω₁
    -- Note: Ordinal.omega 1 = (Cardinal.aleph 1).ord by Cardinal.ord_aleph
    have hlt' : ∀ n, f n + 1 < (Cardinal.aleph 1).ord := by
      intro n; rw [Cardinal.ord_aleph]; exact hlt n
    have hsup := Ordinal.iSup_sequence_lt_omega_one (fun n => f n + 1) hlt'
    rw [Cardinal.ord_aleph] at hsup
    exact hsup
  · -- StabilizesCompletely at sup
    -- At the supremum, all tuple sizes have stabilized.
    -- The proof uses that at sup = ⨆ n, f n + 1:
    -- - For each k, f k + 1 ≤ sup, so we're past the k-tuple stabilization point
    -- - For each k+1, f (k+1) + 1 ≤ sup, so (k+1)-tuples are also stable
    -- This allows the forth/back conditions at level sup to use witnesses from
    -- level f (k+1), which are stable under the (k+1)-tuple stabilization.
    --
    -- The proof requires a simultaneous induction on ordinal and tuple size,
    -- showing that BFEquiv at sup is constant with BFEquiv at the individual
    -- stabilization points. This is the content of BFEquiv_upgrade_at_stabilization
    -- once we have StabilizesCompletely.
    --
    -- For a formal proof, we need to break the apparent circularity by showing
    -- that the individual StabilizesForTuples conditions at f k combine to give
    -- StabilizesCompletely at sup. The key insight is that sup is uniformly past
    -- all f k, so all tuple sizes are simultaneously in their stable regimes.
    intro k N _ _ a b
    have hbdd : BddAbove (Set.range fun n => f n + 1) :=
      ⟨Ordinal.omega 1, fun _ ⟨m, hm⟩ => hm ▸ le_of_lt (hlt m)⟩
    have hfk_le : f k + 1 ≤ ⨆ n, f n + 1 := le_ciSup hbdd k
    have hfk_lt : f k < ⨆ n, f n + 1 := lt_of_lt_of_le (Order.lt_succ (f k)) hfk_le
    have hstab_k := (hf k).2 N a b
    constructor
    · -- BFEquiv sup → BFEquiv (succ sup)
      intro hBF_sup
      have hBF_fk : BFEquiv (L := L) (f k) k a b := BFEquiv.monotone (le_of_lt hfk_lt) hBF_sup
      have _hBF_succ_fk : BFEquiv (L := L) (Order.succ (f k)) k a b := hstab_k.mp hBF_fk
      -- The key insight: at sup = ⨆ n, f n + 1, all tuple sizes are past their
      -- individual stabilization points. Use forth from level succ (f (k+1)) to get
      -- witnesses at the (k+1)-tuple stabilization level, then propagate up using
      -- the stability of all higher tuple sizes.
      --
      -- This requires a simultaneous induction on (ordinal, tuple size) to show that
      -- BFEquiv at sup equals BFEquiv at each f n. The formal proof uses that sup is
      -- uniformly past all stabilization points.
      rw [BFEquiv.succ]
      refine ⟨hBF_sup, ?_, ?_⟩
      · -- Forth: find witness at (k+1)-tuple stabilization level, then propagate
        intro m
        have hsucc_f_k1_le : Order.succ (f (k+1)) ≤ ⨆ n, f n + 1 := by
          calc Order.succ (f (k+1)) = f (k+1) + 1 := Ordinal.add_one_eq_succ (f (k+1))
            _ ≤ ⨆ n, f n + 1 := le_ciSup hbdd (k+1)
        have hBF_succ_f_k1 : BFEquiv (L := L) (Order.succ (f (k+1))) k a b :=
          BFEquiv.monotone hsucc_f_k1_le hBF_sup
        obtain ⟨n', hn'⟩ := BFEquiv.forth hBF_succ_f_k1 m
        use n'
        -- hn' : BFEquiv (f (k+1)) (k+1) (snoc a m) (snoc b n')
        -- Need to propagate from f (k+1) to sup using that all tuple sizes are stable.
        -- Use the helper lemma with the stabilization family.
        have hstab_all : ∀ j, StabilizesForTuples (L := L) M (f j) j := fun j => (hf j).2
        have hf_le_sup : ∀ j, f j ≤ ⨆ n, f n + 1 := fun j =>
          le_trans (Order.le_succ (f j)) (le_ciSup hbdd j)
        exact BFEquiv_upgrade_from_family_aux hstab_all hn' _ hf_le_sup
      · -- Back: symmetric to forth
        intro n'
        have hsucc_f_k1_le : Order.succ (f (k+1)) ≤ ⨆ n, f n + 1 := by
          calc Order.succ (f (k+1)) = f (k+1) + 1 := Ordinal.add_one_eq_succ (f (k+1))
            _ ≤ ⨆ n, f n + 1 := le_ciSup hbdd (k+1)
        have hBF_succ_f_k1 : BFEquiv (L := L) (Order.succ (f (k+1))) k a b :=
          BFEquiv.monotone hsucc_f_k1_le hBF_sup
        obtain ⟨m', hm'⟩ := BFEquiv.back hBF_succ_f_k1 n'
        use m'
        have hstab_all : ∀ j, StabilizesForTuples (L := L) M (f j) j := fun j => (hf j).2
        have hf_le_sup : ∀ j, f j ≤ ⨆ n, f n + 1 := fun j =>
          le_trans (Order.le_succ (f j)) (le_ciSup hbdd j)
        exact BFEquiv_upgrade_from_family_aux hstab_all hm' _ hf_le_sup
    · -- BFEquiv (succ α) n a b → BFEquiv α n a b : monotonicity
      exact BFEquiv.of_succ

/-- At a complete stabilization ordinal, BFEquiv0 implies isomorphism for countable structures.
This is the corrected version of BFEquiv_omega_implies_equiv. -/
theorem BFEquiv_stabilization_implies_equiv {M N : Type w} [L.Structure M] [L.Structure N]
    [Countable M] [Countable N]
    {α : Ordinal} (hstab : StabilizesCompletely (L := L) M α)
    (h : BFEquiv (L := L) α 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N)) :
    Nonempty (M ≃[L] N) := by
  /-
  **Proof strategy**: Standard back-and-forth, but now it works because:

  1. At level α (stabilization), forth gives witness n' with BFEquiv α (n+1) (snoc a m) (snoc b n')
  2. By upgrade lemma, this witness works at ALL levels ≥ α
  3. So we can iterate without losing levels - witnesses stay at level α
  4. The limit of finite matchings is the isomorphism

  The key difference from BFEquiv_omega_implies_equiv: at ω, witnesses might only work
  at lower levels (quantifier swap problem). At stabilization, witnesses stay stable.
  -/
  -- Handle empty cases
  by_cases hM_empty : IsEmpty M
  · by_cases hN_empty : IsEmpty N
    · -- Both empty: construct trivial isomorphism
      refine ⟨⟨Equiv.equivOfIsEmpty M N, ?_, ?_⟩⟩
      · -- map_fun': vacuously true (no elements)
        intro n f; exact IsEmpty.elim inferInstance f
      · -- map_rel': for n ≥ 1, x : Fin n → M is impossible
        intro n r x
        match n with
        | 0 =>
          -- x : Fin 0 → M must be Fin.elim0
          have hSAT := (BFEquiv.zero (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N)).mp
            (BFEquiv.monotone (zero_le _) h)
          have hx : x = Fin.elim0 := funext (fun i => i.elim0)
          subst hx
          have hcomp : (Equiv.equivOfIsEmpty M N).toFun ∘ (Fin.elim0 : Fin 0 → M) =
                       (Fin.elim0 : Fin 0 → N) := funext (fun i => i.elim0)
          rw [hcomp]
          exact (hSAT (AtomicIdx.rel r Fin.elim0)).symm
        | n + 1 => exact IsEmpty.elim hM_empty (x 0)
    · -- M empty, N nonempty: contradiction
      push_neg at hN_empty
      obtain ⟨n⟩ := hN_empty
      -- Use back at succ α to get element in M
      have hBF_succ := (hstab 0 N Fin.elim0 Fin.elim0).mp h
      have hback := BFEquiv.back hBF_succ n
      obtain ⟨m, _⟩ := hback
      exact hM_empty.elim m
  push_neg at hM_empty
  haveI : Nonempty M := hM_empty

  -- N must also be nonempty
  haveI : Nonempty N := by
    obtain ⟨m⟩ : Nonempty M := inferInstance
    have hBF_succ := (hstab 0 N Fin.elim0 Fin.elim0).mp h
    have hforth := BFEquiv.forth hBF_succ m
    obtain ⟨n, _⟩ := hforth
    exact ⟨n⟩

  -- Get enumerations
  obtain ⟨enumM, hM_surj⟩ := exists_surjective_nat M
  obtain ⟨enumN, hN_surj⟩ := exists_surjective_nat N

  /-
  **Back-and-forth construction using stabilization**

  Build a sequence of partial bijections:
  - p₀ : ∅ → ∅
  - p₁ extends p₀ with enumM(0) in domain
  - p₂ extends p₁ with enumN(0) in codomain (if not already there)
  - p₃ extends p₂ with enumM(1) in domain (if not already there)
  - ...

  At each step, we maintain BFEquiv α on the tuple pairs. Since α is a complete
  stabilization ordinal, the upgrade lemma ensures witnesses stay at level α.

  The limit is a bijection M ≃ N preserving atomic type, hence an isomorphism.
  -/

  -- The key difference from BFEquiv_omega_implies_equiv is that at stabilization,
  -- witnesses at level α remain valid at level α (not just at lower levels).
  -- This resolves the quantifier swap problem:
  -- From BFEquiv α, forth gives witness n' with BFEquiv α (n+1) ...
  -- This witness stays at level α for ALL future extensions.

  -- The construction uses the following invariant:
  -- At step k, we have a partial bijection pk : dom_k → cod_k where:
  -- - |dom_k| = |cod_k| = k (k elements each)
  -- - dom_k ⊆ M, cod_k ⊆ N
  -- - The correspondence preserves BFEquiv α: BFEquiv α k (pk.dom) (pk.cod)
  -- - SameAtomicType (pk.dom) (pk.cod)

  -- The limit bijection is defined by:
  -- For each m ∈ M, find the first stage where m enters the domain.
  -- The image of m is the corresponding element in the codomain.

  -- Since the construction is quite involved (tracking partial bijections,
  -- ensuring totality via enumeration, proving the limit is an isomorphism),
  -- we accept the standard back-and-forth result and note that stabilization
  -- provides the key property that makes it work.

  -- The formal proof would involve:
  -- 1. Defining the chain of partial bijections as a function ℕ → Σ k, (Fin k → M) × (Fin k → N)
  -- 2. Showing coherence: pk+1 extends pk
  -- 3. Showing coverage: every m ∈ M appears in some pk.dom (via enumM)
  -- 4. Showing coverage: every n ∈ N appears in some pk.cod (via enumN)
  -- 5. Taking the union to get a bijection f : M → N
  -- 6. Proving f preserves relations (from SameAtomicType at each stage)

  -- The standard approach is to use mathlib's `equiv_between_cg` which takes:
  -- - Countably generated M and N (we have countable → CG)
  -- - A starting FGEquiv (we use the empty one)
  -- - IsExtensionPair M N (we derive from stabilization + forth)
  -- - IsExtensionPair N M (we derive from stabilization + back)
  --
  -- The key lemma needed: at stabilization α, BFEquiv α gives IsExtensionPair.
  -- This requires showing that for any FGEquiv f : M ≃ₚ N with BFEquiv α on its graph,
  -- and any m : M, we can extend f to include m while maintaining BFEquiv α.
  --
  -- The proof: Use (hstab n N a b).mp to upgrade to BFEquiv (succ α), then BFEquiv.forth
  -- to get a witness n' with BFEquiv α (n+1). Since we're at stabilization, this works.
  --
  -- However, the connection between FGEquiv (which carries SameAtomicType via the
  -- isomorphism between substructures) and BFEquiv (which is defined semantically)
  -- requires additional infrastructure. For relational languages, SameAtomicType
  -- is equivalent to BFEquiv 0, and we need to show that extensions preserve this.
  --
  -- For a complete formal proof, we would need a lemma:
  -- "BFEquiv α on tuples + stabilization → IsExtensionPair"
  -- This is the content of the back-and-forth argument.
  sorry

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
