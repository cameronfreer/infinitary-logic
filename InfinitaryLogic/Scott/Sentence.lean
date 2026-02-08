/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Scott.Formula
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
    simp only [AtomicIdx.holds]
    constructor
    · intro h; exact congrArg f h
    · intro h; exact f.injective h
  | rel R g =>
    simp only [AtomicIdx.holds]
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

/-- For countable M, there exists α < ω₁ where all tuples stabilize completely:
`BFEquiv α n a b ↔ BFEquiv (succ α) n a b` for ALL countable N and tuples b.

This is a standard result in infinitary model theory (see Marker, "Lectures on
Infinitary Model Theory", or Keisler-Knight §1.3). The key point is that for countable
structures, the BFEquiv refinement chain must stabilize at a countable ordinal.

**Mathematical argument**: For each n-tuple `a` from M, the Scott formula
`scottFormula a α` gets logically stronger as α increases. The set of structures
satisfying it shrinks monotonically. Full stabilization at α means the formulas
`SF a α` and `SF a (succ α)` are logically equivalent (agree on ALL structures),
which is strictly stronger than self-stabilization (agreement on M only).

**Important**: Self-stabilization (`SelfStabilizesCompletely`) does NOT imply full
stabilization (`StabilizesCompletely`). Counterexample: M = {a, b} with an empty
relational language, N = {c} (one element), α = 1. Self-stabilization holds at α = 1
(all M-types are stable), but `BFEquiv 1 0 elim0 elim0_N` holds while
`BFEquiv 2 0 elim0 elim0_N` fails (the forth condition at level 1 detects the
cardinality mismatch). Full stabilization holds at α = 2 for this example.

**Proof strategy** (using `StabilizesForTuples.downward_propagation`):

1. By `downward_propagation`: `StabilizesForTuples M α (n+1) → StabilizesForTuples M (succ α) n`.
   So full stabilization at tuple-size (n+1) implies full stabilization at tuple-size n.

2. For each M-tuple `a`, define `γ(a) = sInf {α | SF a α ⟷ SF a (succ α)}`.
   Once all (n+1)-extensions `(snoc a m)` have stabilized (at ordinals γ(snoc a m)),
   the FORTH/BACK conditions at level `sup_m γ(snoc a m)` become consequences of
   `SF a` (because the inner formulas have stabilized and the existentials are "baked in"
   at the next level). So `γ(a) ≤ succ(sup_m γ(snoc a m))`.

3. The recursion `γ(a) ≤ succ(sup_m γ(snoc a m))` goes to higher tuple sizes.
   Each `γ(snoc a m) < ω₁` implies `γ(a) < ω₁` (by regularity of ω₁ and
   countability of M). The chain of γ-values across all tuple sizes is bounded
   because at each ordinal α, only countably many M-tuples can have γ = α.

**Status**: Sorry — the coinductive argument showing γ(a) < ω₁ for all a
requires careful handling of the proper class of countable structures. The result
is mathematically standard (see Marker, Barwise, or Keisler-Knight). -/
theorem exists_complete_stabilization (M : Type w) [L.Structure M] [Countable M] :
    ∃ α < (Ordinal.omega 1 : Ordinal.{0}), StabilizesCompletely (L := L) M α := by
  -- For each M-tuple a : Fin n → M, define the "instability bound":
  -- the first ordinal past which BFEquiv α n a b → BFEquiv (succ α) n a b for ALL (N, b).
  -- This is sup {α | ∃ (N, b), BFEquiv α n a b ∧ ¬BFEquiv (succ α) n a b} + 1.
  --
  -- Key bound: instabilityBound(a) ≤ succ(sup_m instabilityBound(snoc a m))
  -- (by downward propagation applied per-tuple).
  --
  -- We show instabilityBound(a) < ω₁ for all a by contradiction:
  -- if not, regularity of ω₁ gives an infinite chain of extensions with unbounded
  -- instability, which by the descent property gives an infinite strictly decreasing
  -- sequence of ordinals, contradicting well-foundedness.
  --
  -- Step 1: For each M-tuple, define the per-tuple bound ordinal.
  -- For each (n, a), we need: ∃ γ < ω₁, ∀ α, γ ≤ α → α < ω₁ → succ α < ω₁ →
  --   ∀ (N : Type w) [L.Structure N] [Countable N] (b : Fin n → N),
  --     BFEquiv α n a b ↔ BFEquiv (succ α) n a b
  --
  -- The proof works by showing that for each M-tuple a, the set of "bad" ordinals
  -- (where the iff fails) is bounded below ω₁.
  --
  -- We use the key fact: if BFEquiv α n a b but ¬BFEquiv (succ α) n a b,
  -- then the forth or back condition fails at α. This means:
  -- (1) ∃ m : M such that ∀ n' : N, ¬BFEquiv α (n+1) (snoc a m) (snoc b n'), OR
  -- (2) ∃ n' : N such that ∀ m : M, ¬BFEquiv α (n+1) (snoc a m) (snoc b n').
  -- In case (1): from BFEquiv α n a b (if α = succ δ), BFEquiv.forth at δ gives
  --   a witness n' with BFEquiv δ (n+1) but ¬BFEquiv α (n+1). So δ is "bad" for (snoc a m).
  -- This gives the descent: bad ordinals for a map to bad ordinals for extensions at
  --   strictly smaller ordinals.
  --
  -- We prove the bound for ALL M-tuples simultaneously using well-founded induction.

  -- Step 1: For each sigma type element t = (n, a), extract a bound ordinal < ω₁.
  -- The approach mirrors exists_complete_self_stabilization but for all countable N.
  have hTuple : ∀ (t : Σ n, Fin n → M),
      ∃ γ < (Ordinal.omega 1 : Ordinal.{0}),
        ∀ α, γ ≤ α → α < Ordinal.omega 1 → Order.succ α < Ordinal.omega 1 →
          ∀ (N : Type w) [L.Structure N] [Countable N] (b : Fin t.1 → N),
            (BFEquiv (L := L) α t.1 t.2 b ↔ BFEquiv (L := L) (Order.succ α) t.1 t.2 b) := by
    intro ⟨n, a⟩; simp only
    -- For each (N, b) pair, the function α ↦ BFEquiv α n a b is antitone.
    -- So for each (N, b), either BFEquiv holds at all α < ω₁, or there's a unique
    -- "change point" cp(N,b) where it switches from True to False.
    -- After cp, both sides of the iff are False, so the iff holds.
    -- Before cp, both sides are True, so the iff holds.
    -- The iff fails only at the predecessor of cp.
    --
    -- The set of "bad" ordinals for a = {pred(cp(N,b)) | (N,b), cp exists and < ω₁}.
    -- We need this set to be bounded below ω₁.
    --
    -- Using the descent property: each bad ordinal for a maps to a bad ordinal for
    -- some extension (snoc a m), at a strictly smaller ordinal.
    -- So the set of bad ordinals for a is bounded by the sets of bad ordinals for
    -- all extensions, shifted up by 1.
    --
    -- By well-founded induction on ordinals: the bad ordinals for ALL tuples
    -- form a well-founded tree, so they can't be cofinal in ω₁.
    --
    -- More concretely: if the bad ordinals for a were cofinal in ω₁,
    -- then by regularity of ω₁, some extension (snoc a m) would also have
    -- bad ordinals cofinal in ω₁. Iterating gives an infinite sequence of extensions,
    -- each with cofinal bad ordinals. Picking one bad ordinal from each and using
    -- the descent gives an infinite strictly decreasing sequence of ordinals.

    -- For each (N, b), the function α ↦ BFEquiv α n a b is antitone.
    -- Define the "change ordinal" for (N, b) as sInf {δ | ¬BFEquiv δ n a b}.
    -- If this set is nonempty, the change ordinal is the first level where BFEquiv fails.
    -- Past the change ordinal, both sides of the iff are False, so the iff holds.
    -- The iff fails only at the predecessor of the change ordinal (if it's a successor).
    -- If the change ordinal is a limit, the iff holds everywhere.
    --
    -- Strategy: Use the same change-point argument as self-stabilization.
    -- For each (N, b) pair, at most one ordinal can be "bad" (predecessor of change point).
    -- We DON'T enumerate all (N, b) pairs. Instead, we use the Scott formula to reduce
    -- the problem: the iff BFEquiv α ↔ BFEquiv (succ α) holds for ALL (N, b)
    -- iff scottFormula a α logically implies scottFormula a (succ α).
    -- Using realize_scottFormula_iff_BFEquiv, this is a formula-level property.
    --
    -- The formula scottFormula a (succ α) = scottFormula a α ⊓ FORTH(α) ⊓ BACK(α).
    -- FORTH(α) and BACK(α) reference scottFormula(snoc a m, α) for m ∈ M.
    -- Once all extension formulas have stabilized (same at α and succ α for all models),
    -- FORTH and BACK are constant, and the base formula stabilizes within 1 more step.
    --
    -- The stabilization ordinal for (n, a) is bounded by
    --   sup_m (stabilization ordinal for (n+1, snoc a m)) + 1.
    -- Since M is countable and (Σ k, Fin k → M) is countable, we take the global sup
    -- of all stabilization ordinals. By regularity of ω₁, this sup is < ω₁.
    --
    -- Formally: we prove the bound for all tuples simultaneously by observing that
    -- the global sup Γ satisfies Γ < ω₁ because it's a countable sup and each term
    -- is well-defined (the formula chain scottFormula a α stabilizes because
    -- at limit ordinals, once extensions have stabilized, FORTH/BACK are implied
    -- by the conjunction of earlier levels which already includes them).
    --
    -- For now, we use the self-stabilization ordinal plus the recursive bound.
    -- At self-stabilization α₀: BFEquiv partition on M is fixed.
    -- The formula scottFormula c α₀ is the "final M-type" of c.
    -- Past α₀, the formulas can still change on non-M models, but each successor step
    -- adds conjuncts built from FIXED M-types. The chain of conjuncts stabilizes
    -- because the set of possible conjuncts is determined by M (countable).

    -- Use the same approach as self-stabilization: for each (N, b) pair,
    -- define the change point and show it contributes at most one bad ordinal.
    -- The set of bad ordinals equals {pred(cp) | (N,b) with successor change point}.
    -- This set is bounded by the self-stabilization analysis applied to formulas.

    -- Proof by contradiction using the descent property of bad ordinals.
    -- A "bad ordinal" for (n, a) is an ordinal α where ∃ (N, b) with
    -- BFEquiv α n a b ∧ ¬BFEquiv (succ α) n a b.
    --
    -- Key descent property: from any bad ordinal α for (n, a, N, b), we can
    -- find a strictly smaller bad ordinal for some extension (n+1, snoc a m, N, snoc b n').
    --
    -- If the bad ordinals for (n, a) were unbounded in ω₁, we could build an infinite
    -- strictly decreasing sequence of ordinals, contradicting well-foundedness.
    --
    -- For successor α = succ β: BFEquiv (succ β) n a b gives forth at β, producing
    -- n' with BFEquiv β (n+1). Since BFEquiv (succ(succ β)) fails, FORTH at succ β
    -- fails, meaning BFEquiv (succ β) (n+1) fails for the witness n'. So β is bad
    -- for (n+1, snoc a m, N, snoc b n').
    --
    -- For limit α: BFEquiv α = ∀ γ < α, BFEquiv γ. FORTH at α fails for some m:
    -- ∀ n', ¬BFEquiv α (n+1) (snoc a m) (snoc b n'). For each n', BFEquiv fails
    -- at some γ_n' < α. Since each γ_n' is a change point (successor ordinal),
    -- the predecessor δ_n' < α is bad for the extension. Any such δ_n' < α works.
    --
    -- Formal proof using well-founded descent:
    by_contra h_unbounded
    push_neg at h_unbounded
    -- h_unbounded : ∀ γ < ω₁, ∃ α ≥ γ, α < ω₁ ∧ succ α < ω₁ ∧
    --   ∃ N, ∃ _ : L.Structure N, ∃ _ : Countable N, ∃ b,
    --     ¬(BFEquiv α n a b ↔ BFEquiv (succ α) n a b)
    -- Actually the negation is more complex. Let me restructure.
    -- The claim is: ∃ γ < ω₁, ∀ α ≥ γ, α < ω₁ → succ α < ω₁ →
    --   ∀ N b, BFEquiv α n a b ↔ BFEquiv (succ α) n a b.
    -- Negation: ∀ γ < ω₁, ∃ α ≥ γ, α < ω₁ ∧ succ α < ω₁ ∧
    --   ∃ N b, ¬(BFEquiv α n a b ↔ BFEquiv (succ α) n a b).
    -- Since BFEquiv (succ α) → BFEquiv α (by of_succ), the iff fails only when
    -- BFEquiv α holds but BFEquiv (succ α) doesn't.
    -- So: ∃ N b, BFEquiv α n a b ∧ ¬BFEquiv (succ α) n a b.
    sorry
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
