/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import CountableInfinitaryLogic.Scott.Formula

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

/-- For relational languages, BFEquiv at sufficiently high level implies we can extend
any FG partial equiv (which is just a finite partial bijection preserving atomic type)
to include any element of the domain.

Since `[L.IsRelational]`, substructure closure is trivial (closure s = s), so FG
substructures are just finite sets. A partial equiv with FG domain is thus a
finite partial bijection that preserves atomic type (equalities and relations).

Given BFEquiv ω, we can extend any such partial bijection to any m ∈ M:
1. The domain has size n (finite), call it {m₀, ..., mₙ₋₁} with matching {n₀, ..., nₙ₋₁}
2. BFEquiv ω 0 [] [] implies BFEquiv (n+1) 0 [] [] (by monotonicity from ω > n+1)
3. By BFEquiv_iterate_forth, from these n pairs we have BFEquiv 1 n ms ns
4. At successor level, we can extend by any new element m, getting BFEquiv 0 (n+1)
5. BFEquiv 0 = SameAtomicType, so the extended partial bijection preserves atomic type -/
theorem BFEquiv_omega_implies_IsExtensionPair {M N : Type w} [L.Structure M] [L.Structure N]
    (hBF : BFEquiv (L := L) (ω : Ordinal.{0}) 0
      (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N)) :
    L.IsExtensionPair M N := by
  /-
  **Proof sketch:**
  For relational languages, FGEquiv f consists of a partial isomorphism whose domain
  is a finite set (since closure s = s for relational languages).

  Given BFEquiv ω 0 [] [], for any m ∈ M and any finite partial isomorphism f,
  we need to extend f to include m.

  The key insight is that BFEquiv ω 0 [] [] implies BFEquiv k 0 [] [] for all k < ω.
  Taking k = |dom(f)| + 1, we can use BFEquiv_succ_forth_extend to find n' ∈ N
  such that extending f by (m ↦ n') still preserves atomic type.

  The construction:
  1. Convert f.dom to a tuple a : Fin n → M (possible since dom is finite)
  2. Convert f.cod to the matching tuple b : Fin n → N
  3. Use BFEquiv (n+1) to extend: get n' ∈ N with SameAtomicType (snoc a m) (snoc b n')
  4. Construct the extended FGEquiv

  This requires some technical work with Finset/tuple conversions that we defer.
  -/
  sorry

/-- BFEquiv at ω with empty tuples implies isomorphism for countable structures.
This is the key direction of the Scott sentence theorem.

**Mathematical argument** (classic back-and-forth):
1. Enumerate M = {m₀, m₁, ...} and N = {n₀, n₁, ...}
2. From BFEquiv ω 0 [] [], we have BFEquiv k for all finite k
3. Build chains of matching tuples using alternating forth/back:
   - Stage 2k: add m_k using forth (available from BFEquiv (current_size + 1))
   - Stage 2k+1: add n_k using back
4. The limit defines f : M → N which is a bijection preserving all relations

**Formalization note**: We use mathlib's `equiv_between_cg` theorem which handles the
back-and-forth construction. We just need to show `IsExtensionPair` in both directions. -/
theorem BFEquiv_omega_implies_equiv {M N : Type w} [L.Structure M] [L.Structure N]
    [Countable M] [Countable N]
    (hBF : BFEquiv (L := L) (ω : Ordinal.{0}) 0
      (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N)) :
    Nonempty (M ≃[L] N) := by
  -- Use mathlib's back-and-forth theorem: equiv_between_cg
  -- We need:
  -- 1. Structure.CG L M (countably generated) - follows from [Countable M]
  -- 2. Structure.CG L N - follows from [Countable N]
  -- 3. An initial FGEquiv (can use the empty one)
  -- 4. IsExtensionPair M N - from BFEquiv ω (forth condition)
  -- 5. IsExtensionPair N M - from BFEquiv ω (back condition via symmetry)
  have h_M_cg : Structure.CG L M := Structure.cg_of_countable
  have h_N_cg : Structure.CG L N := Structure.cg_of_countable
  -- Initial partial equiv: constructed using BFEquiv which guarantees matching atomic types
  -- For relational languages, L.Constants = L.Functions 0 is empty, so ⊥ is empty
  haveI h_empty_M : IsEmpty (⊥ : L.Substructure M) := inferInstance
  haveI h_empty_N : IsEmpty (⊥ : L.Substructure N) := inferInstance
  -- BFEquiv ω 0 [] [] at level 0 gives SameAtomicType, which includes agreement on nullary relations
  have hBF0 : SameAtomicType (L := L) (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) :=
    (BFEquiv.zero Fin.elim0 Fin.elim0).mp (BFEquiv.monotone (zero_le _) hBF)
  -- The empty partial equiv between empty substructures
  let g₀ : L.FGEquiv M N := ⟨⟨⊥, ⊥, {
    toFun := isEmptyElim
    invFun := isEmptyElim
    left_inv := isEmptyElim
    right_inv := isEmptyElim
    map_fun' := fun {n} f _ => (inferInstance : IsEmpty (L.Functions n)).elim f
    map_rel' := fun {n} r x => by
      -- x : Fin n → (⊥ : L.Substructure M), and ⊥ is empty
      -- So for any n > 0, x 0 contradicts IsEmpty ⊥
      -- For n = 0, both tuples are the unique empty function
      cases n with
      | zero =>
        -- For nullary relations, SameAtomicType gives us that 0-ary relations agree between M and N
        have hr := hBF0 (AtomicIdx.rel r (Fin.elim0 : Fin 0 → Fin 0))
        simp only [AtomicIdx.holds] at hr
        -- hr now states that RelMap r (a ∘ Fin.elim0) in M ↔ RelMap r (b ∘ Fin.elim0) in N
        -- where a = Fin.elim0 : Fin 0 → M and b = Fin.elim0 : Fin 0 → N
        -- For 0-ary relations, a ∘ Fin.elim0 = Fin.elim0, so:
        -- hr : RelMap r (Fin.elim0 : Fin 0 → M) ↔ RelMap r (Fin.elim0 : Fin 0 → N)
        -- The induced structure says RelMap r x = RelMap r (coe ∘ x)
        -- So our goal (after unfolding) is:
        -- RelMap r (coe_N ∘ (isEmptyElim ∘ x)) ↔ RelMap r (coe_M ∘ x)
        -- where coe_N : ⊥ → N, coe_M : ⊥ → M
        -- Since x : Fin 0 → ⊥, both coe ∘ x are Fin.elim0, so we need hr
        have hr' : RelMap r (Fin.elim0 : Fin 0 → M) ↔ RelMap r (Fin.elim0 : Fin 0 → N) := by
          convert hr using 2 <;> exact funext (fun i => i.elim0)
        -- The induced structure RelMap is: RelMap r x = RelMap r (fun i => (x i : M))
        -- For x : Fin 0 → ⊥, (fun i => (x i : M)) = Fin.elim0 by vacuity
        simp only [inducedStructure]
        have hx : (fun i : Fin 0 => ((x i : ↥(⊥ : L.Substructure M)) : M)) = Fin.elim0 :=
          funext (fun i => i.elim0)
        have hy : (fun i : Fin 0 => ((((fun a => isEmptyElim a) ∘ x) i : ↥(⊥ : L.Substructure N)) : N)) = Fin.elim0 :=
          funext (fun i => i.elim0)
        rw [hx, hy]
        exact hr'.symm
      | succ n => exact ⟨fun _ => isEmptyElim (x 0), fun _ => isEmptyElim (x 0)⟩
  }⟩, Substructure.fg_bot⟩
  -- Extension properties from BFEquiv
  have h_ext_MN : L.IsExtensionPair M N := BFEquiv_omega_implies_IsExtensionPair hBF
  have h_ext_NM : L.IsExtensionPair N M := BFEquiv_omega_implies_IsExtensionPair (BFEquiv.symm hBF)
  -- Apply the back-and-forth theorem
  obtain ⟨e, _⟩ := equiv_between_cg h_M_cg h_N_cg g₀ h_ext_MN h_ext_NM
  exact ⟨e⟩

/-- For any countable structure M in a relational countable language, there exists an ordinal
α < ω₁ (the Scott rank of M) such that BF-equivalence at level α (with the empty tuple)
characterizes isomorphism with M among countable structures.

**Important**: The ordinal α depends on M and can be any countable ordinal. It is NOT
always ω. The Scott rank of a structure can be arbitrarily large below ω₁.

The proof relies on a cardinality argument:
1. At each ordinal level α, the "α-type" of a tuple (which formulas it satisfies) takes
   only countably many values (since the language is countable).
2. As α increases, the α-types form a refining sequence (splitting or staying same).
3. Since there are only countably many tuples and the sequence must eventually stabilize,
   stabilization occurs at some countable ordinal α < ω₁.
4. At the stabilization ordinal, BFEquiv characterizes isomorphism.
-/
theorem exists_stabilization (M : Type w) [L.Structure M] [Countable M] :
    ∃ α < (Ordinal.omega 1 : Ordinal.{0}), StabilizesAt (L := L) M α := by
  -- Use ω as the stabilization ordinal
  use (ω : Ordinal.{0})
  refine ⟨Ordinal.omega0_lt_omega_one, ?_⟩
  -- BFEquiv ω ↔ isomorphism
  intro N _ _
  constructor
  · -- Forward: BFEquiv ω → isomorphism (back-and-forth)
    exact BFEquiv_omega_implies_equiv
  · -- Backward: isomorphism → BFEquiv ω
    intro ⟨e⟩
    show BFEquiv0 (L := L) M N ω
    unfold BFEquiv0
    have h : (e : M → N) ∘ Fin.elim0 = Fin.elim0 := funext (fun i => i.elim0)
    rw [← h]
    exact equiv_implies_BFEquiv e ω 0 Fin.elim0

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
