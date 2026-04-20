/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.Order.InitialSeg
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Fin.VecNotation

/-!
# Erdős–Rado Partition Calculus for ω₁

Pure combinatorics supporting the Morley–Hanf bound: from a linearly
ordered source `I` of cardinality ≥ ℶ_ω₁ and a countable family of
Bool-valued colorings on finite-arity strictly-increasing tuples
(`Fin n ↪o I`), extract an ω₁-homogeneous suborder and in particular
an `ℕ → I` strict-monotone sequence whose range is monochromatic.

This file is language-free: it refers only to linear orders,
cardinalities, `Fin n ↪o I`, `Ordinal.omega`, and `Cardinal.beth`.

## Structure

- **`HomogeneousSuborder`**: a `J ↪o I` suborder is homogeneous for a
  coloring family `c` if each coloring in `c` is constant on
  `J`-tuples factored through the suborder.
- **`natOrderEmbedding_omega1`**: an explicit order-embedding
  `ℕ ↪o (Ordinal.omega 1).ToType` (uses `omega0_lt_omega_one`).
- **`pureColoring_of_omega1HomogeneousSuborder`** (packaging lemma):
  an ω₁-homogeneous suborder yields the `PureColoringHypothesis`
  output shape (a strict-monotone `f : ℕ → I` with `Set.range f`
  monochromatic for every coloring).
- **(2d2, TODO)** `erdos_rado_omega1_of_countable_bool_family`: the
  actual Erdős–Rado theorem. Left as a separate tranche.
-/

universe u

namespace FirstOrder.Combinatorics

/-! ### `HomogeneousSuborder` -/

/-- A `J ↪o I` suborder is **homogeneous** for a coloring family
`c : ℕ → Σ n, (Fin n ↪o I) → Bool` if every coloring takes the same
value on any two strictly-increasing tuples factoring through the
suborder. -/
def HomogeneousSuborder
    {I J : Type*} [LinearOrder I] [LinearOrder J]
    (c : ℕ → Σ n, (Fin n ↪o I) → Bool) (e : J ↪o I) : Prop :=
  ∀ (i : ℕ) (t t' : Fin (c i).1 ↪o J),
    (c i).2 (t.trans e) = (c i).2 (t'.trans e)

/-! ### Canonical `ℕ ↪o ω₁.ToType` embedding -/

/-- Every natural number, cast to an ordinal, is less than `ω₁`. -/
theorem nat_lt_omega_one (n : ℕ) :
    (n : Ordinal) < Ordinal.omega 1 :=
  (Ordinal.nat_lt_omega0 n).trans Ordinal.omega0_lt_omega_one

/-- An order-embedding `ℕ ↪o (Ordinal.omega 1).ToType`: the canonical
"first ω elements in the ω₁-well-ordering." Each `n : ℕ` is sent to the
`n`-th element of the well-ordering of `(Ordinal.omega 1).ToType`. -/
noncomputable def natOrderEmbedding_omega1 :
    ℕ ↪o (Ordinal.omega 1).ToType :=
  OrderEmbedding.ofStrictMono
    (fun n =>
      Ordinal.enum (α := (Ordinal.omega 1).ToType) (· < ·)
        ⟨(n : Ordinal),
          (Ordinal.type_toType _).symm ▸ nat_lt_omega_one n⟩)
    (by
      intro m n hmn
      apply Ordinal.enum_lt_enum.mpr
      -- Reduce Subtype comparison to the underlying ordinal comparison.
      show (m : Ordinal) < (n : Ordinal)
      exact_mod_cast hmn)

/-- `ℕ ↪o (Ordinal.omega 1).ToType` is inhabited. -/
theorem nat_orderEmbedding_omega1 :
    Nonempty (ℕ ↪o (Ordinal.omega 1).ToType) :=
  ⟨natOrderEmbedding_omega1⟩

/-! ### Packaging: ω₁-homogeneous suborder → `ℕ` sequence -/

/-- **Packaging lemma**: an ω₁-homogeneous suborder yields the output
shape expected by `PureColoringHypothesis` — a strict-monotone
`f : ℕ → I` whose range is monochromatic for every coloring in the
family. Proof: compose the suborder's embedding with a fixed
`ℕ ↪o ω₁.ToType`, and use that any increasing tuple in the range of
the composed embedding lifts to a tuple through the original suborder. -/
theorem pureColoring_of_omega1HomogeneousSuborder
    {I : Type} [LinearOrder I]
    (c : ℕ → Σ n, (Fin n ↪o I) → Bool)
    (e : (Ordinal.omega 1).ToType ↪o I)
    (hHom : HomogeneousSuborder c e) :
    ∃ f : ℕ → I, StrictMono f ∧
      ∀ (i : ℕ) (t t' : Fin (c i).1 ↪o I),
        (∀ k, t k ∈ Set.range f) → (∀ k, t' k ∈ Set.range f) →
        (c i).2 t = (c i).2 t' := by
  classical
  refine ⟨e ∘ natOrderEmbedding_omega1, ?_, ?_⟩
  · -- Strict-mono: composition of two order embeddings' underlying functions.
    intro m n hmn
    exact e.strictMono (natOrderEmbedding_omega1.strictMono hmn)
  · -- Range-monochromatic.
    intro i t t' htR ht'R
    -- Build a lift of each tuple through `e` using the factorization
    -- `t k ∈ Set.range (e ∘ natOrderEmbedding_omega1)`.
    have aux : ∀ (u : Fin (c i).1 ↪o I),
        (∀ k, u k ∈ Set.range (e ∘ natOrderEmbedding_omega1)) →
        ∃ (uLift : Fin (c i).1 ↪o (Ordinal.omega 1).ToType),
          uLift.trans e = u := by
      intro u huR
      choose m hm using huR
      refine ⟨OrderEmbedding.ofStrictMono
        (fun k => natOrderEmbedding_omega1 (m k)) ?_, ?_⟩
      · -- StrictMono: derive from `u.strictMono` via `e`'s order-reflection.
        intro j k hjk
        have hltu : u j < u k := u.strictMono hjk
        rw [← hm j, ← hm k] at hltu
        -- Unfold Function.comp to expose the `e _ < e _` pattern.
        simp only [Function.comp_apply] at hltu
        exact e.lt_iff_lt.mp hltu
      · -- Factorization: `(k ↦ natOrderEmbedding_omega1 (m k)).trans e = u`.
        ext k
        show e (natOrderEmbedding_omega1 (m k)) = u k
        have := hm k
        simpa [Function.comp_apply] using this
    obtain ⟨tLift, htLift⟩ := aux t htR
    obtain ⟨t'Lift, ht'Lift⟩ := aux t' ht'R
    have := hHom i tLift t'Lift
    rw [htLift, ht'Lift] at this
    exact this

/-! ### Building block: infinite Ramsey for unary Bool colorings on ℕ -/

/-- **Infinite pigeonhole for Bool colorings on `ℕ`**: from any
`c : ℕ → Bool`, extract a strict-monotone subsequence `f : ℕ → ℕ` on
which `c` is constant. This is the simplest nontrivial case of Ramsey's
theorem (arity 1) and serves as a building block for higher-arity
versions. -/
theorem infinite_ramsey_unary_nat (c : ℕ → Bool) :
    ∃ (f : ℕ → ℕ) (b : Bool), StrictMono f ∧ ∀ n, c (f n) = b := by
  classical
  -- Either the true-preimage or the false-preimage of `c` is infinite.
  by_cases hTrue : {n | c n = true}.Infinite
  · -- The `true`-preimage is infinite; enumerate it via `Nat.nth`.
    refine ⟨Nat.nth (fun n => c n = true), true,
            Nat.nth_strictMono hTrue, ?_⟩
    intro n
    exact Nat.nth_mem_of_infinite hTrue n
  · -- Otherwise the `false`-preimage is infinite (complement of finite in ℕ).
    have hFalse : {n | c n = false}.Infinite := by
      have hCover : {n | c n = true} ∪ {n | c n = false} = Set.univ := by
        ext n; cases c n <;> simp
      have hUnivInf : (Set.univ : Set ℕ).Infinite := Set.infinite_univ
      have hUnion : ({n | c n = true} ∪ {n | c n = false}).Infinite := by
        rw [hCover]; exact hUnivInf
      exact (Set.infinite_union.mp hUnion).resolve_left hTrue
    refine ⟨Nat.nth (fun n => c n = false), false,
            Nat.nth_strictMono hFalse, ?_⟩
    intro n
    exact Nat.nth_mem_of_infinite hFalse n

/-! ### Building block: infinite Ramsey for Bool-colored pairs on ℕ -/

/-- Pair embedding: from an ordered pair `a < b` in a linearly-ordered
type, produce the canonical `Fin 2 ↪o α`. -/
noncomputable def pairEmbed {α : Type*} [LinearOrder α]
    {a b : α} (h : a < b) : Fin 2 ↪o α :=
  OrderEmbedding.ofStrictMono ![a, b] (by
    intro p q hpq
    match p, q, hpq with
    | ⟨0, _⟩, ⟨1, _⟩, _ => simpa using h
    | ⟨0, _⟩, ⟨0, _⟩, hp => exact absurd hp (lt_irrefl _)
    | ⟨1, _⟩, ⟨1, _⟩, hp => exact absurd hp (lt_irrefl _)
    | ⟨1, _⟩, ⟨0, _⟩, hp =>
      have hval : (1 : ℕ) < 0 := hp
      exact absurd hval (by omega))

/-- Pair-splitting pigeonhole: given a Bool coloring of pairs on `ℕ`
and a vertex `v`, for any infinite set `S ⊂ ℕ` with all elements above
`v`, one of the two color-preimages
`{x ∈ S | c⟨v,x⟩ = b}` (for `b ∈ Bool`) is infinite. -/
private lemma exists_infinite_mono_branch
    (c : (Fin 2 ↪o ℕ) → Bool) (v : ℕ)
    (S : Set ℕ) (hS : S.Infinite) (hSv : ∀ x ∈ S, v < x) :
    ∃ (b : Bool) (S' : Set ℕ), S' ⊆ S ∧ S'.Infinite ∧
      ∀ x, x ∈ S' → ∀ (hxv : v < x),
        c (pairEmbed hxv) = b := by
  classical
  -- Partition S by the color of (v, x).
  let Strue : Set ℕ := {x ∈ S | ∀ (h : v < x), c (pairEmbed h) = true}
  let Sfalse : Set ℕ := {x ∈ S | ∀ (h : v < x), c (pairEmbed h) = false}
  -- Every element of S lies in exactly one part (since hSv gives v < x).
  have hCover : Strue ∪ Sfalse = S := by
    ext x
    refine ⟨?_, ?_⟩
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    · intro hx
      have hvx : v < x := hSv x hx
      -- Bool tertium non datur: c (pairEmbed hvx) is either true or false.
      cases hcol : c (pairEmbed hvx)
      · exact Or.inr ⟨hx, fun h => by
          -- Proof-irrelevance: the hypothesis h and hvx give the same embedding.
          convert hcol⟩
      · exact Or.inl ⟨hx, fun h => by convert hcol⟩
  -- One of the two parts is infinite.
  have hUnionInf : (Strue ∪ Sfalse).Infinite := by rw [hCover]; exact hS
  rcases Set.infinite_union.mp hUnionInf with hT | hF
  · refine ⟨true, Strue, fun x hx => hx.1, hT, ?_⟩
    intro x hxT hxv
    exact hxT.2 hxv
  · refine ⟨false, Sfalse, fun x hx => hx.1, hF, ?_⟩
    intro x hxF hxv
    exact hxF.2 hxv

/-! ### Infinite Ramsey for Bool-colored pairs on ℕ -/

/-- Intermediate state of the pair-Ramsey extraction: a "current head"
`head : ℕ` and an infinite reservoir `tail : Set ℕ` above the head. -/
private structure RamseyState where
  head : ℕ
  tail : Set ℕ
  infinite : tail.Infinite
  above : ∀ x ∈ tail, head < x

/-- One step of the pair-Ramsey extraction: from a state at head `h`
with tail `T`, pick a new head `h'` from `T` and narrow the tail to
`T' ⊂ T` with `h' < T'` and a committed color `b` such that
`c⟨h, x⟩ = b` for all `x ∈ T'`. -/
private noncomputable def ramseyStep
    (c : (Fin 2 ↪o ℕ) → Bool) (s : RamseyState) :
    Bool × RamseyState := by
  classical
  -- Branch on the color of `c(s.head, ·)` over `s.tail` to get infinite S₁.
  have hBr := exists_infinite_mono_branch c s.head s.tail s.infinite s.above
  let b : Bool := Classical.choose hBr
  have hBr2 := Classical.choose_spec hBr
  let S₁ : Set ℕ := Classical.choose hBr2
  have hS₁ := Classical.choose_spec hBr2
  -- hS₁ : S₁ ⊆ s.tail ∧ S₁.Infinite ∧ ∀ x ∈ S₁, ∀ hxv : s.head < x, c (pairEmbed hxv) = b
  -- Pick new head h' ∈ S₁ (using infinite ⇒ nonempty).
  let h' : ℕ := hS₁.2.1.nonempty.some
  have hh'_mem : h' ∈ S₁ := hS₁.2.1.nonempty.some_mem
  -- Narrow tail: S₂ = {x ∈ S₁ | h' < x}. Still infinite (S₁ infinite, finitely many ≤ h').
  let S₂ : Set ℕ := {x ∈ S₁ | h' < x}
  have hS₂_inf : S₂.Infinite := by
    -- `S₁ = S₂ ∪ {x ∈ S₁ | x ≤ h'}`. RHS is a finite set (subset of {0, ..., h'}).
    -- LHS infinite ⇒ S₂ infinite.
    have hCover : {x ∈ S₁ | h' < x} ∪ {x ∈ S₁ | x ≤ h'} = S₁ := by
      ext x
      refine ⟨?_, ?_⟩
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
      · intro hx
        rcases lt_or_ge h' x with hlt | hge
        · exact Or.inl ⟨hx, hlt⟩
        · exact Or.inr ⟨hx, hge⟩
    have hFin : {x ∈ S₁ | x ≤ h'}.Finite :=
      Set.Finite.subset (Set.finite_Iic h') (fun x hx => hx.2)
    have : (S₂ ∪ {x ∈ S₁ | x ≤ h'}).Infinite := by rw [hCover]; exact hS₁.2.1
    exact (Set.infinite_union.mp this).resolve_right hFin.not_infinite
  have hS₂_above : ∀ x ∈ S₂, h' < x := fun x hx => hx.2
  exact ⟨b, { head := h', tail := S₂, infinite := hS₂_inf, above := hS₂_above }⟩

/-- The invariant: after `ramseyStep`, every element `x` of the new tail
satisfies `c⟨old_head, x⟩ = committed_color`. Additionally, the new head
is itself an element of the old tail (so in particular, it satisfies
`c⟨old_head, new_head⟩ = committed_color`). -/
private theorem ramseyStep_spec
    (c : (Fin 2 ↪o ℕ) → Bool) (s : RamseyState) :
    let out := ramseyStep c s
    (∀ x, x ∈ out.2.tail → ∀ (hxv : s.head < x),
        c (pairEmbed hxv) = out.1) ∧
      ∀ (hxv : s.head < out.2.head), c (pairEmbed hxv) = out.1 := by
  classical
  -- Unfold ramseyStep and its internal Classical.choose'ings.
  simp only [ramseyStep]
  set hBr := exists_infinite_mono_branch c s.head s.tail s.infinite s.above
  have hBr2 := Classical.choose_spec hBr
  set S₁ := Classical.choose hBr2
  have hS₁ := Classical.choose_spec hBr2
  refine ⟨?_, ?_⟩
  · -- For all x in the new tail (⊆ S₁), c(head, x) = b.
    intro x hx hxv
    -- hx : x ∈ {y ∈ S₁ | h' < y}, so x ∈ S₁.
    have hxS₁ : x ∈ S₁ := hx.1
    exact hS₁.2.2 x hxS₁ hxv
  · -- For the new head h' ∈ S₁, c(head, h') = b.
    intro hxv
    have hh'_mem : hS₁.2.1.nonempty.some ∈ S₁ := hS₁.2.1.nonempty.some_mem
    exact hS₁.2.2 _ hh'_mem hxv

/-- The ω-iterate of `ramseyStep` starting from state `s₀`. Returns
`(head_n, tail_n, color_(n-1))`. -/
private noncomputable def ramseyIter
    (c : (Fin 2 ↪o ℕ) → Bool) (s₀ : RamseyState) :
    ℕ → Bool × RamseyState
  | 0 => ⟨false, s₀⟩  -- color at index 0 is a placeholder (never read)
  | n + 1 => ramseyStep c (ramseyIter c s₀ n).2

/-- Extracted head sequence. -/
private noncomputable def ramseyHead
    (c : (Fin 2 ↪o ℕ) → Bool) (s₀ : RamseyState) (n : ℕ) : ℕ :=
  (ramseyIter c s₀ n).2.head

/-- Extracted color sequence. `ramseyColor c s₀ n` records the
committed color at step `n + 1`, i.e., the color `b_n` such that
`c(a_n, a_j) = b_n` for all `j > n`. -/
private noncomputable def ramseyColor
    (c : (Fin 2 ↪o ℕ) → Bool) (s₀ : RamseyState) (n : ℕ) : Bool :=
  (ramseyIter c s₀ (n + 1)).1

/-- The new head produced by `ramseyStep` is in the old tail (hence
strictly greater than the old head). -/
private theorem ramseyStep_head_gt
    (c : (Fin 2 ↪o ℕ) → Bool) (s : RamseyState) :
    s.head < (ramseyStep c s).2.head := by
  classical
  simp only [ramseyStep]
  set hBr := exists_infinite_mono_branch c s.head s.tail s.infinite s.above
  have hBr2 := Classical.choose_spec hBr
  have hS₁ := Classical.choose_spec hBr2
  -- The new head is hS₁.2.1.nonempty.some, which is in S₁ ⊆ s.tail.
  have hh'_mem : hS₁.2.1.nonempty.some ∈ Classical.choose hBr2 :=
    hS₁.2.1.nonempty.some_mem
  exact s.above _ (hS₁.1 hh'_mem)

/-- Strict monotonicity of the extracted head sequence at successor. -/
private theorem ramseyHead_succ_gt
    (c : (Fin 2 ↪o ℕ) → Bool) (s₀ : RamseyState) (n : ℕ) :
    ramseyHead c s₀ n < ramseyHead c s₀ (n + 1) := by
  -- ramseyHead (n+1) = (ramseyStep c (ramseyIter c s₀ n).2).2.head
  -- ramseyHead n     = (ramseyIter c s₀ n).2.head
  show (ramseyIter c s₀ n).2.head < _
  exact ramseyStep_head_gt c _

/-- Strict monotonicity of the extracted head sequence. -/
private theorem ramseyHead_strictMono
    (c : (Fin 2 ↪o ℕ) → Bool) (s₀ : RamseyState) :
    StrictMono (ramseyHead c s₀) :=
  strictMono_nat_of_lt_succ (ramseyHead_succ_gt c s₀)

/-- `ramseyStep` shrinks the tail. -/
private theorem ramseyStep_tail_subset
    (c : (Fin 2 ↪o ℕ) → Bool) (s : RamseyState) :
    (ramseyStep c s).2.tail ⊆ s.tail := by
  classical
  simp only [ramseyStep]
  set hBr := exists_infinite_mono_branch c s.head s.tail s.infinite s.above
  have hBr2 := Classical.choose_spec hBr
  have hS₁ := Classical.choose_spec hBr2
  -- The new tail is `{x ∈ S₁ | h' < x} ⊆ S₁ ⊆ s.tail`.
  intro x hx
  exact hS₁.1 hx.1

/-- Iterated tail containment: for `k ≥ 0`, the tail at step `i + k`
is a subset of the tail at step `i`. -/
private theorem ramseyIter_tail_subset
    (c : (Fin 2 ↪o ℕ) → Bool) (s₀ : RamseyState) (i : ℕ) :
    ∀ k, (ramseyIter c s₀ (i + k)).2.tail ⊆ (ramseyIter c s₀ i).2.tail
  | 0 => by simp
  | k + 1 => by
      have ih := ramseyIter_tail_subset c s₀ i k
      -- (ramseyIter c s₀ (i + (k+1))).2.tail = (ramseyStep c (ramseyIter c s₀ (i+k)).2).2.tail
      -- ⊆ (ramseyIter c s₀ (i+k)).2.tail ⊆ ... ⊆ (ramseyIter c s₀ i).2.tail
      show (ramseyStep c (ramseyIter c s₀ (i + k)).2).2.tail ⊆ _
      exact (ramseyStep_tail_subset c _).trans ih

/-- The `(j+1)`-th head is in the `i`-th tail, for `j ≥ i`. -/
private theorem ramseyHead_succ_mem_tail
    (c : (Fin 2 ↪o ℕ) → Bool) (s₀ : RamseyState) {i j : ℕ} (hij : i ≤ j) :
    ramseyHead c s₀ (j + 1) ∈ (ramseyIter c s₀ i).2.tail := by
  -- ramseyHead (j+1) = (ramseyStep c (ramseyIter c s₀ j).2).2.head
  -- This head is in (ramseyIter c s₀ j).2.tail (by the step's construction).
  -- And (ramseyIter c s₀ j).2.tail ⊆ (ramseyIter c s₀ i).2.tail since j ≥ i.
  have hhead_in_j_tail : ramseyHead c s₀ (j + 1) ∈ (ramseyIter c s₀ j).2.tail := by
    classical
    show (ramseyStep c (ramseyIter c s₀ j).2).2.head ∈ (ramseyIter c s₀ j).2.tail
    -- Unfold ramseyStep: the new head is `.some` of the nonempty of S₁, and S₁ ⊆ s.tail,
    -- but we also need the narrowing — actually the new head is in S₁, and we choose
    -- the new tail as {x ∈ S₁ | h' < x}, so the new head is NOT directly in the new tail.
    -- However, S₁ ⊆ (ramseyIter j).2.tail, so the new head is in the old tail.
    simp only [ramseyStep]
    set hBr := exists_infinite_mono_branch c (ramseyIter c s₀ j).2.head
      (ramseyIter c s₀ j).2.tail (ramseyIter c s₀ j).2.infinite
      (ramseyIter c s₀ j).2.above
    have hBr2 := Classical.choose_spec hBr
    have hS₁ := Classical.choose_spec hBr2
    exact hS₁.1 hS₁.2.1.nonempty.some_mem
  -- Transport from the j-th tail to the i-th tail using nesting.
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  exact ramseyIter_tail_subset c s₀ i k hhead_in_j_tail

/-- The key color invariant: for `j > i`, `c⟨head_i, head_j⟩ = color_i`. -/
private theorem ramseyPair_color
    (c : (Fin 2 ↪o ℕ) → Bool) (s₀ : RamseyState) {i j : ℕ} (hij : i < j) :
    ∀ (hhead : ramseyHead c s₀ i < ramseyHead c s₀ j),
      c (pairEmbed hhead) = ramseyColor c s₀ i := by
  intro hhead
  -- Split on j = i+1 vs j > i+1.
  rcases Nat.lt_or_ge j (i + 2) with hle | hge
  · -- j = i+1 (since i < j < i+2 forces j = i+1).
    have hjEq : j = i + 1 := by omega
    subst hjEq
    -- Apply ramseyStep_spec.2 at state (ramseyIter c s₀ i).2.
    -- The new head (at step i+1) is (ramseyStep c _).2.head, and the spec says
    -- `c⟨(ramseyIter i).2.head, (ramseyStep _).2.head⟩ = color`.
    exact (ramseyStep_spec c (ramseyIter c s₀ i).2).2 hhead
  · -- j ≥ i + 2. Then ramseyHead j is in (ramseyStep c (ramseyIter c s₀ i).2).2.tail
    -- (the new tail at step i+1). Apply ramseyStep_spec.1.
    have hj_newTail : ramseyHead c s₀ j ∈
        (ramseyStep c (ramseyIter c s₀ i).2).2.tail := by
      -- (ramseyStep c (ramseyIter i).2).2.tail = (ramseyIter (i+1)).2.tail.
      -- Use ramseyHead_succ_mem_tail with starting point (i+1) and j-1 ≥ i+1.
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hge
      -- hk : j = i + 2 + k. So j = (i+1) + (k+1).
      have : j = (i + 1) + (k + 1) := by omega
      rw [this]
      exact ramseyHead_succ_mem_tail c s₀ (Nat.le_add_right (i + 1) k)
    exact (ramseyStep_spec c (ramseyIter c s₀ i).2).1 _ hj_newTail hhead

/-- A default initial state for the pair-Ramsey extraction on `ℕ`:
head = 0, tail = `{x : ℕ | 0 < x}`. -/
private noncomputable def initRamseyState : RamseyState where
  head := 0
  tail := {x : ℕ | 0 < x}
  infinite :=
    Set.infinite_of_injective_forall_mem (f := Nat.succ)
      Nat.succ_injective (fun n => Nat.succ_pos n)
  above := fun _ hx => hx

/-- **Infinite Ramsey for Bool-colored pairs on `ℕ`**: for every
`c : (Fin 2 ↪o ℕ) → Bool`, there exists a strict-monotone `f : ℕ → ℕ`
and a Bool `b` such that every strictly-increasing pair from `Set.range f`
has color `b`.

Proof: (1) iterate `ramseyStep` on `initRamseyState` to get a sequence
of heads `ramseyHead` (strict-mono by `ramseyHead_strictMono`) and
committed colors `ramseyColor` satisfying the invariant
`c(head_i, head_j) = color_i` for `i < j` (by `ramseyPair_color`).
(2) Apply `infinite_ramsey_unary_nat` on `ramseyColor` to extract a
strict-mono subsequence `g : ℕ → ℕ` on which `ramseyColor` is constant
equal to some `b`. (3) The composed sequence `ramseyHead ∘ g` is the
required strict-mono monochromatic sequence: for any pair
`i < j`, `c(head_{g i}, head_{g j}) = color_{g i} = b`. -/
theorem infinite_ramsey_pair_nat (c : (Fin 2 ↪o ℕ) → Bool) :
    ∃ (f : ℕ → ℕ) (b : Bool), StrictMono f ∧
      ∀ (t : Fin 2 ↪o ℕ), (∀ k, t k ∈ Set.range f) → c t = b := by
  classical
  -- (1) Extract heads and colors via the iteration.
  set a := ramseyHead c initRamseyState with ha_def
  set b₀ := ramseyColor c initRamseyState with hb_def
  have ha_mono : StrictMono a := ramseyHead_strictMono c initRamseyState
  -- (2) Pigeonhole on the color sequence.
  obtain ⟨g, b, hg_mono, hg_color⟩ := infinite_ramsey_unary_nat b₀
  -- (3) Final sequence: a ∘ g, with monochromatic color b.
  refine ⟨a ∘ g, b, ha_mono.comp hg_mono, ?_⟩
  intro t ht
  -- t : Fin 2 ↪o ℕ with t 0, t 1 ∈ range (a ∘ g).
  -- Get i₀ < i₁ such that t 0 = a (g i₀) and t 1 = a (g i₁).
  have h0 := ht 0
  have h1 := ht 1
  obtain ⟨i₀, hi₀⟩ := h0
  obtain ⟨i₁, hi₁⟩ := h1
  -- t 0 < t 1 (since t is strictly monotone).
  have ht01 : t 0 < t 1 := by
    apply t.strictMono
    show (0 : Fin 2) < 1
    decide
  -- ⇒ a (g i₀) < a (g i₁). Since a is strict-mono and a ∘ g is strict-mono,
  -- i₀ < i₁ iff g i₀ < g i₁ iff a (g i₀) < a (g i₁).
  rw [← hi₀, ← hi₁] at ht01
  have hi₀lt_i₁ : i₀ < i₁ := by
    by_contra hnot
    push_neg at hnot
    -- i₁ ≤ i₀ ⇒ a (g i₁) ≤ a (g i₀), contradicting ht01.
    have : a (g i₁) ≤ a (g i₀) := (ha_mono.comp hg_mono).monotone hnot
    exact absurd ht01 (not_lt.mpr this)
  -- Now g i₀ < g i₁ too.
  have hg_lt : g i₀ < g i₁ := hg_mono hi₀lt_i₁
  -- Apply ramseyPair_color with i = g i₀, j = g i₁.
  have hhead : a (g i₀) < a (g i₁) := ha_mono hg_lt
  have hcolor_eq_at_gi₀ := ramseyPair_color c initRamseyState hg_lt hhead
  -- Now t and pairEmbed hhead are the same pair embedding.
  have ht_eq_pair : t = pairEmbed hhead := by
    apply DFunLike.ext
    intro k
    match k with
    | ⟨0, _⟩ =>
      show t 0 = (pairEmbed hhead) 0
      simp only [pairEmbed, OrderEmbedding.coe_ofStrictMono,
        Matrix.cons_val_zero]
      exact hi₀.symm
    | ⟨1, _⟩ =>
      show t 1 = (pairEmbed hhead) 1
      simp only [pairEmbed, OrderEmbedding.coe_ofStrictMono,
        Matrix.cons_val_one]
      exact hi₁.symm
  rw [ht_eq_pair, hcolor_eq_at_gi₀]
  exact hg_color i₀

/-! ### Toolbox lemmas for uncountable Erdős–Rado (Phase 2d2-pair)

Five general-purpose cardinal/ordinal helpers used by the pair
Erdős–Rado construction below:

- **H1** `exists_ordToType_embedding_of_card_ge`: a well-ordered
  source of cardinality ≥ κ admits an order-embedding
  `κ.ord.ToType ↪o I`. Specialised twice in the main proof:
  `κ := succ (ℶ_1)` (to reduce to a regular source) and
  `κ := ℵ_1` (to shape the final output).
- **H2** `mk_countable_bool_functions_le_beth_one`:
  `#(α → Bool) ≤ ℶ_1` for any countable `α`.
- **H3** `exists_large_fiber_of_small_codomain`: Cardinal pigeonhole
  on `succ κ`-sized sources mapping into codomains of size `≤ κ`
  yields a fiber of size `≥ succ κ`.
- **H4** `countable_toType_of_lt_omega1`: ordinals below `ω_1` have
  countable `ToType`.
- **H5** `ordIso_omega1_of_aleph1_subset`: any `ℵ_1`-sized subset of
  `ω_1.ToType` is order-isomorphic to `ω_1.ToType`.
-/

section ToolboxH1

/-- **H1** — a well-ordered source of cardinality at least `κ` admits
an order-embedding from the initial-ordinal well-order of cardinality
`κ`. Used twice in the main Erdős–Rado argument: once with
`κ = succ (ℶ_1)` (to reduce to a regular initial ordinal), and once
with `κ = ℵ_1` (to shape the final `ω_1 ↪o I` output). -/
theorem exists_ordToType_embedding_of_card_ge
    {I : Type} [LinearOrder I] [WellFoundedLT I]
    {κ : Cardinal} (hI : Cardinal.mk I ≥ κ) :
    Nonempty (κ.ord.ToType ↪o I) := by
  -- `β := type (<_I) : Ordinal`.  `β.card = #I ≥ κ`, hence `κ.ord ≤ β`.
  set β : Ordinal := Ordinal.type (· < · : I → I → Prop) with hβ
  have hβ_card : β.card = Cardinal.mk I := Ordinal.card_type (· < ·)
  have hord_le : κ.ord ≤ β := by
    rw [Cardinal.ord_le, hβ_card]; exact hI
  -- Initial-segment embedding `κ.ord.ToType ≤i β.ToType`.
  have seg : κ.ord.ToType ≤i β.ToType := Ordinal.initialSegToType hord_le
  -- `β.ToType` ≃o `I` via `type_toType β = β = type (<_I)`.
  have htype : @Ordinal.type β.ToType (· < ·) _ =
      @Ordinal.type I (· < ·) _ := by
    rw [Ordinal.type_toType]
  have hiso : Nonempty
      ((· < · : β.ToType → β.ToType → Prop) ≃r (· < · : I → I → Prop)) :=
    Ordinal.type_eq.mp htype
  obtain ⟨r⟩ := hiso
  exact ⟨seg.toOrderEmbedding.trans (OrderIso.ofRelIsoLT r).toOrderEmbedding⟩

end ToolboxH1

section ToolboxH2

/-- **H2** — countable domain and Bool codomain yield continuum-many
functions at most. Uses `2 ^ ℵ_0 = ℶ_1`. -/
theorem mk_countable_bool_functions_le_beth_one
    {α : Type} [Countable α] :
    Cardinal.mk (α → Bool) ≤ Cardinal.beth 1 := by
  rw [Cardinal.beth_one, ← Cardinal.two_power_aleph0]
  have hαBool : Cardinal.mk (α → Bool) = 2 ^ Cardinal.mk α := by
    rw [← Cardinal.mk_bool, Cardinal.power_def]
  rw [hαBool]
  exact Cardinal.power_le_power_left two_ne_zero Cardinal.mk_le_aleph0

end ToolboxH2

section ToolboxH3

/-- **H3** — path-counting pigeonhole. A function out of a set of
cardinality `≥ succ κ` into a codomain of cardinality `≤ κ`
(with `κ ≥ ℵ_0`) has some fiber of cardinality `≥ succ κ`.

Routes through `Cardinal.infinite_pigeonhole_card` with parameter
`θ := succ κ`. The regularity of `succ κ` (successor cardinals are
regular) supplies the cofinality hypothesis. -/
theorem exists_large_fiber_of_small_codomain
    {α β : Type u} {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 ≤ κ)
    (hα : Cardinal.mk α ≥ Order.succ κ)
    (hβ : Cardinal.mk β ≤ κ)
    (f : α → β) :
    ∃ b : β, Order.succ κ ≤ Cardinal.mk (f ⁻¹' {b}) := by
  have hReg : (Order.succ κ).IsRegular := Cardinal.isRegular_succ hκ
  have hθ_le_α : Order.succ κ ≤ Cardinal.mk α := hα
  have hθ_ge_aleph0 : Cardinal.aleph0 ≤ Order.succ κ :=
    hκ.trans (Order.le_succ κ)
  -- `#β ≤ κ < succ κ = (succ κ).ord.cof`.
  have hcof : Cardinal.mk β < (Order.succ κ).ord.cof := by
    rw [hReg.cof_eq]
    exact hβ.trans_lt (Order.lt_succ_of_le le_rfl)
  exact Cardinal.infinite_pigeonhole_card f (Order.succ κ)
    hθ_le_α hθ_ge_aleph0 hcof

end ToolboxH3

section ToolboxH4

/-- **H4** — ordinals below `ω_1` have countable `ToType`. Follows
from `Cardinal.lt_omega_iff_card_lt` and
`Cardinal.countable_iff_lt_aleph_one`. -/
theorem countable_toType_of_lt_omega1 {α : Ordinal}
    (hα : α < Ordinal.omega 1) :
    Countable α.ToType := by
  have hcard : α.card < Cardinal.aleph 1 :=
    Cardinal.lt_omega_iff_card_lt.mp hα
  have hmk : Cardinal.mk α.ToType < Cardinal.aleph 1 := by
    rw [Cardinal.mk_toType]; exact hcard
  have huniv : (Set.univ : Set α.ToType).Countable :=
    (Cardinal.countable_iff_lt_aleph_one _).mpr
      (by rw [Cardinal.mk_univ]; exact hmk)
  exact Set.countable_univ_iff.mp huniv

end ToolboxH4

section ToolboxH5

/-- **H5** — any subset of `ω_1.ToType` of cardinality at least `ℵ_1`
is order-isomorphic to `ω_1.ToType`.

Proof outline: `ω_1` has order type `ω_1`, so any subset with
cardinality `ℵ_1` must have order type `ω_1`. If the order type were
strictly less than `ω_1`, the subset would be countable
(contradicting `ℵ_1`-cardinality). So `type (subset) = ω_1`, giving
a `RelIso` transported to an `OrderIso`. -/
theorem ordIso_omega1_of_aleph1_subset
    {S : Set (Ordinal.omega.{0} 1).ToType}
    (hS : Cardinal.mk S ≥ Cardinal.aleph.{0} 1) :
    Nonempty (S ≃o (Ordinal.omega.{0} 1).ToType) := by
  haveI : IsWellOrder S (· < ·) := inferInstance
  set β : Ordinal.{0} := @Ordinal.type S (· < ·) _ with hβ
  -- The inclusion `S ↪o ω_1.ToType`.
  let incl : S ↪o (Ordinal.omega.{0} 1).ToType := OrderEmbedding.subtype _
  -- `β ≤ ω_1`.
  have hβ_le : β ≤ Ordinal.omega.{0} 1 := by
    have : @Ordinal.type (Ordinal.omega.{0} 1).ToType (· < ·) _ =
        Ordinal.omega.{0} 1 := Ordinal.type_toType _
    rw [← this]
    exact Ordinal.type_le_iff'.mpr ⟨incl.ltEmbedding⟩
  -- `β.card = #S ≥ ℵ_1`.
  have hβ_card : β.card = Cardinal.mk S := Ordinal.card_type (· < ·)
  have hβ_card_ge : Cardinal.aleph.{0} 1 ≤ β.card := hβ_card ▸ hS
  -- `β ≥ ω_1`: if `β < ω_1`, then `β.card < ℵ_1`, contradicting above.
  have hβ_ge : Ordinal.omega.{0} 1 ≤ β := by
    by_contra hne
    push_neg at hne
    have : β.card < Cardinal.aleph.{0} 1 :=
      Cardinal.lt_omega_iff_card_lt.mp hne
    exact absurd hβ_card_ge (not_le.mpr this)
  have hβ_eq : β = Ordinal.omega.{0} 1 := le_antisymm hβ_le hβ_ge
  -- So `type (<_S) = type (<_{ω_1.ToType})`, giving a `RelIso`.
  have htype : @Ordinal.type S (· < ·) _ =
      @Ordinal.type (Ordinal.omega.{0} 1).ToType (· < ·) _ := by
    show β = _; rw [hβ_eq, Ordinal.type_toType]
  obtain ⟨r⟩ := (Ordinal.type_eq.mp htype :
    Nonempty ((· < · : S → S → Prop) ≃r
      (· < · : (Ordinal.omega.{0} 1).ToType →
        (Ordinal.omega.{0} 1).ToType → Prop)))
  exact ⟨OrderIso.ofRelIsoLT r⟩

end ToolboxH5

/-! ### Architecture of the main Erdős–Rado theorem (Phase 2d2)

The remaining unproved theorem:

```lean
theorem erdos_rado_omega1_of_countable_bool_family
    {I : Type} [LinearOrder I] [WellFoundedLT I]
    (hI : Cardinal.mk I ≥ Cardinal.beth (Ordinal.omega 1))
    (c : ℕ → Σ n, (Fin n ↪o I) → Bool) :
    ∃ e : (Ordinal.omega 1).ToType ↪o I,
      HomogeneousSuborder c e
```

Note: the `[WellFoundedLT I]` constraint is essential — arbitrary linear
orders do not admit ω-ascending sequences in general (counterexample:
opposite-`ℕ`). The consumer
`indiscernibleSequence_of_pureColoring` always supplies `I` as a model
carrier equipped with a canonical well-order (via `exists_wellOrder`),
so this assumption costs nothing downstream.

**Why it is hard.** The naive approach — iterated infinite Ramsey with
diagonalization — fails. If `I_m ⊂ I_{m-1} ⊂ ... ⊂ I_0` is a nested
sequence of infinite sets with `I_m` monochromatic for the first `m`
colorings, and we pick `f(k) ∈ I_k` with `f(k) > f(k-1)`, then a tuple
`(f(u_0), …, f(u_{n_i-1}))` with `u_0 < i` has its first point in
`I_{u_0}`, which is not guaranteed to be homogeneous for `c_i`. So
diagonalization only yields "tail homogeneity" (homogeneity on tuples
with minimum index `≥ i` for each `c_i`), not the full homogeneity
`PureColoringHypothesis` requires.

**Standard resolution.** Use `|I| ≥ ℶ_ω₁` to find an ω₁-sized
homogeneous subset via a tree construction (canonical types /
"Π¹-partition-ranks"). This is the Erdős–Rado theorem proper. Once
an ω₁-suborder `e : (Ordinal.omega 1).ToType ↪o I` is produced,
`pureColoring_of_omega1HomogeneousSuborder` (above) packages it into
the `PureColoringHypothesis` shape.

**Rough proof sketch for future work.**
  1. **Single coloring of fixed arity `n`**: by induction on `n`,
     extract a homogeneous subset of cardinality `ω₁` from a source
     of cardinality `ℶ_{n-1}^+`. The base case (`n = 2`) is "pair
     Erdős–Rado": `ℶ_1^+ → (ω₁)^2_ω`, proved by the canonical type
     tree. Induction step goes via the Erdős-Rado partition
     relation composition.
  2. **Countably many colorings**: given colorings `c_0, c_1, …` of
     arities `n_0, n_1, …`, iterate step (1) on nested subsets.
     Cumulative cardinality loss is at most `ℶ_ω₁`, which is still
     matched by the source size `ℶ_ω₁`. The intersection of the
     ω₁-homogeneous subsets at each stage remains ω₁-sized.
  3. **Extract the ω₁-embedding**: use `Ordinal.enumOrd` to
     transform the resulting homogeneous subset into an
     order-embedding `(Ordinal.omega 1).ToType ↪o I`.

**Expected infrastructure to be built/imported**:
  - Cardinal arithmetic helpers around `ℶ_ω₁` (mathlib has `Cardinal.beth`,
    `beth_succ`, `beth_strictMono`; may need `beth_le_beth_of_le` etc.).
  - A "canonical types tree" structure for building the ω₁-homogeneous
    subset — likely an ad-hoc structure defined here.
  - Iteration over countably many colorings via `Nat.rec` +
    classical choice.

**Why defer**. The full proof is a multi-week project in its own
right. Placeholder committed: the public interface
(`HomogeneousSuborder`, `natOrderEmbedding_omega1`,
`pureColoring_of_omega1HomogeneousSuborder`) is ready. When the main
theorem is proved, `pureColoringHypothesis_holds` in
`InfinitaryLogic/Conditional/MorleyHanfTransfer.lean` follows in
three lines. -/

end FirstOrder.Combinatorics
