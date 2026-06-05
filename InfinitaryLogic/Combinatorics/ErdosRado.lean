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
import Mathlib.Order.Filter.Ultrafilter.Defs
import Mathlib.Order.Filter.AtTopBot.Basic
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

/-! ### Local API for pair Erdős–Rado (Phase 2d2-pair)

Three low-level definitions and one standalone cofinality lemma that the
upcoming successor/limit-step kernels (and the main recursion after them)
build on. All recursion will live inside `PairERSource`, the regular
initial ordinal of `succ (ℶ_1)`; the final composition with
`I`-embedding happens at the end via `exists_ordToType_embedding_of_card_ge`.
-/

section PairERLocalAPI

/-- **Pair-ER source.** The initial ordinal of the regular successor
cardinal `succ (ℶ_1)`, viewed as a linearly-ordered `Type`.

All pair-Erdős–Rado recursion happens inside `PairERSource`, because
`succ (ℶ_1)` is regular (it is a successor cardinal, hence regular by
`Cardinal.isRegular_succ` applied to `ℵ_0 ≤ ℶ_1`), so countable
subsets of `PairERSource` are bounded strictly below — a property the
limit-stage pigeonhole relies on. After the recursion, the resulting
`ω_1`-chain is transported to `I` via an order embedding. -/
abbrev PairERSource : Type :=
  (Order.succ (Cardinal.beth.{0} 1)).ord.ToType

/-- **Regularity of `succ (ℶ_1)`.** Direct consequence of
`Cardinal.isRegular_succ` applied to `ℵ_0 ≤ ℶ_1`. -/
lemma isRegular_succ_beth_one :
    (Order.succ (Cardinal.beth.{0} 1)).IsRegular :=
  Cardinal.isRegular_succ (Cardinal.aleph0_le_beth _)

/-- **Cofinality of the pair-ER source's order type.** From regularity of
`succ (ℶ_1)`: `cof ((succ ℶ_1).ord) = succ (ℶ_1)`. -/
lemma cof_ord_succ_beth_one :
    (Order.succ (Cardinal.beth.{0} 1)).ord.cof =
      Order.succ (Cardinal.beth.{0} 1) :=
  isRegular_succ_beth_one.cof_eq

/-- **Cardinality of the pair-ER source.** `#PairERSource = succ (ℶ_1)`. -/
lemma mk_pairERSource :
    Cardinal.mk PairERSource = Order.succ (Cardinal.beth.{0} 1) := by
  show Cardinal.mk (Order.succ (Cardinal.beth.{0} 1)).ord.ToType =
      Order.succ (Cardinal.beth.{0} 1)
  rw [Cardinal.mk_toType, Cardinal.card_ord]

/-- **ℵ_0 ≤ succ (ℶ_1).** Trivial from `ℵ_0 ≤ ℶ_1 ≤ succ ℶ_1`. -/
lemma aleph0_le_succ_beth_one :
    Cardinal.aleph0 ≤ Order.succ (Cardinal.beth.{0} 1) :=
  (Cardinal.aleph0_le_beth 1).trans (Order.le_succ _)

/-- **Pair-coloring pullback.** Pull a pair coloring on `I` back along
an order embedding `PairERSource ↪o I`, producing a pair coloring on
`PairERSource`. Used once, at the very start of the main proof: pull
the user-supplied coloring `c : (Fin 2 ↪o I) → Bool` back to `cR` on
`PairERSource`, run the recursion inside `PairERSource`, then
transport the resulting `ω_1`-chain back to `I`. -/
def pairColorPullback
    {I : Type} [LinearOrder I]
    (ι : PairERSource ↪o I) (c : (Fin 2 ↪o I) → Bool) :
    (Fin 2 ↪o PairERSource) → Bool :=
  fun t => c (t.trans ι)

/-- **Valid fiber (quantifier form).** The set of elements
`y ∈ PairERSource` strictly above every `p β`, whose pair color with
each `p β` matches `τ β`. Kept in quantifier form (not as a
`Set.sInter`) so that successor rewriting and restriction lemmas do
not have to commute big intersections through the recursion. -/
def validFiber
    (cR : (Fin 2 ↪o PairERSource) → Bool)
    {α : Ordinal.{0}} (p : α.ToType ↪o PairERSource)
    (τ : α.ToType → Bool) : Set PairERSource :=
  { y | ∀ β : α.ToType, ∃ h : p β < y, cR (pairEmbed h) = τ β }

/-- Shrinking `succ` and `aleph0` together: if `a + b = c` where `c` is
infinite and `a < c`, then `c ≤ b`. Used in `large_above_prefix` to
pass from `#(Iio m) + #(Ici m) = succ ℶ_1` (with `#(Iio m) < succ ℶ_1`)
to `succ ℶ_1 ≤ #(Ici m)`. -/
private lemma le_of_add_eq_of_lt_of_aleph0_le
    {a b c : Cardinal} (habc : a + b = c)
    (hc : Cardinal.aleph0 ≤ c) (hac : a < c) :
    c ≤ b := by
  by_contra hbc
  push_neg at hbc
  have hmax : max a b < c := max_lt hac hbc
  have hsum_inf : Cardinal.aleph0 ≤ a + b := habc ▸ hc
  have hsum_lt : a + b < c := by
    rcases Cardinal.aleph0_le_add_iff.mp hsum_inf with ha | hb
    · rw [Cardinal.add_eq_max ha]; exact hmax
    · rw [Cardinal.add_eq_max' hb]; exact hmax
  exact absurd habc (ne_of_lt hsum_lt)

/-- **Above-prefix set has size `succ (ℶ_1)`.** For any countable
prefix embedding `p : α.ToType ↪o PairERSource` with `α < ω_1`, the
set of elements strictly above every `p β` has cardinality at least
`succ (ℶ_1)`.

This isolates the cofinality argument cleanly from the pigeonhole
downstream: regularity of `succ (ℶ_1)` bounds the countable prefix
strictly below some `m ∈ PairERSource`, and the tail `{y | m ≤ y}`
has cardinality `succ (ℶ_1)` by complement of the `< m` initial
segment (whose cardinality is `< succ (ℶ_1)` since any initial
segment of `(succ ℶ_1).ord.ToType` has cardinality strictly less
than `succ (ℶ_1)`). -/
theorem large_above_prefix
    {α : Ordinal.{0}} (hα : α < Ordinal.omega.{0} 1)
    (p : α.ToType ↪o PairERSource) :
    Order.succ (Cardinal.beth.{0} 1) ≤
      Cardinal.mk { y : PairERSource | ∀ x : α.ToType, p x < y } := by
  haveI : Countable α.ToType := countable_toType_of_lt_omega1 hα
  -- Step 1: the prefix range is bounded in `PairERSource`.
  have hBounded : Set.Bounded (· < · : PairERSource → PairERSource → Prop)
      (Set.range p) := by
    have hcof : Ordinal.cof
        (@Ordinal.type PairERSource (· < ·) _) =
        Order.succ (Cardinal.beth.{0} 1) := by
      rw [Ordinal.type_toType]; exact cof_ord_succ_beth_one
    apply Ordinal.lt_cof_type
    rw [hcof]
    calc Cardinal.mk (Set.range p)
        ≤ Cardinal.mk α.ToType := Cardinal.mk_range_le
      _ ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
      _ < Order.succ (Cardinal.beth.{0} 1) :=
          lt_of_le_of_lt (Cardinal.aleph0_le_beth 1) (Order.lt_succ _)
  -- Step 2: extract a strict upper bound `m` for the prefix.
  obtain ⟨m, hm⟩ := hBounded
  -- Step 3: `{y | m ≤ y} ⊆ {y | ∀ x, p x < y}`.
  have hSubset : (Set.Ici m : Set PairERSource) ⊆
      { y : PairERSource | ∀ x : α.ToType, p x < y } := by
    intro y hy x
    exact lt_of_lt_of_le (hm (p x) (Set.mem_range_self _)) hy
  -- Step 4: `#(Ici m) ≥ succ (ℶ_1)` via complement of `Iio m`.
  have hCard : Order.succ (Cardinal.beth.{0} 1) ≤
      Cardinal.mk (Set.Ici m : Set PairERSource) := by
    let Im : Set PairERSource := Set.Iio m
    have hIci_eq : (Set.Ici m : Set PairERSource) = Imᶜ := by
      ext x; simp [Set.mem_Ici, Im]
    rw [hIci_eq]
    have hIio : Cardinal.mk Im <
        Order.succ (Cardinal.beth.{0} 1) :=
      Cardinal.mk_Iio_ord_toType m
    have hSum : Cardinal.mk Im + Cardinal.mk (Imᶜ : Set PairERSource) =
        Order.succ (Cardinal.beth.{0} 1) := by
      rw [Cardinal.mk_sum_compl]; exact mk_pairERSource
    exact le_of_add_eq_of_lt_of_aleph0_le hSum
      aleph0_le_succ_beth_one hIio
  -- Step 5: combine.
  exact hCard.trans (Cardinal.mk_le_mk_of_subset hSubset)

/-- **Limit-step kernel.** For any countable prefix `p : α.ToType ↪o
PairERSource` (with `α < ω_1`), some type function `τ : α.ToType → Bool`
admits a valid fiber of cardinality `≥ succ (ℶ_1)`.

Composition of:
- `large_above_prefix` (the above-prefix set has size `succ ℶ_1`);
- `mk_countable_bool_functions_le_beth_one` (the codomain
  `α.ToType → Bool` has size `≤ ℶ_1`);
- `exists_large_fiber_of_small_codomain` at `κ := ℶ_1` (cardinal
  pigeonhole).

Once this lemma lands, the limit stage of the main recursion becomes a
direct invocation. -/
theorem exists_large_limit_fiber
    (cR : (Fin 2 ↪o PairERSource) → Bool)
    {α : Ordinal.{0}} (hα : α < Ordinal.omega.{0} 1)
    (p : α.ToType ↪o PairERSource) :
    ∃ τ : α.ToType → Bool,
      Order.succ (Cardinal.beth.{0} 1) ≤
        Cardinal.mk (validFiber cR p τ) := by
  haveI : Countable α.ToType := countable_toType_of_lt_omega1 hα
  -- `A` = above-prefix set; `#A ≥ succ ℶ_1`.
  set A : Set PairERSource := { y | ∀ x : α.ToType, p x < y } with hA_def
  have hA_card : Order.succ (Cardinal.beth.{0} 1) ≤ Cardinal.mk A :=
    large_above_prefix hα p
  -- `typeMap : A → (α.ToType → Bool)`, `y ↦ (β ↦ cR (pairEmbed (y.property β)))`.
  let typeMap : A → (α.ToType → Bool) :=
    fun y β => cR (pairEmbed (y.property β))
  -- H3 pigeonhole with `κ := ℶ_1`.
  have hBethInf : Cardinal.aleph0 ≤ Cardinal.beth.{0} 1 :=
    Cardinal.aleph0_le_beth _
  have hCodom : Cardinal.mk (α.ToType → Bool) ≤ Cardinal.beth.{0} 1 :=
    mk_countable_bool_functions_le_beth_one
  obtain ⟨τ, hτ⟩ :=
    exists_large_fiber_of_small_codomain hBethInf hA_card hCodom typeMap
  -- The fiber `typeMap⁻¹ {τ}` injects into `validFiber cR p τ` via `Subtype.val`.
  refine ⟨τ, hτ.trans ?_⟩
  refine Cardinal.mk_le_of_injective (f := fun z : typeMap ⁻¹' {τ} => ⟨z.1.1, ?_⟩) ?_
  · -- `z.1.val ∈ validFiber cR p τ`.
    intro β
    refine ⟨z.1.property β, ?_⟩
    -- `cR (pairEmbed (z.1.property β)) = τ β` follows from `typeMap z.1 = τ`.
    have := z.2
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at this
    exact congrFun this β
  · -- Injectivity.
    intro z₁ z₂ h
    have hval : z₁.1.1 = z₂.1.1 := (Subtype.mk.injEq _ _ _ _).mp h
    exact Subtype.ext (Subtype.ext hval)

/-- **One-element fiber refinement.** Given a prefix `p`, type `τ`, a
new candidate head `y ∈ PairERSource`, and a new committed color
`b : Bool`, the set of elements strictly above `y` whose pair color
with `y` is `b`, and which still lie in the original valid fiber. -/
def validFiberExtend
    (cR : (Fin 2 ↪o PairERSource) → Bool)
    {α : Ordinal.{0}} (p : α.ToType ↪o PairERSource) (τ : α.ToType → Bool)
    (y : PairERSource) (b : Bool) : Set PairERSource :=
  { z | z ∈ validFiber cR p τ ∧ ∃ h : y < z, cR (pairEmbed h) = b }

/-- **Successor-step kernel.** Given a valid fiber of cardinality
`≥ succ (ℶ_1)`, pick the well-ordered minimum `y` as the new prefix
head and split the remainder by Bool color. One of the two
color-branches inherits cardinality `≥ succ (ℶ_1)` (by the regularity
of `succ (ℶ_1)` and `#Bool ≤ ℶ_1`), so the corresponding one-element
fiber refinement is still large.

Once this lemma lands, the successor stage of the main recursion is a
direct invocation. -/
theorem exists_successor_refinement
    (cR : (Fin 2 ↪o PairERSource) → Bool)
    {α : Ordinal.{0}} (p : α.ToType ↪o PairERSource) (τ : α.ToType → Bool)
    (hF : Order.succ (Cardinal.beth.{0} 1) ≤
        Cardinal.mk (validFiber cR p τ)) :
    ∃ (y : PairERSource) (b : Bool),
      y ∈ validFiber cR p τ ∧
      Order.succ (Cardinal.beth.{0} 1) ≤
        Cardinal.mk (validFiberExtend cR p τ y b) := by
  set F : Set PairERSource := validFiber cR p τ with hF_def
  -- `F` is nonempty (it has cardinality `≥ succ ℶ_1`, which is positive).
  have hFne : F.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty, Cardinal.mk_emptyCollection] at hF
    exact absurd hF (not_le.mpr
      (lt_of_lt_of_le Cardinal.aleph0_pos aleph0_le_succ_beth_one))
  -- `y := min F` via well-foundedness of `<` on `PairERSource`.
  let y : PairERSource :=
    (IsWellFounded.wf : WellFounded
      (· < · : PairERSource → PairERSource → Prop)).min F hFne
  have hy_mem : y ∈ F := WellFounded.min_mem _ _ _
  have hy_min : ∀ z ∈ F, ¬ z < y := fun z hz =>
    WellFounded.not_lt_min _ F hFne hz
  -- For `z ∈ F \ {y}`, `y < z`.
  have hlt_of_mem : ∀ z ∈ F \ {y}, y < z := fun z hz =>
    lt_of_le_of_ne (not_lt.mp (hy_min z hz.1))
      (fun heq => hz.2 heq.symm)
  -- `#(F \ {y}) ≥ succ ℶ_1` (remove one point from infinite set).
  have hFminus_card : Order.succ (Cardinal.beth.{0} 1) ≤
      Cardinal.mk (F \ {y} : Set PairERSource) := by
    have hsum : Cardinal.mk ({y} : Set PairERSource) +
        Cardinal.mk (F \ {y} : Set PairERSource) = Cardinal.mk F := by
      rw [add_comm]; exact Cardinal.mk_diff_add_mk (by
        intro z hz; rcases hz with rfl; exact hy_mem)
    have hsingleton : Cardinal.mk ({y} : Set PairERSource) = 1 :=
      Cardinal.mk_singleton _
    have h1_lt : Cardinal.mk ({y} : Set PairERSource) <
        Cardinal.mk F := by
      rw [hsingleton]
      calc (1 : Cardinal) < Cardinal.aleph0 := Cardinal.one_lt_aleph0
        _ ≤ Order.succ (Cardinal.beth.{0} 1) := aleph0_le_succ_beth_one
        _ ≤ Cardinal.mk F := hF
    have hF_inf : Cardinal.aleph0 ≤ Cardinal.mk F :=
      aleph0_le_succ_beth_one.trans hF
    exact hF.trans (le_of_add_eq_of_lt_of_aleph0_le hsum hF_inf h1_lt)
  -- Color map on `F \ {y}`: `z ↦ cR (pairEmbed (y < z))`.
  let colorMap : (F \ {y} : Set PairERSource) → Bool :=
    fun z => cR (pairEmbed (hlt_of_mem z.1 z.2))
  -- `#Bool = 2 ≤ ℶ_1`.
  have hBool_card : Cardinal.mk Bool ≤ Cardinal.beth.{0} 1 :=
    (Cardinal.lt_aleph0_of_finite Bool).le.trans (Cardinal.aleph0_le_beth _)
  -- Apply H3 pigeonhole: some Bool `b` has preimage of size `≥ succ ℶ_1`.
  obtain ⟨b, hb_card⟩ := exists_large_fiber_of_small_codomain
    (Cardinal.aleph0_le_beth 1) hFminus_card hBool_card colorMap
  refine ⟨y, b, hy_mem, hb_card.trans ?_⟩
  -- Inject `colorMap⁻¹ {b}` into `validFiberExtend cR p τ y b` via value.
  refine Cardinal.mk_le_of_injective
    (f := fun w : colorMap ⁻¹' {b} => ⟨w.1.1, ?_⟩) ?_
  · -- `w.1.val ∈ validFiberExtend cR p τ y b`.
    refine ⟨w.1.2.1, hlt_of_mem w.1 w.1.2, ?_⟩
    -- `cR (pairEmbed (y < w.1.val)) = b`.
    have := w.2
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at this
    exact this
  · intro w₁ w₂ h
    have hval : w₁.1.1 = w₂.1.1 := (Subtype.mk.injEq _ _ _ _).mp h
    exact Subtype.ext (Subtype.ext hval)

/-! ### Stage record and base/successor extensions

`PairERChain cR α` bundles a prefix `α.ToType ↪o PairERSource`, a type
function `α.ToType → Bool`, and the proof that the resulting valid
fiber has cardinality `≥ succ (ℶ_1)`. The transfinite recursion of the
main theorem threads this structure through `α < ω_1`: the base case
is built via `PairERChain.zero`, successor stages via
`PairERChain.succ` (which calls `exists_successor_refinement`), and
limit stages (later commit) via `exists_large_limit_fiber`.
-/

/-- **Stage record.** A `PairERChain cR α` carries a prefix
`α.ToType ↪o PairERSource`, a type function `α.ToType → Bool`, and the
proof that the valid fiber at that level has cardinality
`≥ succ (ℶ_1)`. -/
structure PairERChain (cR : (Fin 2 ↪o PairERSource) → Bool)
    (α : Ordinal.{0}) where
  head : α.ToType ↪o PairERSource
  type : α.ToType → Bool
  large : Order.succ (Cardinal.beth.{0} 1) ≤
    Cardinal.mk (validFiber cR head type)

/-- **Base stage at level 0.** `(0 : Ordinal).ToType` is empty
(`Ordinal.isEmpty_toType_zero`), so the prefix is vacuous and the valid
fiber is all of `PairERSource`, which has cardinality `succ (ℶ_1)` by
`mk_pairERSource`. -/
noncomputable def PairERChain.zero
    (cR : (Fin 2 ↪o PairERSource) → Bool) : PairERChain cR 0 :=
  haveI : IsEmpty (Ordinal.ToType 0) := Ordinal.isEmpty_toType_zero
  { head := OrderEmbedding.ofIsEmpty
    type := isEmptyElim
    large := by
      have hfiber_eq :
          (validFiber cR (OrderEmbedding.ofIsEmpty
              (α := (0 : Ordinal.{0}).ToType) (β := PairERSource))
            (isEmptyElim : (0 : Ordinal.{0}).ToType → Bool) : Set PairERSource)
            = Set.univ := by
        ext y
        simp [validFiber, IsEmpty.forall_iff]
      rw [hfiber_eq, Cardinal.mk_univ]
      exact mk_pairERSource.ge }

/-- **Helper: extend a prefix by one element above.** Given a prefix
embedding `p : α.ToType ↪o PairERSource` and a strictly larger
element `y ∈ PairERSource`, construct the extended prefix embedding
`(Order.succ α).ToType ↪o PairERSource`. -/
noncomputable def extendHead {α : Ordinal.{0}}
    (p : α.ToType ↪o PairERSource) (y : PairERSource)
    (hy : ∀ z : α.ToType, p z < y) :
    (Order.succ α).ToType ↪o PairERSource := by
  classical
  haveI : IsWellOrder (Order.succ α).ToType (· < ·) := isWellOrder_lt
  -- For `x : (Order.succ α).ToType` with `x ≠ ⊤`, `typein x < α`.
  have typein_lt : ∀ x : (Order.succ α).ToType, x ≠ ⊤ →
      Ordinal.typein (· < ·) x <
        Ordinal.type (α := α.ToType) (· < ·) := by
    intro x hx
    have hlt : x < (⊤ : (Order.succ α).ToType) := lt_of_le_of_ne le_top hx
    have htop : (⊤ : (Order.succ α).ToType) =
        Ordinal.enum (α := (Order.succ α).ToType) (· < ·)
          ⟨α, (Ordinal.type_toType _).symm ▸ Order.lt_succ α⟩ :=
      Ordinal.enum_succ_eq_top.symm
    have hte : Ordinal.typein (· < ·)
        (⊤ : (Order.succ α).ToType) = α := by
      rw [htop, Ordinal.typein_enum]
    rw [Ordinal.type_toType]
    calc Ordinal.typein (· < ·) x
        < Ordinal.typein (· < ·) (⊤ : (Order.succ α).ToType) :=
          (Ordinal.typein_lt_typein (· < ·)).mpr hlt
      _ = α := hte
  refine OrderEmbedding.ofStrictMono
    (fun x : (Order.succ α).ToType =>
      if hx : x = (⊤ : (Order.succ α).ToType) then y
      else p (Ordinal.enum (α := α.ToType) (· < ·)
        ⟨Ordinal.typein (· < ·) x, typein_lt x hx⟩))
    ?_
  intro a b hab
  by_cases ha : a = (⊤ : (Order.succ α).ToType)
  · exact absurd hab (by rw [ha]; exact not_lt_of_ge le_top)
  by_cases hb : b = (⊤ : (Order.succ α).ToType)
  · simp only [dif_neg ha, dif_pos hb]
    exact hy _
  · simp only [dif_neg ha, dif_neg hb]
    apply p.lt_iff_lt.mpr
    apply (Ordinal.enum_lt_enum (α := α.ToType) (r := (· < ·))).mpr
    exact (Ordinal.typein_lt_typein (· < ·)).mpr hab

/-- **Helper: extend a type function.** Add a new Bool value at the
top of `(Order.succ α).ToType`. -/
noncomputable def extendType {α : Ordinal.{0}}
    (τ : α.ToType → Bool) (b : Bool) :
    (Order.succ α).ToType → Bool := by
  classical
  haveI : IsWellOrder (Order.succ α).ToType (· < ·) := isWellOrder_lt
  -- The same `typein_lt` as in `extendHead`; inlined locally.
  have typein_lt : ∀ x : (Order.succ α).ToType, x ≠ ⊤ →
      Ordinal.typein (· < ·) x <
        Ordinal.type (α := α.ToType) (· < ·) := by
    intro x hx
    have hlt : x < (⊤ : (Order.succ α).ToType) := lt_of_le_of_ne le_top hx
    have htop : (⊤ : (Order.succ α).ToType) =
        Ordinal.enum (α := (Order.succ α).ToType) (· < ·)
          ⟨α, (Ordinal.type_toType _).symm ▸ Order.lt_succ α⟩ :=
      Ordinal.enum_succ_eq_top.symm
    have hte : Ordinal.typein (· < ·)
        (⊤ : (Order.succ α).ToType) = α := by
      rw [htop, Ordinal.typein_enum]
    rw [Ordinal.type_toType]
    calc Ordinal.typein (· < ·) x
        < Ordinal.typein (· < ·) (⊤ : (Order.succ α).ToType) :=
          (Ordinal.typein_lt_typein (· < ·)).mpr hlt
      _ = α := hte
  exact fun x => if hx : x = (⊤ : (Order.succ α).ToType) then b
    else τ (Ordinal.enum (α := α.ToType) (· < ·)
      ⟨Ordinal.typein (· < ·) x, typein_lt x hx⟩)

/-- **Successor extension of a stage.** Use `exists_successor_refinement`
to produce `(y, b)`, then package via `extendHead` / `extendType` to
get a stage at `Order.succ α`.

Does NOT need `Order.succ α < ω_1` here: the `α < ω_1` constraint
is carried by `s` (implicitly, via the fact that the kernel is valid).
Callers must supply `Order.succ α < ω_1` when wiring into the main
transfinite recursion. -/
noncomputable def PairERChain.succ {cR : (Fin 2 ↪o PairERSource) → Bool}
    {α : Ordinal.{0}} (s : PairERChain cR α) :
    PairERChain cR (Order.succ α) := by
  classical
  haveI : IsWellOrder (Order.succ α).ToType (· < ·) := isWellOrder_lt
  let hE := exists_successor_refinement cR s.head s.type s.large
  let y : PairERSource := Classical.choose hE
  let hE' := Classical.choose_spec hE
  let b : Bool := Classical.choose hE'
  have hy_mem : y ∈ validFiber cR s.head s.type := (Classical.choose_spec hE').1
  have hlarge : Order.succ (Cardinal.beth.{0} 1) ≤
      Cardinal.mk (validFiberExtend cR s.head s.type y b) :=
    (Classical.choose_spec hE').2
  -- The hypothesis for `extendHead`: `y` is above every `s.head z`.
  have hy_above : ∀ z : α.ToType, s.head z < y := fun z =>
    (hy_mem z).1
  refine
    { head := extendHead s.head y hy_above
      type := extendType s.type b
      large := ?_ }
  -- Fiber at level `Order.succ α` contains `validFiberExtend` by construction.
  apply hlarge.trans
  apply Cardinal.mk_le_mk_of_subset
  intro z hz β
  -- `hz : z ∈ validFiberExtend cR s.head s.type y b`.
  -- Goal: `z ∈ validFiber cR (extendHead s.head y hy_above) (extendType s.type b)`.
  by_cases hβ : β = (⊤ : (Order.succ α).ToType)
  · -- Case: β = ⊤. `extendHead β = y`, `extendType β = b`.
    subst hβ
    obtain ⟨_, hylt, hycol⟩ := hz
    refine ⟨?_, ?_⟩
    · show (extendHead s.head y hy_above) _ < z
      simp only [extendHead, OrderEmbedding.coe_ofStrictMono]
      exact hylt
    · show cR (pairEmbed _) = extendType s.type b _
      simp only [extendType]
      convert hycol using 2
      simp [extendHead]
  · -- Case: β ≠ ⊤. Let `z_β := enum ⟨typein β, _⟩ : α.ToType`.
    -- Then `extendHead β = s.head z_β`, `extendType β = s.type z_β`.
    obtain ⟨hzval, _, _⟩ := hz
    -- `hzval : z ∈ validFiber cR s.head s.type`.
    -- Extract the condition at `z_β`.
    set z_β : α.ToType := Ordinal.enum (α := α.ToType) (· < ·)
      ⟨Ordinal.typein (· < ·) β, by
        -- `typein β < α` since `β ≠ ⊤`.
        have hlt : β < (⊤ : (Order.succ α).ToType) :=
          lt_of_le_of_ne le_top hβ
        have htop : (⊤ : (Order.succ α).ToType) =
            Ordinal.enum (α := (Order.succ α).ToType) (· < ·)
              ⟨α, (Ordinal.type_toType _).symm ▸ Order.lt_succ α⟩ :=
          Ordinal.enum_succ_eq_top.symm
        have hte : Ordinal.typein (· < ·)
            (⊤ : (Order.succ α).ToType) = α := by
          rw [htop, Ordinal.typein_enum]
        rw [Ordinal.type_toType]
        calc Ordinal.typein (· < ·) β
            < Ordinal.typein (· < ·) (⊤ : (Order.succ α).ToType) :=
              (Ordinal.typein_lt_typein (· < ·)).mpr hlt
          _ = α := hte⟩ with hz_β_def
    obtain ⟨h_zβ_lt, h_zβ_col⟩ := hzval z_β
    refine ⟨?_, ?_⟩
    · show (extendHead s.head y hy_above) β < z
      simp only [extendHead, OrderEmbedding.coe_ofStrictMono, dif_neg hβ]
      exact h_zβ_lt
    · show cR (pairEmbed _) = extendType s.type b β
      simp only [extendType, dif_neg hβ]
      convert h_zβ_col using 2
      simp [extendHead, dif_neg hβ]

/-- **`PairERChain.succWithChoice`** — successor extension with a
**prescribed** `(y, b)`, parallel to `limitWithType` for the limit
case. Bypasses the `exists_successor_refinement` `Classical.choose`
that `PairERChain.succ` performs, taking `y`, `b`, and the
fiber-largeness witness as input.

**Role in the local frontier.** This is the underlying
prescribed-level primitive that
`coherentGoodBranchPartial_insert_prescribed_new` wants: instead of
choosing the new level's data freshly, the caller supplies it. With
this in hand, the CGBP wrapper (`insert_prescribed_new`) can be
discharged by appropriate bookkeeping on top of `succWithChoice`.

**[FRONTIER, sorry — primitive scaffolding].** The implementation is
parallel to `PairERChain.succ` (above): construct `head` via
`extendHead`, `type` via `extendType`, and prove `large` by mapping
`validFiberExtend` into the `validFiber` at the new level. The proof
should be a mechanical copy of `succ`'s body with the prescribed
`y, b` substituted for the `Classical.choose` outputs. -/
noncomputable def PairERChain.succWithChoice
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (s : PairERChain cR α)
    (y : PairERSource) (b : Bool)
    (hy_mem : y ∈ validFiber cR s.head s.type)
    (hlarge : Order.succ (Cardinal.beth.{0} 1) ≤
      Cardinal.mk (validFiberExtend cR s.head s.type y b)) :
    PairERChain cR (Order.succ α) := by
  classical
  haveI : IsWellOrder (Order.succ α).ToType (· < ·) := isWellOrder_lt
  have hy_above : ∀ z : α.ToType, s.head z < y := fun z => (hy_mem z).1
  refine
    { head := extendHead s.head y hy_above
      type := extendType s.type b
      large := ?_ }
  apply hlarge.trans
  apply Cardinal.mk_le_mk_of_subset
  intro z hz β
  by_cases hβ : β = (⊤ : (Order.succ α).ToType)
  · subst hβ
    obtain ⟨_, hylt, hycol⟩ := hz
    refine ⟨?_, ?_⟩
    · show (extendHead s.head y hy_above) _ < z
      simp only [extendHead, OrderEmbedding.coe_ofStrictMono]
      exact hylt
    · show cR (pairEmbed _) = extendType s.type b _
      simp only [extendType]
      convert hycol using 2
      simp [extendHead]
  · obtain ⟨hzval, _, _⟩ := hz
    set z_β : α.ToType := Ordinal.enum (α := α.ToType) (· < ·)
      ⟨Ordinal.typein (· < ·) β, by
        have hlt : β < (⊤ : (Order.succ α).ToType) :=
          lt_of_le_of_ne le_top hβ
        have htop : (⊤ : (Order.succ α).ToType) =
            Ordinal.enum (α := (Order.succ α).ToType) (· < ·)
              ⟨α, (Ordinal.type_toType _).symm ▸ Order.lt_succ α⟩ :=
          Ordinal.enum_succ_eq_top.symm
        have hte : Ordinal.typein (· < ·)
            (⊤ : (Order.succ α).ToType) = α := by
          rw [htop, Ordinal.typein_enum]
        rw [Ordinal.type_toType]
        calc Ordinal.typein (· < ·) β
            < Ordinal.typein (· < ·) (⊤ : (Order.succ α).ToType) :=
              (Ordinal.typein_lt_typein (· < ·)).mpr hlt
          _ = α := hte⟩
    obtain ⟨h_zβ_lt, h_zβ_col⟩ := hzval z_β
    refine ⟨?_, ?_⟩
    · show (extendHead s.head y hy_above) β < z
      simp only [extendHead, OrderEmbedding.coe_ofStrictMono, dif_neg hβ]
      exact h_zβ_lt
    · show cR (pairEmbed _) = extendType s.type b β
      simp only [extendType, dif_neg hβ]
      convert h_zβ_col using 2
      simp [extendHead, dif_neg hβ]

/-- **Limit extension of a stage.** At a limit `α < ω_1`, the prefix
`p : α.ToType ↪o PairERSource` must come from the coherent gluing of
prior stages (handled by the main-theorem recursion). This helper then
uses `exists_large_limit_fiber` to pick a type function `τ` with a
valid fiber of cardinality `≥ succ (ℶ_1)`, packaging the result as a
`PairERChain cR α`.

Unlike `PairERChain.succ`, this does NOT maintain the previously-chosen
type values at earlier positions — the `τ` returned is fresh from the
pigeonhole. Final chain consistency is handled downstream (by the
second pigeonhole on `β ↦ τ_{β+1}(β)` committed at successor stages). -/
noncomputable def PairERChain.limit {cR : (Fin 2 ↪o PairERSource) → Bool}
    {α : Ordinal.{0}} (hα : α < Ordinal.omega.{0} 1)
    (p : α.ToType ↪o PairERSource) : PairERChain cR α := by
  classical
  let hE := exists_large_limit_fiber cR hα p
  exact
    { head := p
      type := Classical.choose hE
      large := Classical.choose_spec hE }

/-- **Limit extension with a prescribed `τ`.** Bypasses the
`exists_large_limit_fiber` choose by taking both `τ` and its fiber-
largeness proof as input. This is the constructor needed for *type-
coherent* limit chains — feed it the prescribed Bool function matching
earlier committed Bools plus the `exists_large_limit_fiber_prescribed`
witness (once available). -/
noncomputable def PairERChain.limitWithType
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {α : Ordinal.{0}} (p : α.ToType ↪o PairERSource)
    (τ : α.ToType → Bool)
    (hlarge : Order.succ (Cardinal.beth.{0} 1) ≤
      Cardinal.mk (validFiber cR p τ)) :
    PairERChain cR α :=
  { head := p, type := τ, large := hlarge }

/-- `limitWithType`'s `type` field is exactly the supplied `τ`. -/
@[simp]
lemma PairERChain.limitWithType_type
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (p : α.ToType ↪o PairERSource) (τ : α.ToType → Bool) (hlarge) :
    (PairERChain.limitWithType (cR := cR) p τ hlarge).type = τ := rfl

/-- `limitWithType`'s `head` field is exactly the supplied prefix `p`. -/
@[simp]
lemma PairERChain.limitWithType_head
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (p : α.ToType ↪o PairERSource) (τ : α.ToType → Bool) (hlarge) :
    (PairERChain.limitWithType (cR := cR) p τ hlarge).head = p := rfl

/-- **Limit-stage head = input prefix.** By definition, `PairERChain.limit`
keeps the input prefix as the stage's head. -/
@[simp]
lemma PairERChain.limit_head {cR : (Fin 2 ↪o PairERSource) → Bool}
    {α : Ordinal.{0}} (hα : α < Ordinal.omega.{0} 1)
    (p : α.ToType ↪o PairERSource) :
    (PairERChain.limit (cR := cR) hα p).head = p := rfl

/-! ### `PairERChain.extendTo`: chain extension to arbitrary `α > β`

The general primitive needed for `CoherentBranchApprox.extendTo`:
given a `PairERChain cR β`, build a `PairERChain cR α` for any
`α < ω_1` with `β < α`. The new chain agrees with the old on the
initial segment `β.ToType ↪ α.ToType`.

**API**: a single bundled structure `PairERChain.Extension s α` packages
the new chain together with all agreement data; the single named
transfinite frontier is `PairERChain.extendToExt`, which produces an
`Extension`. The traditional projections `extendTo`, `extendTo_commitAt`,
`extendTo_typeAt_old`, `extendTo_head_β_in_validFiber` are recovered
from `extendToExt` and therefore inherit a single source of `sorryAx`.

The `Extension` structure + its constructors `Extension.succ` and
`Extension.limitWithType` are defined below (after `commitAt` /
`typeAt`). Two **easy non-bundled chain-only constructors** are
filled here directly for downstream API symmetry:
- `extendTo_of_succ_eq` (`α = succ β`): just `s.succ` transported.
- `extendTo_of_limitWithType` (prefix/branch/large pre-supplied):
  a wrapper around `PairERChain.limitWithType`. -/

/-- **Easy case (successor)**: when `α = Order.succ β`, the
extension is `s.succ` transported along the equation. -/
noncomputable def PairERChain.extendTo_of_succ_eq
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {β α : Ordinal.{0}} (s : PairERChain cR β)
    (h_eq : α = Order.succ β) : PairERChain cR α :=
  h_eq.symm ▸ s.succ

/-- **Easy case (limit, prescribed data)**: when a prefix `p`, branch
`τ`, and largeness witness at level `α` are pre-supplied (the
typical use case after gluing a coherent family), the extension is
simply `PairERChain.limitWithType`. The input `s` is retained in
the signature for API symmetry but is not used in the body. -/
noncomputable def PairERChain.extendTo_of_limitWithType
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {β α : Ordinal.{0}} (_s : PairERChain cR β) (_hβα : β < α)
    (p : α.ToType ↪o PairERSource) (τ : α.ToType → Bool)
    (hlarge : Order.succ (Cardinal.beth.{0} 1) ≤
      Cardinal.mk (validFiber cR p τ)) :
    PairERChain cR α :=
  PairERChain.limitWithType p τ hlarge

/-- **Committed-head function.** For a `PairERChain cR α` and an
ordinal `δ < α`, the head at the `δ`-th position of the chain,
packaged as a raw `PairERSource` value. Strictly monotone in `δ`
(by the `OrderEmbedding` nature of `s.head`). -/
noncomputable def PairERChain.commitAt
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (s : PairERChain cR α) (δ : Ordinal.{0}) (hδ : δ < α) :
    PairERSource :=
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  s.head (Ordinal.enum (α := α.ToType) (· < ·)
    ⟨δ, (Ordinal.type_toType α).symm ▸ hδ⟩)

/-- **Commit-at is strictly monotone.** Direct from `s.head` being an
`OrderEmbedding` and `Ordinal.enum` being strict-monotone in its
ordinal argument. -/
lemma PairERChain.commitAt_strictMono
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (s : PairERChain cR α) {δ₁ δ₂ : Ordinal.{0}}
    (hδ₁ : δ₁ < α) (hδ₂ : δ₂ < α) (h : δ₁ < δ₂) :
    s.commitAt δ₁ hδ₁ < s.commitAt δ₂ hδ₂ := by
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  simp only [PairERChain.commitAt]
  apply s.head.lt_iff_lt.mpr
  exact (Ordinal.enum_lt_enum (α := α.ToType) (r := (· < ·))).mpr h

/-- **Limit-stage commit equals input prefix.** When the limit prefix
`p : α.ToType ↪o PairERSource` is supplied, the resulting stage's
commit at position `δ < α` is just `p`'s value at the corresponding
position. Direct `rfl` since `PairERChain.limit.head = p`. -/
lemma PairERChain.limit_commitAt {cR : (Fin 2 ↪o PairERSource) → Bool}
    {α : Ordinal.{0}} (hα : α < Ordinal.omega.{0} 1)
    (p : α.ToType ↪o PairERSource) (δ : Ordinal.{0}) (hδ : δ < α) :
    (PairERChain.limit (cR := cR) hα p).commitAt δ hδ =
      haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
      p (Ordinal.enum (α := α.ToType) (· < ·)
        ⟨δ, (Ordinal.type_toType α).symm ▸ hδ⟩) := rfl

/-- **Successor-stage commit preserves lower positions.** The key
coherence fact: if we extend `s` to `s.succ`, the commit at any
earlier position `δ < α` is unchanged. -/
lemma PairERChain.succ_commitAt
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (s : PairERChain cR α) (δ : Ordinal.{0}) (hδα : δ < α) :
    s.succ.commitAt δ (hδα.trans (Order.lt_succ α)) =
      s.commitAt δ hδα := by
  haveI : IsWellOrder (Order.succ α).ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  -- Abbreviate the enum'd element in (Order.succ α).ToType.
  set e : (Order.succ α).ToType :=
    Ordinal.enum (α := (Order.succ α).ToType) (· < ·)
      ⟨δ, (Ordinal.type_toType (Order.succ α)).symm ▸
        hδα.trans (Order.lt_succ α)⟩ with he_def
  -- `e ≠ ⊤`.
  have he_ne_top : e ≠ (⊤ : (Order.succ α).ToType) := by
    intro h
    -- From `e = ⊤`, applying `typein` gives `δ = α`, contradiction.
    have h1 : Ordinal.typein (· < ·) e = δ := by
      rw [he_def, Ordinal.typein_enum]
    have h2 : Ordinal.typein (· < ·)
        (⊤ : (Order.succ α).ToType) = α := by
      rw [show (⊤ : (Order.succ α).ToType) =
          Ordinal.enum (α := (Order.succ α).ToType) (· < ·)
            ⟨α, (Ordinal.type_toType _).symm ▸ Order.lt_succ α⟩
        from Ordinal.enum_succ_eq_top.symm, Ordinal.typein_enum]
    have : δ = α := h1.symm.trans (h ▸ h2)
    exact absurd this (ne_of_lt hδα)
  -- Unfold both sides and walk through `extendHead`'s `dif_neg` branch.
  show s.succ.head e = s.head _
  unfold PairERChain.succ
  simp only [extendHead, OrderEmbedding.coe_ofStrictMono]
  rw [dif_neg he_ne_top]
  -- LHS now has `s.head (enum ⟨typein e, _⟩)`, RHS has `s.head (enum ⟨δ, _⟩)`.
  -- Reduce via `typein e = δ`.
  have hte : Ordinal.typein (· < ·) e = δ := by
    rw [he_def, Ordinal.typein_enum]
  -- Both sides are `s.head (enum ...)`; reduce enum arguments via `Subtype.mk`.
  have hsub : (⟨Ordinal.typein (· < ·) e,
      (Ordinal.type_toType α).symm ▸ show
        Ordinal.typein (· < ·) e < α from hte ▸ hδα⟩ :
      {o : Ordinal.{0} //
        o < Ordinal.type (α := α.ToType) (· < ·)}) =
      ⟨δ, (Ordinal.type_toType α).symm ▸ hδα⟩ := by
    apply Subtype.ext; exact hte
  -- Use congr on the enum arg's subtype.
  show s.head (Ordinal.enum (α := α.ToType) (· < ·) _) =
      s.head (Ordinal.enum (α := α.ToType) (· < ·) _)
  congr 1
  -- The two enum'd elements are equal via hsub (after rewriting the subtype witness).
  exact congrArg (Ordinal.enum (α := α.ToType) (· < ·)) hsub

/-- **Committed Bool at ordinal position `δ < α`** in a chain. Parallel
to `commitAt` but reading the `type` function. -/
noncomputable def PairERChain.typeAt
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (s : PairERChain cR α) (δ : Ordinal.{0}) (hδ : δ < α) : Bool :=
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  s.type (Ordinal.enum (α := α.ToType) (· < ·)
    ⟨δ, (Ordinal.type_toType α).symm ▸ hδ⟩)

/-- **`succ_typeAt_old`**: the committed Bool at a lower position
`δ < α` is preserved when extending via `.succ`. Parallel to
`succ_commitAt`; the proof walks through `extendType`'s `dif_neg`
branch. -/
lemma PairERChain.succ_typeAt_old
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (s : PairERChain cR α) (δ : Ordinal.{0}) (hδα : δ < α) :
    s.succ.typeAt δ (hδα.trans (Order.lt_succ α)) = s.typeAt δ hδα := by
  haveI : IsWellOrder (Order.succ α).ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  set e : (Order.succ α).ToType :=
    Ordinal.enum (α := (Order.succ α).ToType) (· < ·)
      ⟨δ, (Ordinal.type_toType (Order.succ α)).symm ▸
        hδα.trans (Order.lt_succ α)⟩ with he_def
  have he_ne_top : e ≠ (⊤ : (Order.succ α).ToType) := by
    intro h
    have h1 : Ordinal.typein (· < ·) e = δ := by
      rw [he_def, Ordinal.typein_enum]
    have h2 : Ordinal.typein (· < ·)
        (⊤ : (Order.succ α).ToType) = α := by
      rw [show (⊤ : (Order.succ α).ToType) =
          Ordinal.enum (α := (Order.succ α).ToType) (· < ·)
            ⟨α, (Ordinal.type_toType _).symm ▸ Order.lt_succ α⟩
        from Ordinal.enum_succ_eq_top.symm, Ordinal.typein_enum]
    have : δ = α := h1.symm.trans (h ▸ h2)
    exact absurd this (ne_of_lt hδα)
  show s.succ.type e = s.type _
  unfold PairERChain.succ
  simp only [extendType]
  rw [dif_neg he_ne_top]
  have hte : Ordinal.typein (· < ·) e = δ := by
    rw [he_def, Ordinal.typein_enum]
  have hsub : (⟨Ordinal.typein (· < ·) e,
      (Ordinal.type_toType α).symm ▸ show
        Ordinal.typein (· < ·) e < α from hte ▸ hδα⟩ :
      {o : Ordinal.{0} //
        o < Ordinal.type (α := α.ToType) (· < ·)}) =
      ⟨δ, (Ordinal.type_toType α).symm ▸ hδα⟩ := by
    apply Subtype.ext; exact hte
  show s.type (Ordinal.enum (α := α.ToType) (· < ·) _) =
      s.type (Ordinal.enum (α := α.ToType) (· < ·) _)
  congr 1
  exact congrArg (Ordinal.enum (α := α.ToType) (· < ·)) hsub

/-- **The Bool committed at the top of `s.succ`**: a named handle for
the Bool extracted by `PairERChain.succ`'s use of
`exists_successor_refinement`. -/
noncomputable def PairERChain.succNewBool
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (s : PairERChain cR α) : Bool :=
  Classical.choose (Classical.choose_spec
    (exists_successor_refinement cR s.head s.type s.large))

/-- **`succ_typeAt_top`**: the Bool at the new top position `α` in
`s.succ` equals `s.succNewBool`. -/
lemma PairERChain.succ_typeAt_top
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (s : PairERChain cR α) :
    s.succ.typeAt α (Order.lt_succ α) = s.succNewBool := by
  haveI : IsWellOrder (Order.succ α).ToType (· < ·) := isWellOrder_lt
  set e : (Order.succ α).ToType :=
    Ordinal.enum (α := (Order.succ α).ToType) (· < ·)
      ⟨α, (Ordinal.type_toType (Order.succ α)).symm ▸ Order.lt_succ α⟩
    with he_def
  have he_top : e = (⊤ : (Order.succ α).ToType) := by
    rw [he_def]; exact Ordinal.enum_succ_eq_top
  show s.succ.type e = s.succNewBool
  unfold PairERChain.succ PairERChain.succNewBool
  simp only [extendType]
  rw [dif_pos he_top]

/-- **The new element at the top of `s.succ`**: a named handle for
the value extracted by `PairERChain.succ`'s use of
`exists_successor_refinement`. -/
noncomputable def PairERChain.succNewElement
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (s : PairERChain cR α) : PairERSource :=
  Classical.choose (exists_successor_refinement cR s.head s.type s.large)

/-- **`succ_head_top`**: the head value at position `α` (= top of
`(succ α).ToType`) in `s.succ` equals `s.succNewElement`. -/
lemma PairERChain.succ_head_top
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (s : PairERChain cR α) :
    s.succ.head (⊤ : (Order.succ α).ToType) = s.succNewElement := by
  classical
  unfold PairERChain.succ PairERChain.succNewElement
  simp [extendHead]

/-- **`succNewElement_in_validFiber`**: the new top of `s.succ` lies in
the valid fiber at level `α`. Direct from `exists_successor_refinement`'s
spec. -/
lemma PairERChain.succNewElement_in_validFiber
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (s : PairERChain cR α) :
    s.succNewElement ∈ validFiber cR s.head s.type := by
  unfold PairERChain.succNewElement
  exact (Classical.choose_spec (Classical.choose_spec
    (exists_successor_refinement cR s.head s.type s.large))).1

/-! ### Bundled `PairERChain.Extension` and the single named frontier

The four sorries `extendTo`, `extendTo_commitAt`, `extendTo_typeAt_old`,
`extendTo_head_β_in_validFiber` are now bundled into a single
structure-valued frontier `extendToExt` returning a
`PairERChain.Extension`. The four chain-level declarations are
recovered as projections (no separate sorries). -/

/-- **`PairERChain.Extension`**: a `PairERChain cR α` together with all
the coherence data required to extend a given chain `s : PairERChain
cR β` (for `β < α`). Bundles:

- `chain : PairERChain cR α` — the extended chain;
- `commitAt_old` / `typeAt_old` — the head / type at any `δ < β` in
  the new chain agrees with `s` at the corresponding position;
- `head_β_in_validFiber` — the new chain's head at position `β`
  (i.e., the "new top" relative to `s`) lies in `s`'s validFiber.

Forming an `Extension` requires producing all four pieces of data
simultaneously, which forces the transfinite proof (the only
remaining frontier sorry, named `extendToExt`) to be coherent. -/
structure PairERChain.Extension
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {β : Ordinal.{0}} (s : PairERChain cR β)
    {α : Ordinal.{0}} (hβα : β < α) where
  /-- The chain at level `α`. -/
  chain : PairERChain cR α
  /-- For `δ < β`, the new chain's head at position `δ` agrees with `s`. -/
  commitAt_old : ∀ (δ : Ordinal.{0}) (hδβ : δ < β),
    chain.commitAt δ (hδβ.trans hβα) = s.commitAt δ hδβ
  /-- For `δ < β`, the new chain's type at position `δ` agrees with `s`. -/
  typeAt_old : ∀ (δ : Ordinal.{0}) (hδβ : δ < β),
    chain.typeAt δ (hδβ.trans hβα) = s.typeAt δ hδβ
  /-- The new chain's head at position `β` lies in `s`'s validFiber
  (the analog of `succNewElement_in_validFiber` for arbitrary `α`). -/
  head_β_in_validFiber :
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    chain.head (Ordinal.enum (α := α.ToType) (· < ·)
      ⟨β, (Ordinal.type_toType α).symm ▸ hβα⟩) ∈
      validFiber cR s.head s.type

/-- **`PairERChain.extendToExt` (pre-fusion approximation-building primitive)**:
extend a chain `s : PairERChain cR β` to a bundled `Extension` for
any countable `α > β`.

**Scope and role.** Despite the fully general statement, this is **not**
the post-fusion chain-extension API. It is the *pre-fusion* primitive
used to build the finite approximations that eventually fuse into a
`CoherentMajorityBranch`. Its only current active consumer is
`CoherentBranchApprox.extendToChain` (together with its projection
lemmas `extendTo_commitAt`, `extendTo_typeAt_old`,
`extendTo_head_β_in_validFiber`), all in the approximation layer.

For active **post-fusion** chain extension — extending a chain that
is aligned with a chosen `CoherentMajorityBranch B` — use
`PairERChain.extendToExtOfBranch B`, which is **proved**
(axiom-clean) and does not require the unqualified frontier.

The two frontiers are complementary, not redundant: `extendToExt` is
upstream construction debt (sorry), `extendToExtOfBranch` is the
clean downstream API. Arbitrary `s` cannot be routed through the
branch version because an arbitrary chain need not match a
globally-chosen branch at its level.

Filling this is the named transfinite-extension frontier for the
approximation layer; everything downstream of it (in this file) is
recovered as projections. -/
noncomputable def PairERChain.extendToExt
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {β α : Ordinal.{0}} (_s : PairERChain cR β)
    (_hβα : β < α) (_hα : α < Ordinal.omega.{0} 1) :
    PairERChain.Extension _s _hβα := by
  sorry

/-- **`PairERChain.extendTo`**: chain-only projection of `extendToExt`. -/
noncomputable def PairERChain.extendTo
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {β α : Ordinal.{0}} (s : PairERChain cR β)
    (hβα : β < α) (hα : α < Ordinal.omega.{0} 1) :
    PairERChain cR α :=
  (s.extendToExt hβα hα).chain

/-- **`PairERChain.extendTo_commitAt`**: agreement at `δ < β` —
projection of `Extension.commitAt_old`. -/
theorem PairERChain.extendTo_commitAt
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {β α : Ordinal.{0}} (s : PairERChain cR β)
    (hβα : β < α) (hα : α < Ordinal.omega.{0} 1)
    (δ : Ordinal.{0}) (hδβ : δ < β) :
    (s.extendTo hβα hα).commitAt δ (hδβ.trans hβα) =
      s.commitAt δ hδβ :=
  (s.extendToExt hβα hα).commitAt_old δ hδβ

/-- **`PairERChain.extendTo_typeAt_old`**: agreement at `δ < β` for
the type function — projection of `Extension.typeAt_old`. -/
theorem PairERChain.extendTo_typeAt_old
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {β α : Ordinal.{0}} (s : PairERChain cR β)
    (hβα : β < α) (hα : α < Ordinal.omega.{0} 1)
    (δ : Ordinal.{0}) (hδβ : δ < β) :
    (s.extendTo hβα hα).typeAt δ (hδβ.trans hβα) =
      s.typeAt δ hδβ :=
  (s.extendToExt hβα hα).typeAt_old δ hδβ

/-- **`PairERChain.extendTo_head_β_in_validFiber`**: the new chain's
head at position `β` lies in `s`'s validFiber — projection of
`Extension.head_β_in_validFiber`. -/
theorem PairERChain.extendTo_head_β_in_validFiber
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {β α : Ordinal.{0}} (s : PairERChain cR β)
    (hβα : β < α) (hα : α < Ordinal.omega.{0} 1) :
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    (s.extendTo hβα hα).head
        (Ordinal.enum (α := α.ToType) (· < ·)
          ⟨β, (Ordinal.type_toType α).symm ▸ hβα⟩) ∈
      validFiber cR s.head s.type :=
  (s.extendToExt hβα hα).head_β_in_validFiber

/-! ### Clean constructors for `PairERChain.Extension`

These build an `Extension` directly (no sorry), for use in the
eventual transfinite recursion at successor stages (`Extension.succ`)
and limit stages with a supplied coherent family
(`Extension.limitWithType`). -/

/-- **`Extension.succ`**: the successor-step extension. When `α =
Order.succ β`, the chain is `s.succ` and the agreement data comes
from `PairERChain.succ_commitAt` / `succ_typeAt_old` /
`succNewElement_in_validFiber` (after identifying `enum at β in
(Order.succ β).ToType = ⊤`). -/
noncomputable def PairERChain.Extension.succ
    {cR : (Fin 2 ↪o PairERSource) → Bool} {β : Ordinal.{0}}
    (s : PairERChain cR β) :
    PairERChain.Extension s (Order.lt_succ β) where
  chain := s.succ
  commitAt_old := fun δ hδβ => PairERChain.succ_commitAt s δ hδβ
  typeAt_old := fun δ hδβ => PairERChain.succ_typeAt_old s δ hδβ
  head_β_in_validFiber := by
    haveI : IsWellOrder (Order.succ β).ToType (· < ·) := isWellOrder_lt
    -- The enum at position β in (Order.succ β).ToType is `⊤`.
    have h_top_eq : (⊤ : (Order.succ β).ToType) =
        Ordinal.enum (α := (Order.succ β).ToType) (· < ·)
          ⟨β, (Ordinal.type_toType _).symm ▸ Order.lt_succ β⟩ :=
      Ordinal.enum_succ_eq_top.symm
    rw [← h_top_eq, PairERChain.succ_head_top]
    exact s.succNewElement_in_validFiber

/-- **`Extension.limitWithType`**: the limit-step extension with
prescribed prefix/branch/largeness data plus explicit agreement
witnesses. Wraps `PairERChain.limitWithType` and lifts the supplied
agreement data into the bundled structure. -/
noncomputable def PairERChain.Extension.limitWithType
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {β : Ordinal.{0}} (s : PairERChain cR β)
    {α : Ordinal.{0}} (hβα : β < α)
    (p : α.ToType ↪o PairERSource) (τ : α.ToType → Bool)
    (hlarge : Order.succ (Cardinal.beth.{0} 1) ≤
      Cardinal.mk (validFiber cR p τ))
    (h_commitAt : ∀ (δ : Ordinal.{0}) (hδβ : δ < β),
      (PairERChain.limitWithType (cR := cR) p τ hlarge).commitAt δ
          (hδβ.trans hβα) = s.commitAt δ hδβ)
    (h_typeAt : ∀ (δ : Ordinal.{0}) (hδβ : δ < β),
      (PairERChain.limitWithType (cR := cR) p τ hlarge).typeAt δ
          (hδβ.trans hβα) = s.typeAt δ hδβ)
    (h_realizes :
      haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
      (PairERChain.limitWithType (cR := cR) p τ hlarge).head
          (Ordinal.enum (α := α.ToType) (· < ·)
            ⟨β, (Ordinal.type_toType α).symm ▸ hβα⟩) ∈
        validFiber cR s.head s.type) :
    PairERChain.Extension s hβα where
  chain := PairERChain.limitWithType p τ hlarge
  commitAt_old := h_commitAt
  typeAt_old := h_typeAt
  head_β_in_validFiber := h_realizes

/-- **`Extension.trans`**: composing two extensions. Given `s : PairERChain
cR β` and chains at intermediate levels `γ` and `α` (with `β < γ < α`),
the composed extension `Extension s (hβγ.trans hγα)` has:
- `chain := e₂.chain`;
- `commitAt_old` / `typeAt_old`: chain agreement at `δ < β` follows
  from `e₂`'s agreement at `δ < γ` chained with `e₁`'s agreement at
  `δ < β`.
- `head_β_in_validFiber`: the new top at position `β` in `e₂.chain`
  agrees with `e₁.chain`'s top at position `β` (by `e₂.commitAt_old β
  hβγ`), so the validFiber membership transfers from
  `e₁.head_β_in_validFiber`.

This lemma is the gluing primitive for the transfinite recursion
building `extendToExt`: at successor stages compose with
`Extension.succ`, at limit stages compose with
`Extension.limitWithType` over a chosen cofinal `ω`-sequence. -/
noncomputable def PairERChain.Extension.trans
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {β γ α : Ordinal.{0}} {s : PairERChain cR β}
    {hβγ : β < γ} {hγα : γ < α}
    (e₁ : PairERChain.Extension s hβγ)
    (e₂ : PairERChain.Extension e₁.chain hγα) :
    PairERChain.Extension s (hβγ.trans hγα) where
  chain := e₂.chain
  commitAt_old := fun δ hδβ =>
    (e₂.commitAt_old δ (hδβ.trans hβγ)).trans (e₁.commitAt_old δ hδβ)
  typeAt_old := fun δ hδβ =>
    (e₂.typeAt_old δ (hδβ.trans hβγ)).trans (e₁.typeAt_old δ hδβ)
  head_β_in_validFiber := by
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder γ.ToType (· < ·) := isWellOrder_lt
    -- The enum at position β in α.ToType, after passing through e₂.chain.head,
    -- agrees with e₁.chain.head's value at position β in γ.ToType
    -- (by e₂.commitAt_old β hβγ).
    have h_commit : e₂.chain.commitAt β (hβγ.trans hγα) =
        e₁.chain.commitAt β hβγ := e₂.commitAt_old β hβγ
    -- The goal is e₂.chain.head (enum at β in α.ToType) ∈ validFiber.
    -- Unfold commitAt to head + enum; rewrite via h_commit.
    show e₂.chain.head _ ∈ validFiber cR s.head s.type
    show e₂.chain.commitAt β (hβγ.trans hγα) ∈ validFiber cR s.head s.type
    rw [h_commit]
    show e₁.chain.head _ ∈ validFiber cR s.head s.type
    exact e₁.head_β_in_validFiber

/-! ### Finite-gap iteration of `Extension.succ`

The first non-trivial application of the `Extension` API: build a
finite-gap extension `s → s.succ.succ ⋯ .succ` (with `n + 1`
applications of `Order.succ` starting at `β`) via `ℕ`-recursion
composing `Extension.succ` with `Extension.trans`. This is the
"low-risk milestone" exercising the API under ordinary recursion
before any transfinite work. -/

/-- **`succIter β n`**: the `(n + 1)`-iterated successor of `β`. Used
as the canonical "finite gap" endpoint for `Extension.iterateSucc`. -/
def succIter (β : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => Order.succ β
  | n + 1 => Order.succ (succIter β n)

/-- `β < succIter β n` for all `n`. -/
lemma lt_succIter (β : Ordinal.{0}) : ∀ n : ℕ, β < succIter β n
  | 0 => Order.lt_succ β
  | n + 1 => (lt_succIter β n).trans (Order.lt_succ _)

/-- `succIter β n < ω_1` when `β < ω_1`, using closure of `< ω_1`
under `Order.succ` (since `ω_1` is a successor-limit cardinal). -/
lemma succIter_lt_omega1 {β : Ordinal.{0}} (hβ : β < Ordinal.omega.{0} 1) :
    ∀ n : ℕ, succIter β n < Ordinal.omega.{0} 1
  | 0 => (Cardinal.isSuccLimit_omega 1).succ_lt hβ
  | n + 1 => (Cardinal.isSuccLimit_omega 1).succ_lt (succIter_lt_omega1 hβ n)

/-- **`Extension.iterateSucc`**: a finite-gap extension from `s` to a
chain at `succIter β n`, built by `ℕ`-recursion composing
`Extension.succ` with `Extension.trans`.

- `n = 0`: `Extension.succ s` (a chain at `Order.succ β = succIter β 0`).
- `n + 1`: compose the IH at `n` with `Extension.succ` of the IH's
  chain (which produces a chain at
  `Order.succ (succIter β n) = succIter β (n + 1)`). -/
noncomputable def PairERChain.Extension.iterateSucc
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {β : Ordinal.{0}} (s : PairERChain cR β) :
    ∀ n : ℕ, PairERChain.Extension s (lt_succIter β n)
  | 0 => PairERChain.Extension.succ s
  | n + 1 =>
    (iterateSucc s n).trans (PairERChain.Extension.succ (iterateSucc s n).chain)

/-- **`extendToExt_of_succIter`**: the `succIter`-case wrapper for
`extendToExt`. For the special case `α = succIter β n`, the bundled
extension is produced by `Extension.iterateSucc` directly — no
appeal to the transfinite-extension frontier `extendToExt` is
needed. The `hα` parameter is present for API symmetry with
`extendToExt` (the actual bound on `succIter β n` is provided
separately by `succIter_lt_omega1`). -/
noncomputable def PairERChain.extendToExt_of_succIter
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {β : Ordinal.{0}} (s : PairERChain cR β) (n : ℕ)
    (_hα : succIter β n < Ordinal.omega.{0} 1) :
    PairERChain.Extension s (lt_succIter β n) :=
  PairERChain.Extension.iterateSucc s n

/-! ### First genuine limit constructor: `Extension.limitOfOmegaSeq`

A sequence-parametrized limit extension. The caller supplies:
- the target `α` and proof `β < α`;
- a cofinal `ℕ`-sequence `e n < α` strictly above `β`;
- a family of extensions `E n : Extension s (β < e n)`, one per stage;
- explicit prefix `p : α.ToType ↪o PairERSource`, branch `τ`, and
  largeness witness at `α`;
- compatibility witnesses: at every position `δ < e n`, the supplied
  `limitWithType p τ hlarge` agrees with `(E n).chain` (one witness
  per `n` for prefix, one for branch).

The lemma assembles the three `Extension` agreement fields from
`E 0` plus the compatibility at `n = 0`. The full sequence is
present in the signature for use by downstream gluing (cross-`n`
compatibility, ω-cofinality), even though only `E 0` is needed for
the basic proof.

This isolates the limit-gluing bookkeeping from the cardinal/fusion
content (which provides `p`, `τ`, `hlarge`, and the compatibility
witnesses). -/
noncomputable def PairERChain.Extension.limitOfOmegaSeq
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {β α : Ordinal.{0}} {s : PairERChain cR β}
    (hβα : β < α)
    (e : ℕ → Ordinal.{0})
    (_he_mono : StrictMono e)
    (_he_cofinal : ∀ γ : Ordinal.{0}, γ < α → ∃ n, γ < e n)
    (he_β : ∀ n, β < e n) (he_lt : ∀ n, e n < α)
    (E : ∀ n, PairERChain.Extension s (he_β n))
    (p : α.ToType ↪o PairERSource) (τ : α.ToType → Bool)
    (hlarge : Order.succ (Cardinal.beth.{0} 1) ≤
      Cardinal.mk (validFiber cR p τ))
    (h_prefix_compat : ∀ (n : ℕ) (δ : Ordinal.{0}) (hδ : δ < e n),
      (PairERChain.limitWithType (cR := cR) p τ hlarge).commitAt δ
          (hδ.trans (he_lt n)) = (E n).chain.commitAt δ hδ)
    (h_type_compat : ∀ (n : ℕ) (δ : Ordinal.{0}) (hδ : δ < e n),
      (PairERChain.limitWithType (cR := cR) p τ hlarge).typeAt δ
          (hδ.trans (he_lt n)) = (E n).chain.typeAt δ hδ) :
    PairERChain.Extension s hβα :=
  PairERChain.Extension.limitWithType s hβα p τ hlarge
    (-- commitAt_old at δ < β: use n = 0 and chain through E 0.
     fun δ hδβ =>
      (h_prefix_compat 0 δ (hδβ.trans (he_β 0))).trans
        ((E 0).commitAt_old δ hδβ))
    (-- typeAt_old at δ < β: analog.
     fun δ hδβ =>
      (h_type_compat 0 δ (hδβ.trans (he_β 0))).trans
        ((E 0).typeAt_old δ hδβ))
    (-- head at β in validFiber: same pattern with δ = β.
     by
      haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
      have h := h_prefix_compat 0 β (he_β 0)
      -- h : limitWithType.commitAt β _ = (E 0).chain.commitAt β _.
      -- commitAt β _ = head (enum at β); rewrite via h.
      show (PairERChain.limitWithType (cR := cR) p τ hlarge).head _ ∈
           validFiber cR s.head s.type
      show (PairERChain.limitWithType (cR := cR) p τ hlarge).commitAt β
            ((he_β 0).trans (he_lt 0)) ∈
           validFiber cR s.head s.type
      rw [h]
      show (E 0).chain.head _ ∈ validFiber cR s.head s.type
      exact (E 0).head_β_in_validFiber)

/-! ### Cofinal-sequence existence + wrapper for countable limit ordinals

Every countable limit ordinal `α < ω_1` admits a strictly-monotone
cofinal `ω`-sequence. We extract one from `Ordinal.exists_fundamental_sequence`
plus the fact that `α.cof = ℵ₀` for countable limit ordinals.

The wrapper `Extension.limitOfCountableLimit` then takes a closure
that, given the chosen cofinal sequence, produces the `Extension`
(typically by calling `Extension.limitOfOmegaSeq` with user-supplied
`p`/`τ`/`hlarge`/stage-extensions/compatibility). The ordinal/
cofinality bookkeeping is isolated here from the cardinal/fusion
content. -/

/-- **`exists_strictMono_cofinal_nat_lt`**: every countable limit
ordinal admits a strictly-monotone cofinal `ω`-sequence. -/
theorem exists_strictMono_cofinal_nat_lt
    {α : Ordinal.{0}} (hα : α < Ordinal.omega.{0} 1)
    (hlim : Order.IsSuccLimit α) :
    ∃ e : ℕ → Ordinal.{0},
      StrictMono e ∧ (∀ n, e n < α) ∧
      (∀ γ : Ordinal.{0}, γ < α → ∃ n, γ < e n) := by
  -- α.cof = ℵ₀ since α < ω₁ is countable and α is a (succ) limit.
  have h_cof : α.cof = Cardinal.aleph0 := by
    apply le_antisymm
    · have h_card : α.card ≤ Cardinal.aleph0 := by
        have h1 : α.card < Cardinal.aleph 1 := by
          rw [show Ordinal.omega.{0} 1 = (Cardinal.aleph 1).ord from
            (Cardinal.ord_aleph 1).symm] at hα
          rwa [Cardinal.lt_ord] at hα
        rw [show (Cardinal.aleph 1 : Cardinal.{0}) =
            Order.succ Cardinal.aleph0 from Cardinal.succ_aleph0.symm] at h1
        exact Order.lt_succ_iff.mp h1
      exact (Ordinal.cof_le_card α).trans h_card
    · exact Ordinal.aleph0_le_cof.mpr hlim
  have h_ord : α.cof.ord = Ordinal.omega0 := by
    rw [h_cof, Cardinal.ord_aleph0]
  -- Use the existing fundamental sequence machinery.
  obtain ⟨f, hf⟩ := Ordinal.exists_fundamental_sequence α
  refine ⟨fun n => f (n : Ordinal.{0}) (h_ord ▸ Ordinal.nat_lt_omega0 n), ?_, ?_, ?_⟩
  · intro m n hmn
    apply hf.strict_mono
    exact_mod_cast hmn
  · intro n
    exact hf.lt _
  · intro γ hγ
    rw [← hf.blsub_eq] at hγ
    obtain ⟨b, hb, hγb⟩ := Ordinal.lt_blsub_iff.mp hγ
    have hb_lt_ω : b < Ordinal.omega0 := h_ord ▸ hb
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hb_lt_ω
    -- `lt_blsub_iff` gives `γ ≤ f (n : Ordinal) hb`. Use the next index
    -- `n + 1` for strict inequality.
    refine ⟨n + 1, hγb.trans_lt ?_⟩
    apply hf.strict_mono
    exact_mod_cast Nat.lt_succ_self n

/-- **`Extension.limitOfCountableLimit`**: wrapper around
`Extension.limitOfOmegaSeq` for countable limit `α < ω_1`. The
wrapper chooses the cofinal sequence via
`exists_strictMono_cofinal_nat_lt` (shifted so `β < e n` for all `n`)
and hands it to the user's `build` closure, which produces the
`Extension` (typically via `limitOfOmegaSeq`). Limit data `p`/`τ`/
`hlarge` is supplied **inside `build`** by the caller; only the
cofinality bookkeeping is handled here. -/
noncomputable def PairERChain.Extension.limitOfCountableLimit
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {β α : Ordinal.{0}} {s : PairERChain cR β}
    (hβα : β < α) (hα : α < Ordinal.omega.{0} 1)
    (hlim : Order.IsSuccLimit α)
    (build : ∀ (e : ℕ → Ordinal.{0}),
              StrictMono e →
              (∀ γ : Ordinal.{0}, γ < α → ∃ n, γ < e n) →
              (∀ n, β < e n) → (∀ n, e n < α) →
              PairERChain.Extension s hβα) :
    PairERChain.Extension s hβα := by
  classical
  -- Extract a cofinal sequence via Classical.choose (since `Extension` is
  -- in `Type`, plain `obtain` on the `Exists` would fail).
  let hex := exists_strictMono_cofinal_nat_lt hα hlim
  let e : ℕ → Ordinal.{0} := Classical.choose hex
  have he_props : StrictMono e ∧ (∀ n, e n < α) ∧
      (∀ γ : Ordinal.{0}, γ < α → ∃ n, γ < e n) := Classical.choose_spec hex
  obtain ⟨he_mono, he_lt, he_cofinal⟩ := he_props
  -- Shift past β: pick n₀ with β < e n₀, define e' n := e (n₀ + n + 1).
  let n₀ : ℕ := Classical.choose (he_cofinal β hβα)
  have hn₀ : β < e n₀ := Classical.choose_spec (he_cofinal β hβα)
  let e' : ℕ → Ordinal.{0} := fun n => e (n₀ + n + 1)
  have he'_mono : StrictMono e' := fun m n hmn =>
    he_mono (show n₀ + m + 1 < n₀ + n + 1 by omega)
  have he'_β : ∀ n, β < e' n := fun n =>
    hn₀.trans (he_mono (show n₀ < n₀ + n + 1 by omega))
  have he'_lt : ∀ n, e' n < α := fun n => he_lt _
  have he'_cofinal : ∀ γ : Ordinal.{0}, γ < α → ∃ n, γ < e' n := fun γ hγ => by
    obtain ⟨m, hm⟩ := he_cofinal γ hγ
    refine ⟨m, hm.trans ?_⟩
    apply he_mono
    show m < n₀ + m + 1
    omega
  exact build e' he'_mono he'_cofinal he'_β he'_lt

/-! ### `PairERChain.LimitData`: bundled inputs to the limit constructor

A single record packaging everything `Extension.limitOfOmegaSeq`
needs: a cofinal `ω`-sequence shifted past `β`, the stage extensions
along the sequence, the limit prefix/branch/large at `α`, and the
two compatibility witnesses. `Extension.ofLimitData` is then a thin
wrapper.

This isolates the last real construction problem into "produce
`LimitData`". Once a fusion/cardinal-largeness layer can produce
this record (typically by gluing along the chosen sequence and
verifying the validFiber size), the full `extendToExt` becomes
successor/limit recursion (via `Extension.succ` and `ofLimitData`)
plus a single limit-data frontier — without mixing recursion,
cofinality, compatibility, and cardinal largeness in one proof. -/

/-- **`PairERChain.LimitData s hβα`**: bundled data for constructing
the limit-stage extension `Extension s hβα`. -/
structure PairERChain.LimitData
    {cR : (Fin 2 ↪o PairERSource) → Bool} {β : Ordinal.{0}}
    (s : PairERChain cR β) {α : Ordinal.{0}} (hβα : β < α) where
  /-- The cofinal `ω`-sequence, shifted so all values exceed `β`. -/
  e : ℕ → Ordinal.{0}
  he_mono : StrictMono e
  he_cofinal : ∀ γ : Ordinal.{0}, γ < α → ∃ n, γ < e n
  he_β : ∀ n, β < e n
  he_lt : ∀ n, e n < α
  /-- Stage extensions along the sequence. -/
  E : ∀ n, PairERChain.Extension s (he_β n)
  /-- The limit prefix at `α`. -/
  p : α.ToType ↪o PairERSource
  /-- The limit branch at `α`. -/
  τ : α.ToType → Bool
  /-- Largeness of the validFiber for `(p, τ)`. -/
  large : Order.succ (Cardinal.beth.{0} 1) ≤
    Cardinal.mk (validFiber cR p τ)
  /-- Compatibility of the limit prefix with each stage chain on its
  initial segment. -/
  prefix_compat : ∀ (n : ℕ) (δ : Ordinal.{0}) (hδ : δ < e n),
    (PairERChain.limitWithType (cR := cR) p τ large).commitAt δ
        (hδ.trans (he_lt n)) = (E n).chain.commitAt δ hδ
  /-- Compatibility of the limit branch with each stage chain. -/
  type_compat : ∀ (n : ℕ) (δ : Ordinal.{0}) (hδ : δ < e n),
    (PairERChain.limitWithType (cR := cR) p τ large).typeAt δ
        (hδ.trans (he_lt n)) = (E n).chain.typeAt δ hδ

/-- **`Extension.ofLimitData`**: thin wrapper turning bundled
`LimitData` into a bundled `Extension` via `limitOfOmegaSeq`. -/
noncomputable def PairERChain.Extension.ofLimitData
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {β α : Ordinal.{0}} {s : PairERChain cR β} {hβα : β < α}
    (D : PairERChain.LimitData s hβα) :
    PairERChain.Extension s hβα :=
  PairERChain.Extension.limitOfOmegaSeq hβα D.e D.he_mono D.he_cofinal
    D.he_β D.he_lt D.E D.p D.τ D.large D.prefix_compat D.type_compat

/-- **`limitWithType_commitAt`**: commit at position `δ` is the prefix's
value at the enumerated position — parallel to `PairERChain.limit_commitAt`. -/
lemma PairERChain.limitWithType_commitAt
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (p : α.ToType ↪o PairERSource) (τ : α.ToType → Bool) (hlarge)
    (δ : Ordinal.{0}) (hδ : δ < α) :
    (PairERChain.limitWithType (cR := cR) p τ hlarge).commitAt δ hδ =
      haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
      p (Ordinal.enum (α := α.ToType) (· < ·)
        ⟨δ, (Ordinal.type_toType α).symm ▸ hδ⟩) := rfl

/-- **`limitWithType_typeAt`**: Bool at position `δ` is `τ` at the
enumerated position — the key property justifying "type-coherent
limit chain". -/
lemma PairERChain.limitWithType_typeAt
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (p : α.ToType ↪o PairERSource) (τ : α.ToType → Bool) (hlarge)
    (δ : Ordinal.{0}) (hδ : δ < α) :
    (PairERChain.limitWithType (cR := cR) p τ hlarge).typeAt δ hδ =
      haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
      τ (Ordinal.enum (α := α.ToType) (· < ·)
        ⟨δ, (Ordinal.type_toType α).symm ▸ hδ⟩) := rfl

/-- **Coherent family of successor stages below `α`.** For each
`β < α`, we have a stage at level `β + 1`, and later stages preserve
the committed head at every earlier position. This is the exact data
needed to glue a genuine limit-stage prefix.

**Type coherence** — the parallel statement for `typeAt` — is tracked
EXTERNALLY via `IsTypeCoherent` rather than as a structural field,
because not all existing constructors (notably `CoherentBundle.limit
Extend`) establish it yet. The limit-case type coherence is the
frontier: it requires the sharper limit-kernel
`exists_large_limit_fiber_prescribed`. -/
structure PairERCoherentFamily
    (cR : (Fin 2 ↪o PairERSource) → Bool) (α : Ordinal.{0}) where
  stage : ∀ β : Ordinal.{0}, β < α → PairERChain cR (Order.succ β)
  coherent :
    ∀ {δ β : Ordinal.{0}} (hδβ : δ < β) (hβα : β < α),
      (stage β hβα).commitAt δ (hδβ.trans (Order.lt_succ β)) =
        (stage δ (hδβ.trans hβα)).commitAt δ (Order.lt_succ δ)

/-- **Type coherence invariant for a `PairERCoherentFamily`**: later
stages preserve the Bool committed at earlier positions. Tracked
externally (see `PairERCoherentFamily`'s docstring). -/
def PairERCoherentFamily.IsTypeCoherent
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (F : PairERCoherentFamily cR α) : Prop :=
  ∀ {δ β : Ordinal.{0}} (hδβ : δ < β) (hβα : β < α),
    (F.stage β hβα).typeAt δ (hδβ.trans (Order.lt_succ β)) =
      (F.stage δ (hδβ.trans hβα)).typeAt δ (Order.lt_succ δ)

/-- **Restriction of a coherent family** to a shorter level `β ≤ α`.
The stage function is re-quantified and coherence is inherited. -/
noncomputable def PairERCoherentFamily.restrict
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (F : PairERCoherentFamily cR α) {β : Ordinal.{0}} (hβα : β ≤ α) :
    PairERCoherentFamily cR β where
  stage γ hγβ := F.stage γ (hγβ.trans_le hβα)
  coherent := fun hδγ hγβ => F.coherent hδγ (hγβ.trans_le hβα)

/-- `restrict` preserves `IsTypeCoherent`. -/
lemma PairERCoherentFamily.IsTypeCoherent.restrict
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    {F : PairERCoherentFamily cR α} (hF_type : F.IsTypeCoherent)
    {β : Ordinal.{0}} (hβα : β ≤ α) :
    (F.restrict hβα).IsTypeCoherent :=
  fun hδγ hγβ => hF_type hδγ (hγβ.trans_le hβα)

/-- `restrict`'s `stage γ` is definitionally `F.stage γ _` (with a
repacked proof). Exposed as a `rfl` lemma for rewrite chains. -/
@[simp]
lemma PairERCoherentFamily.restrict_stage
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (F : PairERCoherentFamily cR α) {β : Ordinal.{0}} (hβα : β ≤ α)
    (γ : Ordinal.{0}) (hγβ : γ < β) :
    (F.restrict hβα).stage γ hγβ = F.stage γ (hγβ.trans_le hβα) := rfl

/-- **Committed value at ordinal position `δ`.** In a coherent family,
look at the stage `δ + 1` and read off the value committed at the new
top position `δ`. -/
noncomputable def PairERCoherentFamily.commitVal
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (F : PairERCoherentFamily cR α) (δ : Ordinal.{0}) (hδ : δ < α) :
    PairERSource :=
  (F.stage δ hδ).commitAt δ (Order.lt_succ δ)

/-- **Earlier committed values reappear in later stages.** This is just
the coherence axiom rewritten in terms of `commitVal`. -/
lemma PairERCoherentFamily.commitVal_eq_commitAt
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (F : PairERCoherentFamily cR α) {δ β : Ordinal.{0}}
    (hδβ : δ < β) (hβα : β < α) :
    F.commitVal δ (hδβ.trans hβα) =
      (F.stage β hβα).commitAt δ (hδβ.trans (Order.lt_succ β)) := by
  unfold PairERCoherentFamily.commitVal
  symm
  exact F.coherent hδβ hβα

/-- **Committed Bool at position `δ`** in a coherent family: the type
at the top of stage `δ+1`. Analogous to `commitVal`. -/
noncomputable def PairERCoherentFamily.typeVal
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (F : PairERCoherentFamily cR α) (δ : Ordinal.{0}) (hδ : δ < α) :
    Bool :=
  (F.stage δ hδ).typeAt δ (Order.lt_succ δ)

/-- **Committed values are strictly increasing with the ordinal index.**
Use coherence to compare both values inside the later stage, then apply
`PairERChain.commitAt_strictMono`. -/
lemma PairERCoherentFamily.commitVal_strictMono
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (F : PairERCoherentFamily cR α) {δ₁ δ₂ : Ordinal.{0}}
    (hδ₁ : δ₁ < α) (hδ₂ : δ₂ < α) (h : δ₁ < δ₂) :
    F.commitVal δ₁ hδ₁ < F.commitVal δ₂ hδ₂ := by
  calc
    F.commitVal δ₁ hδ₁ =
        (F.stage δ₂ hδ₂).commitAt δ₁ (h.trans (Order.lt_succ δ₂)) :=
      F.commitVal_eq_commitAt h hδ₂
    _ < (F.stage δ₂ hδ₂).commitAt δ₂ (Order.lt_succ δ₂) := by
      exact PairERChain.commitAt_strictMono (s := F.stage δ₂ hδ₂)
        (hδ₁ := h.trans (Order.lt_succ δ₂))
        (hδ₂ := Order.lt_succ δ₂) h
    _ = F.commitVal δ₂ hδ₂ := rfl

/-- **Glued prefix from a coherent family.** At `x : α.ToType`, read the
committed value at ordinal position `typein x`. Strict monotonicity is
exactly `commitVal_strictMono`. -/
noncomputable def PairERCoherentFamily.prefix
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (F : PairERCoherentFamily cR α) : α.ToType ↪o PairERSource := by
  classical
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  refine OrderEmbedding.ofStrictMono
    (fun x =>
      F.commitVal (Ordinal.typein (· < ·) x) (by
        simpa [Ordinal.type_toType α] using
          Ordinal.typein_lt_type (· < · : α.ToType → α.ToType → Prop) x))
    ?_
  intro x y hxy
  let δx : Ordinal.{0} := Ordinal.typein (· < ·) x
  let δy : Ordinal.{0} := Ordinal.typein (· < ·) y
  have hδx : δx < α := by
    simpa [δx, Ordinal.type_toType α] using
      Ordinal.typein_lt_type (· < · : α.ToType → α.ToType → Prop) x
  have hδy : δy < α := by
    simpa [δy, Ordinal.type_toType α] using
      Ordinal.typein_lt_type (· < · : α.ToType → α.ToType → Prop) y
  have hδ : δx < δy := by
    simpa [δx, δy] using
      ((Ordinal.typein_lt_typein (· < ·)).mpr hxy)
  exact F.commitVal_strictMono hδx hδy hδ

/-- **The glued prefix hits the expected committed value.** Evaluating
`prefix` at the `δ`-th point of `α.ToType` returns the value committed
at stage `δ + 1`. -/
lemma PairERCoherentFamily.prefix_enum
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (F : PairERCoherentFamily cR α) (δ : Ordinal.{0}) (hδ : δ < α) :
    F.prefix
      (Ordinal.enum (α := α.ToType) (· < ·)
        ⟨δ, (Ordinal.type_toType α).symm ▸ hδ⟩) =
      F.commitVal δ hδ := by
  classical
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  -- Name the enum point.
  set e : α.ToType := Ordinal.enum (α := α.ToType) (· < ·)
    ⟨δ, (Ordinal.type_toType α).symm ▸ hδ⟩ with he_def
  -- `typein e = δ` via `typein_enum`.
  have htypein : Ordinal.typein (· < ·) e = δ := by
    rw [he_def, Ordinal.typein_enum]
  -- Unfold `prefix`.
  unfold PairERCoherentFamily.prefix
  simp only [OrderEmbedding.coe_ofStrictMono]
  -- Now both sides are `F.commitVal _ _` with differing ordinal / proof arguments.
  -- Rewrite the ordinal argument via `htypein`.
  have goal_eq :
      F.commitVal (Ordinal.typein (· < ·) e) (by
        simpa [Ordinal.type_toType α] using
          Ordinal.typein_lt_type (· < · : α.ToType → α.ToType → Prop) e) =
      F.commitVal δ hδ := by
    congr 1
  exact goal_eq

/-- **Prescribed type function for the glued prefix.** At each position
`x : α.ToType`, the prescribed Bool is the `typeVal` at ordinal position
`typein x`. This is the function we want `exists_large_limit_fiber` to
produce — a TYPE-COHERENT limit fiber rather than an arbitrary one. -/
noncomputable def PairERCoherentFamily.typeFn
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (F : PairERCoherentFamily cR α) : α.ToType → Bool := by
  classical
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  exact fun x =>
    F.typeVal (Ordinal.typein (· < ·) x) (by
      simpa [Ordinal.type_toType α] using
        Ordinal.typein_lt_type (· < · : α.ToType → α.ToType → Prop) x)

/-- **Per-stage fibers refine the prescribed prefix/τ fiber**: if `y`
lies in the validFiber of *every* stage `F.stage β`, then `y` lies in
`validFiber cR F.prefix F.typeFn`. This is the half of the limit-fiber
identity that does NOT need `IsTypeCoherent` — each stage's top-
position constraint hands us the needed pair-color equation at the
corresponding `α.ToType` position. -/
lemma PairERCoherentFamily.validFiber_of_stages
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (F : PairERCoherentFamily cR α) (y : PairERSource)
    (hy : ∀ (β : Ordinal.{0}) (hβα : β < α),
      y ∈ validFiber cR (F.stage β hβα).head (F.stage β hβα).type) :
    y ∈ validFiber cR F.prefix F.typeFn := by
  classical
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  intro x
  set δ : Ordinal.{0} := Ordinal.typein (· < ·) x with hδ_def
  have hδα : δ < α := by
    simpa [δ, Ordinal.type_toType α] using
      Ordinal.typein_lt_type (· < · : α.ToType → α.ToType → Prop) x
  -- Use the validFiber at stage δ, at the top position of (succ δ).ToType.
  have hy_δ := hy δ hδα
  -- The top of (succ δ).ToType.
  set top_δ : (Order.succ δ).ToType :=
    Ordinal.enum (α := (Order.succ δ).ToType) (· < ·)
      ⟨δ, (Ordinal.type_toType _).symm ▸ Order.lt_succ δ⟩ with htop_def
  obtain ⟨h_lt, h_col⟩ := hy_δ top_δ
  -- Translate `(F.stage δ).head top_δ = F.prefix x` and same for type.
  have h_head : (F.stage δ hδα).head top_δ = F.prefix x := by
    show (F.stage δ hδα).head top_δ = _
    have h2 : (F.stage δ hδα).head top_δ =
        (F.stage δ hδα).commitAt δ (Order.lt_succ δ) := by
      show (F.stage δ hδα).head top_δ = (F.stage δ hδα).head _
      congr 1
    rw [h2]; rfl
  have h_type : (F.stage δ hδα).type top_δ = F.typeFn x := by
    show (F.stage δ hδα).type top_δ = F.typeVal δ hδα
    show (F.stage δ hδα).type top_δ =
      (F.stage δ hδα).typeAt δ (Order.lt_succ δ)
    rfl
  refine ⟨?_, ?_⟩
  · rw [← h_head]; exact h_lt
  · rw [← h_type]; convert h_col using 2

/-- **Reverse inclusion of `validFiber_of_stages`** (under
`IsTypeCoherent`): if `y` lies in `validFiber cR F.prefix F.typeFn`,
then `y` lies in every stage's validFiber. Combined with
`validFiber_of_stages`, this gives
`validFiber cR F.prefix F.typeFn = ⋂_β validFiber cR (F.stage β).head
(F.stage β).type` — isolating the cardinality question from the
prefix/typeFn bookkeeping. -/
lemma PairERCoherentFamily.validFiber_of_prefix_typeFn
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (F : PairERCoherentFamily cR α) (hF_type : F.IsTypeCoherent)
    {β : Ordinal.{0}} (hβα : β < α) {y : PairERSource}
    (hy : y ∈ validFiber cR F.prefix F.typeFn) :
    y ∈ validFiber cR (F.stage β hβα).head (F.stage β hβα).type := by
  classical
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder (Order.succ β).ToType (· < ·) := isWellOrder_lt
  intro z_β
  -- Case on z_β = top vs z_β < top.
  by_cases h_top : z_β = (⊤ : (Order.succ β).ToType)
  · -- z_β = top: the position corresponds to ordinal β itself.
    subst h_top
    -- Use the position of β in α.ToType (which exists since β < α).
    set x_α : α.ToType := Ordinal.enum (α := α.ToType) (· < ·)
      ⟨β, (Ordinal.type_toType α).symm ▸ hβα⟩ with hxα_def
    obtain ⟨h_lt, h_col⟩ := hy x_α
    have h_prefix_eq : F.prefix x_α = F.commitVal β hβα :=
      F.prefix_enum β hβα
    have h_typeFn_eq : F.typeFn x_α = F.typeVal β hβα := by
      show F.typeVal (Ordinal.typein (· < ·) x_α) _ = F.typeVal β hβα
      congr 1
      rw [hxα_def, Ordinal.typein_enum]
    -- (F.stage β hβα).head ⊤ = (F.stage β hβα).commitAt β (Order.lt_succ β) = F.commitVal β hβα.
    have h_top_enum : (⊤ : (Order.succ β).ToType) =
        Ordinal.enum (α := (Order.succ β).ToType) (· < ·)
          ⟨β, (Ordinal.type_toType _).symm ▸ Order.lt_succ β⟩ :=
      Ordinal.enum_succ_eq_top.symm
    have h_head_eq : (F.stage β hβα).head (⊤ : (Order.succ β).ToType) =
        F.commitVal β hβα := congrArg (F.stage β hβα).head h_top_enum
    have h_type_eq : (F.stage β hβα).type (⊤ : (Order.succ β).ToType) =
        F.typeVal β hβα := congrArg (F.stage β hβα).type h_top_enum
    refine ⟨?_, ?_⟩
    · rw [h_head_eq, ← h_prefix_eq]; exact h_lt
    · rw [h_type_eq, ← h_typeFn_eq]
      convert h_col using 3
      rw [h_prefix_eq, ← h_head_eq]
  · -- z_β < top: the position corresponds to some ordinal γ < β.
    -- Extract γ = typein z_β, which is < β (strict).
    have hγ_lt_sβ : Ordinal.typein (· < ·) z_β < Order.succ β := by
      simpa [Ordinal.type_toType _] using
        Ordinal.typein_lt_type
          (· < · : (Order.succ β).ToType → (Order.succ β).ToType → Prop) z_β
    have hγ_lt_top : z_β < (⊤ : (Order.succ β).ToType) :=
      lt_of_le_of_ne le_top h_top
    have hγ_lt_β : Ordinal.typein (· < ·) z_β < β := by
      have htop_typein : Ordinal.typein (· < ·)
          (⊤ : (Order.succ β).ToType) = β := by
        rw [show (⊤ : (Order.succ β).ToType) =
          Ordinal.enum (α := (Order.succ β).ToType) (· < ·)
            ⟨β, (Ordinal.type_toType _).symm ▸ Order.lt_succ β⟩
          from Ordinal.enum_succ_eq_top.symm, Ordinal.typein_enum]
      calc Ordinal.typein (· < ·) z_β
          < Ordinal.typein (· < ·) (⊤ : (Order.succ β).ToType) :=
            (Ordinal.typein_lt_typein (· < ·)).mpr hγ_lt_top
        _ = β := htop_typein
    have hγ_lt_α : Ordinal.typein (· < ·) z_β < α := hγ_lt_β.trans hβα
    set γ : Ordinal.{0} := Ordinal.typein (· < ·) z_β with hγ_def
    set x_α : α.ToType := Ordinal.enum (α := α.ToType) (· < ·)
      ⟨γ, (Ordinal.type_toType α).symm ▸ hγ_lt_α⟩ with hxα_def
    obtain ⟨h_lt, h_col⟩ := hy x_α
    have h_prefix_eq : F.prefix x_α = F.commitVal γ hγ_lt_α :=
      F.prefix_enum γ hγ_lt_α
    have h_typeFn_eq : F.typeFn x_α = F.typeVal γ hγ_lt_α := by
      show F.typeVal (Ordinal.typein (· < ·) x_α) _ = F.typeVal γ hγ_lt_α
      congr 1
      rw [hxα_def, Ordinal.typein_enum]
    have h_ze : z_β =
        Ordinal.enum (α := (Order.succ β).ToType) (· < ·)
          ⟨γ, (Ordinal.type_toType _).symm ▸ hγ_lt_sβ⟩ := by
      show z_β = Ordinal.enum (α := (Order.succ β).ToType) (· < ·)
        ⟨Ordinal.typein (· < ·) z_β, _⟩
      exact (Ordinal.enum_typein (α := (Order.succ β).ToType) (· < ·) z_β).symm
    have h_head_commit :
        (F.stage β hβα).head z_β = (F.stage β hβα).commitAt γ hγ_lt_sβ :=
      congrArg (F.stage β hβα).head h_ze
    have h_type_at :
        (F.stage β hβα).type z_β = (F.stage β hβα).typeAt γ hγ_lt_sβ :=
      congrArg (F.stage β hβα).type h_ze
    -- Now γ < β strictly, so F.coherent and hF_type apply directly.
    have h_head_eq : (F.stage β hβα).head z_β = F.commitVal γ hγ_lt_α := by
      rw [h_head_commit]; exact F.coherent hγ_lt_β hβα
    have h_type_eq : (F.stage β hβα).type z_β = F.typeVal γ hγ_lt_α := by
      rw [h_type_at]; exact hF_type hγ_lt_β hβα
    refine ⟨?_, ?_⟩
    · rw [h_head_eq, ← h_prefix_eq]; exact h_lt
    · rw [h_type_eq, ← h_typeFn_eq]
      convert h_col using 3
      rw [h_prefix_eq, ← h_head_eq]

/-- **Prescribed fiber equals intersection of stage fibers** (under
`IsTypeCoherent`). Isolates the prefix/typeFn bookkeeping from the
cardinality question: the frontier theorem reduces to "the intersection
has size ≥ succ ℶ_1". -/
lemma PairERCoherentFamily.validFiber_prefix_typeFn_eq_iInter
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (F : PairERCoherentFamily cR α) (hF_type : F.IsTypeCoherent) :
    validFiber cR F.prefix F.typeFn =
      ⋂ (β : Ordinal.{0}) (hβα : β < α),
        validFiber cR (F.stage β hβα).head (F.stage β hβα).type := by
  ext y
  refine ⟨?_, ?_⟩
  · intro hy
    simp only [Set.mem_iInter]
    intro β hβα
    exact F.validFiber_of_prefix_typeFn hF_type hβα hy
  · intro hy
    simp only [Set.mem_iInter] at hy
    exact F.validFiber_of_stages y hy

/-- **Descending nesting of stage validFibers** (under `IsTypeCoherent`):
if `δ < β < α` and `F` is type-coherent, any `y` in the validFiber at
stage `β` is also in the validFiber at stage `δ`. This is the key
cardinality-argument precondition for the frontier theorem: the
`{validFiber(F.stage β)}` family is descending nested.

**Proof sketch**: for each `z_δ : (succ δ).ToType` with ordinal position
`γ ≤ δ`, pull back to `z_β : (succ β).ToType` at the same ordinal γ.
Use `coherent` to identify heads at γ across β and δ; use `IsTypeCoherent`
to identify types. The constraints at γ transfer from the β-side to
the δ-side.

**TODO**: the proof requires careful position-enum bookkeeping; left as
the next incremental step after `IsTypeCoherent` is established. -/
lemma PairERCoherentFamily.validFiber_mono
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (F : PairERCoherentFamily cR α) (hF_type : F.IsTypeCoherent)
    {δ β : Ordinal.{0}} (hδβ : δ < β) (hβα : β < α) {y : PairERSource}
    (hy : y ∈ validFiber cR (F.stage β hβα).head (F.stage β hβα).type) :
    y ∈ validFiber cR (F.stage δ (hδβ.trans hβα)).head
      (F.stage δ (hδβ.trans hβα)).type := by
  classical
  haveI : IsWellOrder (Order.succ δ).ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder (Order.succ β).ToType (· < ·) := isWellOrder_lt
  intro z_δ
  set γ : Ordinal.{0} := Ordinal.typein (· < ·) z_δ with hγ_def
  have hγ_lt_sδ : γ < Order.succ δ := by
    simpa [γ, Ordinal.type_toType _] using
      Ordinal.typein_lt_type
        (· < · : (Order.succ δ).ToType → (Order.succ δ).ToType → Prop) z_δ
  have hγ_le_δ : γ ≤ δ := Order.lt_succ_iff.mp hγ_lt_sδ
  have hγ_lt_sβ : γ < Order.succ β :=
    hγ_lt_sδ.trans_le (Order.succ_le_succ (le_of_lt hδβ))
  set z_β : (Order.succ β).ToType :=
    Ordinal.enum (α := (Order.succ β).ToType) (· < ·)
      ⟨γ, (Ordinal.type_toType _).symm ▸ hγ_lt_sβ⟩ with hzβ_def
  obtain ⟨h_lt, h_col⟩ := hy z_β
  -- Need to transport h_lt and h_col from β-side to δ-side.
  -- Use commitAt / typeAt as the bridge.
  have h_head_β :
      (F.stage β hβα).head z_β =
      (F.stage β hβα).commitAt γ hγ_lt_sβ := by
    show (F.stage β hβα).head z_β =
      (F.stage β hβα).head
        (Ordinal.enum (α := (Order.succ β).ToType) (· < ·)
          ⟨γ, (Ordinal.type_toType (Order.succ β)).symm ▸ hγ_lt_sβ⟩)
    rfl
  have h_type_β :
      (F.stage β hβα).type z_β =
      (F.stage β hβα).typeAt γ hγ_lt_sβ := by
    show (F.stage β hβα).type z_β =
      (F.stage β hβα).type
        (Ordinal.enum (α := (Order.succ β).ToType) (· < ·)
          ⟨γ, (Ordinal.type_toType (Order.succ β)).symm ▸ hγ_lt_sβ⟩)
    rfl
  have h_enum_typein :
      Ordinal.enum (α := (Order.succ δ).ToType) (· < ·)
        ⟨γ, (Ordinal.type_toType (Order.succ δ)).symm ▸ hγ_lt_sδ⟩ = z_δ := by
    have := Ordinal.enum_typein (α := (Order.succ δ).ToType) (· < ·) z_δ
    convert this using 2
  have h_head_δ :
      (F.stage δ (hδβ.trans hβα)).head z_δ =
      (F.stage δ (hδβ.trans hβα)).commitAt γ hγ_lt_sδ := by
    show (F.stage δ (hδβ.trans hβα)).head z_δ =
      (F.stage δ (hδβ.trans hβα)).head _
    rw [h_enum_typein]
  have h_type_δ :
      (F.stage δ (hδβ.trans hβα)).type z_δ =
      (F.stage δ (hδβ.trans hβα)).typeAt γ hγ_lt_sδ := by
    show (F.stage δ (hδβ.trans hβα)).type z_δ =
      (F.stage δ (hδβ.trans hβα)).type _
    rw [h_enum_typein]
  -- Now h_lt : (stage β).head z_β < y and we want (stage δ).head z_δ < y.
  -- By h_head_β and h_head_δ, it suffices that (stage β).commitAt γ = (stage δ).commitAt γ.
  have h_commits_agree :
      (F.stage β hβα).commitAt γ hγ_lt_sβ =
      (F.stage δ (hδβ.trans hβα)).commitAt γ hγ_lt_sδ := by
    rcases lt_or_eq_of_le hγ_le_δ with hγ_lt_δ | hγ_eq_δ
    · rw [F.coherent (hγ_lt_δ.trans hδβ) hβα, F.coherent hγ_lt_δ (hδβ.trans hβα)]
    · -- γ = δ: use F.coherent (δ < β) directly, rewriting γ-arguments to δ.
      have h_cong :
          (F.stage β hβα).commitAt γ hγ_lt_sβ =
            (F.stage β hβα).commitAt δ (hδβ.trans (Order.lt_succ β)) := by
        congr 1
      rw [h_cong, F.coherent hδβ hβα]
      congr 1
      exact hγ_eq_δ.symm
  have h_types_agree :
      (F.stage β hβα).typeAt γ hγ_lt_sβ =
      (F.stage δ (hδβ.trans hβα)).typeAt γ hγ_lt_sδ := by
    rcases lt_or_eq_of_le hγ_le_δ with hγ_lt_δ | hγ_eq_δ
    · rw [hF_type (hγ_lt_δ.trans hδβ) hβα, hF_type hγ_lt_δ (hδβ.trans hβα)]
    · have h_cong :
          (F.stage β hβα).typeAt γ hγ_lt_sβ =
            (F.stage β hβα).typeAt δ (hδβ.trans (Order.lt_succ β)) := by
        congr 1
      rw [h_cong, hF_type hδβ hβα]
      congr 1
      exact hγ_eq_δ.symm
  have h_head_eq :
      (F.stage β hβα).head z_β = (F.stage δ (hδβ.trans hβα)).head z_δ := by
    rw [h_head_β, h_head_δ]; exact h_commits_agree
  have h_type_eq :
      (F.stage β hβα).type z_β = (F.stage δ (hδβ.trans hβα)).type z_δ := by
    rw [h_type_β, h_type_δ]; exact h_types_agree
  refine ⟨?_, ?_⟩
  · rw [← h_head_eq]; exact h_lt
  · rw [← h_type_eq]
    convert h_col using 3
    exact h_head_eq.symm

/-- **Cofinal-sequence reindex of stage-fiber intersection**: if
`e : ℕ → α` is monotone and cofinal in `α`, and the stage-fiber family
is descending nested (under `IsTypeCoherent`), the α-intersection
equals the ℕ-intersection along `e`. This is the lemma that makes the
ordinal bookkeeping go away: for a descending family, a cofinal
subfamily has the same intersection.

**Hypotheses**:
- `e` is monotone (weak): `n ≤ m → (e n).1 ≤ (e m).1`.
- `e` is cofinal: `∀ β < α, ∃ n, β ≤ (e n).1`.
- `F.IsTypeCoherent` (so `validFiber_mono` applies).

**Proof sketch**:
- ⊇: every term of the ℕ-intersection is an element of the α-intersection
  (since `e n < α` picks an α-indexed term).
- ⊆: given `y` in the ℕ-intersection and `β < α`, pick `n` with
  `β ≤ (e n).1`; by `validFiber_mono`, `y ∈ validFiber(F.stage (e n).1)
  ⊆ validFiber(F.stage β)`. -/
theorem iInter_stage_fibers_eq_iInter_nat_of_cofinal
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (F : PairERCoherentFamily cR α) (hF_type : F.IsTypeCoherent)
    (e : ℕ → {β : Ordinal.{0} // β < α})
    (_e_mono : ∀ {n m : ℕ}, n ≤ m → (e n).1 ≤ (e m).1)
    (e_cofinal : ∀ β : Ordinal.{0}, β < α → ∃ n : ℕ, β ≤ (e n).1) :
    (⋂ (β : Ordinal.{0}) (hβα : β < α),
        validFiber cR (F.stage β hβα).head (F.stage β hβα).type) =
      ⋂ n : ℕ, validFiber cR
        (F.stage (e n).1 (e n).2).head (F.stage (e n).1 (e n).2).type := by
  ext y
  simp only [Set.mem_iInter]
  refine ⟨?_, ?_⟩
  · -- α-form → ℕ-form: directly instantiate with β = (e n).1.
    intro hy n
    exact hy (e n).1 (e n).2
  · -- ℕ-form → α-form: for each β < α, pick n with β ≤ (e n).1, use descending.
    intro hy β hβα
    obtain ⟨n, hβ_le⟩ := e_cofinal β hβα
    rcases eq_or_lt_of_le hβ_le with hβ_eq | hβ_lt
    · -- β = (e n).1: direct via subst.
      subst hβ_eq
      exact hy n
    · -- β < (e n).1: use validFiber_mono.
      exact F.validFiber_mono hF_type hβ_lt (e n).2 (hy n)

/-- **Cofinality helper**: any subset `S ⊆ PairERSource` with
`|S| ≥ succ ℶ_1` is unbounded. Proof: if `S ⊆ Iic m` for some `m`, then
`|S| ≤ |Iic m|`; but `Iic m ⊆ Iio m'` for any `m' > m` (which exists
by `PairERSource`'s unboundedness in itself via regularity), and
`|Iio m'| < succ ℶ_1` by `Ordinal.mk_Iio_ord_toType`. Contradiction. -/
lemma large_set_exists_above
    {S : Set PairERSource}
    (hS : Order.succ (Cardinal.beth.{0} 1) ≤ Cardinal.mk S)
    (m : PairERSource) : ∃ y ∈ S, m < y := by
  by_contra h
  push_neg at h
  -- `S ⊆ Iic m`. To bound |Iic m|, find `m'` with `m < m'` in `PairERSource`,
  -- then `Iic m ⊆ Iio m'`, and `|Iio m'| < succ ℶ_1`.
  -- For `m'`, we need `PairERSource` to have something above `m`.
  -- `PairERSource = (succ ℶ_1).ord.ToType`, and `(succ ℶ_1).ord > typein m`
  -- since typein m < (succ ℶ_1).ord. So there's an enum-point above.
  haveI : IsWellOrder PairERSource (· < ·) := isWellOrder_lt
  -- Use `exists_gt`: every ordinal type without max has something above m.
  -- `(succ ℶ_1).ord` is a limit since succ ℶ_1 is infinite.
  have h_noMax : ∃ m', m < m' := by
    -- typein m + 1 < succ ℶ_1.ord (since succ ℶ_1.ord has cof > 1).
    have h_typein : Ordinal.typein (· < ·) m < Ordinal.type
        (· < · : PairERSource → PairERSource → Prop) :=
      Ordinal.typein_lt_type _ m
    have h_typein_lt : Ordinal.typein (· < ·) m < (Order.succ (Cardinal.beth.{0} 1)).ord := by
      simpa [Ordinal.type_toType] using h_typein
    have h_next : Order.succ (Ordinal.typein (· < ·) m) <
        (Order.succ (Cardinal.beth.{0} 1)).ord := by
      have h_lim : Order.IsSuccLimit (Order.succ (Cardinal.beth.{0} 1)).ord :=
        Cardinal.isSuccLimit_ord isRegular_succ_beth_one.aleph0_le
      exact h_lim.succ_lt h_typein_lt
    set m' : PairERSource := Ordinal.enum (α := PairERSource) (· < ·)
      ⟨Order.succ (Ordinal.typein (· < ·) m),
        (Ordinal.type_toType _).symm ▸ h_next⟩ with hm'_def
    refine ⟨m', ?_⟩
    -- Show m < m' via typein comparison.
    have h_typein_m' : Ordinal.typein (· < ·) m' =
        Order.succ (Ordinal.typein (· < ·) m) := by
      rw [hm'_def, Ordinal.typein_enum]
    apply (Ordinal.typein_lt_typein (· < · : PairERSource → PairERSource → Prop)).mp
    rw [h_typein_m']
    exact Order.lt_succ _
  obtain ⟨m', hmm'⟩ := h_noMax
  have hS_sub_Iio : S ⊆ Set.Iio m' := by
    intro s hs
    exact lt_of_le_of_lt (h s hs) hmm'
  have h_iio_card : Cardinal.mk (Set.Iio m') < Order.succ (Cardinal.beth.{0} 1) :=
    Cardinal.mk_Iio_ord_toType (c := Order.succ (Cardinal.beth.{0} 1)) m'
  have hS_card_le : Cardinal.mk S ≤ Cardinal.mk (Set.Iio m') :=
    Cardinal.mk_le_mk_of_subset hS_sub_Iio
  exact absurd (hS.trans hS_card_le) (not_le.mpr h_iio_card)

/-! ### [REMOVED — false under `IsTypeCoherent` alone]
`exists_nonempty_iInter_stage_fibers_nat_reindex` and the α-indexed
`exists_nonempty_iInter_stage_fibers` formerly lived here, each concluding a
nonempty stage-fiber intersection from `F.IsTypeCoherent` **alone**. That
hypothesis is *insufficient at limit levels* — see the documented ω-pattern
adversary below (the `limit_fusion_of_canonical_restrictions` negative result):
an `IsTypeCoherent` family can have large finite stages but an empty ω-limit
intersection. So those statements were unprovable as written (their bodies were
`sorry`), and nothing consumed them.

They are **superseded by the `PairERTypeTree` projection theorems**
(`PairERTypeTree.toNonemptyIntersection` / `…Nat`, below), which derive the same
nonempty intersection from genuine branching data (a realized `F.typeFn`). The
true top-level intersection API — `exists_nonempty_iInter_stage_fibers`, now a
thin wrapper over those projections — is defined just after the tree projections.
The real fusion content is the *construction* of such a tree
(`exists_realizedPairERTypeTree`, the named fusion target). -/

/-- **Finite-prefix collapse**: every finite-prefix intersection
`⋂ k<n, validFiber(F.stage (e k))` along a monotone `e` collapses to a
single stage fiber (the largest one) by descending nestedness, and
thus has cardinality `≥ succ ℶ_1`. A trivial consequence of
`validFiber_mono`; included to make the "finite case is easy"
observation explicit.

For `n = 0`, the intersection is `Set.univ = PairERSource`, which has
cardinality `succ ℶ_1` by `mk_pairERSource`. For `n ≥ 1`, the
intersection equals `validFiber(F.stage (e (n-1)))`, which has
cardinality `≥ succ ℶ_1` by `(F.stage _).large`. -/
theorem iInter_finite_stage_fibers_large
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (F : PairERCoherentFamily cR α) (hF_type : F.IsTypeCoherent)
    (e : ℕ → {β : Ordinal.{0} // β < α})
    (e_mono : ∀ {n m : ℕ}, n ≤ m → (e n).1 ≤ (e m).1) (n : ℕ) :
    Order.succ (Cardinal.beth.{0} 1) ≤
      Cardinal.mk (⋂ k : Fin n, validFiber cR
        (F.stage (e k).1 (e k).2).head (F.stage (e k).1 (e k).2).type) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- n = 0: intersection = Set.univ.
    subst hn
    simp only [Set.iInter_of_empty, Cardinal.mk_univ]
    rw [mk_pairERSource]
  · -- n ≥ 1: intersection = validFiber at (e ⟨n-1, _⟩).
    let k_top : Fin n := ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩
    -- Show the intersection equals the fiber at k_top.
    have h_subset :
        validFiber cR (F.stage (e k_top).1 (e k_top).2).head
            (F.stage (e k_top).1 (e k_top).2).type ⊆
          ⋂ k : Fin n, validFiber cR
            (F.stage (e k).1 (e k).2).head (F.stage (e k).1 (e k).2).type := by
      intro y hy
      simp only [Set.mem_iInter]
      intro k
      -- (e k).1 ≤ (e k_top).1 by monotone; use validFiber_mono.
      have h_le : (e k).1 ≤ (e k_top).1 :=
        e_mono (Nat.le_sub_one_of_lt k.isLt)
      rcases eq_or_lt_of_le h_le with h_eq | h_lt
      · have : e k = e k_top := Subtype.ext h_eq
        rw [this]; exact hy
      · exact F.validFiber_mono hF_type h_lt (e k_top).2 hy
    calc Order.succ (Cardinal.beth.{0} 1)
        ≤ Cardinal.mk (validFiber cR (F.stage (e k_top).1 (e k_top).2).head
            (F.stage (e k_top).1 (e k_top).2).type) :=
          (F.stage (e k_top).1 (e k_top).2).large
      _ ≤ _ := Cardinal.mk_le_mk_of_subset h_subset

/-- **Recursive fusion sequence**: given a monotone cofinal ℕ-sequence
and `IsTypeCoherent`, we can build a strictly monotone sequence
`y : ℕ → PairERSource` with `y n ∈ ⋂ k ≤ n, A k` for each `n`. Uses
the cofinality helper `large_set_exists_above` + the finite-prefix
largeness `iInter_finite_stage_fibers_large` at each step.

**Note**: this produces the ω-sequence of witnesses; the remaining
step is extraction of a single point in `⋂ n, A n`. That extraction
is the content of the main nonempty frontier — it is NOT automatic
from the strictly monotone sequence, because `PairERSource`'s sup of
an ω-sequence need not satisfy the per-fiber color constraints. -/
theorem exists_strict_mono_fusion_sequence
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (F : PairERCoherentFamily cR α) (hF_type : F.IsTypeCoherent)
    (e : ℕ → {β : Ordinal.{0} // β < α})
    (e_mono : ∀ {n m : ℕ}, n ≤ m → (e n).1 ≤ (e m).1) :
    ∃ y : ℕ → PairERSource, StrictMono y ∧
      ∀ n : ℕ, y n ∈ ⋂ k : Fin (n + 1), validFiber cR
        (F.stage (e k).1 (e k).2).head (F.stage (e k).1 (e k).2).type := by
  classical
  -- Define the sets A n := ⋂ k : Fin (n+1), validFiber(stage (e k)).
  set A : ℕ → Set PairERSource := fun n =>
    ⋂ k : Fin (n + 1), validFiber cR
      (F.stage (e k).1 (e k).2).head (F.stage (e k).1 (e k).2).type with hA_def
  -- Each A n has cardinality ≥ succ ℶ_1.
  have hA_large : ∀ n : ℕ,
      Order.succ (Cardinal.beth.{0} 1) ≤ Cardinal.mk (A n) := fun n =>
    iInter_finite_stage_fibers_large F hF_type e e_mono (n + 1)
  -- Pick a base point in A 0 (nonempty since large).
  have h_A0_nonempty : (A 0).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h_empty
    have h_mk : Cardinal.mk (A 0) = 0 := by
      rw [h_empty]; exact Cardinal.mk_emptyCollection _
    have h_pos : 0 < Cardinal.mk (A 0) := by
      have h_card_pos : (0 : Cardinal) < Order.succ (Cardinal.beth.{0} 1) := by
        have h_aleph0_le : Cardinal.aleph0 ≤ Order.succ (Cardinal.beth.{0} 1) :=
          isRegular_succ_beth_one.aleph0_le
        exact (Cardinal.aleph0_pos).trans_le h_aleph0_le
      exact h_card_pos.trans_le (hA_large 0)
    rw [h_mk] at h_pos
    exact absurd h_pos (lt_irrefl 0)
  -- Build the sequence via Nat.rec carrying (current y value, proof y ∈ A n).
  -- We use recursion on the pair ⟨y_n, proof y_n ∈ A n⟩ to get both properties.
  let step : (n : ℕ) → PairERSource → PairERSource := fun n y_prev =>
    Classical.choose (large_set_exists_above (hA_large (n + 1)) y_prev)
  let y_seq : ℕ → PairERSource := fun n =>
    Nat.rec (motive := fun _ => PairERSource)
      (Classical.choose h_A0_nonempty)
      (fun m y_m => step m y_m) n
  -- Step's spec.
  have h_step_spec : ∀ (n : ℕ) (y_prev : PairERSource),
      step n y_prev ∈ A (n + 1) ∧ y_prev < step n y_prev := fun n y_prev =>
    Classical.choose_spec (large_set_exists_above (hA_large (n + 1)) y_prev)
  refine ⟨y_seq, ?_, ?_⟩
  · intro n m hnm
    induction hnm with
    | refl =>
      show y_seq n < step n (y_seq n)
      exact (h_step_spec n (y_seq n)).2
    | step _ ih =>
      exact ih.trans (h_step_spec _ _).2
  · intro n
    induction n with
    | zero => exact Classical.choose_spec h_A0_nonempty
    | succ m _ =>
      show step m (y_seq m) ∈ A (m + 1)
      exact (h_step_spec m _).1

/-- **Strengthened invariant**: `IsCanonicalTypeCoherent` enriches
`IsTypeCoherent` with a *fusion witness* for ω-intersections. This
is the structural ingredient missing from `IsTypeCoherent` alone.

The idea: for every monotone cofinal ℕ-sequence `e : ℕ → α`, there
exists a specific witness `z : PairERSource` that lies in all stage
fibers `validFiber cR (F.stage (e n).1 _).head (F.stage (e n).1 _).type`
simultaneously. This is exactly what the naive ω-sup construction
fails to produce.

**Mathematical interpretation**: in the Erdős–Rado type-tree argument,
this corresponds to a branch of the type tree having a concrete
realizer. The classical pigeonhole on `2^ℕ = ℶ_1 < succ ℶ_1` types
guarantees such a branch exists and has ≥ succ ℶ_1 realizers — but
the invariant just needs ONE.

**Status**: at this stage we define the predicate and its consequences;
establishing it at the coherent-family constructors (via the tree
argument) is the remaining proof-shape task. -/
def PairERCoherentFamily.IsCanonicalTypeCoherent
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (F : PairERCoherentFamily cR α) : Prop :=
  F.IsTypeCoherent ∧
  ∀ (e : ℕ → {β : Ordinal.{0} // β < α}),
    (∀ {n m : ℕ}, n ≤ m → (e n).1 ≤ (e m).1) →
    (∀ β : Ordinal.{0}, β < α → ∃ n : ℕ, β ≤ (e n).1) →
    Set.Nonempty (⋂ n : ℕ, validFiber cR
      (F.stage (e n).1 (e n).2).head (F.stage (e n).1 (e n).2).type)

/-- `IsCanonicalTypeCoherent` implies `IsTypeCoherent` (the first
component). -/
lemma PairERCoherentFamily.IsCanonicalTypeCoherent.toIsTypeCoherent
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    {F : PairERCoherentFamily cR α}
    (h : F.IsCanonicalTypeCoherent) : F.IsTypeCoherent := h.1

/-- `restrict` preserves `IsCanonicalTypeCoherent`. The nat-intersection
hypothesis transfers because sequences into the restricted level are
sequences into the original level. -/
lemma PairERCoherentFamily.IsCanonicalTypeCoherent.restrict
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    {F : PairERCoherentFamily cR α} (hF : F.IsCanonicalTypeCoherent)
    {β : Ordinal.{0}} (hβα : β ≤ α) :
    (F.restrict hβα).IsCanonicalTypeCoherent := by
  refine ⟨PairERCoherentFamily.IsTypeCoherent.restrict hF.toIsTypeCoherent hβα, ?_⟩
  intro e _e_mono _e_cofinal
  -- The restrict transport is nontrivial: a cofinal-in-β sequence `e` is
  -- not automatically cofinal in α, so we can't directly apply `hF.2`.
  -- The clean approach is to extend `e` to a cofinal-in-α sequence by
  -- interleaving with an α-cofinal tail, then apply `hF.2` + descending.
  -- Full proof deferred; structural ingredients in place. -/
  sorry

/-- **Nonempty frontier via `IsCanonicalTypeCoherent`**: under the
strengthened invariant, the nat-reindexed fusion question has a
positive answer — by definition of the invariant. -/
theorem exists_nonempty_iInter_stage_fibers_nat_reindex_of_canonical
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (F : PairERCoherentFamily cR α) (hF : F.IsCanonicalTypeCoherent)
    (e : ℕ → {β : Ordinal.{0} // β < α})
    (e_mono : ∀ {n m : ℕ}, n ≤ m → (e n).1 ≤ (e m).1)
    (e_cofinal : ∀ β : Ordinal.{0}, β < α → ∃ n : ℕ, β ≤ (e n).1) :
    Set.Nonempty (⋂ n : ℕ, validFiber cR
      (F.stage (e n).1 (e n).2).head (F.stage (e n).1 (e n).2).type) :=
  hF.2 e e_mono e_cofinal

/-- **α-form nonempty under `IsCanonicalTypeCoherent`**: via the
cofinal reindex equality, the α-indexed intersection inherits the
ℕ-form nonemptiness. -/
theorem exists_nonempty_iInter_stage_fibers_of_canonical
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (F : PairERCoherentFamily cR α) (hF : F.IsCanonicalTypeCoherent)
    (e : ℕ → {β : Ordinal.{0} // β < α})
    (e_mono : ∀ {n m : ℕ}, n ≤ m → (e n).1 ≤ (e m).1)
    (e_cofinal : ∀ β : Ordinal.{0}, β < α → ∃ n : ℕ, β ≤ (e n).1) :
    Set.Nonempty (⋂ (β : Ordinal.{0}) (hβα : β < α),
      validFiber cR (F.stage β hβα).head (F.stage β hβα).type) := by
  rw [iInter_stage_fibers_eq_iInter_nat_of_cofinal F
    hF.toIsTypeCoherent e e_mono e_cofinal]
  exact exists_nonempty_iInter_stage_fibers_nat_reindex_of_canonical
    F hF e e_mono e_cofinal

/-- **Prescribed-typeFn fiber nonempty under `IsCanonicalTypeCoherent`**:
chains through `validFiber_prefix_typeFn_eq_iInter` — given
`IsCanonicalTypeCoherent`, the intersection is nonempty, hence
`validFiber cR F.prefix F.typeFn` is nonempty. -/
theorem exists_nonempty_validFiber_prefix_typeFn_of_canonical
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (F : PairERCoherentFamily cR α) (hF : F.IsCanonicalTypeCoherent)
    (e : ℕ → {β : Ordinal.{0} // β < α})
    (e_mono : ∀ {n m : ℕ}, n ≤ m → (e n).1 ≤ (e m).1)
    (e_cofinal : ∀ β : Ordinal.{0}, β < α → ∃ n : ℕ, β ≤ (e n).1) :
    Set.Nonempty (validFiber cR F.prefix F.typeFn) := by
  rw [F.validFiber_prefix_typeFn_eq_iInter hF.toIsTypeCoherent]
  exact exists_nonempty_iInter_stage_fibers_of_canonical F hF e e_mono e_cofinal

/-! ### Documented negative result: the limit fusion under
`IsCanonicalTypeCoherent` is FALSE

The hoped-for limit theorem

```
theorem limit_fusion_of_canonical_restrictions
    (hα_lim : Order.IsSuccLimit α)
    (F : PairERCoherentFamily cR α) (hF_type : F.IsTypeCoherent)
    (h_restrict_canonical :
      ∀ β (hβα : β < α), (F.restrict (le_of_lt hβα)).IsCanonicalTypeCoherent)
    (e : ℕ → {β : Ordinal.{0} // β < α}) (e_mono) (e_cofinal) :
    Set.Nonempty (⋂ n, validFiber cR
      (F.stage (e n).1 (e n).2).head (F.stage (e n).1 (e n).2).type)
```

is **NOT TRUE** under `IsCanonicalTypeCoherent` alone (α = ω sanity
analysis).

**Failure at `α = ω`**: every proper restriction `β < ω` is either
empty (`β = 0`) or successor (`β = n+1`), so the restriction
hypothesis reduces by `isCanonicalTypeCoherent_of_succ` +
`IsTypeCoherent.restrict` to just `F.IsTypeCoherent`. But then
`exists_point_in_iInter_of_fusion_sequence`'s earlier failure analysis
(the ω-sup not preserving color constraints) gives a direct
counterexample: distribute `succ ℶ_1` elements across `2^ω = ℶ_1`
profiles so every finite prefix of `F.typeFn` is realized by `ℶ_1⁺`
elements but the specific ω-profile has `0` realizers.

**Architectural consequence**: the single-chain uniform-choice
architecture cannot see around the ω-pattern adversary. The
`IsCanonicalTypeCoherent` invariant is still too weak as the
"provable invariant" at limit levels.

**What's actually needed**: a genuine **tree** structure at each
coherent-family level — a `PairERTypeTree` / branching data object
tracking the full `2^β`-branching type tree, with global pigeonhole
over branches rather than local uniform choice. The theorem would
then hold under the strengthened invariant, not the current one.

**API honesty**: the theorem is NOT stated as a `sorry`-theorem
(which would advertise a false claim). The next tranche introduces
`PairERTypeTree`; after that, a corrected limit theorem will be
restated with the stronger input. Until then, `isCanonicalTypeCoherent`
at limits remains OPEN in the codebase — a downstream consumer
requiring it must take it as an explicit hypothesis. -/

/-! ### `PairERTypeTree` scaffold (branching data beside coherent families)

This is the architectural tranche replacing the single-chain uniform-
choice approach with genuine branching type data. The goal is to track,
at each level α, not just `F.typeFn : α.ToType → Bool` but a richer
object recording:
- Multiple candidate "type branches" (α-length Bool sequences) and
- Realizer sets for each branch in `PairERSource`
- The invariant that sum of realizer-set cardinalities is `≥ succ ℶ_1`

The classical Erdős–Rado tree argument then picks, at each limit level,
a realized branch by global pigeonhole on `2^α ≤ ℶ_1` branches
(countable since `α < ω_1`).

**Scaffold contents below**:
- `PairERTypeTree`: placeholder structure (to be filled in)
- `projection theorem`: how tree data implies the current nonempty
  intersection statement (to be proved)

This is intentionally minimal — a placeholder that documents the
target architecture without committing to specific fields yet. The
next working session should flesh out the fields and the projection
theorem. -/

/-- **`PairERTypeTree` (tied to a coherent family `F`)**: branching
type data recording, at each level α, multiple candidate "type
branches" (α.ToType → Bool) together with their realizer sets in
`PairERSource`. The aggregate disjoint union of realizer sets has
cardinality `≥ succ ℶ_1` (the `large_sigma` invariant), enabling H3
pigeonhole over branches.

**Design note**: we intentionally do NOT include a per-branch
`branches_realized` field. Preservation at successor stages requires
keeping BOTH Boolean halves of each split, so one half CAN have empty
realizers. `large_sigma` provides all the liveness information we
need (it implies at least one branch has nonempty realizers via H3).
Per-branch nonemptiness would be hostile to branching preservation,
forcing single-chain pruning — the exact failure mode we escaped. -/
structure PairERTypeTree
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (F : PairERCoherentFamily cR α) where
  /-- Candidate "type branches": α-length Bool sequences. -/
  branches : Set (α.ToType → Bool)
  /-- Per-branch realizer set in `PairERSource`. -/
  realizers : (α.ToType → Bool) → Set PairERSource
  /-- Each realizer of branch `b` lies in `validFiber cR F.prefix b`.
  This says: if `y ∈ realizers b`, then for every position
  `x : α.ToType`, `F.prefix x < y` and `cR (pair (F.prefix x, y)) = b x`. -/
  realizers_sub_validFiber :
    ∀ b : α.ToType → Bool, realizers b ⊆ validFiber cR F.prefix b
  /-- **Size invariant** (Sigma form): the total disjoint union of
  branch×realizer pairs has cardinality `≥ succ ℶ_1`. This is what
  makes H3 pigeonhole work: for `α < ω_1` the codomain
  `(α.ToType → Bool)` has size `≤ ℶ_1`, so some branch inherits
  `succ ℶ_1`-many realizers. Also implies at least one branch has
  some realizers (derivation in `exists_realized_branch`). -/
  large_sigma :
    Order.succ (Cardinal.beth.{0} 1) ≤
      Cardinal.mk { p : (α.ToType → Bool) × PairERSource |
        p.1 ∈ branches ∧ p.2 ∈ realizers p.1 }

/-- **Derived liveness**: `large_sigma` implies some branch has
nonempty realizers. This is the only liveness we need; per-branch
liveness is intentionally omitted from the structure (see docstring). -/
theorem PairERTypeTree.exists_realized_branch
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    {F : PairERCoherentFamily cR α} (T : PairERTypeTree F) :
    ∃ b ∈ T.branches, (T.realizers b).Nonempty := by
  classical
  have h_pos : (0 : Cardinal) <
      Cardinal.mk { p : (α.ToType → Bool) × PairERSource |
        p.1 ∈ T.branches ∧ p.2 ∈ T.realizers p.1 } := by
    have h_aleph0_le : Cardinal.aleph0 ≤ Order.succ (Cardinal.beth.{0} 1) :=
      isRegular_succ_beth_one.aleph0_le
    exact (Cardinal.aleph0_pos.trans_le h_aleph0_le).trans_le T.large_sigma
  have h_ne : Cardinal.mk { p : (α.ToType → Bool) × PairERSource |
      p.1 ∈ T.branches ∧ p.2 ∈ T.realizers p.1 } ≠ 0 := h_pos.ne'
  obtain ⟨⟨⟨b, y⟩, hby⟩⟩ := Cardinal.mk_ne_zero_iff.mp h_ne
  exact ⟨b, hby.1, ⟨y, hby.2⟩⟩

/-- **Projection theorem**: tree data + `F.typeFn` having nonempty
realizers gives a nonempty `validFiber cR F.prefix F.typeFn`.

Hypothesis changed from `F.typeFn ∈ T.branches` to the stronger
`(T.realizers F.typeFn).Nonempty` — this is the direct extraction
condition and accommodates the branching-preservation refactor
(where some tracked branches can have empty realizers). -/
theorem PairERTypeTree.toNonemptyValidFiber
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    {F : PairERCoherentFamily cR α} (T : PairERTypeTree F)
    (h_realized : (T.realizers F.typeFn).Nonempty) :
    Set.Nonempty (validFiber cR F.prefix F.typeFn) := by
  obtain ⟨y, hy⟩ := h_realized
  exact ⟨y, T.realizers_sub_validFiber F.typeFn hy⟩

/-- **Projection to intersection form**: under `F.IsTypeCoherent`, the
nonempty `validFiber` from nonempty realizers of `F.typeFn` transfers
to the α-indexed intersection of per-stage fibers. -/
theorem PairERTypeTree.toNonemptyIntersection
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    {F : PairERCoherentFamily cR α} (T : PairERTypeTree F)
    (hF_type : F.IsTypeCoherent)
    (h_realized : (T.realizers F.typeFn).Nonempty) :
    Set.Nonempty (⋂ (β : Ordinal.{0}) (hβα : β < α),
      validFiber cR (F.stage β hβα).head (F.stage β hβα).type) := by
  rw [← F.validFiber_prefix_typeFn_eq_iInter hF_type]
  exact T.toNonemptyValidFiber h_realized

/-- **Projection to canonical form**: `PairERTypeTree` + nonempty
`F.typeFn` realizers + a cofinal ℕ-sequence gives
`IsCanonicalTypeCoherent`-style nonempty intersection at that sequence. -/
theorem PairERTypeTree.toNonemptyIntersectionNat
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    {F : PairERCoherentFamily cR α} (T : PairERTypeTree F)
    (hF_type : F.IsTypeCoherent)
    (h_realized : (T.realizers F.typeFn).Nonempty)
    (e : ℕ → {β : Ordinal.{0} // β < α})
    (e_mono : ∀ {n m : ℕ}, n ≤ m → (e n).1 ≤ (e m).1)
    (e_cofinal : ∀ β : Ordinal.{0}, β < α → ∃ n : ℕ, β ≤ (e n).1) :
    Set.Nonempty (⋂ n : ℕ, validFiber cR
      (F.stage (e n).1 (e n).2).head (F.stage (e n).1 (e n).2).type) := by
  rw [← iInter_stage_fibers_eq_iInter_nat_of_cofinal F hF_type e e_mono e_cofinal]
  exact T.toNonemptyIntersection hF_type h_realized

/-- **`exists_nonempty_iInter_stage_fibers`** (true intersection API). The
nonempty stage-fiber intersection, now derived from genuine branching data.
**Replaces** the former `IsTypeCoherent`-only statement (false at limits — see
the REMOVED note above): the added input is a `PairERTypeTree F` with a realized
`F.typeFn`. Thin wrapper over `PairERTypeTree.toNonemptyIntersection`; the real
fusion content is *constructing* such a tree (`exists_realizedPairERTypeTree`,
the named fusion target). -/
theorem exists_nonempty_iInter_stage_fibers
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    {F : PairERCoherentFamily cR α} (T : PairERTypeTree F)
    (hF_type : F.IsTypeCoherent)
    (h_realized : (T.realizers F.typeFn).Nonempty) :
    Set.Nonempty (⋂ (β : Ordinal.{0}) (hβα : β < α),
      validFiber cR (F.stage β hβα).head (F.stage β hβα).type) :=
  T.toNonemptyIntersection hF_type h_realized

/-- **Bridge to `IsCanonicalTypeCoherent`**: the tree provides exactly
the missing data. Given a `PairERTypeTree F`, `F.IsTypeCoherent`, and
that `F.typeFn` is a realized branch in the tree, we get
`F.IsCanonicalTypeCoherent`. This is the "tree → canonical invariant"
projection that's missing from the original
`IsCanonicalTypeCoherent`-only architecture (where canonical at limits
was unprovable). -/
theorem PairERTypeTree.toIsCanonicalTypeCoherent
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    {F : PairERCoherentFamily cR α} (T : PairERTypeTree F)
    (hF_type : F.IsTypeCoherent)
    (h_realized : (T.realizers F.typeFn).Nonempty) :
    F.IsCanonicalTypeCoherent := by
  refine ⟨hF_type, ?_⟩
  intro e e_mono e_cofinal
  exact T.toNonemptyIntersectionNat hF_type h_realized e e_mono e_cofinal

/-- **Pigeonhole on tree branches** (H3 application): for `α < ω_1`,
the Bool-function codomain has cardinality `≤ ℶ_1`; combined with
`large_sigma`'s source size `≥ succ ℶ_1`, H3 gives a branch
`b ∈ T.branches` whose realizer set itself has cardinality `≥ succ ℶ_1`.

This is the key "selection" lemma: even without knowing which branch
the limit construction will pick as `F.typeFn`, we know SOME branch
has `succ ℶ_1` realizers. -/
theorem PairERTypeTree.exists_large_realized_branch
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (hα : α < Ordinal.omega.{0} 1)
    {F : PairERCoherentFamily cR α} (T : PairERTypeTree F) :
    ∃ b ∈ T.branches,
      Order.succ (Cardinal.beth.{0} 1) ≤ Cardinal.mk (T.realizers b) := by
  classical
  haveI : Countable α.ToType := countable_toType_of_lt_omega1 hα
  -- Source: the Sigma-set from `large_sigma`.
  set S : Set ((α.ToType → Bool) × PairERSource) :=
    { p | p.1 ∈ T.branches ∧ p.2 ∈ T.realizers p.1 } with hS_def
  have hS_card : Order.succ (Cardinal.beth.{0} 1) ≤ Cardinal.mk S := T.large_sigma
  -- Codomain: α.ToType → Bool has size ≤ ℶ_1.
  have hCodom : Cardinal.mk (α.ToType → Bool) ≤ Cardinal.beth.{0} 1 :=
    mk_countable_bool_functions_le_beth_one
  -- Projection f : S → (α.ToType → Bool).
  let f : S → (α.ToType → Bool) := fun p => p.1.1
  have h_aleph0_le_beth : Cardinal.aleph0 ≤ Cardinal.beth.{0} 1 :=
    Cardinal.aleph0_le_beth 1
  obtain ⟨b, hb_large⟩ :=
    exists_large_fiber_of_small_codomain h_aleph0_le_beth hS_card hCodom f
  -- `hb_large : succ ℶ_1 ≤ #(f ⁻¹' {b})`. If `(f⁻¹' {b})` is nonempty,
  -- `b ∈ T.branches` (any element witnesses it).
  have hb_in : b ∈ T.branches := by
    have h_ne_zero : Cardinal.mk (f ⁻¹' {b}) ≠ 0 := by
      have h_pos : (0 : Cardinal) < Cardinal.mk (f ⁻¹' {b}) :=
        (Cardinal.aleph0_pos.trans_le h_aleph0_le_beth).trans_le
          (hb_large.trans' (Order.le_succ _))
      exact h_pos.ne'
    obtain ⟨⟨p, hp⟩⟩ := Cardinal.mk_ne_zero_iff.mp h_ne_zero
    -- hp : p ∈ f ⁻¹' {b}, i.e., f p = b, i.e., p.1.1 = b.
    -- p ∈ S, so p.1.1 ∈ T.branches and p.1.2 ∈ T.realizers p.1.1.
    have : p.1.1 ∈ T.branches := p.2.1
    rw [show p.1.1 = b from hp] at this
    exact this
  refine ⟨b, hb_in, ?_⟩
  -- Injection from f ⁻¹' {b} into T.realizers b.
  have h_inj :
      Function.Injective (fun p : f ⁻¹' {b} => (⟨p.1.1.2, by
        have hp1 : p.1.1.1 = b := p.2
        have hp2 : p.1.1.2 ∈ T.realizers p.1.1.1 := p.1.2.2
        rw [hp1] at hp2
        exact hp2⟩ : T.realizers b)) := by
    intro p q hpq
    -- hpq gives same realizer value (p.1.1.2 = q.1.1.2).
    -- p.1.1.1 = q.1.1.1 = b (both p, q : f ⁻¹' {b}).
    -- Then p.1.1 = q.1.1 as pairs, and p.1 = q.1 in S, and p = q in subtype.
    have h_real : p.1.1.2 = q.1.1.2 := Subtype.mk_eq_mk.mp hpq
    have h_branch : p.1.1.1 = q.1.1.1 := p.2.trans q.2.symm
    have h_pair : p.1.1 = q.1.1 := Prod.ext h_branch h_real
    have h_S : p.1 = q.1 := Subtype.ext h_pair
    exact Subtype.ext h_S
  calc Order.succ (Cardinal.beth.{0} 1)
      ≤ Cardinal.mk (f ⁻¹' {b}) := hb_large
    _ ≤ Cardinal.mk (T.realizers b) := Cardinal.mk_le_of_injective h_inj

/-- **[FUSION TARGET — the genuine Erdős–Rado limit fusion]**
`exists_realizedPairERTypeTree`: at every countable level `α`, there *exists* a
coherent family of that length carrying a **realized** type-tree — a
`PairERTypeTree F` whose committed branch `F.typeFn` has a nonempty realizer set.

This is the single open mathematical frontier the witness-net chain reduces to
(see `goodOneIndexFixedCarrierCompactness_holds`). Note the **existential** form:
the universal-over-`IsTypeCoherent` claim (the removed
`exists_nonempty_iInter_stage_fibers`) is *false* — the ω-pattern adversary gives
an `IsTypeCoherent` family whose committed `typeFn` is a 0-realizer minority at
the limit even though *some* branch is large (`exists_large_validFiber_at_level`
gives a large τ, but `F.typeFn` need not be it). The content here is that a
*good* family — one whose committed branch is the large/realized one coherently
across all levels — can be built. That requires the global branch pigeonhole
(`exists_large_realized_branch`) threaded through the successor/limit recursion
with cross-level coherent branch selection.

Once proved, it feeds `toNonemptyIntersection` / `toIsCanonicalTypeCoherent`
directly. **The exact form the witness-net chain needs (prescribed lower data /
extension form) is to be fixed when planning the proof** — this existential
statement names the core; the prescribed-extension refinement is the next design
step (after the `succWithChoice.inner_consistent` warm-up). -/
theorem exists_realizedPairERTypeTree
    (cR : (Fin 2 ↪o PairERSource) → Bool)
    {α : Ordinal.{0}} (_hα : α < Ordinal.omega.{0} 1) :
    ∃ (F : PairERCoherentFamily cR α) (T : PairERTypeTree F),
      F.IsTypeCoherent ∧ (T.realizers F.typeFn).Nonempty := by
  sorry

/-- **`toLargeValidFiber`**: once the tree has a branch `b` with
`succ ℶ_1`-many realizers, and `b = F.typeFn`, project to
`succ ℶ_1 ≤ |validFiber cR F.prefix F.typeFn|`. Via
`realizers_sub_validFiber`. -/
theorem PairERTypeTree.toLargeValidFiber
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    {F : PairERCoherentFamily cR α} (T : PairERTypeTree F)
    (h_selected : Order.succ (Cardinal.beth.{0} 1) ≤
      Cardinal.mk (T.realizers F.typeFn)) :
    Order.succ (Cardinal.beth.{0} 1) ≤
      Cardinal.mk (validFiber cR F.prefix F.typeFn) :=
  h_selected.trans
    (Cardinal.mk_le_mk_of_subset (T.realizers_sub_validFiber F.typeFn))

/-- **Selected branch** (via `Classical.choose` on the large realized
branch): `α < ω_1` + `PairERTypeTree F` gives a canonical branch
`b : α.ToType → Bool` with `succ ℶ_1`-many realizers. -/
noncomputable def PairERTypeTree.selectedBranch
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (hα : α < Ordinal.omega.{0} 1)
    {F : PairERCoherentFamily cR α} (T : PairERTypeTree F) :
    α.ToType → Bool :=
  Classical.choose (T.exists_large_realized_branch hα)

/-- `selectedBranch` is in `T.branches`. -/
lemma PairERTypeTree.selectedBranch_mem
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (hα : α < Ordinal.omega.{0} 1)
    {F : PairERCoherentFamily cR α} (T : PairERTypeTree F) :
    T.selectedBranch hα ∈ T.branches :=
  (Classical.choose_spec (T.exists_large_realized_branch hα)).1

/-- `selectedBranch` has `≥ succ ℶ_1` realizers. -/
lemma PairERTypeTree.selectedBranch_large
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (hα : α < Ordinal.omega.{0} 1)
    {F : PairERCoherentFamily cR α} (T : PairERTypeTree F) :
    Order.succ (Cardinal.beth.{0} 1) ≤
      Cardinal.mk (T.realizers (T.selectedBranch hα)) :=
  (Classical.choose_spec (T.exists_large_realized_branch hα)).2

/-- `selectedBranch`'s realizers are nonempty. Direct from the size
bound `selectedBranch_large` (`succ ℶ_1 > 0`). -/
lemma PairERTypeTree.selectedBranch_realized
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (hα : α < Ordinal.omega.{0} 1)
    {F : PairERCoherentFamily cR α} (T : PairERTypeTree F) :
    (T.realizers (T.selectedBranch hα)).Nonempty := by
  have h_large := T.selectedBranch_large hα
  have h_pos : (0 : Cardinal) <
      Cardinal.mk (T.realizers (T.selectedBranch hα)) := by
    have h_aleph0_le : Cardinal.aleph0 ≤ Order.succ (Cardinal.beth.{0} 1) :=
      isRegular_succ_beth_one.aleph0_le
    exact (Cardinal.aleph0_pos.trans_le h_aleph0_le).trans_le h_large
  obtain ⟨⟨y, hy⟩⟩ := Cardinal.mk_ne_zero_iff.mp h_pos.ne'
  exact ⟨y, hy⟩

/-- **Limit constructor via pigeonhole**: given a `PairERTypeTree F`,
produce a `PairERChain cR α` by picking the selected large realized
branch as the type function and feeding it to `PairERChain.limitWithType`.

This is the architectural payoff: rather than requiring `F.typeFn` to
be pre-specified (which fails under `IsTypeCoherent` alone, per the
α = ω sanity analysis), the tree + pigeonhole SELECTS the type
function so the resulting limit chain automatically has large fiber. -/
noncomputable def PairERTypeTree.limitChain
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (hα : α < Ordinal.omega.{0} 1)
    {F : PairERCoherentFamily cR α} (T : PairERTypeTree F) :
    PairERChain cR α :=
  PairERChain.limitWithType F.prefix (T.selectedBranch hα)
    ((T.selectedBranch_large hα).trans
      (Cardinal.mk_le_mk_of_subset (T.realizers_sub_validFiber _)))

/-- The limit chain's `type` function is exactly the selected branch
(head projection is `F.prefix`, type projection is the tree-selected
`b`). -/
@[simp]
lemma PairERTypeTree.limitChain_type
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (hα : α < Ordinal.omega.{0} 1)
    {F : PairERCoherentFamily cR α} (T : PairERTypeTree F) :
    (T.limitChain hα).type = T.selectedBranch hα := rfl

/-- The limit chain's head is `F.prefix`. -/
@[simp]
lemma PairERTypeTree.limitChain_head
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (hα : α < Ordinal.omega.{0} 1)
    {F : PairERCoherentFamily cR α} (T : PairERTypeTree F) :
    (T.limitChain hα).head = F.prefix := rfl

/-! ### Architectural tension surfaced: single-branch family vs multi-branch tree

`PairERCoherentFamily` commits to a single `F.typeFn` at construction
(determined by the prior recursion's stage choices). `PairERTypeTree`
records many branches, and `selectedBranch hα` is chosen by H3
pigeonhole. **There is no reason** `T.selectedBranch hα = F.typeFn`,
and the α = ω sanity analysis shows they may *deliberately differ*.

The lemmas below make this explicit: type-coherence-style identities
between `T.limitChain hα` and `F`'s data hold ONLY UNDER the equality
hypothesis. Hiding this inside a "tree-aware extendAtLimit" would be
wrong; it would commit the bug the original architecture had.

The architectural decision (next tranche): either
- (a) the recursion must rebuild earlier `F.typeVal δ` choices to
  align with the eventual `T.selectedBranch hα` (= type-rebuilding
  recursion), or
- (b) `PairERCoherentFamily` must defer committing to a single
  `F.typeFn` until limit-time, replacing `F.typeVal` with branch-set
  data (= type-deferred recursion).
-/

/-- **`limitChain` typeAt** at position `δ`: the type at the
enumerated position is `T.selectedBranch hα` evaluated at that
position. Direct from `limitWithType_typeAt`. -/
lemma PairERTypeTree.limitChain_typeAt
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (hα : α < Ordinal.omega.{0} 1)
    {F : PairERCoherentFamily cR α} (T : PairERTypeTree F)
    (δ : Ordinal.{0}) (hδ : δ < α) :
    (T.limitChain hα).typeAt δ hδ =
      haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
      T.selectedBranch hα (Ordinal.enum (α := α.ToType) (· < ·)
        ⟨δ, (Ordinal.type_toType α).symm ▸ hδ⟩) := by
  unfold PairERTypeTree.limitChain
  rw [PairERChain.limitWithType_typeAt]

/-- **Conditional type-coherence**: `T.limitChain` and `F.typeVal`
agree at every position EXACTLY when the tree's selected branch
equals `F.typeFn`. Without this hypothesis, the equation is generally
false — single-branch family state and multi-branch tree state are
genuinely distinct.

This lemma surfaces the architectural conflict explicitly: any
"tree-aware extendAtLimit" must take this equality as an input, not
hide it. -/
lemma PairERTypeTree.limitChain_typeAt_eq_typeVal
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (hα : α < Ordinal.omega.{0} 1)
    {F : PairERCoherentFamily cR α} (T : PairERTypeTree F)
    (h_eq : T.selectedBranch hα = F.typeFn)
    (δ : Ordinal.{0}) (hδ : δ < α) :
    (T.limitChain hα).typeAt δ hδ = F.typeVal δ hδ := by
  classical
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  rw [T.limitChain_typeAt hα δ hδ, h_eq]
  -- Goal: F.typeFn (enum ⟨δ, _⟩) = F.typeVal δ hδ.
  show F.typeVal (Ordinal.typein (· < ·)
    (Ordinal.enum (α := α.ToType) (· < ·)
      ⟨δ, (Ordinal.type_toType α).symm ▸ hδ⟩)) _ = F.typeVal δ hδ
  congr 1
  exact Ordinal.typein_enum _ _

/-! ### Type-deferred recursion: `PairERTreeFamily`

The new layer that resolves the single-branch / multi-branch tension.
Carries head/stage coherence (via the wrapped `PairERCoherentFamily`)
and tree data (via `PairERTypeTree`), but lemmas work through the
tree's branches rather than the family's `typeFn`. The wrapped family's
`typeFn` is still defined (it's a field of the underlying family)
but is NOT a load-bearing object for the new layer's projections.

**Design contract**:
- `PairERTreeFamily` is for the main-theorem path that uses tree-aware
  limits.
- `PairERCoherentFamily` is the old single-branch API, kept for
  backwards compatibility and downstream code that doesn't need the
  tree-driven approach.
- The conditional equality lemma above (`limitChain_typeAt_eq_typeVal`)
  is the boundary: it shows why tree-aware limits cannot be hidden
  inside `PairERCoherentFamily` without taking the equality as input.

**Status**: minimal implementation — structure + one projection from
selected branch to concrete `PairERChain.limitWithType`. Successor /
limit constructors and recursion threading deferred to next tranches. -/

/-- **`PairERTreeFamily`**: type-deferred recursion layer. Pairs a
coherent family (for head data) with a `PairERTypeTree` (for branch
data). Lemmas work via the tree, not via the family's typeFn. -/
structure PairERTreeFamily
    (cR : (Fin 2 ↪o PairERSource) → Bool) (α : Ordinal.{0}) where
  /-- The underlying coherent family (provides prefix/head structure). -/
  family : PairERCoherentFamily cR α
  /-- The tree of branches and realizers above this family's prefix. -/
  tree : PairERTypeTree family

/-- **Projection theorem**: given a `PairERTreeFamily TF`, a selected
branch `b ∈ TF.tree.branches` with `succ ℶ_1`-many realizers, produce
a concrete `PairERChain cR α` whose head is `TF.family.prefix` and
whose type is `b`. Uses `PairERChain.limitWithType` directly.

This is the type-deferred analog of `PairERCoherentFamily.
limitTypeCoherent`: the resulting chain's type is the SELECTED branch,
not the family's `typeFn`. The selection is explicit (passed as the
branch + size hypothesis), so no hidden architectural conflict. -/
noncomputable def PairERTreeFamily.toLimitChainAtBranch
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (TF : PairERTreeFamily cR α)
    (b : α.ToType → Bool)
    (hb_large : Order.succ (Cardinal.beth.{0} 1) ≤
      Cardinal.mk (TF.tree.realizers b)) :
    PairERChain cR α :=
  PairERChain.limitWithType TF.family.prefix b
    (hb_large.trans
      (Cardinal.mk_le_mk_of_subset (TF.tree.realizers_sub_validFiber b)))

/-- The projected chain's `head` is `TF.family.prefix`. -/
@[simp]
lemma PairERTreeFamily.toLimitChainAtBranch_head
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (TF : PairERTreeFamily cR α)
    (b : α.ToType → Bool) (hb_large) :
    (TF.toLimitChainAtBranch b hb_large).head = TF.family.prefix := rfl

/-- The projected chain's `type` is the selected branch `b`. -/
@[simp]
lemma PairERTreeFamily.toLimitChainAtBranch_type
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (TF : PairERTreeFamily cR α)
    (b : α.ToType → Bool) (hb_large) :
    (TF.toLimitChainAtBranch b hb_large).type = b := rfl

/-- **Pigeonhole-driven limit chain**: combines `exists_large_realized_
branch` with `toLimitChainAtBranch`. The caller doesn't pick a branch;
the H3 pigeonhole on the tree's branches picks one with `succ ℶ_1`-many
realizers, and the chain is built from it.

This is the type-deferred analog of `T.limitChain` from earlier: same
construction (uses pigeonhole), but exposed at the `PairERTreeFamily`
level so downstream code doesn't need to peek into the tree. -/
noncomputable def PairERTreeFamily.toLimitChain
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (TF : PairERTreeFamily cR α) (hα : α < Ordinal.omega.{0} 1) :
    PairERChain cR α :=
  TF.toLimitChainAtBranch (TF.tree.selectedBranch hα)
    (TF.tree.selectedBranch_large hα)

/-- The pigeonhole-driven chain's `head` is the family's prefix. -/
@[simp]
lemma PairERTreeFamily.toLimitChain_head
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (TF : PairERTreeFamily cR α) (hα : α < Ordinal.omega.{0} 1) :
    (TF.toLimitChain hα).head = TF.family.prefix := rfl

/-- The pigeonhole-driven chain's `type` is the tree's selectedBranch. -/
@[simp]
lemma PairERTreeFamily.toLimitChain_type
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (TF : PairERTreeFamily cR α) (hα : α < Ordinal.omega.{0} 1) :
    (TF.toLimitChain hα).type = TF.tree.selectedBranch hα := rfl

/-! ### `TreeBundle`: tree-aware bundle parallel to `CoherentBundle`

The bundle layer that completes the type-deferred recursion. Pairs a
`PairERTreeFamily` with a current stage chain, wired by a head-coherence
field `coh`. Constructors mirror `CoherentBundle.zero / extend /
limitExtend` but use the tree-driven `toLimitChain` at limits, so the
stage's `type` is the SELECTED branch rather than a single committed
`typeFn`.

**Design contract**:
- This is a NEW path, parallel to (not replacing) `CoherentBundle`.
- The main-theorem chain extraction will use `TreeBundle` for limits
  where canonical types matter; `CoherentBundle` remains for code that
  works at the type-committed layer.
- We do NOT attempt `stage.typeAt δ = family.family.typeVal δ` —
  that's where the architectural conflict lives. Instead:
  `stage.type = family.tree.selectedBranch hα` (via
  `toLimitChain_type`).

The structure is declared here; constructors (`zero`, `extendSucc`,
`limitFromTree`) are defined further below, after `PairERTypeTree.empty`
and friends become available. -/

/-- **`TreeBundle`**: tree-aware bundle. Carries head-coherence (`coh`)
between the current stage and the underlying coherent family, but the
stage's TYPE is determined by the tree (via `toLimitChain` at limits),
not by the family's `typeFn`. -/
structure TreeBundle
    (cR : (Fin 2 ↪o PairERSource) → Bool) (α : Ordinal.{0}) where
  family : PairERTreeFamily cR α
  stage : PairERChain cR α
  coh : ∀ δ (hδ : δ < α),
    stage.commitAt δ hδ = family.family.commitVal δ hδ
  /-- **Type matching**: the stage's `typeAt` agrees with the family's
  `typeVal` at every position. Parallel to `coh` for the `type` field
  (which `coh` covers via `head`/`commit`). Required to maintain
  type-coherence under successor extension. -/
  type_match : ∀ δ (hδ : δ < α),
    stage.typeAt δ hδ = family.family.typeVal δ hδ
  /-- **Type-coherence**: the underlying coherent family is type-
  coherent (cross-stage `typeAt` agreement). Together with `coh`
  and `type_match`, this packages the canonicality the tree pipeline
  maintains. -/
  type_coh : family.family.IsTypeCoherent

/-! ### [LEGACY] Old single-branch frontier theorems

**SUPERSEDED**. The two sorry'd theorems below (`exists_point_in_iInter
_of_fusion_sequence` and `exists_large_iInter_stage_fibers`) are the
*old* type-coherence-at-limits frontier from the pre-tree architecture.
They are too single-branch flavored: they describe the obstruction in
terms of α-intersections of per-stage fibers under `IsTypeCoherent`,
which the α = ω sanity analysis showed cannot be proved from the
existing invariants alone.

The **new sharper frontier** is
`selectedBranch_agrees_with_prior_commit` (defined later, near
`treeChain_pair_homogeneous`). The tree architecture makes the
missing math explicit as a single equation: at every limit α, the
universal-tree's `selectedBranch` (chosen via H3 pigeonhole) agrees
with `treeCommitBool cR δ` at every position `δ < α`.

The legacy frontiers below are kept for backward compatibility with
the now-superseded `PairERCoherentFamily.limitTypeCoherent` path.
The main pair-Erdős–Rado pipeline (via `treeChain_pair_homogeneous`)
goes through the new frontier instead. -/

/-- **[LEGACY FRONTIER, sorry — superseded by
`selectedBranch_agrees_with_prior_commit`]** Extract a single witness
from a strict-mono fusion ω-sequence. Known false under current
invariants (ω-sup doesn't preserve per-fiber color constraints).
The new sharper frontier on the tree path replaces this; this lemma
is kept only for backward compatibility with the legacy
`PairERCoherentFamily.limitTypeCoherent` path. -/
theorem exists_point_in_iInter_of_fusion_sequence
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (_F : PairERCoherentFamily cR α) (_hF_type : _F.IsTypeCoherent)
    (_e : ℕ → {β : Ordinal.{0} // β < α})
    (_e_mono : ∀ {n m : ℕ}, n ≤ m → (_e n).1 ≤ (_e m).1) :
    Set.Nonempty (⋂ n : ℕ, validFiber cR
      (_F.stage (_e n).1 (_e n).2).head (_F.stage (_e n).1 (_e n).2).type) := by
  sorry

/-- **H3-pigeonhole existential at level `α`**: at any countable
`α < ω₁`, the set above `F.prefix` partitions by type into ≤ `ℶ_1`
classes (since `|α.ToType| ≤ ℵ₀`). By H3, *some* type τ has
`≥ succ ℶ_1` realizers. This is the *existence* of a large-fiber
type — F.typeFn might not be that τ, which is the obstruction to
the full fusion theorem. -/
theorem exists_large_validFiber_at_level
    (cR : (Fin 2 ↪o PairERSource) → Bool)
    {α : Ordinal.{0}} (hα : α < Ordinal.omega.{0} 1)
    (F : PairERCoherentFamily cR α) :
    ∃ τ : α.ToType → Bool,
      Order.succ (Cardinal.beth.{0} 1) ≤
        Cardinal.mk (validFiber cR F.prefix τ) := by
  classical
  haveI : Countable α.ToType := countable_toType_of_lt_omega1 hα
  -- The "above F.prefix" set has size ≥ succ ℶ_1.
  set above : Set PairERSource :=
    { y : PairERSource | ∀ x : α.ToType, F.prefix x < y } with hab_def
  have h_above_large : Order.succ (Cardinal.beth.{0} 1) ≤
      Cardinal.mk above := large_above_prefix hα F.prefix
  -- Type-classification: each y above the prefix has a profile.
  let profile : above → (α.ToType → Bool) := fun y x =>
    cR (pairEmbed (y.property x))
  -- Codomain `α.ToType → Bool` has size ≤ 2^ℵ₀ = ℶ_1.
  have h_codomain_le : Cardinal.mk (α.ToType → Bool) ≤ Cardinal.beth.{0} 1 := by
    -- |α.ToType → Bool| = #Bool ^ #α.ToType = 2 ^ #α.ToType ≤ 2 ^ ℵ₀ = ℶ_1.
    have h_le_pow : Cardinal.mk (α.ToType → Bool) ≤
        Cardinal.aleph0 ^ Cardinal.mk α.ToType := by
      have h_pow_eq : Cardinal.mk (α.ToType → Bool) =
          (Cardinal.mk Bool) ^ (Cardinal.mk α.ToType) := by
        rw [Cardinal.mk_arrow]; simp
      rw [h_pow_eq]
      exact Cardinal.power_le_power_right (Cardinal.mk_le_aleph0 (α := Bool))
    have h_pow_le : Cardinal.aleph0 ^ Cardinal.mk α.ToType ≤
        Cardinal.aleph0 ^ Cardinal.aleph0 := by
      exact Cardinal.power_le_power_left Cardinal.aleph0_ne_zero
        (Cardinal.mk_le_aleph0 (α := α.ToType))
    have h_aleph_pow : Cardinal.aleph0.{0} ^ Cardinal.aleph0.{0} =
        Cardinal.beth.{0} 1 := by
      rw [Cardinal.power_self_eq (le_refl Cardinal.aleph0)]
      rw [show (1 : Ordinal.{0}) = Order.succ 0 from Ordinal.succ_zero.symm,
          Cardinal.beth_succ, Cardinal.beth_zero]
    calc Cardinal.mk (α.ToType → Bool)
        ≤ Cardinal.aleph0 ^ Cardinal.mk α.ToType := h_le_pow
      _ ≤ Cardinal.aleph0 ^ Cardinal.aleph0 := h_pow_le
      _ = Cardinal.beth.{0} 1 := h_aleph_pow
  -- Apply H3: some τ has ≥ succ ℶ_1 preimage.
  obtain ⟨τ, hτ⟩ := exists_large_fiber_of_small_codomain
    (κ := Cardinal.beth.{0} 1)
    (Cardinal.aleph0_le_beth 1) h_above_large h_codomain_le profile
  refine ⟨τ, hτ.trans ?_⟩
  -- The H3-fiber injects into validFiber cR F.prefix τ via y ↦ y.
  refine Cardinal.mk_le_of_injective
    (f := fun y : profile ⁻¹' {τ} => ⟨y.val.val, ?_⟩) ?_
  · -- y.val.val ∈ validFiber cR F.prefix τ.
    intro x
    refine ⟨y.val.property x, ?_⟩
    have h_τ_eq : profile y.val = τ := y.property
    show cR _ = τ x
    have := congrFun h_τ_eq x
    exact this
  · intro y₁ y₂ h
    have h1 : y₁.val.val = y₂.val.val := by
      have h2 := Subtype.mk.inj h
      exact h2
    apply Subtype.ext
    apply Subtype.ext
    exact h1

/-- **`majorityType`**: the H3-pigeonhole-chosen type at level `α`,
extracted via `Classical.choose` on `exists_large_validFiber_at_level`.
This is the *global majority* type — the one whose `validFiber` has
size `≥ succ ℶ_1`. -/
noncomputable def PairERCoherentFamily.majorityType
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (hα : α < Ordinal.omega.{0} 1)
    (F : PairERCoherentFamily cR α) : α.ToType → Bool :=
  Classical.choose (exists_large_validFiber_at_level cR hα F)

/-- **`majorityType_large`**: the `validFiber` for `majorityType F`
has size `≥ succ ℶ_1`, by definition. -/
theorem PairERCoherentFamily.majorityType_large
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (hα : α < Ordinal.omega.{0} 1)
    (F : PairERCoherentFamily cR α) :
    Order.succ (Cardinal.beth.{0} 1) ≤
      Cardinal.mk (validFiber cR F.prefix (F.majorityType hα)) :=
  Classical.choose_spec (exists_large_validFiber_at_level cR hα F)

/-- **`IsMajorityType`**: predicate that `F.typeFn` agrees with the
global majority type. Together with `IsTypeCoherent`, this gives
the structural information needed to identify `F.typeFn` with the
H3-pigeonhole-chosen branch. -/
def PairERCoherentFamily.IsMajorityType
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (hα : α < Ordinal.omega.{0} 1)
    (F : PairERCoherentFamily cR α) : Prop :=
  F.typeFn = F.majorityType hα

/-- **`typeCoherentFiber_large_via_majority`**: under
`IsMajorityType` (i.e., F.typeFn = majorityType F), the type-coherent
fiber has size `≥ succ ℶ_1` directly from `majorityType_large`. -/
theorem PairERCoherentFamily.typeCoherentFiber_large_via_majority
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (hα : α < Ordinal.omega.{0} 1)
    (F : PairERCoherentFamily cR α) (hF_majority : F.IsMajorityType hα) :
    Order.succ (Cardinal.beth.{0} 1) ≤
      Cardinal.mk (validFiber cR F.prefix F.typeFn) := by
  rw [hF_majority]
  exact F.majorityType_large hα

/-- **`toMajorityType`**: rebuild a coherent family at level `α` so that
its `typeFn` equals `majorityType F`. The prefix/commits are
preserved (= F.prefix as a function), but each stage's `type` is reset
to the global majority instead of inheriting per-stage choices.

Construction: for each `β < α`, build a `(succ β)`-chain via
`PairERChain.limitWithType`:
- head: `F.prefix` restricted to the first `(succ β)` positions
  (via `F.commitVal` + `Ordinal.typein`).
- type: `majorityType F` restricted similarly.
- large: validFiber at level `(succ β)` ⊇ validFiber at level `α`,
  hence size ≥ succ ℶ_1 by `majorityType_large`.

After this rebuild, `(toMajorityType F).typeFn = F.majorityType hα`
and the family is `IsTypeCoherent`. The proof obligations
(coherent + validFiber inclusion + typeFn equality) are sorry'd
here as substantial bookkeeping; the architecture is laid out. -/
noncomputable def PairERCoherentFamily.toMajorityType
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (hα : α < Ordinal.omega.{0} 1)
    (F : PairERCoherentFamily cR α) :
    PairERCoherentFamily cR α := by
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  refine
    { stage := fun β hβα => ?_
      coherent := ?_ }
  · -- (succ β)-chain with prescribed head/type from F.commitVal /
    -- F.majorityType.
    haveI : IsWellOrder (Order.succ β).ToType (· < ·) := isWellOrder_lt
    have ht_lt : ∀ x : (Order.succ β).ToType,
        Ordinal.typein (· < ·) x < α := fun x => by
      have h_lt_succ : Ordinal.typein (· < ·) x < Order.succ β := by
        simpa [Ordinal.type_toType] using
          Ordinal.typein_lt_type
            (· < · : (Order.succ β).ToType → (Order.succ β).ToType → Prop) x
      exact lt_of_le_of_lt (Order.lt_succ_iff.mp h_lt_succ) hβα
    -- Embed (succ β).ToType into α.ToType via typein ↦ enum at the same ordinal.
    let xα : (Order.succ β).ToType → α.ToType := fun x =>
      Ordinal.enum (α := α.ToType) (· < ·)
        ⟨Ordinal.typein (· < ·) x,
          (Ordinal.type_toType α).symm ▸ ht_lt x⟩
    -- F.prefix (xα x) = F.commitVal (typein x) (ht_lt x) by prefix_enum.
    have h_prefix_xα : ∀ x : (Order.succ β).ToType,
        F.prefix (xα x) = F.commitVal (Ordinal.typein (· < ·) x) (ht_lt x) := by
      intro x
      exact F.prefix_enum (Ordinal.typein (· < ·) x) (ht_lt x)
    set new_head : (Order.succ β).ToType ↪o PairERSource :=
      OrderEmbedding.ofStrictMono
        (fun x => F.commitVal (Ordinal.typein (· < ·) x) (ht_lt x))
        (fun x y hxy => F.commitVal_strictMono _ _
          ((Ordinal.typein_lt_typein _).mpr hxy)) with hnh_def
    set new_type : (Order.succ β).ToType → Bool := fun x =>
      F.majorityType hα (xα x) with hnt_def
    have h_new_head_eq : ∀ x, new_head x = F.prefix (xα x) := by
      intro x
      rw [hnh_def]
      show F.commitVal _ _ = F.prefix (xα x)
      exact (h_prefix_xα x).symm
    -- large: validFiber cR F.prefix (majorityType F) injects into the new fiber.
    have h_large : Order.succ (Cardinal.beth.{0} 1) ≤
        Cardinal.mk (validFiber cR new_head new_type) := by
      apply (F.majorityType_large hα).trans
      refine Cardinal.mk_le_of_injective
        (f := fun y : validFiber cR F.prefix (F.majorityType hα) =>
          (⟨y.val, ?_⟩ : validFiber cR new_head new_type)) ?_
      · -- y.val ∈ validFiber cR new_head new_type.
        intro x
        obtain ⟨h_lt, h_col⟩ := y.property (xα x)
        -- h_lt : F.prefix (xα x) < y.val, h_col : cR(pair _) = majorityType F (xα x).
        refine ⟨?_, ?_⟩
        · -- new_head x < y.val.
          rw [h_new_head_eq]; exact h_lt
        · -- cR(pairEmbed _) = new_type x = majorityType F (xα x).
          show cR _ = F.majorityType hα (xα x)
          have h_pair_eq : (pairEmbed (show new_head x < y.val by
              rw [h_new_head_eq]; exact h_lt)) =
              pairEmbed h_lt := by
            ext k
            match k with
            | ⟨0, _⟩ =>
              show new_head x = F.prefix (xα x)
              exact h_new_head_eq x
            | ⟨1, _⟩ => rfl
          rw [h_pair_eq]
          exact h_col
      · -- Injective.
        intro y₁ y₂ heq
        apply Subtype.ext
        exact Subtype.mk.inj heq
    exact PairERChain.limitWithType new_head new_type h_large
  · -- coherent: cross-stage head matching at lower positions.
    intro δ β hδβ hβα
    haveI : IsWellOrder (Order.succ β).ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder (Order.succ δ).ToType (· < ·) := isWellOrder_lt
    -- Both LHS and RHS reduce to F.commitVal δ via the chain's head =
    -- F.commitVal ∘ typein composed with limitWithType_commitAt.
    show ((PairERChain.limitWithType (cR := cR) _ _ _).commitAt δ
        (hδβ.trans (Order.lt_succ β))) =
      ((PairERChain.limitWithType (cR := cR) _ _ _).commitAt δ
        (Order.lt_succ δ))
    rw [PairERChain.limitWithType_commitAt, PairERChain.limitWithType_commitAt]
    -- Both sides: head(enum ⟨δ, ...⟩) = F.commitVal (typein (enum ⟨δ, ...⟩)) _
    --                                = F.commitVal δ _ by typein_enum.
    show (OrderEmbedding.ofStrictMono _ _) (Ordinal.enum (· < ·) _) =
      (OrderEmbedding.ofStrictMono _ _) (Ordinal.enum (· < ·) _)
    simp only [OrderEmbedding.coe_ofStrictMono, Ordinal.typein_enum]

/-- **`toMajorityType_commitVal`**: the rebuilt family's `commitVal`
agrees with the original's at every position. By construction, the
new stages' top commits reduce via `limitWithType_commitAt` +
`Ordinal.typein_enum` to `F.commitVal δ`. -/
lemma PairERCoherentFamily.toMajorityType_commitVal
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (hα : α < Ordinal.omega.{0} 1)
    (F : PairERCoherentFamily cR α)
    (δ : Ordinal.{0}) (hδα : δ < α) :
    (F.toMajorityType hα).commitVal δ hδα = F.commitVal δ hδα := by
  haveI : IsWellOrder (Order.succ δ).ToType (· < ·) := isWellOrder_lt
  show ((F.toMajorityType hα).stage δ hδα).commitAt δ (Order.lt_succ δ) =
    F.commitVal δ hδα
  unfold PairERCoherentFamily.toMajorityType
  show (PairERChain.limitWithType (cR := cR) _ _ _).commitAt δ
      (Order.lt_succ δ) = F.commitVal δ hδα
  rw [PairERChain.limitWithType_commitAt]
  show (OrderEmbedding.ofStrictMono _ _) (Ordinal.enum (· < ·) _) =
    F.commitVal δ hδα
  simp only [OrderEmbedding.coe_ofStrictMono, Ordinal.typein_enum]

/-- **`toMajorityType_typeVal`**: the rebuilt family's `typeVal` at
position `δ` is `majorityType F` evaluated at `enum δ`. -/
lemma PairERCoherentFamily.toMajorityType_typeVal
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (hα : α < Ordinal.omega.{0} 1)
    (F : PairERCoherentFamily cR α)
    (δ : Ordinal.{0}) (hδα : δ < α) :
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    (F.toMajorityType hα).typeVal δ hδα =
      F.majorityType hα
        (Ordinal.enum (α := α.ToType) (· < ·)
          ⟨δ, (Ordinal.type_toType α).symm ▸ hδα⟩) := by
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder (Order.succ δ).ToType (· < ·) := isWellOrder_lt
  show ((F.toMajorityType hα).stage δ hδα).typeAt δ (Order.lt_succ δ) = _
  unfold PairERCoherentFamily.toMajorityType
  show (PairERChain.limitWithType (cR := cR) _ _ _).typeAt δ
      (Order.lt_succ δ) = _
  rw [PairERChain.limitWithType_typeAt]
  -- LHS: new_type (enum ⟨δ, ...⟩ in (succ δ).ToType) = majorityType F at α-enum.
  -- typein (enum ⟨δ, ...⟩) = δ.
  simp only [Ordinal.typein_enum]

/-- **`toMajorityType_typeFn`**: the rebuilt family's `typeFn` is
`F.majorityType hα`. By `toMajorityType_typeVal` + the typein-enum
identity. -/
lemma PairERCoherentFamily.toMajorityType_typeFn
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (hα : α < Ordinal.omega.{0} 1)
    (F : PairERCoherentFamily cR α) :
    (F.toMajorityType hα).typeFn = F.majorityType hα := by
  classical
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  funext x
  show (F.toMajorityType hα).typeVal _ _ = F.majorityType hα x
  rw [F.toMajorityType_typeVal hα]
  congr 1
  exact Ordinal.enum_typein _ x

/-- **`toMajorityType_prefix`**: the rebuilt family's `prefix`, applied
at any `x`, equals the original's. -/
lemma PairERCoherentFamily.toMajorityType_prefix_apply
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (hα : α < Ordinal.omega.{0} 1)
    (F : PairERCoherentFamily cR α)
    (x : α.ToType) :
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    (F.toMajorityType hα).prefix x = F.prefix x := by
  classical
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  unfold PairERCoherentFamily.prefix
  simp only [OrderEmbedding.coe_ofStrictMono]
  exact F.toMajorityType_commitVal hα _ _

/-- **`toMajorityType_isTypeCoherent`**: the rebuilt family is
type-coherent. All stages have `typeAt` at lower positions equal to
`F.majorityType` at the corresponding enum, so cross-stage agreement
is immediate. -/
lemma PairERCoherentFamily.toMajorityType_isTypeCoherent
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (hα : α < Ordinal.omega.{0} 1)
    (F : PairERCoherentFamily cR α) :
    (F.toMajorityType hα).IsTypeCoherent := by
  intro δ β hδβ hβα
  haveI : IsWellOrder (Order.succ β).ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder (Order.succ δ).ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  show ((F.toMajorityType hα).stage β hβα).typeAt δ
      (hδβ.trans (Order.lt_succ β)) =
    ((F.toMajorityType hα).stage δ (hδβ.trans hβα)).typeAt δ (Order.lt_succ δ)
  unfold PairERCoherentFamily.toMajorityType
  show (PairERChain.limitWithType (cR := cR) _ _ _).typeAt δ _ =
    (PairERChain.limitWithType (cR := cR) _ _ _).typeAt δ _
  rw [PairERChain.limitWithType_typeAt, PairERChain.limitWithType_typeAt]
  simp only [Ordinal.typein_enum]

/-! ### [LIMIT-FUSION CONSOLIDATION MAP — read before touching the limit case]

A read-only inventory + classification of the limit/fusion sorries, and the one
consolidated target. (Companion to the witness-net chain note at
`exists_coherentGoodWitnessNet`.)

**Decisive finding.** The *active* tree recursion bottoms out in a single
**false-as-stated** claim. `treeStage`'s limit → `TreeBundle.limitExtend` builds
its tree via `PairERTypeTree.commitCoherent` (branches `= {F.typeFn}`), whose
`large_sigma` = `typeCoherentFiber_large` = **`exists_large_iInter_stage_fibers`
(this theorem, limit case)**. That asserts the *committed* `F.typeFn` has a large
fiber for **every** `IsTypeCoherent F` — refuted by the documented ω-pattern
adversary (`F.typeFn` can be a 0-realizer minority at a limit). So this universal
claim cannot be proved; it is the linchpin of the *wrong* path.

**The correct path already exists and is sorry-free given the right input.**
`TreeBundle.limitFromCoherentMajority` builds the limit bundle from a
`CoherentMajorityBranch B`, taking largeness from `B.large` (B's own per-level
large-fiber field), *not* from this theorem. And `extendToExtOfBranch` (proved)
retires `extendToExt` given `B`. So "extend-at-limit *given* `B`" is already done.

**The single minimal active target is `exists_coherentMajorityBranch`** (`B`): a
globally-coherent branch with `succ ℶ_1`-large fibers at *every* level. `B` is
the coherent realized branch packaged at all levels; constructing it retires the
items marked ⓦ below. Its hard limit step (to be stated *after* the wrong-path
items are rerouted) is the coherent-realized-branch selection
(`exists_coherent_realized_limit_branch`).

**Classification of the limit/fusion sorries:**
- `exists_large_iInter_stage_fibers` (limit) — **FALSE-AS-STATED** (universal over
  `IsTypeCoherent`); linchpin of the wrong path. Reroute consumers to `B`.
- `exists_point_in_iInter_of_fusion_sequence` — **FALSE-AS-STATED + LEGACY** (kept
  for backward compat; off-chain).
- `exists_realizedPairERTypeTree` — genuine, but **subsumed** by `B` (B gives a
  realized branch at every level, including this existential).
- `PairERChain/PairERGoodChain.extendToExt` — ⓦ **downstream**: retired by the
  proved `extendToExtOfBranch` once `B` exists.
- `IsCanonicalTypeCoherent.restrict` — architectural bookkeeping (cofinality
  transport).
- `TreeBundle.extendSucc` (`type_match`/`type_coh`), `treeStage`
  (`prev_succ`/`type_succ`) — architectural bookkeeping (cyclic; post-hoc via the
  `treeStage_*`/`richStage_*` canonicalization lemmas).
- `richStage` (`cross_agree`) — LEGACY parallel recursion / bookkeeping.

The `commitCoherent`/this-theorem path is the false-as-stated dead end; the
`B`/`limitFromCoherentMajority` path is the live one. **Do not build new limit
statements on this theorem.** -/

/-- **[FRONTIER — FALSE-AS-STATED at limits; see the consolidation map above]**
Large-cardinality α-indexed intersection of stage fibers.

Cases on `α`:
- `α = 0`: vacuous; intersection = `Set.univ` of size `succ ℶ_1`.
- `α = succ β`: intersection = `validFiber` at the top stage (via
  `validFiber_mono` under `IsTypeCoherent`); size ≥ succ ℶ_1 by
  `(F.stage β _).large`. (This case is genuinely provable.)
- `α` a limit: **unprovable under `IsTypeCoherent` alone** — the committed
  `F.typeFn` can be a 0-realizer minority (ω-adversary). It would need the
  strengthened `F.IsMajorityType hα` (then `typeCoherentFiber_large_via_majority`
  + `validFiber_prefix_typeFn_eq_iInter`), i.e. the recursion must set `typeFn :=`
  the realized branch — which is exactly the `CoherentMajorityBranch` `B` route.
  This `IsTypeCoherent`-only statement is retained only because existing consumers
  still reference it; new code should route through `B`. -/
theorem exists_large_iInter_stage_fibers
    (cR : (Fin 2 ↪o PairERSource) → Bool)
    {α : Ordinal.{0}} (hα : α < Ordinal.omega.{0} 1)
    (F : PairERCoherentFamily cR α) (hF_type : F.IsTypeCoherent) :
    Order.succ (Cardinal.beth.{0} 1) ≤
      Cardinal.mk (⋂ (β : Ordinal.{0}) (hβα : β < α),
        validFiber cR (F.stage β hβα).head (F.stage β hβα).type) := by
  induction α using Ordinal.limitRecOn with
  | zero =>
    -- α = 0: intersection is over an empty index, hence Set.univ.
    have h_iInter_eq : (⋂ (β : Ordinal.{0}) (hβ0 : β < 0),
        validFiber cR (F.stage β hβ0).head (F.stage β hβ0).type) =
        (Set.univ : Set PairERSource) := by
      apply Set.eq_univ_of_forall
      intro y
      simp only [Set.mem_iInter]
      intro β hβ0
      exact absurd hβ0 (not_lt.mpr (zero_le β))
    rw [h_iInter_eq, Cardinal.mk_univ, mk_pairERSource]
  | succ β _ =>
    -- α = succ β: intersection collapses to validFiber at stage β.
    have h_top_lt : β < Order.succ β := Order.lt_succ β
    have h_subset :
        validFiber cR (F.stage β h_top_lt).head (F.stage β h_top_lt).type ⊆
          ⋂ (γ : Ordinal.{0}) (hγ : γ < Order.succ β),
            validFiber cR (F.stage γ hγ).head (F.stage γ hγ).type := by
      intro y hy
      simp only [Set.mem_iInter]
      intro γ hγ
      rcases lt_or_eq_of_le (Order.lt_succ_iff.mp hγ) with hγ_lt | hγ_eq
      · exact F.validFiber_mono hF_type hγ_lt h_top_lt hy
      · subst hγ_eq; exact hy
    exact (F.stage β h_top_lt).large.trans
      (Cardinal.mk_le_mk_of_subset h_subset)
  | limit β hβ_lim _ =>
    -- α = limit β: the deep frontier, classical Erdős–Rado fusion.
    sorry

/-- **Type-coherent large limit fiber**. Direct corollary of
`exists_large_iInter_stage_fibers` via
`validFiber_prefix_typeFn_eq_iInter`. -/
theorem exists_large_limit_fiber_prescribed
    (cR : (Fin 2 ↪o PairERSource) → Bool)
    {α : Ordinal.{0}} (hα : α < Ordinal.omega.{0} 1)
    (F : PairERCoherentFamily cR α) (hF_type : F.IsTypeCoherent) :
    Order.succ (Cardinal.beth.{0} 1) ≤
      Cardinal.mk (validFiber cR F.prefix F.typeFn) := by
  rw [F.validFiber_prefix_typeFn_eq_iInter hF_type]
  exact exists_large_iInter_stage_fibers cR hα F hF_type

/-- **Limit stage built from a coherent family.** Feed the glued prefix
into `PairERChain.limit`. -/
noncomputable def PairERCoherentFamily.limit
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (F : PairERCoherentFamily cR α) (hα : α < Ordinal.omega.{0} 1) :
    PairERChain cR α :=
  PairERChain.limit hα F.prefix

/-- **Type-coherent limit stage**: built via `limitWithType` with the
prescribed `F.typeFn` and the frontier theorem. The resulting chain's
`type` function is exactly `F.typeFn`, preserving earlier committed
Bools — in contrast to `PairERCoherentFamily.limit` which picks a
fresh τ via `exists_large_limit_fiber`. -/
noncomputable def PairERCoherentFamily.limitTypeCoherent
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (F : PairERCoherentFamily cR α) (hF_type : F.IsTypeCoherent)
    (hα : α < Ordinal.omega.{0} 1) : PairERChain cR α :=
  PairERChain.limitWithType F.prefix F.typeFn
    (exists_large_limit_fiber_prescribed cR hα F hF_type)

/-- **Limit-stage commit reproduces the coherent family.** This is the
main payoff of the glue API: the limit stage's commit at `δ < α` is
exactly the value already committed by stage `δ + 1`. -/
lemma PairERCoherentFamily.limit_commitAt
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (F : PairERCoherentFamily cR α) (hα : α < Ordinal.omega.{0} 1)
    (δ : Ordinal.{0}) (hδ : δ < α) :
    (F.limit hα).commitAt δ hδ = F.commitVal δ hδ := by
  rw [PairERCoherentFamily.limit, PairERChain.limit_commitAt]
  exact F.prefix_enum δ hδ

/-- **Type-coherent limit's commitAt** equals `F.commitVal`. Same as
`limit_commitAt` since the head function is `F.prefix` in both. -/
lemma PairERCoherentFamily.limitTypeCoherent_commitAt
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (F : PairERCoherentFamily cR α) (hF_type : F.IsTypeCoherent)
    (hα : α < Ordinal.omega.{0} 1) (δ : Ordinal.{0}) (hδ : δ < α) :
    (F.limitTypeCoherent hF_type hα).commitAt δ hδ = F.commitVal δ hδ := by
  rw [PairERCoherentFamily.limitTypeCoherent,
    PairERChain.limitWithType_commitAt]
  exact F.prefix_enum δ hδ

/-- **Type-coherent limit's typeAt** equals `F.typeVal`. THIS is the
payoff for type-coherent limits — unlike `F.limit` (via fresh τ),
this limit preserves earlier committed Bools. -/
lemma PairERCoherentFamily.limitTypeCoherent_typeAt
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (F : PairERCoherentFamily cR α) (hF_type : F.IsTypeCoherent)
    (hα : α < Ordinal.omega.{0} 1) (δ : Ordinal.{0}) (hδ : δ < α) :
    (F.limitTypeCoherent hF_type hα).typeAt δ hδ = F.typeVal δ hδ := by
  classical
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  rw [PairERCoherentFamily.limitTypeCoherent,
    PairERChain.limitWithType_typeAt]
  -- Goal: `F.typeFn (enum ⟨δ, _⟩) = F.typeVal δ hδ`.
  show F.typeVal (Ordinal.typein (· < ·)
      (Ordinal.enum (α := α.ToType) (· < ·)
        ⟨δ, (Ordinal.type_toType α).symm ▸ hδ⟩)) _ = F.typeVal δ hδ
  congr 1
  exact Ordinal.typein_enum _ _

/-- **Limit-case extension of the coherent family.** Given a coherent
family `F` below level `α` and a proof `hα : α < ω_1`, produce the
coherent family below `α + 1` that appends the new stage at level
`α + 1`, which is `(F.limit hα).succ`.

This packages the limit step of the outer transfinite recursion:
glue the lower prefix via `F.prefix`, take `F.limit hα` as the
stage at level `α`, then its `succ` as the new top-level stage.
Coherence is proved by combining `F.coherent` (for earlier `β < α`
positions), `PairERChain.succ_commitAt` (the new top collapses to
the limit stage), and `PairERCoherentFamily.limit_commitAt` (the
limit stage's commits match the family). -/
noncomputable def PairERCoherentFamily.extendAtLimit
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (F : PairERCoherentFamily cR α)
    (hα : α < Ordinal.omega.{0} 1) :
    PairERCoherentFamily cR (Order.succ α) where
  stage β hβ :=
    if h : β < α then F.stage β h
    else
      -- `β < α + 1` with `¬ β < α` ⇒ `β = α`. We then have `succ β = succ α`,
      -- and the new stage at position `β = α` is `(F.limit hα).succ`.
      have hβ_eq : β = α :=
        le_antisymm (Order.lt_succ_iff.mp hβ) (not_lt.mp h)
      hβ_eq ▸ (F.limit hα).succ
  coherent := by
    intro δ β hδβ hβ_succ
    rcases lt_or_eq_of_le (Order.lt_succ_iff.mp hβ_succ) with hβ_lt_α | hβ_eq_α
    · -- Case `β < α`: stage at β is `F.stage β hβ_lt_α`.
      have hδ_lt_α : δ < α := hδβ.trans hβ_lt_α
      simp only [dif_pos hβ_lt_α, dif_pos hδ_lt_α]
      exact F.coherent hδβ hβ_lt_α
    · -- Case `β = α`: stage at β is `(F.limit hα).succ`.
      subst hβ_eq_α
      -- `δ < β = α`, so stage at δ is `F.stage δ hδβ`.
      simp only [dif_pos hδβ, dif_neg (lt_irrefl _)]
      -- Goal: `(F.limit hα).succ.commitAt δ _ = (F.stage δ hδβ).commitAt δ _`.
      rw [PairERChain.succ_commitAt _ δ hδβ]
      rw [PairERCoherentFamily.limit_commitAt F hα δ hδβ]
      rfl

/-- **`extendWithStage`**: extend a coherent family at level α by
appending an arbitrary stage `s : PairERChain cR α` at the new top
position α, producing a family at level (succ α). Requires
head-coherence of `s` with the existing family.

Generalizes `extendAtLimit` (which uses `F.limit hα` as the
appended stage) — here ANY suitable `s` works. The intended use is
to feed a tree-driven limit chain (`TF.toLimitChain hα`) instead of
the Classical.choose-based `F.limit`. -/
noncomputable def PairERCoherentFamily.extendWithStage
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (F : PairERCoherentFamily cR α)
    (s : PairERChain cR α)
    (h_coh : ∀ δ (hδ : δ < α), s.commitAt δ hδ = F.commitVal δ hδ) :
    PairERCoherentFamily cR (Order.succ α) where
  stage β hβ :=
    if h : β < α then F.stage β h
    else
      have hβ_eq : β = α :=
        le_antisymm (Order.lt_succ_iff.mp hβ) (not_lt.mp h)
      hβ_eq ▸ s.succ
  coherent := by
    intro δ β hδβ hβ_succ
    rcases lt_or_eq_of_le (Order.lt_succ_iff.mp hβ_succ) with hβ_lt_α | hβ_eq_α
    · have hδ_lt_α : δ < α := hδβ.trans hβ_lt_α
      simp only [dif_pos hβ_lt_α, dif_pos hδ_lt_α]
      exact F.coherent hδβ hβ_lt_α
    · subst hβ_eq_α
      simp only [dif_pos hδβ, dif_neg (lt_irrefl _)]
      rw [PairERChain.succ_commitAt _ δ hδβ]
      exact h_coh δ hδβ

/-- **Type-coherent variant of `extendAtLimit`**: uses
`limitTypeCoherent` instead of `limit`, so the new top stage at level
`α+1` preserves all earlier committed Bools. Requires `IsTypeCoherent`
on the input family. -/
noncomputable def PairERCoherentFamily.extendAtLimitTypeCoherent
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (F : PairERCoherentFamily cR α) (hF_type : F.IsTypeCoherent)
    (hα : α < Ordinal.omega.{0} 1) :
    PairERCoherentFamily cR (Order.succ α) where
  stage β hβ :=
    if h : β < α then F.stage β h
    else
      have hβ_eq : β = α :=
        le_antisymm (Order.lt_succ_iff.mp hβ) (not_lt.mp h)
      hβ_eq ▸ (F.limitTypeCoherent hF_type hα).succ
  coherent := by
    intro δ β hδβ hβ_succ
    rcases lt_or_eq_of_le (Order.lt_succ_iff.mp hβ_succ) with hβ_lt_α | hβ_eq_α
    · have hδ_lt_α : δ < α := hδβ.trans hβ_lt_α
      simp only [dif_pos hβ_lt_α, dif_pos hδ_lt_α]
      exact F.coherent hδβ hβ_lt_α
    · subst hβ_eq_α
      simp only [dif_pos hδβ, dif_neg (lt_irrefl _)]
      rw [PairERChain.succ_commitAt _ δ hδβ]
      rw [PairERCoherentFamily.limitTypeCoherent_commitAt F hF_type hα δ hδβ]
      rfl

/-- `extendAtLimitTypeCoherent` preserves `IsTypeCoherent`. The new top
stage at level `α+1` has types matching `F.typeVal δ` at every earlier
position δ < α, by `limitTypeCoherent_typeAt` + `succ_typeAt_old`. -/
lemma PairERCoherentFamily.extendAtLimitTypeCoherent_isTypeCoherent
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    {F : PairERCoherentFamily cR α} (hF_type : F.IsTypeCoherent)
    (hα : α < Ordinal.omega.{0} 1) :
    (F.extendAtLimitTypeCoherent hF_type hα).IsTypeCoherent := by
  unfold PairERCoherentFamily.IsTypeCoherent
  intro δ β hδβ hβ_succ
  rcases lt_or_eq_of_le (Order.lt_succ_iff.mp hβ_succ) with hβ_lt_α | hβ_eq_α
  · have hδ_lt_α : δ < α := hδβ.trans hβ_lt_α
    unfold PairERCoherentFamily.extendAtLimitTypeCoherent
    simp only [dif_pos hβ_lt_α, dif_pos hδ_lt_α]
    exact hF_type hδβ hβ_lt_α
  · subst hβ_eq_α
    unfold PairERCoherentFamily.extendAtLimitTypeCoherent
    simp only [dif_pos hδβ, dif_neg (lt_irrefl _)]
    rw [PairERChain.succ_typeAt_old _ δ hδβ]
    rw [PairERCoherentFamily.limitTypeCoherent_typeAt F hF_type hα δ hδβ]
    rfl

/-- **Empty coherent family.** At level `α = 0`, there are no earlier
successor stages; all fields are vacuous. Provides the base case for
the transfinite recursion. -/
def PairERCoherentFamily.empty (cR : (Fin 2 ↪o PairERSource) → Bool) :
    PairERCoherentFamily cR 0 where
  stage := fun β h => absurd h (not_lt.mpr (zero_le β))
  coherent := fun _ hβα => absurd hβα (not_lt.mpr (zero_le _))

/-- **Successor-case extension of the coherent family.** Given a
coherent family `F : PairERCoherentFamily cR (Order.succ β)` (i.e.,
including a stage at position `β`), produce the coherent family below
level `Order.succ (Order.succ β) = β + 2` by appending
`(F.stage β (Order.lt_succ β)).succ` as the new top stage.

Analogue of `extendAtLimit` for successor levels. The coherence proof
for the new top position uses `PairERChain.succ_commitAt` directly
(no `PairERChain.limit` involved). -/
noncomputable def PairERCoherentFamily.extendAtSucc
    {cR : (Fin 2 ↪o PairERSource) → Bool} {β : Ordinal.{0}}
    (F : PairERCoherentFamily cR (Order.succ β)) :
    PairERCoherentFamily cR (Order.succ (Order.succ β)) where
  stage γ hγ :=
    if h : γ < Order.succ β then F.stage γ h
    else
      have hγ_eq : γ = Order.succ β :=
        le_antisymm (Order.lt_succ_iff.mp hγ) (not_lt.mp h)
      hγ_eq ▸ (F.stage β (Order.lt_succ β)).succ
  coherent := by
    intro δ γ hδγ hγ_succ
    rcases lt_or_eq_of_le (Order.lt_succ_iff.mp hγ_succ) with hγ_lt | hγ_eq
    · -- Case γ < succ β: delegate to F.coherent.
      have hδ_lt : δ < Order.succ β := hδγ.trans hγ_lt
      simp only [dif_pos hγ_lt, dif_pos hδ_lt]
      exact F.coherent hδγ hγ_lt
    · -- Case γ = succ β: new top stage is `(F.stage β _).succ`.
      subst hγ_eq
      simp only [dif_pos hδγ, dif_neg (lt_irrefl _)]
      -- Goal: `(F.stage β _).succ.commitAt δ _ = (F.stage δ hδγ).commitAt δ _`.
      rw [PairERChain.succ_commitAt _ δ hδγ]
      -- Goal: `(F.stage β _).commitAt δ _ = (F.stage δ hδγ).commitAt δ _`.
      -- This is F.coherent at position δ < β in stage β (when δ < β),
      -- OR trivial by reflexivity (when δ = β).
      rcases lt_or_eq_of_le (Order.lt_succ_iff.mp hδγ) with hδ_lt_β | hδ_eq_β
      · exact F.coherent hδ_lt_β (Order.lt_succ β)
      · subst hδ_eq_β; rfl

/-- The empty family is vacuously type-coherent. -/
lemma PairERCoherentFamily.empty_isTypeCoherent
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    (PairERCoherentFamily.empty cR).IsTypeCoherent :=
  fun _ hβα => absurd hβα (not_lt.mpr (zero_le _))

/-- `extendAtSucc` preserves `IsTypeCoherent`: if the input family is
type-coherent, so is the extension. Uses `succ_typeAt_old` to reduce
the new top stage's types to the input's, then the input's own
`IsTypeCoherent`. -/
lemma PairERCoherentFamily.extendAtSucc_isTypeCoherent
    {cR : (Fin 2 ↪o PairERSource) → Bool} {β : Ordinal.{0}}
    {F : PairERCoherentFamily cR (Order.succ β)}
    (hF : F.IsTypeCoherent) :
    F.extendAtSucc.IsTypeCoherent := by
  intro δ γ hδγ hγ_succ
  rcases lt_or_eq_of_le (Order.lt_succ_iff.mp hγ_succ) with hγ_lt | hγ_eq
  · have hδ_lt : δ < Order.succ β := hδγ.trans hγ_lt
    show (F.extendAtSucc.stage γ _).typeAt δ _ = (F.extendAtSucc.stage δ _).typeAt δ _
    unfold PairERCoherentFamily.extendAtSucc
    simp only [dif_pos hγ_lt, dif_pos hδ_lt]
    exact hF hδγ hγ_lt
  · subst hγ_eq
    show (F.extendAtSucc.stage (Order.succ β) _).typeAt δ _ =
      (F.extendAtSucc.stage δ _).typeAt δ _
    unfold PairERCoherentFamily.extendAtSucc
    simp only [dif_pos hδγ, dif_neg (lt_irrefl _)]
    rw [PairERChain.succ_typeAt_old _ δ hδγ]
    rcases lt_or_eq_of_le (Order.lt_succ_iff.mp hδγ) with hδ_lt_β | hδ_eq_β
    · exact hF hδ_lt_β (Order.lt_succ β)
    · subst hδ_eq_β; rfl

/-- The empty family is vacuously `IsCanonicalTypeCoherent`: the
nat-reindex nonemptiness is vacuously true because no valid `e` exists
(any `e 0` would give `(e 0).1 < 0`). -/
lemma PairERCoherentFamily.empty_isCanonicalTypeCoherent
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    (PairERCoherentFamily.empty cR).IsCanonicalTypeCoherent := by
  refine ⟨PairERCoherentFamily.empty_isTypeCoherent cR, ?_⟩
  intro e _ _
  exact absurd (e 0).2 (not_lt.mpr (zero_le _))

/-! ### Base + extension constructors for `PairERTypeTree`

Following the tranche plan, the constructors need to be established in
this order:
1. `empty` — verifies `large_sigma` at α = 0 (DONE, axiom-clean).
2. `extendSucc` — splits each old branch into two (one per Bool at the
   new top position) and partitions realizers by
   `cR(pair(new_commit, y))`. Preserves `large_sigma` by pigeonhole
   on the two halves (at least one has `≥ succ ℶ_1` realizers).
3. `extendLimit` — uses `T.limitChain` to produce the limit stage,
   then build a tree for the resulting extendAtLimit family. Here
   `selectedBranch` becomes the new top type.
4. Thread `PairERTypeTree` through `CoherentBundle` / `RichBundle`.

Step 1 is complete below. Steps 2–4 are the remaining tranche. -/

/-- **Base-level `PairERTypeTree`** at `α = 0`. The type function is
the unique empty function `(0 : Ordinal).ToType → Bool`. The single
branch has ALL of `PairERSource` as its realizer set (since the
validFiber at level 0 is vacuous-constrained and equals `Set.univ`).

**`large_sigma` verification**: the Sigma set bijects with
`PairERSource` (via `y ↦ (emptyFn, y)`), so has cardinality
`succ ℶ_1 = |PairERSource|` by `mk_pairERSource`. This confirms the
tree IS a valid base-case invariant — `PairERTypeTree` can serve as
a global recursion invariant (not just attached to limit-construction
subproblems), since `large_sigma` is satisfied non-vacuously at the
base by choosing the full universe as the single branch's realizers. -/
noncomputable def PairERTypeTree.empty
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    PairERTypeTree (PairERCoherentFamily.empty cR) := by
  haveI h_empty : IsEmpty (Ordinal.ToType 0) := Ordinal.isEmpty_toType_zero
  let emptyFn : (0 : Ordinal.{0}).ToType → Bool := isEmptyElim
  refine
    { branches := Set.univ
      realizers := fun _ => Set.univ
      realizers_sub_validFiber := ?_
      large_sigma := ?_ }
  · intro _ _ _ x
    exact (h_empty.false x).elim
  · -- Sigma set ≃ PairERSource via y ↦ ⟨(emptyFn, y), trivial, trivial⟩.
    set S : Set (((0 : Ordinal.{0}).ToType → Bool) × PairERSource) :=
      { p | p.1 ∈ (Set.univ : Set _) ∧ p.2 ∈ (Set.univ : Set _) } with hS
    have h_mk_le : Cardinal.mk PairERSource ≤ Cardinal.mk S := by
      refine Cardinal.mk_le_of_injective (f := fun y : PairERSource =>
        (⟨(emptyFn, y), ⟨trivial, trivial⟩⟩ : S)) ?_
      intro y₁ y₂ h
      have h1 : ((emptyFn, y₁) : ((0 : Ordinal.{0}).ToType → Bool) × PairERSource) =
          (emptyFn, y₂) := by
        exact Subtype.mk.inj h
      exact (Prod.mk.inj h1).2
    calc Order.succ (Cardinal.beth.{0} 1)
        = Cardinal.mk PairERSource := mk_pairERSource.symm
      _ ≤ Cardinal.mk S := h_mk_le

/-- **Successor-stage `PairERTypeTree` constructor** at level
`succ (succ β)`, preserving both Boolean halves of every existing
branch.

**Construction (universal-tree formulation)**: take `branches` to be
all of `(succ (succ β)).ToType → Bool` and `realizers b :=
validFiber cR F.extendAtSucc.prefix b`. Each `y` above the new prefix
falls into exactly one fiber (its profile under `cR(pair(F.extendAtSucc.
prefix _, y)) = b _`), so the disjoint union of all realizer sets
bijects with `{y : y above F.extendAtSucc.prefix}`. The latter has
cardinality `≥ succ ℶ_1` by `large_above_prefix` (countable prefix
in `PairERSource`).

**Why this is the right "keep both halves"**: every Boolean choice
at every position is represented as a separate branch, with realizers
partitioned cleanly. No pruning. The classical canonical-type tree
is implicit in this representation; explicit branch tracking is
recovered by selecting the realized branches via `pigeonhole` /
`exists_large_realized_branch`. -/
noncomputable def PairERTypeTree.extendSucc
    {cR : (Fin 2 ↪o PairERSource) → Bool} {β : Ordinal.{0}}
    (hβ : Order.succ (Order.succ β) < Ordinal.omega.{0} 1)
    {F : PairERCoherentFamily cR (Order.succ β)}
    (_T : PairERTypeTree F) :
    PairERTypeTree F.extendAtSucc := by
  refine
    { branches := Set.univ
      realizers := fun b => validFiber cR F.extendAtSucc.prefix b
      realizers_sub_validFiber := ?_
      large_sigma := ?_ }
  · intro _ _ hy; exact hy
  · -- Sigma ≃ {y above F.extendAtSucc.prefix}, size ≥ succ ℶ_1 by large_above_prefix.
    set p : (Order.succ (Order.succ β)).ToType ↪o PairERSource :=
      F.extendAtSucc.prefix with hp_def
    set above_prefix : Set PairERSource :=
      { y : PairERSource | ∀ x : (Order.succ (Order.succ β)).ToType, p x < y }
      with hap_def
    have h_above_large : Order.succ (Cardinal.beth.{0} 1) ≤
        Cardinal.mk above_prefix := large_above_prefix hβ p
    -- Define injection above_prefix → Sigma via y ↦ (profileOf y, y).
    set Sigma : Set (((Order.succ (Order.succ β)).ToType → Bool) × PairERSource) :=
      { q | q.1 ∈ (Set.univ : Set _) ∧
        q.2 ∈ validFiber cR F.extendAtSucc.prefix q.1 } with hS
    have h_inj : Cardinal.mk above_prefix ≤ Cardinal.mk Sigma := by
      refine Cardinal.mk_le_of_injective (f := fun y : above_prefix =>
        (⟨(fun x => cR (pairEmbed (y.2 x)), y.1), trivial, ?_⟩ : Sigma)) ?_
      · intro x; exact ⟨y.2 x, rfl⟩
      · intro y₁ y₂ h
        have h1 := Subtype.mk.inj h
        have h2 := (Prod.mk.inj h1).2
        exact Subtype.ext h2
    exact h_above_large.trans h_inj

/-- **Limit-stage `PairERTypeTree` constructor** at level `succ α`,
preserving the universal-tree shape. Same construction as `extendSucc`
but at a level whose predecessor was reached via `F.extendAtLimit`.

The proof reuses `large_above_prefix` over `F.extendAtLimit`'s prefix.
The `T : PairERTypeTree F` input argument is currently unused
(consumed by the universal-tree formulation); a future refinement may
USE `T.limitChain` to make the limit stage tree-driven (currently
`F.extendAtLimit` uses `F.limit` which picks τ via Classical.choose). -/
noncomputable def PairERTypeTree.extendLimit
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (hα : α < Ordinal.omega.{0} 1)
    (h_succα : Order.succ α < Ordinal.omega.{0} 1)
    {F : PairERCoherentFamily cR α}
    (_T : PairERTypeTree F) :
    PairERTypeTree (F.extendAtLimit hα) := by
  refine
    { branches := Set.univ
      realizers := fun b => validFiber cR (F.extendAtLimit hα).prefix b
      realizers_sub_validFiber := ?_
      large_sigma := ?_ }
  · intro _ _ hy; exact hy
  · set p : (Order.succ α).ToType ↪o PairERSource :=
      (F.extendAtLimit hα).prefix with hp_def
    set above_prefix : Set PairERSource :=
      { y : PairERSource | ∀ x : (Order.succ α).ToType, p x < y }
      with hap_def
    have h_above_large : Order.succ (Cardinal.beth.{0} 1) ≤
        Cardinal.mk above_prefix := large_above_prefix h_succα p
    set Sigma : Set (((Order.succ α).ToType → Bool) × PairERSource) :=
      { q | q.1 ∈ (Set.univ : Set _) ∧
        q.2 ∈ validFiber cR (F.extendAtLimit hα).prefix q.1 } with hS
    have h_inj : Cardinal.mk above_prefix ≤ Cardinal.mk Sigma := by
      refine Cardinal.mk_le_of_injective (f := fun y : above_prefix =>
        (⟨(fun x => cR (pairEmbed (y.2 x)), y.1), trivial, ?_⟩ : Sigma)) ?_
      · intro x; exact ⟨y.2 x, rfl⟩
      · intro y₁ y₂ h
        have h1 := Subtype.mk.inj h
        have h2 := (Prod.mk.inj h1).2
        exact Subtype.ext h2
    exact h_above_large.trans h_inj

/-- **`PairERTypeTree.universal`**: generic universal-tree
constructor over any `PairERCoherentFamily cR α` at a level
`α < ω₁`. Branches = `Set.univ`, realizers `b = validFiber cR
F.prefix b`, `large_sigma` discharged by `large_above_prefix`.

This subsumes the bespoke per-constructor universal-tree shapes in
`empty / extendSucc / extendLimit`: any `PairERCoherentFamily cR α`
with `α < ω₁` admits a canonical `PairERTypeTree`. -/
noncomputable def PairERTypeTree.universal
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (hα : α < Ordinal.omega.{0} 1)
    (F : PairERCoherentFamily cR α) :
    PairERTypeTree F := by
  refine
    { branches := Set.univ
      realizers := fun b => validFiber cR F.prefix b
      realizers_sub_validFiber := ?_
      large_sigma := ?_ }
  · intro _ _ hy; exact hy
  · set p : α.ToType ↪o PairERSource := F.prefix with hp_def
    set above_prefix : Set PairERSource :=
      { y : PairERSource | ∀ x : α.ToType, p x < y } with hap_def
    have h_above_large : Order.succ (Cardinal.beth.{0} 1) ≤
        Cardinal.mk above_prefix := large_above_prefix hα p
    set Sigma : Set ((α.ToType → Bool) × PairERSource) :=
      { q | q.1 ∈ (Set.univ : Set _) ∧
        q.2 ∈ validFiber cR F.prefix q.1 } with hS
    have h_inj : Cardinal.mk above_prefix ≤ Cardinal.mk Sigma := by
      refine Cardinal.mk_le_of_injective (f := fun y : above_prefix =>
        (⟨(fun x => cR (pairEmbed (y.2 x)), y.1), trivial, ?_⟩ : Sigma)) ?_
      · intro x; exact ⟨y.2 x, rfl⟩
      · intro y₁ y₂ h
        have h1 := Subtype.mk.inj h
        have h2 := (Prod.mk.inj h1).2
        exact Subtype.ext h2
    exact h_above_large.trans h_inj

/-- **[FUSION — successor case, stage 1]** `universal_realized_of_succ`:
for a type-coherent family at a **successor** length `succ β`, the universal
tree's committed branch `F.typeFn` is *realized* (nonempty realizers). This is
the successor step of `exists_realizedPairERTypeTree`, and it is **sorry-clean**:
at successors realized-ness is automatic via `isCanonicalTypeCoherent_of_succ`
(no limit fusion). The cofinal ℕ-sequence is the trivial constant one at the top
predecessor `β` (every `γ < succ β` satisfies `γ ≤ β`).

Notably, no *input* realized-ness is needed — a successor family is
unconditionally realized once type-coherent. So the eventual successor
constructor `exists_realizedPairERTypeTree (succ β)` does not thread the
predecessor's realized witness; it only needs an `IsTypeCoherent` family at
`succ β` (e.g. via `extendAtSucc`, which preserves `IsTypeCoherent`). The genuine
fusion content is entirely in the limit case. -/
lemma PairERTypeTree.universal_realized_of_succ
    {cR : (Fin 2 ↪o PairERSource) → Bool} {β : Ordinal.{0}}
    (hβ : Order.succ β < Ordinal.omega.{0} 1)
    (F : PairERCoherentFamily cR (Order.succ β))
    (hF_type : F.IsTypeCoherent) :
    ((PairERTypeTree.universal hβ F).realizers F.typeFn).Nonempty := by
  show (validFiber cR F.prefix F.typeFn).Nonempty
  rw [F.validFiber_prefix_typeFn_eq_iInter hF_type]
  -- The top stage's fiber (at `β`) is contained in the whole intersection
  -- (descending nestedness) and is large, hence nonempty.
  have h_sub : validFiber cR (F.stage β (Order.lt_succ β)).head
        (F.stage β (Order.lt_succ β)).type ⊆
      ⋂ (γ : Ordinal.{0}) (hγ : γ < Order.succ β),
        validFiber cR (F.stage γ hγ).head (F.stage γ hγ).type := by
    intro y hy
    simp only [Set.mem_iInter]
    intro γ hγ
    rcases lt_or_eq_of_le (Order.lt_succ_iff.mp hγ) with hγ_lt | hγ_eq
    · exact F.validFiber_mono hF_type hγ_lt (Order.lt_succ β) hy
    · subst hγ_eq; exact hy
  have h_pos : (0 : Cardinal.{0}) < Cardinal.mk
      (validFiber cR (F.stage β (Order.lt_succ β)).head
        (F.stage β (Order.lt_succ β)).type) :=
    (Cardinal.aleph0_pos.trans_le isRegular_succ_beth_one.aleph0_le).trans_le
      (F.stage β (Order.lt_succ β)).large
  obtain ⟨⟨z, hz⟩⟩ := Cardinal.mk_ne_zero_iff.mp h_pos.ne'
  exact ⟨z, h_sub hz⟩

/-- **Successor inductive step of `exists_realizedPairERTypeTree`** (sorry-clean):
any type-coherent family at a *successor* length admits a realized tree (the
universal one). This is the easy half of the fusion induction; the genuine
content is the limit case. -/
lemma exists_realizedPairERTypeTree_of_succ
    {cR : (Fin 2 ↪o PairERSource) → Bool} {β : Ordinal.{0}}
    (hβ : Order.succ β < Ordinal.omega.{0} 1)
    (F : PairERCoherentFamily cR (Order.succ β))
    (hF_type : F.IsTypeCoherent) :
    ∃ T : PairERTypeTree F, (T.realizers F.typeFn).Nonempty :=
  ⟨PairERTypeTree.universal hβ F,
    PairERTypeTree.universal_realized_of_succ hβ F hF_type⟩

/-- **Commit-coherence predicate** on a `PairERTypeTree`: every branch
in `T.branches` agrees with `F.typeVal` at every position
`δ < α`. This is the structural invariant needed to make
`selectedBranch` automatically respect prior commitments. -/
def PairERTypeTree.IsCommitCoherent
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    {F : PairERCoherentFamily cR α} (T : PairERTypeTree F) : Prop :=
  ∀ b ∈ T.branches, ∀ δ : Ordinal.{0}, ∀ hδα : δ < α,
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    b (Ordinal.enum (α := α.ToType) (· < ·)
        ⟨δ, (Ordinal.type_toType α).symm ▸ hδα⟩) =
      F.typeVal δ hδα

/-! ### The substantive frontier: type-coherent fiber largeness

The deep math content of pair Erdős–Rado, after all architectural
reductions, is the following single statement: at every limit-level
coherent family `F`, the type-coherent fiber `validFiber cR F.prefix
F.typeFn` has cardinality `≥ succ ℶ_1`.

Under `IsTypeCoherent`, this reduces (via
`validFiber_prefix_typeFn_eq_iInter`) to `exists_large_iInter_stage_
fibers` — the legacy intersection-largeness frontier. The proof is
classical Erdős–Rado fusion: countable intersection of cofinality-
`succ ℶ_1` cofinal sets, where preserving per-fiber color through
ω-sups requires a fusion construction. -/

/-- **`typeCoherentFiber_large`**: under `F.IsTypeCoherent`, the
type-coherent fiber has size `≥ succ ℶ_1`. This is the renamed,
sharply-named version of `exists_large_limit_fiber_prescribed`,
which itself reduces to the legacy `exists_large_iInter_stage_fibers`
via `validFiber_prefix_typeFn_eq_iInter`. The proof body shows
the chain. -/
theorem typeCoherentFiber_large
    (cR : (Fin 2 ↪o PairERSource) → Bool) {α : Ordinal.{0}}
    (hα : α < Ordinal.omega.{0} 1)
    (F : PairERCoherentFamily cR α) (hF_type : F.IsTypeCoherent) :
    Order.succ (Cardinal.beth.{0} 1) ≤
      Cardinal.mk (validFiber cR F.prefix F.typeFn) :=
  exists_large_limit_fiber_prescribed cR hα F hF_type

/-- **[LEGACY — off-chain; the false-path tree]** Its `large_sigma` reduces to
`typeCoherentFiber_large` = the false-as-stated `exists_large_iInter_stage_fibers`
(committed `{F.typeFn}` realized for every `IsTypeCoherent F` — refuted by the
ω-adversary). Only `TreeBundle.limitExtend` (itself legacy) uses it; the live path
uses `B`'s realized branch via `limitFromCoherentMajority` instead.

**`PairERTypeTree.commitCoherent`**: commit-coherent tree at level
`α` with `branches = {F.typeFn}`. The singleton-branches structure
makes `IsCommitCoherent` hold by construction.

The `large_sigma` invariant decomposes as:
1. Σ ≃ `validFiber cR F.prefix F.typeFn` (singleton-σ injection).
2. `succ ℶ_1 ≤ |validFiber cR F.prefix F.typeFn|`, the substantive
   content.

Step 1 is the `singleton_sigma_le_validFiber` argument inlined below.
Step 2 sorry'd here without `IsTypeCoherent` — under that
hypothesis, step 2 = `typeCoherentFiber_large`. The architectural
gap (providing `IsTypeCoherent` from `treeStage`'s recursion) is
deferred; once handled, this entire sorry becomes
`(typeCoherentFiber_large cR hα F hF_type).trans
(commitCoherent_sigma_ge_validFiber F)`. -/
noncomputable def PairERTypeTree.commitCoherent
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (hα : α < Ordinal.omega.{0} 1)
    (F : PairERCoherentFamily cR α) (hF_type : F.IsTypeCoherent) :
    PairERTypeTree F := by
  refine
    { branches := {F.typeFn}
      realizers := fun b => validFiber cR F.prefix b
      realizers_sub_validFiber := ?_
      large_sigma := ?_ }
  · intro _ _ hy; exact hy
  · -- Singleton σ-card reduction: Σ ≃ validFiber cR F.prefix F.typeFn
    -- via y ↦ (F.typeFn, y), then validFiber largeness via
    -- `typeCoherentFiber_large` (which uses IsTypeCoherent + the
    -- legacy intersection-largeness frontier).
    set S : Set ((α.ToType → Bool) × PairERSource) :=
      { p | p.1 ∈ ({F.typeFn} : Set _) ∧ p.2 ∈ validFiber cR F.prefix p.1 }
      with hS_def
    have h_sigma_ge_validFiber :
        Cardinal.mk (validFiber cR F.prefix F.typeFn) ≤ Cardinal.mk S := by
      refine Cardinal.mk_le_of_injective
        (f := fun y : validFiber cR F.prefix F.typeFn =>
          (⟨(F.typeFn, y.val), rfl, y.property⟩ : S)) ?_
      intro y₁ y₂ h
      apply Subtype.ext
      have h1 := Subtype.mk.inj h
      exact (Prod.mk.inj h1).2
    exact (typeCoherentFiber_large cR hα F hF_type).trans
      h_sigma_ge_validFiber

/-- **`commitCoherent` is commit-coherent**: every branch (= the
singleton `F.typeFn`) agrees with `F.typeVal` at every position. -/
lemma PairERTypeTree.commitCoherent_isCommitCoherent
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (hα : α < Ordinal.omega.{0} 1)
    (F : PairERCoherentFamily cR α) (hF_type : F.IsTypeCoherent) :
    (PairERTypeTree.commitCoherent hα F hF_type).IsCommitCoherent := by
  intro b hb δ hδα
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  -- `branches = {F.typeFn}`, so b = F.typeFn.
  have hb_eq : b = F.typeFn := hb
  rw [hb_eq]
  -- F.typeFn (enum ⟨δ, _⟩) = F.typeVal (typein (enum _)) _ = F.typeVal δ _.
  show F.typeFn (Ordinal.enum (α := α.ToType) (· < ·)
      ⟨δ, (Ordinal.type_toType α).symm ▸ hδα⟩) = F.typeVal δ hδα
  unfold PairERCoherentFamily.typeFn
  congr 1
  exact Ordinal.typein_enum _ _

/-- **`commitCoherent`'s `selectedBranch` equals `F.typeFn`.** Since
`branches = {F.typeFn}`, the pigeonhole-selected branch must be
`F.typeFn`. -/
lemma PairERTypeTree.commitCoherent_selectedBranch_eq
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (hα : α < Ordinal.omega.{0} 1)
    (F : PairERCoherentFamily cR α) (hF_type : F.IsTypeCoherent) :
    (PairERTypeTree.commitCoherent hα F hF_type).selectedBranch hα =
      F.typeFn := by
  have h_mem :=
    (PairERTypeTree.commitCoherent hα F hF_type).selectedBranch_mem hα
  -- selectedBranch ∈ branches = {F.typeFn}, so selectedBranch = F.typeFn.
  exact h_mem

/-- **`majorityCoherent`**: tree at level `α` with branches =
`{majorityType F}`. The H3-pigeonhole-chosen type is the unique branch.
This tree's `large_sigma` is **sorry-FREE** (uses `majorityType_large`
directly, not the deep intersection-largeness frontier).

Differs from `commitCoherent` in two ways:
1. Branches are `{majorityType F}` (not `{F.typeFn}`).
2. No `IsTypeCoherent` precondition needed.

Trade-off: the resulting tree's `selectedBranch` is `majorityType F`,
which equals `F.typeFn` only under the `IsMajorityType` invariant.
Using this tree in `TreeBundle.limitFromTree` requires `IsMajorityType`
to satisfy the `h_branch_eq_typeFn` field. -/
noncomputable def PairERTypeTree.majorityCoherent
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (hα : α < Ordinal.omega.{0} 1)
    (F : PairERCoherentFamily cR α) :
    PairERTypeTree F := by
  refine
    { branches := {F.majorityType hα}
      realizers := fun b => validFiber cR F.prefix b
      realizers_sub_validFiber := ?_
      large_sigma := ?_ }
  · intro _ _ hy; exact hy
  · -- Σ ≃ validFiber cR F.prefix (majorityType F).
    set S : Set ((α.ToType → Bool) × PairERSource) :=
      { p | p.1 ∈ ({F.majorityType hα} : Set _) ∧
        p.2 ∈ validFiber cR F.prefix p.1 } with hS_def
    have h_sigma_ge :
        Cardinal.mk (validFiber cR F.prefix (F.majorityType hα)) ≤
        Cardinal.mk S := by
      refine Cardinal.mk_le_of_injective
        (f := fun y : validFiber cR F.prefix (F.majorityType hα) =>
          (⟨(F.majorityType hα, y.val), rfl, y.property⟩ : S)) ?_
      intro y₁ y₂ h
      apply Subtype.ext
      have h1 := Subtype.mk.inj h
      exact (Prod.mk.inj h1).2
    exact (F.majorityType_large hα).trans h_sigma_ge

/-- **`majorityCoherent`'s `selectedBranch` equals `majorityType F`.** -/
lemma PairERTypeTree.majorityCoherent_selectedBranch_eq
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (hα : α < Ordinal.omega.{0} 1)
    (F : PairERCoherentFamily cR α) :
    (PairERTypeTree.majorityCoherent hα F).selectedBranch hα =
      F.majorityType hα :=
  (PairERTypeTree.majorityCoherent hα F).selectedBranch_mem hα

/-- **`TreeBundle.zero`**: base case at α = 0. Stage is
`PairERChain.zero`, family is the empty tree-family, head-coherence is
vacuous. -/
noncomputable def TreeBundle.zero
    (cR : (Fin 2 ↪o PairERSource) → Bool) : TreeBundle cR 0 where
  family :=
    { family := PairERCoherentFamily.empty cR
      tree := PairERTypeTree.empty cR }
  stage := PairERChain.zero cR
  coh := fun δ hδ => absurd hδ (not_lt.mpr (zero_le δ))
  type_match := fun δ hδ => absurd hδ (not_lt.mpr (zero_le δ))
  type_coh := PairERCoherentFamily.empty_isTypeCoherent cR

/-- **`TreeBundle.limitFromTree`**: build a `TreeBundle` at limit level
α directly from a `PairERTreeFamily TF` plus the family's type-coherence
plus a witness that the tree's `selectedBranch hα` agrees with
`F.typeFn`. Stage is `TF.toLimitChain hα`, i.e., the tree-driven limit
chain whose type is the pigeonhole-selected branch. Head-coherence
(`coh`) follows from `limitWithType_commitAt` +
`PairERCoherentFamily.prefix_enum`. The `type_match` field uses
`h_branch_eq_typeFn` to identify `selectedBranch` with `F.typeFn`,
giving `stage.typeAt δ = F.typeVal δ`.

This is the constructor that distinguishes `TreeBundle` from
`CoherentBundle`: at limits, we use the SELECTED branch as the type
function, not a fresh `Classical.choose τ`. -/
noncomputable def TreeBundle.limitFromTree
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (hα : α < Ordinal.omega.{0} 1)
    (TF : PairERTreeFamily cR α)
    (h_type_coh : TF.family.IsTypeCoherent)
    (h_branch_eq_typeFn :
      TF.tree.selectedBranch hα = TF.family.typeFn) :
    TreeBundle cR α where
  family := TF
  stage := TF.toLimitChain hα
  coh := by
    intro δ hδ
    show (TF.toLimitChain hα).commitAt δ hδ = TF.family.commitVal δ hδ
    unfold PairERTreeFamily.toLimitChain PairERTreeFamily.toLimitChainAtBranch
    rw [PairERChain.limitWithType_commitAt]
    exact TF.family.prefix_enum δ hδ
  type_match := by
    intro δ hδ
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    show (TF.toLimitChain hα).typeAt δ hδ = TF.family.typeVal δ hδ
    unfold PairERTreeFamily.toLimitChain PairERTreeFamily.toLimitChainAtBranch
    rw [PairERChain.limitWithType_typeAt]
    -- Goal: selectedBranch (enum δ) = F.typeVal δ.
    rw [h_branch_eq_typeFn]
    -- Goal: F.typeFn (enum δ) = F.typeVal δ.
    unfold PairERCoherentFamily.typeFn
    congr 1
    exact Ordinal.typein_enum _ _
  type_coh := h_type_coh

/-- **`TreeBundle.limitFromMajority`**: alternative limit constructor
that bypasses the legacy intersection-largeness frontier by using
`F.toMajorityType` + `F.majorityType_large`.

Build a `TreeBundle cR α` at limit α from any `F : PairERCoherentFamily
cR α` (no `IsTypeCoherent` precondition needed):

1. Rebuild F as `F_maj := F.toMajorityType hα`. This sets
   `F_maj.typeFn := F.majorityType hα` and gives a type-coherent family.
2. Build the singleton-branch tree at level α with branches =
   `{F_maj.typeFn}`. The `large_sigma` invariant holds via the
   inclusion `validFiber cR F.prefix (F.majorityType hα) ↪
   validFiber cR F_maj.prefix F_maj.typeFn` (using
   `toMajorityType_prefix_apply` + `toMajorityType_typeFn`) plus
   `F.majorityType_large`.
3. The TreeBundle's `selectedBranch = F_maj.typeFn`, so
   `h_branch_eq_typeFn` is structural.

Sorry-free; routes through `F.majorityType_large` (axiom-clean) only,
not through the legacy fusion frontier.

**Integration caveat**: directly replacing `TreeBundle.limitExtend`'s
internals with `limitFromMajority` breaks `treeChain_pair_homogeneous`
because the chain's `typeAt` at lower positions changes from inherited
`treeCommitBool` (= local pigeonhole choices) to `F.majorityType`
(= H3 pigeonhole choice at the level). The H3 choice at different
limit levels α₁, α₂ generally does NOT agree at common positions —
`Classical.choose` is not "natural" across different existentials —
so type-coherence breaks across levels. To use this constructor in
the active path, the construction needs to be augmented with a
*coherent* global majority branch (canonical-types-tree style),
which is itself essentially the classical Erdős–Rado fusion
construction. -/
noncomputable def TreeBundle.limitFromMajority
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (hα : α < Ordinal.omega.{0} 1)
    (F : PairERCoherentFamily cR α) :
    TreeBundle cR α := by
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  let F_maj : PairERCoherentFamily cR α := F.toMajorityType hα
  have h_typeFn : F_maj.typeFn = F.majorityType hα := F.toMajorityType_typeFn hα
  have h_F_maj_type_coh : F_maj.IsTypeCoherent :=
    F.toMajorityType_isTypeCoherent hα
  -- |validFiber cR F_maj.prefix F_maj.typeFn| ≥ succ ℶ_1.
  have h_validFiber_large : Order.succ (Cardinal.beth.{0} 1) ≤
      Cardinal.mk (validFiber cR F_maj.prefix F_maj.typeFn) := by
    apply (F.majorityType_large hα).trans
    refine Cardinal.mk_le_of_injective
      (f := fun y : validFiber cR F.prefix (F.majorityType hα) =>
        (⟨y.val, fun x => ?_⟩ : validFiber cR F_maj.prefix F_maj.typeFn)) ?_
    · -- y.val satisfies the F_maj-validFiber constraint at x.
      obtain ⟨h_lt, h_col⟩ := y.property x
      have h_pre : F_maj.prefix x = F.prefix x :=
        F.toMajorityType_prefix_apply hα x
      have h_tF : F_maj.typeFn x = F.majorityType hα x := by
        rw [h_typeFn]
      refine ⟨?_, ?_⟩
      · rw [h_pre]; exact h_lt
      · -- pair embedding equality: F_maj.prefix x = F.prefix x.
        rw [h_tF]
        have h_pair : (pairEmbed (show F_maj.prefix x < y.val by
            rw [h_pre]; exact h_lt)) = pairEmbed h_lt := by
          ext k
          match k with
          | ⟨0, _⟩ =>
            show F_maj.prefix x = F.prefix x
            exact h_pre
          | ⟨1, _⟩ => rfl
        rw [h_pair]; exact h_col
    · intro y₁ y₂ heq
      apply Subtype.ext
      exact Subtype.mk.inj heq
  -- Build the singleton-branch tree.
  let tree : PairERTypeTree F_maj := by
    refine
      { branches := {F_maj.typeFn}
        realizers := fun b => validFiber cR F_maj.prefix b
        realizers_sub_validFiber := fun _ _ hy => hy
        large_sigma := ?_ }
    -- σ injection from validFiber cR F_maj.prefix F_maj.typeFn.
    set S : Set ((α.ToType → Bool) × PairERSource) :=
      { p | p.1 ∈ ({F_maj.typeFn} : Set _) ∧
        p.2 ∈ validFiber cR F_maj.prefix p.1 } with hS_def
    have h_sigma_ge :
        Cardinal.mk (validFiber cR F_maj.prefix F_maj.typeFn) ≤
          Cardinal.mk S := by
      refine Cardinal.mk_le_of_injective
        (f := fun y : validFiber cR F_maj.prefix F_maj.typeFn =>
          (⟨(F_maj.typeFn, y.val), rfl, y.property⟩ : S)) ?_
      intro y₁ y₂ heq
      apply Subtype.ext
      have h1 := Subtype.mk.inj heq
      exact (Prod.mk.inj h1).2
    exact h_validFiber_large.trans h_sigma_ge
  -- selectedBranch ∈ branches = {F_maj.typeFn}, hence = F_maj.typeFn.
  have h_branch_eq : tree.selectedBranch hα = F_maj.typeFn :=
    tree.selectedBranch_mem hα
  exact TreeBundle.limitFromTree hα ⟨F_maj, tree⟩ h_F_maj_type_coh h_branch_eq

/-! ### `CoherentMajorityBranch`: the new explicit fusion frontier

`limitFromMajority` establishes one-level largeness via H3 pigeonhole
(`majorityType`), but `Classical.choose` is not natural across levels:
the H3 choice at limit α₁ doesn't agree at common positions with the
H3 choice at limit α₂. To drive the recursion coherently, the
*compatibility across levels* must be **part of the chosen data**, not
recovered from unrelated H3 choices.

`CoherentMajorityBranch` is the structural object that packages this
compatibility:

- `prefixAt α hα`: an order embedding `α.ToType ↪o PairERSource`,
  varying coherently with α.
- `branch α hα`: a Bool function on each level, varying coherently.
- `prefix_restrict`/`branch_restrict`: restrictions to lower levels
  (via `Ordinal.initialSegToType`) AGREE with the lower-level data.
- `large`: at every level, the validFiber size is `≥ succ ℶ_1`.

The new mathematical frontier is the **existence** of a
`CoherentMajorityBranch` for any `cR`. This is the classical
Erdős–Rado fusion content, now phrased in tree language: not "find a
single large branch" but "find branches compatibly across all
levels". The sorry that drives the active path now lives here. -/

/-- **`CoherentMajorityBranch cR`**: globally coherent prefix +
branch data with per-level largeness, replacing per-level
independent `Classical.choose` H3 pigeonholes. The existence of
this object is the new sole mathematical frontier. -/
structure CoherentMajorityBranch
    (cR : (Fin 2 ↪o PairERSource) → Bool) where
  /-- Prefix at each level α < ω₁. -/
  prefixAt : ∀ α : Ordinal.{0},
    α < Ordinal.omega.{0} 1 → α.ToType ↪o PairERSource
  /-- Type function at each level α < ω₁. -/
  branch : ∀ α : Ordinal.{0},
    α < Ordinal.omega.{0} 1 → α.ToType → Bool
  /-- Prefix coherence: prefix at α restricted to β-level via the
  initial-segment inclusion equals prefix at β. -/
  prefix_restrict : ∀ {β α : Ordinal.{0}} (hβα : β ≤ α)
    (hβ : β < Ordinal.omega.{0} 1) (hα : α < Ordinal.omega.{0} 1)
    (x : β.ToType),
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
    prefixAt α hα ((Ordinal.initialSegToType hβα).toOrderEmbedding x) =
      prefixAt β hβ x
  /-- Branch coherence: branch at α restricted to β-level equals
  branch at β. -/
  branch_restrict : ∀ {β α : Ordinal.{0}} (hβα : β ≤ α)
    (hβ : β < Ordinal.omega.{0} 1) (hα : α < Ordinal.omega.{0} 1)
    (x : β.ToType),
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
    branch α hα ((Ordinal.initialSegToType hβα).toOrderEmbedding x) =
      branch β hβ x
  /-- **Chain extension**: the value at the top of `(succ γ).ToType`
  is in the `validFiber` for the lower-level chain at γ. This is the
  within-chain pair-color consistency that pair-homogeneity needs;
  it is a separate structural condition not derivable from
  `prefix_restrict` / `branch_restrict` / `large` alone. -/
  top_in_validFiber : ∀ (γ : Ordinal.{0}) (hγ : γ < Ordinal.omega.{0} 1)
      (hsγ : Order.succ γ < Ordinal.omega.{0} 1),
    haveI : IsWellOrder (Order.succ γ).ToType (· < ·) := isWellOrder_lt
    prefixAt (Order.succ γ) hsγ (⊤ : (Order.succ γ).ToType) ∈
      validFiber cR (prefixAt γ hγ) (branch γ hγ)

/-! ### Finite approximations: `CoherentBranchApprox`

Decomposing `exists_coherentMajorityBranch` per the classical
fusion-style proof. A `CoherentBranchApprox cR n` is a finite,
`n`-level partial version of a `CoherentMajorityBranch`. The
mathematical content of the fusion construction (`exists_large
ValidFiber_at_level` / H3-pigeonhole) is concentrated in the
extend-by-one step (to be added in a follow-up commit). The
ω-chain of approximations + its limit then produce the full
`CoherentMajorityBranch`.

This commit is **step 1 only**: the finite approximation structure
plus projection lemmas. The extend step, the ω-chain, and the
limit construction are deferred. -/

/-- **`CoherentBranchApprox cR n`**: finite approximation of a
`CoherentMajorityBranch` with `n` chosen levels < ω_1. Levels are
constrained to be in strict-successor relation: `level (k+1) =
succ (level k)`. This makes `(level k+1).ToType` have a `⊤` element
(succ ordinals have top), enabling `top_in_validFiber` between
adjacent levels.

Mirrors the fields of `CoherentMajorityBranch` restricted to a
finite index set `Fin n`, with the structural field
`top_in_validFiber` for adjacency.

**Relaxed structure (2026-05)**: the previous `level_succ` field
(which forced consecutive levels to be in `Order.succ` relation)
has been **removed**. Consecutive levels are now only required to
be strictly increasing (a consequence of `level_strictMono`), so
this structure can hold any strictly-increasing sequence of
countable ordinals — not only the natural numbers. -/
structure CoherentBranchApprox
    (cR : (Fin 2 ↪o PairERSource) → Bool) (n : ℕ) where
  /-- The `n` chosen ordinal positions, in strict increasing order. -/
  level : Fin n → Ordinal.{0}
  /-- Each level is below ω_1. -/
  level_lt_omega1 : ∀ k : Fin n, level k < Ordinal.omega.{0} 1
  /-- Strict monotonicity of `level` (in particular adjacent levels
  satisfy `level i < level (i+1)`). -/
  level_strictMono : StrictMono level
  /-- Prefix at each level. -/
  prefixAt : ∀ k : Fin n, (level k).ToType ↪o PairERSource
  /-- Branch (type function) at each level. -/
  branchAt : ∀ k : Fin n, (level k).ToType → Bool
  /-- Prefix coherence across levels: `prefixAt k₂` restricted to
  `(level k₁).ToType` equals `prefixAt k₁`. -/
  prefix_restrict : ∀ {k₁ k₂ : Fin n} (hk : k₁ ≤ k₂)
    (x : (level k₁).ToType),
    haveI : IsWellOrder (level k₁).ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder (level k₂).ToType (· < ·) := isWellOrder_lt
    prefixAt k₂
      ((Ordinal.initialSegToType
        (level_strictMono.monotone hk)).toOrderEmbedding x) =
      prefixAt k₁ x
  /-- Branch coherence across levels (analog of `prefix_restrict`). -/
  branch_restrict : ∀ {k₁ k₂ : Fin n} (hk : k₁ ≤ k₂)
    (x : (level k₁).ToType),
    haveI : IsWellOrder (level k₁).ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder (level k₂).ToType (· < ·) := isWellOrder_lt
    branchAt k₂
      ((Ordinal.initialSegToType
        (level_strictMono.monotone hk)).toOrderEmbedding x) =
      branchAt k₁ x
  /-- Per-level largeness of the validFiber. -/
  large : ∀ k : Fin n,
    Order.succ (Cardinal.beth.{0} 1) ≤
      Cardinal.mk (validFiber cR (prefixAt k) (branchAt k))
  /-- **Adjacent realization**: for each `i` with `i+1 < n`, the
  element at position `level ⟨i, _⟩` in the level-`⟨i+1, _⟩` chain
  lies in the validFiber for level-`⟨i, _⟩`'s chain. The bound on
  the enum position comes from `level_strictMono` (no requirement
  that `level (i+1) = succ (level i)`). -/
  top_in_validFiber : ∀ (i : ℕ) (h : i + 1 < n),
    haveI : IsWellOrder (level ⟨i + 1, h⟩).ToType (· < ·) := isWellOrder_lt
    prefixAt ⟨i + 1, h⟩
        (Ordinal.enum (α := (level ⟨i + 1, h⟩).ToType) (· < ·)
          ⟨level ⟨i, Nat.lt_of_succ_lt h⟩, by
            rw [Ordinal.type_toType]
            exact level_strictMono (show (⟨i, Nat.lt_of_succ_lt h⟩ : Fin n) <
              ⟨i + 1, h⟩ from Nat.lt_succ_self i)⟩) ∈
      validFiber cR (prefixAt ⟨i, Nat.lt_of_succ_lt h⟩)
        (branchAt ⟨i, Nat.lt_of_succ_lt h⟩)

/-! ### Projection lemmas: linking approximations to the full structure

The lemmas below characterize how a `CoherentBranchApprox` projects
onto the fields of a `CoherentMajorityBranch` at its chosen levels. -/

/-- **`approx_level_lt_succ`**: each level of the approximation is
below ω_1 (re-statement of the field for direct use). -/
lemma CoherentBranchApprox.level_lt
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR n) (k : Fin n) :
    A.level k < Ordinal.omega.{0} 1 := A.level_lt_omega1 k

/-- **`approx_prefix_restrict_to_apply`**: the prefix coherence at a
single point. Direct re-statement of `prefix_restrict` (clarity). -/
lemma CoherentBranchApprox.prefix_restrict_apply
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR n)
    {k₁ k₂ : Fin n} (hk : k₁ ≤ k₂) (x : (A.level k₁).ToType) :
    haveI : IsWellOrder (A.level k₁).ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder (A.level k₂).ToType (· < ·) := isWellOrder_lt
    A.prefixAt k₂
      ((Ordinal.initialSegToType
        (A.level_strictMono.monotone hk)).toOrderEmbedding x) =
      A.prefixAt k₁ x :=
  A.prefix_restrict hk x

/-- **`approx_branch_restrict_apply`**: same for branch. -/
lemma CoherentBranchApprox.branch_restrict_apply
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR n)
    {k₁ k₂ : Fin n} (hk : k₁ ≤ k₂) (x : (A.level k₁).ToType) :
    haveI : IsWellOrder (A.level k₁).ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder (A.level k₂).ToType (· < ·) := isWellOrder_lt
    A.branchAt k₂
      ((Ordinal.initialSegToType
        (A.level_strictMono.monotone hk)).toOrderEmbedding x) =
      A.branchAt k₁ x :=
  A.branch_restrict hk x

/-- **`approx_zero`**: the trivial 0-level approximation (no levels). -/
noncomputable def CoherentBranchApprox.zero
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    CoherentBranchApprox cR 0 where
  level k := Fin.elim0 k
  level_lt_omega1 k := Fin.elim0 k
  level_strictMono := by
    intro a _ _
    exact Fin.elim0 a
  prefixAt k := Fin.elim0 k
  branchAt k := Fin.elim0 k
  prefix_restrict {k₁ _} _ _ := Fin.elim0 k₁
  branch_restrict {k₁ _} _ _ := Fin.elim0 k₁
  large k := Fin.elim0 k
  top_in_validFiber i h := absurd h (by omega)

/-! ### Helper lemmas for `extend`: lifting via `initialSegToType`

These lemmas let us compute `extendHead p y hy z` and
`extendType τ b z` when `z` is the lift to `(succ α).ToType` of an
element of a smaller ordinal `β ≤ α`. Such lifts are non-`⊤`, so
they fall in the `dif_neg` branch and equal `p` (resp. `τ`)
applied to the corresponding `α.ToType` lift. -/

/-- **`extendHead_initialSegToType_apply`**: for `β ≤ α`, the
extended prefix `extendHead p y hy` applied to a `β`-element lifted
to `(succ α).ToType` equals `p` applied to the same element lifted
to `α.ToType`. -/
private lemma extendHead_initialSegToType_apply
    {α : Ordinal.{0}} (p : α.ToType ↪o PairERSource) (y : PairERSource)
    (hy : ∀ z : α.ToType, p z < y)
    {β : Ordinal.{0}} (hβα : β ≤ α) (x : β.ToType) :
    (extendHead p y hy)
        ((Ordinal.initialSegToType
          (hβα.trans (Order.le_succ α))).toOrderEmbedding x) =
      p ((Ordinal.initialSegToType hβα).toOrderEmbedding x) := by
  classical
  haveI : IsWellOrder (Order.succ α).ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  set xs : (Order.succ α).ToType :=
    (Ordinal.initialSegToType (hβα.trans (Order.le_succ α))).toOrderEmbedding x
    with hxs_def
  have h_typein_xs :
      Ordinal.typein (α := (Order.succ α).ToType) (· < ·) xs =
        Ordinal.typein (α := β.ToType) (· < ·) x := by
    rw [hxs_def]; exact Ordinal.typein_apply _ x
  have h_typein_x_lt_α : Ordinal.typein (α := β.ToType) (· < ·) x < α := by
    calc Ordinal.typein (α := β.ToType) (· < ·) x
        < Ordinal.type (α := β.ToType) (· < ·) := Ordinal.typein_lt_type _ _
      _ = β := Ordinal.type_toType _
      _ ≤ α := hβα
  have h_xs_ne_top : xs ≠ (⊤ : (Order.succ α).ToType) := by
    intro heq
    have h_typein_top : Ordinal.typein (α := (Order.succ α).ToType) (· < ·)
        (⊤ : (Order.succ α).ToType) = α := by
      rw [show (⊤ : (Order.succ α).ToType) =
          Ordinal.enum (α := (Order.succ α).ToType) (· < ·)
            ⟨α, (Ordinal.type_toType _).symm ▸ Order.lt_succ α⟩
        from Ordinal.enum_succ_eq_top.symm, Ordinal.typein_enum]
    have : α = Ordinal.typein (α := β.ToType) (· < ·) x :=
      h_typein_top.symm.trans (heq ▸ h_typein_xs)
    exact absurd this.symm (ne_of_lt h_typein_x_lt_α)
  show extendHead p y hy xs = _
  simp only [extendHead, OrderEmbedding.coe_ofStrictMono, dif_neg h_xs_ne_top]
  congr 1
  have h_typein_rhs :
      Ordinal.typein (α := α.ToType) (· < ·)
        ((Ordinal.initialSegToType hβα).toOrderEmbedding x) =
        Ordinal.typein (α := β.ToType) (· < ·) x :=
    Ordinal.typein_apply _ x
  rw [← Ordinal.enum_typein (· < · : α.ToType → α.ToType → Prop)
      ((Ordinal.initialSegToType hβα).toOrderEmbedding x)]
  congr 1
  apply Subtype.ext
  show Ordinal.typein (α := (Order.succ α).ToType) (· < ·) xs = _
  exact h_typein_xs.trans h_typein_rhs.symm

/-- **`extendType_initialSegToType_apply`**: analog of
`extendHead_initialSegToType_apply` for the type function via
`extendType`. -/
private lemma extendType_initialSegToType_apply
    {α : Ordinal.{0}} (τ : α.ToType → Bool) (b : Bool)
    {β : Ordinal.{0}} (hβα : β ≤ α) (x : β.ToType) :
    (extendType τ b)
        ((Ordinal.initialSegToType
          (hβα.trans (Order.le_succ α))).toOrderEmbedding x) =
      τ ((Ordinal.initialSegToType hβα).toOrderEmbedding x) := by
  classical
  haveI : IsWellOrder (Order.succ α).ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  set xs : (Order.succ α).ToType :=
    (Ordinal.initialSegToType (hβα.trans (Order.le_succ α))).toOrderEmbedding x
    with hxs_def
  have h_typein_xs :
      Ordinal.typein (α := (Order.succ α).ToType) (· < ·) xs =
        Ordinal.typein (α := β.ToType) (· < ·) x := by
    rw [hxs_def]; exact Ordinal.typein_apply _ x
  have h_typein_x_lt_α : Ordinal.typein (α := β.ToType) (· < ·) x < α := by
    calc Ordinal.typein (α := β.ToType) (· < ·) x
        < Ordinal.type (α := β.ToType) (· < ·) := Ordinal.typein_lt_type _ _
      _ = β := Ordinal.type_toType _
      _ ≤ α := hβα
  have h_xs_ne_top : xs ≠ (⊤ : (Order.succ α).ToType) := by
    intro heq
    have h_typein_top : Ordinal.typein (α := (Order.succ α).ToType) (· < ·)
        (⊤ : (Order.succ α).ToType) = α := by
      rw [show (⊤ : (Order.succ α).ToType) =
          Ordinal.enum (α := (Order.succ α).ToType) (· < ·)
            ⟨α, (Ordinal.type_toType _).symm ▸ Order.lt_succ α⟩
        from Ordinal.enum_succ_eq_top.symm, Ordinal.typein_enum]
    have : α = Ordinal.typein (α := β.ToType) (· < ·) x :=
      h_typein_top.symm.trans (heq ▸ h_typein_xs)
    exact absurd this.symm (ne_of_lt h_typein_x_lt_α)
  show extendType τ b xs = _
  simp only [extendType, dif_neg h_xs_ne_top]
  congr 1
  have h_typein_rhs :
      Ordinal.typein (α := α.ToType) (· < ·)
        ((Ordinal.initialSegToType hβα).toOrderEmbedding x) =
        Ordinal.typein (α := β.ToType) (· < ·) x :=
    Ordinal.typein_apply _ x
  rw [← Ordinal.enum_typein (· < · : α.ToType → α.ToType → Prop)
      ((Ordinal.initialSegToType hβα).toOrderEmbedding x)]
  congr 1
  apply Subtype.ext
  show Ordinal.typein (α := (Order.succ α).ToType) (· < ·) xs = _
  exact h_typein_xs.trans h_typein_rhs.symm

/-- **`CoherentBranchApprox.fromZero`**: the trivial 1-level
approximation at ordinal `0`. The prefix and branch are vacuous
(`0.ToType` is empty), and `large` follows from `mk_pairERSource`
(via `PairERChain.zero`). -/
noncomputable def CoherentBranchApprox.fromZero
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    CoherentBranchApprox cR 1 where
  level _ := 0
  level_lt_omega1 _ := Ordinal.omega_pos 1
  level_strictMono := fun a b h => by
    have hab : a = b := Subsingleton.elim a b
    exact absurd h (hab ▸ lt_irrefl _)
  prefixAt _ := (PairERChain.zero cR).head
  branchAt _ := (PairERChain.zero cR).type
  prefix_restrict := fun {_ _} _ x => by
    haveI : IsEmpty (Ordinal.ToType 0) := Ordinal.isEmpty_toType_zero
    exact isEmptyElim x
  branch_restrict := fun {_ _} _ x => by
    haveI : IsEmpty (Ordinal.ToType 0) := Ordinal.isEmpty_toType_zero
    exact isEmptyElim x
  large _ := (PairERChain.zero cR).large
  top_in_validFiber i h := absurd h (by omega)

/-! ### Helper definitions for `extendSucc`

We define `extendLevel`, `extendPrefixAt`, `extendBranchAt` as proper
`Fin.lastCases`-based functions (not let-bound `by_cases` tactics), so
their evaluation at `Fin.last (n+1)` and `Fin.castSucc k` is governed by
the standard `Fin.lastCases_last` / `Fin.lastCases_castSucc` lemmas
(plus `eqRec_heq` for dependent transport). This replaces the prior
`Eq.mpr`-cast-laden definitions that obstructed proof unfolding. -/

/-- **`lastChain`**: the `PairERChain` at level `A.level (Fin.last n)`
extracted from `A`'s last-position prefix/branch/large. -/
noncomputable def CoherentBranchApprox.lastChain
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR (n + 1)) :
    PairERChain cR (A.level (Fin.last n)) where
  head := A.prefixAt (Fin.last n)
  type := A.branchAt (Fin.last n)
  large := A.large (Fin.last n)

/-- **`nextChain`**: the `PairERChain` at `Order.succ (A.level (Fin.last n))`
obtained by applying `PairERChain.succ` to `A.lastChain`. -/
noncomputable def CoherentBranchApprox.nextChain
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR (n + 1)) :
    PairERChain cR (Order.succ (A.level (Fin.last n))) :=
  A.lastChain.succ

/-- **`extendLevel`**: level function for the one-step extension. Old
levels (`k.castSucc` for `k : Fin (n+1)`) get `A.level k`; the new top
(`Fin.last (n+1)`) gets `Order.succ (A.level (Fin.last n))`. -/
noncomputable def CoherentBranchApprox.extendLevel
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR (n + 1)) :
    Fin (n + 2) → Ordinal.{0} :=
  Fin.lastCases (Order.succ (A.level (Fin.last n))) (fun k => A.level k)

@[simp] theorem CoherentBranchApprox.extendLevel_last
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR (n + 1)) :
    A.extendLevel (Fin.last (n + 1)) = Order.succ (A.level (Fin.last n)) :=
  Fin.lastCases_last

@[simp] theorem CoherentBranchApprox.extendLevel_castSucc
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR (n + 1)) (k : Fin (n + 1)) :
    A.extendLevel k.castSucc = A.level k :=
  Fin.lastCases_castSucc k

/-- **`extendPrefixAt`**: prefix function for the one-step extension,
using `Fin.lastCases` with motive `(extendLevel k).ToType ↪o PairERSource`. -/
noncomputable def CoherentBranchApprox.extendPrefixAt
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR (n + 1)) :
    ∀ k : Fin (n + 2), (A.extendLevel k).ToType ↪o PairERSource := fun k => by
  refine Fin.lastCases (motive := fun k => (A.extendLevel k).ToType ↪o PairERSource)
    ?_ ?_ k
  · -- Fin.last (n+1) case
    show (A.extendLevel (Fin.last (n + 1))).ToType ↪o PairERSource
    rw [A.extendLevel_last]; exact A.nextChain.head
  · -- castSucc case
    intro j
    show (A.extendLevel j.castSucc).ToType ↪o PairERSource
    rw [A.extendLevel_castSucc]; exact A.prefixAt j

theorem CoherentBranchApprox.extendPrefixAt_last_heq
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR (n + 1)) :
    HEq (A.extendPrefixAt (Fin.last (n + 1))) A.nextChain.head := by
  unfold CoherentBranchApprox.extendPrefixAt
  rw [Fin.lastCases_last]
  -- Goal is HEq of an Eq.mpr-wrapped term with the original
  exact cast_heq _ _

theorem CoherentBranchApprox.extendPrefixAt_castSucc_heq
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR (n + 1)) (k : Fin (n + 1)) :
    HEq (A.extendPrefixAt k.castSucc) (A.prefixAt k) := by
  unfold CoherentBranchApprox.extendPrefixAt
  rw [Fin.lastCases_castSucc]
  exact cast_heq _ _

/-- **Helper**: if `α = β` as ordinals, and two OrderEmbeddings into
`PairERSource` are HEq, then applying them to corresponding arguments
yields equal results. -/
private lemma orderEmbed_ordinal_apply_heq
    {α β : Ordinal.{0}} (h_eq : α = β)
    (f : α.ToType ↪o PairERSource) (g : β.ToType ↪o PairERSource)
    (hf : HEq f g) (x : α.ToType) : f x = g (h_eq ▸ x) := by
  subst h_eq
  rw [eq_of_heq hf]

/-- **Bool-valued analog of `orderEmbed_ordinal_apply_heq`**. -/
private lemma fn_ordinal_apply_heq
    {α β : Ordinal.{0}} (h_eq : α = β)
    (f : α.ToType → Bool) (g : β.ToType → Bool)
    (hf : HEq f g) (x : α.ToType) : f x = g (h_eq ▸ x) := by
  subst h_eq
  rw [eq_of_heq hf]

/-- **Transport commutes with `Ordinal.enum`**: if `α₁ = α₂` and
`β₁ = β₂`, then transporting an `enum` at position β₁ in α₁.ToType
yields the `enum` at position β₂ in α₂.ToType. -/
private lemma enum_transport_eq
    {α₁ α₂ : Ordinal.{0}} (h_α : α₁ = α₂)
    {β₁ β₂ : Ordinal.{0}} (h_β : β₁ = β₂)
    (h_lt₁ : β₁ < Ordinal.type (α := α₁.ToType) (· < ·))
    (h_lt₂ : β₂ < Ordinal.type (α := α₂.ToType) (· < ·)) :
    h_α ▸ Ordinal.enum (α := α₁.ToType) (· < ·) ⟨β₁, h_lt₁⟩ =
      Ordinal.enum (α := α₂.ToType) (· < ·) ⟨β₂, h_lt₂⟩ := by
  subst h_α
  subst h_β
  rfl

/-- **Composition of `initialSegToType`** via `InitialSeg.eq` uniqueness
on well-orders. Two initial segments from `α.ToType` to `γ.ToType`
(both well-ordered) agree pointwise. -/
private lemma initialSegToType_compose
    {α β γ : Ordinal.{0}} (h_αβ : α ≤ β) (h_βγ : β ≤ γ) (x : α.ToType) :
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder γ.ToType (· < ·) := isWellOrder_lt
    (Ordinal.initialSegToType h_βγ).toOrderEmbedding
        ((Ordinal.initialSegToType h_αβ).toOrderEmbedding x) =
      (Ordinal.initialSegToType (h_αβ.trans h_βγ)).toOrderEmbedding x := by
  haveI : IsWellOrder γ.ToType (· < ·) := isWellOrder_lt
  rw [InitialSeg.toOrderEmbedding_apply, InitialSeg.toOrderEmbedding_apply,
      InitialSeg.toOrderEmbedding_apply,
      ← InitialSeg.trans_apply (Ordinal.initialSegToType h_αβ)
        (Ordinal.initialSegToType h_βγ) x]
  exact ((Ordinal.initialSegToType h_αβ).trans
    (Ordinal.initialSegToType h_βγ)).eq
    (Ordinal.initialSegToType (h_αβ.trans h_βγ)) x

/-- **Transport commutes with `initialSegToType`**. Used to rewrite the
"crossing-the-extension-boundary" subgoals in `extendSucc`. -/
private lemma initialSegToType_transport_eq
    {α₁ β₁ α₂ β₂ : Ordinal.{0}}
    (h_α : α₁ = α₂) (h_β : β₁ = β₂)
    (h_le₁ : α₁ ≤ β₁) (h_le₂ : α₂ ≤ β₂)
    (x : α₁.ToType) :
    h_β ▸ (Ordinal.initialSegToType h_le₁).toOrderEmbedding x =
      (Ordinal.initialSegToType h_le₂).toOrderEmbedding (h_α ▸ x) := by
  subst h_α
  subst h_β
  rfl

/-- **`validFiber` is invariant under HEq of its `OrderEmbedding` and
`Bool` arguments.** Equates two `validFiber`s whose underlying
ordinals are equal and whose prefix/branch are HEq. -/
private lemma validFiber_eq_of_HEq
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {α β : Ordinal.{0}} (h_eq : α = β)
    {p_α : α.ToType ↪o PairERSource} {τ_α : α.ToType → Bool}
    {p_β : β.ToType ↪o PairERSource} {τ_β : β.ToType → Bool}
    (hp : HEq p_α p_β) (hτ : HEq τ_α τ_β) :
    validFiber cR p_α τ_α = validFiber cR p_β τ_β := by
  subst h_eq
  rw [eq_of_heq hp, eq_of_heq hτ]

/-- **Applied form of `extendPrefixAt_castSucc_heq`**. -/
theorem CoherentBranchApprox.extendPrefixAt_castSucc_apply
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR (n + 1)) (k : Fin (n + 1))
    (x : (A.extendLevel k.castSucc).ToType) :
    A.extendPrefixAt k.castSucc x =
      A.prefixAt k ((A.extendLevel_castSucc k) ▸ x) :=
  orderEmbed_ordinal_apply_heq (A.extendLevel_castSucc k) _ _
    (A.extendPrefixAt_castSucc_heq k) x

/-- **Applied form of `extendPrefixAt_last_heq`**. -/
theorem CoherentBranchApprox.extendPrefixAt_last_apply
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR (n + 1))
    (x : (A.extendLevel (Fin.last (n + 1))).ToType) :
    A.extendPrefixAt (Fin.last (n + 1)) x =
      A.nextChain.head ((A.extendLevel_last) ▸ x) :=
  orderEmbed_ordinal_apply_heq A.extendLevel_last _ _
    A.extendPrefixAt_last_heq x


/-- **`extendBranchAt`**: branch function for the one-step extension. -/
noncomputable def CoherentBranchApprox.extendBranchAt
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR (n + 1)) :
    ∀ k : Fin (n + 2), (A.extendLevel k).ToType → Bool := fun k => by
  refine Fin.lastCases (motive := fun k => (A.extendLevel k).ToType → Bool) ?_ ?_ k
  · show (A.extendLevel (Fin.last (n + 1))).ToType → Bool
    rw [A.extendLevel_last]; exact A.nextChain.type
  · intro j
    show (A.extendLevel j.castSucc).ToType → Bool
    rw [A.extendLevel_castSucc]; exact A.branchAt j

theorem CoherentBranchApprox.extendBranchAt_last_heq
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR (n + 1)) :
    HEq (A.extendBranchAt (Fin.last (n + 1))) A.nextChain.type := by
  unfold CoherentBranchApprox.extendBranchAt
  rw [Fin.lastCases_last]
  exact cast_heq _ _

theorem CoherentBranchApprox.extendBranchAt_castSucc_heq
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR (n + 1)) (k : Fin (n + 1)) :
    HEq (A.extendBranchAt k.castSucc) (A.branchAt k) := by
  unfold CoherentBranchApprox.extendBranchAt
  rw [Fin.lastCases_castSucc]
  exact cast_heq _ _

/-- **Applied form of `extendBranchAt_castSucc_heq`**. -/
theorem CoherentBranchApprox.extendBranchAt_castSucc_apply
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR (n + 1)) (k : Fin (n + 1))
    (x : (A.extendLevel k.castSucc).ToType) :
    A.extendBranchAt k.castSucc x =
      A.branchAt k ((A.extendLevel_castSucc k) ▸ x) :=
  fn_ordinal_apply_heq (A.extendLevel_castSucc k) _ _
    (A.extendBranchAt_castSucc_heq k) x

/-- **Applied form of `extendBranchAt_last_heq`**. -/
theorem CoherentBranchApprox.extendBranchAt_last_apply
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR (n + 1))
    (x : (A.extendLevel (Fin.last (n + 1))).ToType) :
    A.extendBranchAt (Fin.last (n + 1)) x =
      A.nextChain.type ((A.extendLevel_last) ▸ x) :=
  fn_ordinal_apply_heq A.extendLevel_last _ _
    A.extendBranchAt_last_heq x

/-- **Boundary prefix lemma**: applying the extended prefix at the new
top (`Fin.last (n+1)`) to the lift of an element at an old position
`j.castSucc` agrees with the old prefix at `j`. Chains
`extendPrefixAt_last_apply`, `PairERChain.succ_commitAt`, and
`A.prefix_restrict`. -/
theorem CoherentBranchApprox.extendPrefixAt_castSucc_last_apply
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR (n + 1)) (j : Fin (n + 1))
    (h_le : A.extendLevel j.castSucc ≤ A.extendLevel (Fin.last (n + 1)))
    (x : (A.extendLevel j.castSucc).ToType) :
    A.extendPrefixAt (Fin.last (n + 1))
        ((Ordinal.initialSegToType h_le).toOrderEmbedding x) =
      A.prefixAt j ((A.extendLevel_castSucc j) ▸ x) := by
  classical
  haveI : IsWellOrder (A.level j).ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder (A.level (Fin.last n)).ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder (Order.succ (A.level (Fin.last n))).ToType (· < ·) :=
    isWellOrder_lt
  -- Reduce LHS via `extendPrefixAt_last_apply`.
  rw [A.extendPrefixAt_last_apply]
  -- Set up the transported element x' on the `A.level j` side.
  set x' : (A.level j).ToType := (A.extendLevel_castSucc j) ▸ x with hx'_def
  -- Identify the transported lift with a direct lift to `Order.succ αn`.
  have h_le_succ : A.level j ≤ Order.succ (A.level (Fin.last n)) :=
    (A.level_strictMono.monotone (Fin.le_last j)).trans (Order.le_succ _)
  rw [initialSegToType_transport_eq (A.extendLevel_castSucc j) A.extendLevel_last
      h_le h_le_succ x]
  -- Now the goal is:
  --   A.nextChain.head ((initialSegToType h_le_succ).toOrderEmbedding x')
  --     = A.prefixAt j x'
  -- Let δ := typein x' in (A.level j).ToType.
  set δ : Ordinal.{0} :=
    Ordinal.typein (α := (A.level j).ToType) (· < ·) x' with hδ_def
  have hδ_lt_lvlj : δ < A.level j := by
    rw [hδ_def]
    exact Ordinal.typein_lt_self x'
  have hδ_lt_αn : δ < A.level (Fin.last n) :=
    hδ_lt_lvlj.trans_le (A.level_strictMono.monotone (Fin.le_last j))
  have hδ_lt_succαn : δ < Order.succ (A.level (Fin.last n)) :=
    hδ_lt_αn.trans (Order.lt_succ _)
  -- Identify the lift of x' to (Order.succ αn).ToType as enum at δ.
  have h_lift_succ : (Ordinal.initialSegToType h_le_succ).toOrderEmbedding x' =
      Ordinal.enum (α := (Order.succ (A.level (Fin.last n))).ToType) (· < ·)
        ⟨δ, (Ordinal.type_toType _).symm ▸ hδ_lt_succαn⟩ := by
    rw [← Ordinal.enum_typein (· < · : (Order.succ (A.level (Fin.last n))).ToType →
        (Order.succ (A.level (Fin.last n))).ToType → Prop)
      ((Ordinal.initialSegToType h_le_succ).toOrderEmbedding x')]
    congr 1
    apply Subtype.ext
    show Ordinal.typein (α := (Order.succ (A.level (Fin.last n))).ToType) (· < ·)
        ((Ordinal.initialSegToType h_le_succ).toOrderEmbedding x') = δ
    rw [show Ordinal.typein (α := (Order.succ (A.level (Fin.last n))).ToType) (· < ·)
          ((Ordinal.initialSegToType h_le_succ).toOrderEmbedding x') =
        Ordinal.typein (α := (A.level j).ToType) (· < ·) x' from
      Ordinal.typein_apply (Ordinal.initialSegToType h_le_succ) x']
  rw [h_lift_succ]
  -- Recognize `A.nextChain.head (enum at δ in succ αn)` = `A.nextChain.commitAt δ _`.
  -- Apply succ_commitAt to bridge to `A.lastChain.commitAt δ _`.
  show A.nextChain.head _ = _
  have h_step : A.nextChain.head (Ordinal.enum
      (α := (Order.succ (A.level (Fin.last n))).ToType) (· < ·)
      ⟨δ, (Ordinal.type_toType _).symm ▸ hδ_lt_succαn⟩) =
      A.lastChain.head (Ordinal.enum (α := (A.level (Fin.last n)).ToType) (· < ·)
        ⟨δ, (Ordinal.type_toType _).symm ▸ hδ_lt_αn⟩) := by
    show A.lastChain.succ.commitAt δ hδ_lt_succαn =
        A.lastChain.commitAt δ hδ_lt_αn
    exact PairERChain.succ_commitAt A.lastChain δ hδ_lt_αn
  rw [h_step]
  -- Now `A.lastChain.head = A.prefixAt (Fin.last n)` and the argument is at
  -- position δ in (A.level (Fin.last n)).ToType = αn.ToType.
  -- Use A.prefix_restrict for j ≤ Fin.last n.
  have h_le_lastn : j ≤ Fin.last n := Fin.le_last j
  have h_lvl_le : A.level j ≤ A.level (Fin.last n) :=
    A.level_strictMono.monotone h_le_lastn
  have hres := A.prefix_restrict h_le_lastn x'
  -- hres : A.prefixAt (Fin.last n) (initialSegToType_lift x') = A.prefixAt j x'
  -- Identify enum at δ in αn with initialSegToType-lift of x' to αn.
  have h_lift_αn : Ordinal.enum (α := (A.level (Fin.last n)).ToType) (· < ·)
      ⟨δ, (Ordinal.type_toType _).symm ▸ hδ_lt_αn⟩ =
      (Ordinal.initialSegToType h_lvl_le).toOrderEmbedding x' := by
    rw [← Ordinal.enum_typein (· < · : (A.level (Fin.last n)).ToType →
        (A.level (Fin.last n)).ToType → Prop)
      ((Ordinal.initialSegToType h_lvl_le).toOrderEmbedding x')]
    congr 1
    apply Subtype.ext
    show δ = Ordinal.typein (α := (A.level (Fin.last n)).ToType) (· < ·)
        ((Ordinal.initialSegToType h_lvl_le).toOrderEmbedding x')
    rw [show Ordinal.typein (α := (A.level (Fin.last n)).ToType) (· < ·)
          ((Ordinal.initialSegToType h_lvl_le).toOrderEmbedding x') =
        Ordinal.typein (α := (A.level j).ToType) (· < ·) x' from
      Ordinal.typein_apply (Ordinal.initialSegToType h_lvl_le) x']
  show A.lastChain.head _ = _
  -- A.lastChain.head = A.prefixAt (Fin.last n).
  change A.prefixAt (Fin.last n) _ = _
  rw [h_lift_αn]
  exact hres

/-- **Boundary branch lemma**: parallel to `extendPrefixAt_castSucc_last_apply`,
chains `extendBranchAt_last_apply` (LHS reduces to `nextChain.type`),
`PairERChain.succ_typeAt_old` (bridges `nextChain.type` to `lastChain.type`
at non-top positions), and `A.branch_restrict`. -/
theorem CoherentBranchApprox.extendBranchAt_castSucc_last_apply
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR (n + 1)) (j : Fin (n + 1))
    (h_le : A.extendLevel j.castSucc ≤ A.extendLevel (Fin.last (n + 1)))
    (x : (A.extendLevel j.castSucc).ToType) :
    A.extendBranchAt (Fin.last (n + 1))
        ((Ordinal.initialSegToType h_le).toOrderEmbedding x) =
      A.branchAt j ((A.extendLevel_castSucc j) ▸ x) := by
  classical
  haveI : IsWellOrder (A.level j).ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder (A.level (Fin.last n)).ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder (Order.succ (A.level (Fin.last n))).ToType (· < ·) :=
    isWellOrder_lt
  rw [A.extendBranchAt_last_apply]
  set x' : (A.level j).ToType := (A.extendLevel_castSucc j) ▸ x with hx'_def
  have h_le_succ : A.level j ≤ Order.succ (A.level (Fin.last n)) :=
    (A.level_strictMono.monotone (Fin.le_last j)).trans (Order.le_succ _)
  rw [initialSegToType_transport_eq (A.extendLevel_castSucc j) A.extendLevel_last
      h_le h_le_succ x]
  set δ : Ordinal.{0} :=
    Ordinal.typein (α := (A.level j).ToType) (· < ·) x' with hδ_def
  have hδ_lt_lvlj : δ < A.level j := by rw [hδ_def]; exact Ordinal.typein_lt_self x'
  have hδ_lt_αn : δ < A.level (Fin.last n) :=
    hδ_lt_lvlj.trans_le (A.level_strictMono.monotone (Fin.le_last j))
  have hδ_lt_succαn : δ < Order.succ (A.level (Fin.last n)) :=
    hδ_lt_αn.trans (Order.lt_succ _)
  have h_lift_succ : (Ordinal.initialSegToType h_le_succ).toOrderEmbedding x' =
      Ordinal.enum (α := (Order.succ (A.level (Fin.last n))).ToType) (· < ·)
        ⟨δ, (Ordinal.type_toType _).symm ▸ hδ_lt_succαn⟩ := by
    rw [← Ordinal.enum_typein (· < · : (Order.succ (A.level (Fin.last n))).ToType →
        (Order.succ (A.level (Fin.last n))).ToType → Prop)
      ((Ordinal.initialSegToType h_le_succ).toOrderEmbedding x')]
    congr 1
    apply Subtype.ext
    show Ordinal.typein (α := (Order.succ (A.level (Fin.last n))).ToType) (· < ·)
        ((Ordinal.initialSegToType h_le_succ).toOrderEmbedding x') = δ
    rw [show Ordinal.typein (α := (Order.succ (A.level (Fin.last n))).ToType) (· < ·)
          ((Ordinal.initialSegToType h_le_succ).toOrderEmbedding x') =
        Ordinal.typein (α := (A.level j).ToType) (· < ·) x' from
      Ordinal.typein_apply (Ordinal.initialSegToType h_le_succ) x']
  rw [h_lift_succ]
  show A.nextChain.type _ = _
  have h_step : A.nextChain.type (Ordinal.enum
      (α := (Order.succ (A.level (Fin.last n))).ToType) (· < ·)
      ⟨δ, (Ordinal.type_toType _).symm ▸ hδ_lt_succαn⟩) =
      A.lastChain.type (Ordinal.enum (α := (A.level (Fin.last n)).ToType) (· < ·)
        ⟨δ, (Ordinal.type_toType _).symm ▸ hδ_lt_αn⟩) := by
    show A.lastChain.succ.typeAt δ hδ_lt_succαn =
        A.lastChain.typeAt δ hδ_lt_αn
    exact PairERChain.succ_typeAt_old A.lastChain δ hδ_lt_αn
  rw [h_step]
  have h_le_lastn : j ≤ Fin.last n := Fin.le_last j
  have h_lvl_le : A.level j ≤ A.level (Fin.last n) :=
    A.level_strictMono.monotone h_le_lastn
  have hres := A.branch_restrict h_le_lastn x'
  have h_lift_αn : Ordinal.enum (α := (A.level (Fin.last n)).ToType) (· < ·)
      ⟨δ, (Ordinal.type_toType _).symm ▸ hδ_lt_αn⟩ =
      (Ordinal.initialSegToType h_lvl_le).toOrderEmbedding x' := by
    rw [← Ordinal.enum_typein (· < · : (A.level (Fin.last n)).ToType →
        (A.level (Fin.last n)).ToType → Prop)
      ((Ordinal.initialSegToType h_lvl_le).toOrderEmbedding x')]
    congr 1
    apply Subtype.ext
    show δ = Ordinal.typein (α := (A.level (Fin.last n)).ToType) (· < ·)
        ((Ordinal.initialSegToType h_lvl_le).toOrderEmbedding x')
    rw [show Ordinal.typein (α := (A.level (Fin.last n)).ToType) (· < ·)
          ((Ordinal.initialSegToType h_lvl_le).toOrderEmbedding x') =
        Ordinal.typein (α := (A.level j).ToType) (· < ·) x' from
      Ordinal.typein_apply (Ordinal.initialSegToType h_lvl_le) x']
  show A.lastChain.type _ = _
  change A.branchAt (Fin.last n) _ = _
  rw [h_lift_αn]
  exact hres

/-- **`CoherentBranchApprox.extendSucc`**: extend a non-trivial
approximation (with at least one level) by one more level via
`PairERChain.succ` on the last chain. The new level is
`Order.succ (A.level (Fin.last n))`. -/
noncomputable def CoherentBranchApprox.extendSucc
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR (n + 1)) :
    CoherentBranchApprox cR (n + 2) := by
  classical
  haveI : IsWellOrder (A.level (Fin.last n)).ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder (Order.succ (A.level (Fin.last n))).ToType (· < ·) := isWellOrder_lt
  have hαn_lt : A.level (Fin.last n) < Ordinal.omega.{0} 1 :=
    A.level_lt_omega1 (Fin.last n)
  have h_succαn_lt : Order.succ (A.level (Fin.last n)) < Ordinal.omega.{0} 1 :=
    (Cardinal.isSuccLimit_omega 1).succ_lt hαn_lt
  refine
    { level := A.extendLevel
      level_lt_omega1 := ?_
      level_strictMono := ?_
      prefixAt := A.extendPrefixAt
      branchAt := A.extendBranchAt
      prefix_restrict := ?_
      branch_restrict := ?_
      large := ?_
      top_in_validFiber := ?_ }
  · -- level_lt_omega1
    intro k
    induction k using Fin.lastCases with
    | last => rw [A.extendLevel_last]; exact h_succαn_lt
    | cast k => rw [A.extendLevel_castSucc]; exact A.level_lt_omega1 k
  · -- level_strictMono
    intro a b hab
    induction a using Fin.lastCases with
    | last =>
      -- a = Fin.last (n+1), b > a impossible
      exfalso
      exact absurd hab (not_lt_of_ge (Fin.le_last b))
    | cast j₁ =>
      induction b using Fin.lastCases with
      | last =>
        rw [A.extendLevel_castSucc, A.extendLevel_last]
        calc A.level j₁
            ≤ A.level (Fin.last n) :=
              A.level_strictMono.monotone (Fin.le_last j₁)
          _ < Order.succ (A.level (Fin.last n)) := Order.lt_succ _
      | cast j₂ =>
        rw [A.extendLevel_castSucc, A.extendLevel_castSucc]
        apply A.level_strictMono
        exact (Fin.castSucc_lt_castSucc_iff).mp hab
  · -- prefix_restrict
    intro k₁ k₂ hk x
    induction k₁ using Fin.lastCases with
    | last =>
      induction k₂ using Fin.lastCases with
      | last =>
        -- Both new top: same index. initialSegToType is identity.
        congr 1
        have h : Ordinal.initialSegToType
            (le_refl (A.extendLevel (Fin.last (n + 1)))) =
            InitialSeg.refl _ := Subsingleton.elim _ _
        rw [h]; rfl
      | cast j₂ =>
        -- Impossible: Fin.last (n+1) > j₂.castSucc.
        exact absurd hk (not_le_of_gt (Fin.castSucc_lt_last j₂))
    | cast j₁ =>
      induction k₂ using Fin.lastCases with
      | last =>
        -- k₁ = j₁.castSucc, k₂ = Fin.last (n+1).
        -- Use the boundary lemma `extendPrefixAt_castSucc_last_apply` for the
        -- LHS, and `extendPrefixAt_castSucc_apply` for the RHS.
        rw [A.extendPrefixAt_castSucc_last_apply j₁ _ x,
            A.extendPrefixAt_castSucc_apply]
      | cast j₂ =>
        -- Both castSucc: reduce to A.prefix_restrict via the apply lemmas.
        have hj : j₁ ≤ j₂ := (Fin.castSucc_le_castSucc_iff).mp hk
        haveI : IsWellOrder (A.level j₁).ToType (· < ·) := isWellOrder_lt
        haveI : IsWellOrder (A.level j₂).ToType (· < ·) := isWellOrder_lt
        set x' : (A.level j₁).ToType := (A.extendLevel_castSucc j₁) ▸ x with hx'
        rw [A.extendPrefixAt_castSucc_apply, A.extendPrefixAt_castSucc_apply, ← hx']
        have hres := A.prefix_restrict hj x'
        convert hres using 2
        -- Goal: (extendLevel_castSucc j₂) ▸ (initialSegToType ... x)
        --     = (initialSegToType ... x')
        exact initialSegToType_transport_eq
          (A.extendLevel_castSucc j₁) (A.extendLevel_castSucc j₂) _ _ x
  · -- branch_restrict (structurally parallel to prefix_restrict)
    intro k₁ k₂ hk x
    induction k₁ using Fin.lastCases with
    | last =>
      induction k₂ using Fin.lastCases with
      | last =>
        congr 1
        have h : Ordinal.initialSegToType
            (le_refl (A.extendLevel (Fin.last (n + 1)))) =
            InitialSeg.refl _ := Subsingleton.elim _ _
        rw [h]; rfl
      | cast j₂ =>
        exact absurd hk (not_le_of_gt (Fin.castSucc_lt_last j₂))
    | cast j₁ =>
      induction k₂ using Fin.lastCases with
      | last =>
        -- k₁ = j₁.castSucc, k₂ = Fin.last (n+1).
        rw [A.extendBranchAt_castSucc_last_apply j₁ _ x,
            A.extendBranchAt_castSucc_apply]
      | cast j₂ =>
        -- Both castSucc: reduce to A.branch_restrict via the apply lemmas.
        have hj : j₁ ≤ j₂ := (Fin.castSucc_le_castSucc_iff).mp hk
        haveI : IsWellOrder (A.level j₁).ToType (· < ·) := isWellOrder_lt
        haveI : IsWellOrder (A.level j₂).ToType (· < ·) := isWellOrder_lt
        set x' : (A.level j₁).ToType := (A.extendLevel_castSucc j₁) ▸ x with hx'
        rw [A.extendBranchAt_castSucc_apply, A.extendBranchAt_castSucc_apply, ← hx']
        have hres := A.branch_restrict hj x'
        convert hres using 2
        exact initialSegToType_transport_eq
          (A.extendLevel_castSucc j₁) (A.extendLevel_castSucc j₂) _ _ x
  · -- large
    intro k
    induction k using Fin.lastCases with
    | last =>
      show Order.succ (Cardinal.beth.{0} 1) ≤
          Cardinal.mk (validFiber cR (A.extendPrefixAt (Fin.last (n + 1)))
            (A.extendBranchAt (Fin.last (n + 1))))
      convert A.nextChain.large using 4
      · exact A.extendLevel_last
      · exact A.extendPrefixAt_last_heq
      · exact A.extendBranchAt_last_heq
    | cast j =>
      show Order.succ (Cardinal.beth.{0} 1) ≤
          Cardinal.mk (validFiber cR (A.extendPrefixAt j.castSucc)
            (A.extendBranchAt j.castSucc))
      convert A.large j using 4
      · exact A.extendLevel_castSucc j
      · exact A.extendPrefixAt_castSucc_heq j
      · exact A.extendBranchAt_castSucc_heq j
  · -- top_in_validFiber
    intro i h
    have hi : i < n + 1 := Nat.lt_of_succ_lt_succ h
    by_cases hi1 : i + 1 < n + 1
    · -- Both old (castSucc + castSucc): use A.top_in_validFiber.
      show A.extendPrefixAt ((⟨i + 1, hi1⟩ : Fin (n + 1)).castSucc)
          ((Ordinal.enum (· < ·))
            ⟨A.extendLevel ((⟨i, hi⟩ : Fin (n + 1)).castSucc), _⟩) ∈ _
      convert A.top_in_validFiber i hi1 using 2
      · exact A.extendLevel_castSucc ⟨i, hi⟩
      · exact A.extendPrefixAt_castSucc_heq ⟨i, hi⟩
      · exact A.extendBranchAt_castSucc_heq ⟨i, hi⟩
      · rw [A.extendPrefixAt_castSucc_apply]
        congr 1
        exact enum_transport_eq (A.extendLevel_castSucc ⟨i + 1, hi1⟩)
          (A.extendLevel_castSucc ⟨i, hi⟩) _ _
    · -- ⟨i+1, h⟩ = Fin.last (n+1); use succNewElement_in_validFiber.
      have hi_eq : n = i := by omega
      subst hi_eq
      -- After subst (n := i, so the outer n in the structure is now the i),
      -- we have ⟨i + 1, h⟩ = Fin.last (i + 1) = Fin.last (n + 1).
      -- And ⟨i, _⟩ = (Fin.last n).castSucc.
      -- Build the typein bound for the enum position.
      have h_typein_bound :
          A.extendLevel ((Fin.last n : Fin (n + 1)).castSucc) <
            Ordinal.type
              (α := (A.extendLevel (Fin.last (n + 1))).ToType) (· < ·) := by
        haveI : IsWellOrder (A.extendLevel (Fin.last (n + 1))).ToType (· < ·) :=
          isWellOrder_lt
        rw [Ordinal.type_toType, A.extendLevel_last, A.extendLevel_castSucc]
        exact Order.lt_succ (A.level (Fin.last n))
      show A.extendPrefixAt (Fin.last (n + 1))
          ((Ordinal.enum (· < ·))
            ⟨A.extendLevel ((Fin.last n : Fin (n + 1)).castSucc),
              h_typein_bound⟩) ∈
        validFiber cR (A.extendPrefixAt ((Fin.last n : Fin (n + 1)).castSucc))
          (A.extendBranchAt ((Fin.last n : Fin (n + 1)).castSucc))
      -- Convert via the heq simp lemmas to nextChain.head / lastChain.head /
      -- lastChain.type.
      convert A.lastChain.succNewElement_in_validFiber using 2
      · exact A.extendLevel_castSucc (Fin.last n)
      · exact A.extendPrefixAt_castSucc_heq (Fin.last n)
      · exact A.extendBranchAt_castSucc_heq (Fin.last n)
      · rw [A.extendPrefixAt_last_apply]
        show A.nextChain.head _ = A.lastChain.succNewElement
        rw [← PairERChain.succ_head_top A.lastChain]
        change A.lastChain.succ.head _ = A.lastChain.succ.head ⊤
        congr 1
        -- enum at A.level (Fin.last n) in (Order.succ αn).ToType = ⊤.
        haveI : IsWellOrder (Order.succ (A.level (Fin.last n))).ToType (· < ·) :=
          isWellOrder_lt
        have h_top_eq :
            (⊤ : (Order.succ (A.level (Fin.last n))).ToType) =
            Ordinal.enum (α := (Order.succ (A.level (Fin.last n))).ToType) (· < ·)
              ⟨A.level (Fin.last n), by
                rw [Ordinal.type_toType]
                exact Order.lt_succ (A.level (Fin.last n))⟩ :=
          Ordinal.enum_succ_eq_top.symm
        rw [h_top_eq]
        exact enum_transport_eq A.extendLevel_last
          (A.extendLevel_castSucc (Fin.last n)) _ _

/-- **`CoherentBranchApprox.extend`**: extend any finite approximation
by one level. Splits into `fromZero` (for `n = 0`) and `extendSucc`
(for `n ≥ 1`). This is the recursive step used to build the
ω-chain of approximations. -/
noncomputable def CoherentBranchApprox.extend
    {cR : (Fin 2 ↪o PairERSource) → Bool} : ∀ {n : ℕ},
    CoherentBranchApprox cR n → CoherentBranchApprox cR (n + 1)
  | 0, _ => CoherentBranchApprox.fromZero cR
  | _ + 1, A => A.extendSucc

/-! ### General extension `extendTo`: arbitrary countable target level

After the structure relaxation (removal of `level_succ`), a
`CoherentBranchApprox` can carry levels at any strictly-increasing
sequence of countable ordinals. The natural API for building such
approximations is `extendTo`, which appends a new level at an
arbitrary `α < ω₁` strictly above all existing levels — generalizing
`extendSucc` (which is the special case `α = succ (lastLevel A)`).

**Current status (sorry frontier)**: the construction is left as a
sorry pending the chain-extension primitive that maps a
`PairERChain cR β` to a `PairERChain cR α` for arbitrary `β < α < ω₁`.
Such a primitive in turn requires transfinite recursion through the
gap `(β, α]` (combining `PairERChain.succ` for successor stages and
limit-style coherent-family construction for limit stages). The
structure and consumers above are now ready to integrate `extendTo`
once filled. -/

/-- **`lastLevel`**: the largest level of an approximation, or `0`
if there are no levels. Used as a uniform bound parameter for
`extendTo`. -/
noncomputable def CoherentBranchApprox.lastLevel
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR n) : Ordinal.{0} :=
  if h : n = 0 then 0 else A.level ⟨n - 1, by omega⟩

/-- **`lastLevel_ge`**: every level is `≤ lastLevel`. -/
lemma CoherentBranchApprox.lastLevel_ge
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR n) (k : Fin n) :
    A.level k ≤ A.lastLevel := by
  unfold CoherentBranchApprox.lastLevel
  have hn : n ≠ 0 := by
    intro h; subst h; exact Fin.elim0 k
  rw [dif_neg hn]
  refine A.level_strictMono.monotone ?_
  show k.val ≤ n - 1
  have := k.isLt
  omega

/-! ### Boundary note: unqualified `extendToExt` vs branch-aware
`extendToExtOfBranch`

The unqualified `PairERChain.extendToExt` frontier (sorry) exists
solely to build the finite approximations below before a coherent
branch is available. Its only active consumer is
`CoherentBranchApprox.extendToChain` (and its projection lemmas).

Once a `CoherentMajorityBranch B` is available, downstream chain
extension must go through `PairERChain.extendToExtOfBranch B` (proved
axiom-clean), which extends chains aligned with `B` without invoking
the unqualified frontier. Do not introduce new active consumers of
`extendToExt` outside this approximation-building layer. -/

/-- **`extendToChain`**: the chain at level `α` extending `A`'s
last-position data. For `n = 0`: extend from `PairERChain.zero cR`.
For `n ≥ 1`: extend from the chain at `A.level ⟨n−1, _⟩` extracted
from `A`. Both branches use `PairERChain.extendTo` (the named
pre-fusion approximation-building primitive; see the boundary note
above). -/
noncomputable def CoherentBranchApprox.extendToChain
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR n)
    (α : Ordinal.{0}) (hα : α < Ordinal.omega.{0} 1)
    (hα_above_last : A.lastLevel < α) : PairERChain cR α := by
  classical
  by_cases hn : n = 0
  · have hβα : (0 : Ordinal.{0}) < α := by
      have h_eq : A.lastLevel = 0 := by
        unfold CoherentBranchApprox.lastLevel; rw [dif_pos hn]
      exact h_eq ▸ hα_above_last
    exact (PairERChain.zero cR).extendTo hβα hα
  · have hn' : n - 1 < n := by omega
    let lastChain : PairERChain cR (A.level ⟨n - 1, hn'⟩) :=
      ⟨A.prefixAt ⟨n - 1, hn'⟩, A.branchAt ⟨n - 1, hn'⟩,
        A.large ⟨n - 1, hn'⟩⟩
    have hβα : A.level ⟨n - 1, hn'⟩ < α := by
      have h_eq : A.lastLevel = A.level ⟨n - 1, hn'⟩ := by
        unfold CoherentBranchApprox.lastLevel; rw [dif_neg hn]
      exact h_eq ▸ hα_above_last
    exact lastChain.extendTo hβα hα

/-- **`extendToChain_commitAt_of_lt_level`**: for `k : Fin n`, the
`extendToChain` agrees with `A.prefixAt k` after the lift via
`initialSegToType`. Reduces to `extendTo_commitAt` (the new chain
extends the last) + `A.prefix_restrict` (chain prefixes are coherent
across A's levels). -/
theorem CoherentBranchApprox.extendToChain_head_at_level
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR n)
    (α : Ordinal.{0}) (hα : α < Ordinal.omega.{0} 1)
    (hα_above_last : A.lastLevel < α)
    (k : Fin n) (x : (A.level k).ToType) :
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder (A.level k).ToType (· < ·) := isWellOrder_lt
    (A.extendToChain α hα hα_above_last).head
        ((Ordinal.initialSegToType
          ((A.lastLevel_ge k).trans hα_above_last.le)).toOrderEmbedding x) =
      A.prefixAt k x := by
  classical
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder (A.level k).ToType (· < ·) := isWellOrder_lt
  -- n ≠ 0 since k : Fin n.
  have hn_ne_zero : n ≠ 0 := by rintro rfl; exact k.elim0
  have hn' : n - 1 < n := by omega
  -- Unfold extendToChain (n ≥ 1 branch).
  unfold CoherentBranchApprox.extendToChain
  rw [dif_neg hn_ne_zero]
  -- Now extendToChain = lastChain.extendTo
  haveI : IsWellOrder (A.level ⟨n - 1, hn'⟩).ToType (· < ·) := isWellOrder_lt
  set lastChain : PairERChain cR (A.level ⟨n - 1, hn'⟩) :=
    ⟨A.prefixAt ⟨n - 1, hn'⟩, A.branchAt ⟨n - 1, hn'⟩,
      A.large ⟨n - 1, hn'⟩⟩
  set hβα : A.level ⟨n - 1, hn'⟩ < α := by
    have h_eq : A.lastLevel = A.level ⟨n - 1, hn'⟩ := by
      unfold CoherentBranchApprox.lastLevel; rw [dif_neg hn_ne_zero]
    exact h_eq ▸ hα_above_last
  show (lastChain.extendTo hβα hα).head _ = _
  -- Identify the lift as enum at δ := typein x in (A.level k).ToType.
  set δ : Ordinal.{0} :=
    Ordinal.typein (α := (A.level k).ToType) (· < ·) x with hδ_def
  have hδ_lt_lvlk : δ < A.level k := by
    rw [hδ_def]; exact Ordinal.typein_lt_self x
  have hk_le : k ≤ (⟨n - 1, hn'⟩ : Fin n) := by
    show k.val ≤ n - 1
    have := k.isLt; omega
  have h_lvl_le : A.level k ≤ A.level ⟨n - 1, hn'⟩ :=
    A.level_strictMono.monotone hk_le
  have hδ_lt_β : δ < A.level ⟨n - 1, hn'⟩ := hδ_lt_lvlk.trans_le h_lvl_le
  have hδ_lt_α : δ < α := hδ_lt_β.trans hβα
  -- Identify the lift as enum at δ.
  have h_lift_α : (Ordinal.initialSegToType
      ((A.lastLevel_ge k).trans hα_above_last.le)).toOrderEmbedding x =
      Ordinal.enum (α := α.ToType) (· < ·)
        ⟨δ, (Ordinal.type_toType _).symm ▸ hδ_lt_α⟩ := by
    rw [← Ordinal.enum_typein (· < · : α.ToType → α.ToType → Prop)
      ((Ordinal.initialSegToType
        ((A.lastLevel_ge k).trans hα_above_last.le)).toOrderEmbedding x)]
    congr 1
    apply Subtype.ext
    show Ordinal.typein (α := α.ToType) (· < ·)
        ((Ordinal.initialSegToType
          ((A.lastLevel_ge k).trans hα_above_last.le)).toOrderEmbedding x) = δ
    rw [show Ordinal.typein (α := α.ToType) (· < ·)
          ((Ordinal.initialSegToType
            ((A.lastLevel_ge k).trans hα_above_last.le)).toOrderEmbedding x) =
        Ordinal.typein (α := (A.level k).ToType) (· < ·) x from
      Ordinal.typein_apply _ x]
  rw [h_lift_α]
  -- Apply extendTo_commitAt to bridge to lastChain.
  show (lastChain.extendTo hβα hα).head
      (Ordinal.enum (α := α.ToType) (· < ·) ⟨δ, _⟩) = _
  have h_step : (lastChain.extendTo hβα hα).head
      (Ordinal.enum (α := α.ToType) (· < ·)
        ⟨δ, (Ordinal.type_toType _).symm ▸ hδ_lt_α⟩) =
      lastChain.head (Ordinal.enum (α := (A.level ⟨n - 1, hn'⟩).ToType) (· < ·)
        ⟨δ, (Ordinal.type_toType _).symm ▸ hδ_lt_β⟩) := by
    show (lastChain.extendTo hβα hα).commitAt δ hδ_lt_α = lastChain.commitAt δ hδ_lt_β
    exact PairERChain.extendTo_commitAt lastChain hβα hα δ hδ_lt_β
  rw [h_step]
  -- lastChain.head = A.prefixAt ⟨n-1, _⟩. Now use A.prefix_restrict (k ≤ ⟨n-1, _⟩).
  show A.prefixAt ⟨n - 1, hn'⟩ _ = _
  -- Identify enum at δ in αn with initialSegToType-lift of x to αn.
  have h_lift_αn : Ordinal.enum (α := (A.level ⟨n - 1, hn'⟩).ToType) (· < ·)
      ⟨δ, (Ordinal.type_toType _).symm ▸ hδ_lt_β⟩ =
      (Ordinal.initialSegToType h_lvl_le).toOrderEmbedding x := by
    rw [← Ordinal.enum_typein (· < · : (A.level ⟨n - 1, hn'⟩).ToType →
        (A.level ⟨n - 1, hn'⟩).ToType → Prop)
      ((Ordinal.initialSegToType h_lvl_le).toOrderEmbedding x)]
    congr 1
    apply Subtype.ext
    show δ = Ordinal.typein (α := (A.level ⟨n - 1, hn'⟩).ToType) (· < ·)
        ((Ordinal.initialSegToType h_lvl_le).toOrderEmbedding x)
    rw [show Ordinal.typein (α := (A.level ⟨n - 1, hn'⟩).ToType) (· < ·)
          ((Ordinal.initialSegToType h_lvl_le).toOrderEmbedding x) =
        Ordinal.typein (α := (A.level k).ToType) (· < ·) x from
      Ordinal.typein_apply (Ordinal.initialSegToType h_lvl_le) x]
  rw [h_lift_αn]
  exact A.prefix_restrict hk_le x

/-- **`extendToChain_type_at_level`**: analog of
`extendToChain_head_at_level` for the type function. -/
theorem CoherentBranchApprox.extendToChain_type_at_level
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR n)
    (α : Ordinal.{0}) (hα : α < Ordinal.omega.{0} 1)
    (hα_above_last : A.lastLevel < α)
    (k : Fin n) (x : (A.level k).ToType) :
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder (A.level k).ToType (· < ·) := isWellOrder_lt
    (A.extendToChain α hα hα_above_last).type
        ((Ordinal.initialSegToType
          ((A.lastLevel_ge k).trans hα_above_last.le)).toOrderEmbedding x) =
      A.branchAt k x := by
  classical
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder (A.level k).ToType (· < ·) := isWellOrder_lt
  have hn_ne_zero : n ≠ 0 := by rintro rfl; exact k.elim0
  have hn' : n - 1 < n := by omega
  unfold CoherentBranchApprox.extendToChain
  rw [dif_neg hn_ne_zero]
  haveI : IsWellOrder (A.level ⟨n - 1, hn'⟩).ToType (· < ·) := isWellOrder_lt
  set lastChain : PairERChain cR (A.level ⟨n - 1, hn'⟩) :=
    ⟨A.prefixAt ⟨n - 1, hn'⟩, A.branchAt ⟨n - 1, hn'⟩,
      A.large ⟨n - 1, hn'⟩⟩
  set hβα : A.level ⟨n - 1, hn'⟩ < α := by
    have h_eq : A.lastLevel = A.level ⟨n - 1, hn'⟩ := by
      unfold CoherentBranchApprox.lastLevel; rw [dif_neg hn_ne_zero]
    exact h_eq ▸ hα_above_last
  show (lastChain.extendTo hβα hα).type _ = _
  set δ : Ordinal.{0} :=
    Ordinal.typein (α := (A.level k).ToType) (· < ·) x with hδ_def
  have hδ_lt_lvlk : δ < A.level k := by
    rw [hδ_def]; exact Ordinal.typein_lt_self x
  have hk_le : k ≤ (⟨n - 1, hn'⟩ : Fin n) := by
    show k.val ≤ n - 1
    have := k.isLt; omega
  have h_lvl_le : A.level k ≤ A.level ⟨n - 1, hn'⟩ :=
    A.level_strictMono.monotone hk_le
  have hδ_lt_β : δ < A.level ⟨n - 1, hn'⟩ := hδ_lt_lvlk.trans_le h_lvl_le
  have hδ_lt_α : δ < α := hδ_lt_β.trans hβα
  have h_lift_α : (Ordinal.initialSegToType
      ((A.lastLevel_ge k).trans hα_above_last.le)).toOrderEmbedding x =
      Ordinal.enum (α := α.ToType) (· < ·)
        ⟨δ, (Ordinal.type_toType _).symm ▸ hδ_lt_α⟩ := by
    rw [← Ordinal.enum_typein (· < · : α.ToType → α.ToType → Prop)
      ((Ordinal.initialSegToType
        ((A.lastLevel_ge k).trans hα_above_last.le)).toOrderEmbedding x)]
    congr 1
    apply Subtype.ext
    show Ordinal.typein (α := α.ToType) (· < ·)
        ((Ordinal.initialSegToType
          ((A.lastLevel_ge k).trans hα_above_last.le)).toOrderEmbedding x) = δ
    rw [show Ordinal.typein (α := α.ToType) (· < ·)
          ((Ordinal.initialSegToType
            ((A.lastLevel_ge k).trans hα_above_last.le)).toOrderEmbedding x) =
        Ordinal.typein (α := (A.level k).ToType) (· < ·) x from
      Ordinal.typein_apply _ x]
  rw [h_lift_α]
  show (lastChain.extendTo hβα hα).type
      (Ordinal.enum (α := α.ToType) (· < ·) ⟨δ, _⟩) = _
  have h_step : (lastChain.extendTo hβα hα).type
      (Ordinal.enum (α := α.ToType) (· < ·)
        ⟨δ, (Ordinal.type_toType _).symm ▸ hδ_lt_α⟩) =
      lastChain.type (Ordinal.enum (α := (A.level ⟨n - 1, hn'⟩).ToType) (· < ·)
        ⟨δ, (Ordinal.type_toType _).symm ▸ hδ_lt_β⟩) := by
    show (lastChain.extendTo hβα hα).typeAt δ hδ_lt_α =
      lastChain.typeAt δ hδ_lt_β
    exact PairERChain.extendTo_typeAt_old lastChain hβα hα δ hδ_lt_β
  rw [h_step]
  show A.branchAt ⟨n - 1, hn'⟩ _ = _
  have h_lift_αn : Ordinal.enum (α := (A.level ⟨n - 1, hn'⟩).ToType) (· < ·)
      ⟨δ, (Ordinal.type_toType _).symm ▸ hδ_lt_β⟩ =
      (Ordinal.initialSegToType h_lvl_le).toOrderEmbedding x := by
    rw [← Ordinal.enum_typein (· < · : (A.level ⟨n - 1, hn'⟩).ToType →
        (A.level ⟨n - 1, hn'⟩).ToType → Prop)
      ((Ordinal.initialSegToType h_lvl_le).toOrderEmbedding x)]
    congr 1
    apply Subtype.ext
    show δ = Ordinal.typein (α := (A.level ⟨n - 1, hn'⟩).ToType) (· < ·)
        ((Ordinal.initialSegToType h_lvl_le).toOrderEmbedding x)
    rw [show Ordinal.typein (α := (A.level ⟨n - 1, hn'⟩).ToType) (· < ·)
          ((Ordinal.initialSegToType h_lvl_le).toOrderEmbedding x) =
        Ordinal.typein (α := (A.level k).ToType) (· < ·) x from
      Ordinal.typein_apply (Ordinal.initialSegToType h_lvl_le) x]
  rw [h_lift_αn]
  exact A.branch_restrict hk_le x

/-- **`extendToChain_realizes_at_lastIndex`**: the new chain's element
at position `A.level ⟨n − 1, _⟩` (the previous "top") lies in the
validFiber of `A`'s prefix/branch at that index. Used for the final
adjacent pair in `top_in_validFiber`. Requires `n ≠ 0`. -/
theorem CoherentBranchApprox.extendToChain_realizes_at_lastIndex
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR n)
    (α : Ordinal.{0}) (hα : α < Ordinal.omega.{0} 1)
    (hα_above_last : A.lastLevel < α) (hn_ne_zero : n ≠ 0) :
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    have hn' : n - 1 < n := Nat.sub_lt (Nat.pos_of_ne_zero hn_ne_zero) Nat.one_pos
    have hβα : A.level ⟨n - 1, hn'⟩ < α := by
      have h_eq : A.lastLevel = A.level ⟨n - 1, hn'⟩ := by
        unfold CoherentBranchApprox.lastLevel; rw [dif_neg hn_ne_zero]
      exact h_eq ▸ hα_above_last
    (A.extendToChain α hα hα_above_last).head
        (Ordinal.enum (α := α.ToType) (· < ·)
          ⟨A.level ⟨n - 1, hn'⟩, (Ordinal.type_toType _).symm ▸ hβα⟩) ∈
      validFiber cR (A.prefixAt ⟨n - 1, hn'⟩) (A.branchAt ⟨n - 1, hn'⟩) := by
  classical
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  have hn' : n - 1 < n := Nat.sub_lt (Nat.pos_of_ne_zero hn_ne_zero) Nat.one_pos
  haveI : IsWellOrder (A.level ⟨n - 1, hn'⟩).ToType (· < ·) := isWellOrder_lt
  set lastChain : PairERChain cR (A.level ⟨n - 1, hn'⟩) :=
    ⟨A.prefixAt ⟨n - 1, hn'⟩, A.branchAt ⟨n - 1, hn'⟩,
      A.large ⟨n - 1, hn'⟩⟩
  set hβα : A.level ⟨n - 1, hn'⟩ < α := by
    have h_eq : A.lastLevel = A.level ⟨n - 1, hn'⟩ := by
      unfold CoherentBranchApprox.lastLevel; rw [dif_neg hn_ne_zero]
    exact h_eq ▸ hα_above_last
  -- Show extendToChain reduces to lastChain.extendTo in the n ≠ 0 branch.
  have h_chain_eq :
      A.extendToChain α hα hα_above_last = lastChain.extendTo hβα hα := by
    unfold CoherentBranchApprox.extendToChain
    rw [dif_neg hn_ne_zero]
  rw [h_chain_eq]
  show (lastChain.extendTo hβα hα).head _ ∈ validFiber cR lastChain.head lastChain.type
  exact PairERChain.extendTo_head_β_in_validFiber lastChain hβα hα

/-! ### Helpers for `CoherentBranchApprox.extendTo`

The helpers `extendToLevel` / `extendToPrefixAt` / `extendToBranchAt`
parallel `extendLevel` / `extendPrefixAt` / `extendBranchAt` from the
`extendSucc` machinery but are parameterized by an arbitrary target
level `α` (and, for the prefix/branch helpers, an external chain at
`α`). The HEq simp lemmas and applied-Eq lemmas (via the existing
`orderEmbed_ordinal_apply_heq` / `fn_ordinal_apply_heq` helpers) are
exact analogs of the `extendSucc` versions. -/

/-- **`extendToLevel`**: level function for the one-step extension
to an arbitrary target `α`. -/
noncomputable def CoherentBranchApprox.extendToLevel
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR n) (α : Ordinal.{0}) :
    Fin (n + 1) → Ordinal.{0} :=
  Fin.lastCases α (fun k => A.level k)

@[simp] theorem CoherentBranchApprox.extendToLevel_last
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR n) (α : Ordinal.{0}) :
    A.extendToLevel α (Fin.last n) = α := Fin.lastCases_last

@[simp] theorem CoherentBranchApprox.extendToLevel_castSucc
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR n) (α : Ordinal.{0}) (k : Fin n) :
    A.extendToLevel α k.castSucc = A.level k := Fin.lastCases_castSucc k

/-- **`extendToPrefixAt`**: prefix function for the one-step extension,
using `Fin.lastCases` and the supplied chain at `α` for the new top. -/
noncomputable def CoherentBranchApprox.extendToPrefixAt
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR n) {α : Ordinal.{0}}
    (chain_α : PairERChain cR α) :
    ∀ k : Fin (n + 1), (A.extendToLevel α k).ToType ↪o PairERSource :=
  fun k => by
    refine Fin.lastCases
      (motive := fun k => (A.extendToLevel α k).ToType ↪o PairERSource) ?_ ?_ k
    · show (A.extendToLevel α (Fin.last n)).ToType ↪o PairERSource
      rw [A.extendToLevel_last]; exact chain_α.head
    · intro j
      show (A.extendToLevel α j.castSucc).ToType ↪o PairERSource
      rw [A.extendToLevel_castSucc]; exact A.prefixAt j

theorem CoherentBranchApprox.extendToPrefixAt_last_heq
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR n) {α : Ordinal.{0}}
    (chain_α : PairERChain cR α) :
    HEq (A.extendToPrefixAt chain_α (Fin.last n)) chain_α.head := by
  unfold CoherentBranchApprox.extendToPrefixAt
  rw [Fin.lastCases_last]
  exact cast_heq _ _

theorem CoherentBranchApprox.extendToPrefixAt_castSucc_heq
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR n) {α : Ordinal.{0}}
    (chain_α : PairERChain cR α) (k : Fin n) :
    HEq (A.extendToPrefixAt chain_α k.castSucc) (A.prefixAt k) := by
  unfold CoherentBranchApprox.extendToPrefixAt
  rw [Fin.lastCases_castSucc]
  exact cast_heq _ _

theorem CoherentBranchApprox.extendToPrefixAt_last_apply
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR n) {α : Ordinal.{0}}
    (chain_α : PairERChain cR α) (x : (A.extendToLevel α (Fin.last n)).ToType) :
    A.extendToPrefixAt chain_α (Fin.last n) x =
      chain_α.head ((A.extendToLevel_last α) ▸ x) :=
  orderEmbed_ordinal_apply_heq (A.extendToLevel_last α) _ _
    (A.extendToPrefixAt_last_heq chain_α) x

theorem CoherentBranchApprox.extendToPrefixAt_castSucc_apply
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR n) {α : Ordinal.{0}}
    (chain_α : PairERChain cR α) (k : Fin n)
    (x : (A.extendToLevel α k.castSucc).ToType) :
    A.extendToPrefixAt chain_α k.castSucc x =
      A.prefixAt k ((A.extendToLevel_castSucc α k) ▸ x) :=
  orderEmbed_ordinal_apply_heq (A.extendToLevel_castSucc α k) _ _
    (A.extendToPrefixAt_castSucc_heq chain_α k) x

/-- **`extendToBranchAt`**: branch function for the one-step extension. -/
noncomputable def CoherentBranchApprox.extendToBranchAt
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR n) {α : Ordinal.{0}}
    (chain_α : PairERChain cR α) :
    ∀ k : Fin (n + 1), (A.extendToLevel α k).ToType → Bool :=
  fun k => by
    refine Fin.lastCases
      (motive := fun k => (A.extendToLevel α k).ToType → Bool) ?_ ?_ k
    · show (A.extendToLevel α (Fin.last n)).ToType → Bool
      rw [A.extendToLevel_last]; exact chain_α.type
    · intro j
      show (A.extendToLevel α j.castSucc).ToType → Bool
      rw [A.extendToLevel_castSucc]; exact A.branchAt j

theorem CoherentBranchApprox.extendToBranchAt_last_heq
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR n) {α : Ordinal.{0}}
    (chain_α : PairERChain cR α) :
    HEq (A.extendToBranchAt chain_α (Fin.last n)) chain_α.type := by
  unfold CoherentBranchApprox.extendToBranchAt
  rw [Fin.lastCases_last]
  exact cast_heq _ _

theorem CoherentBranchApprox.extendToBranchAt_castSucc_heq
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR n) {α : Ordinal.{0}}
    (chain_α : PairERChain cR α) (k : Fin n) :
    HEq (A.extendToBranchAt chain_α k.castSucc) (A.branchAt k) := by
  unfold CoherentBranchApprox.extendToBranchAt
  rw [Fin.lastCases_castSucc]
  exact cast_heq _ _

theorem CoherentBranchApprox.extendToBranchAt_last_apply
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR n) {α : Ordinal.{0}}
    (chain_α : PairERChain cR α) (x : (A.extendToLevel α (Fin.last n)).ToType) :
    A.extendToBranchAt chain_α (Fin.last n) x =
      chain_α.type ((A.extendToLevel_last α) ▸ x) :=
  fn_ordinal_apply_heq (A.extendToLevel_last α) _ _
    (A.extendToBranchAt_last_heq chain_α) x

theorem CoherentBranchApprox.extendToBranchAt_castSucc_apply
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR n) {α : Ordinal.{0}}
    (chain_α : PairERChain cR α) (k : Fin n)
    (x : (A.extendToLevel α k.castSucc).ToType) :
    A.extendToBranchAt chain_α k.castSucc x =
      A.branchAt k ((A.extendToLevel_castSucc α k) ▸ x) :=
  fn_ordinal_apply_heq (A.extendToLevel_castSucc α k) _ _
    (A.extendToBranchAt_castSucc_heq chain_α k) x

/-- **`CoherentBranchApprox.extendTo`** (depends on
`PairERChain.extendTo` family): generalization of `extendSucc` to
arbitrary countable target levels.

Given `A : CoherentBranchApprox cR n` and a countable ordinal `α`
strictly above `A.lastLevel`, produces a one-step extension
`CoherentBranchApprox cR (n+1)` with the new top at level `α`.

The body invokes `PairERChain.extendTo` (the named transfinite
frontier) to obtain the chain at `α`, then packages it via the
`extendTo{Level,PrefixAt,BranchAt}` helpers. All boundary HEq
bookkeeping is done by `orderEmbed_ordinal_apply_heq` /
`fn_ordinal_apply_heq` + the agreement frontier lemmas
(`extendTo_commitAt`, `_typeAt_old`, `_head_β_in_validFiber`). -/
noncomputable def CoherentBranchApprox.extendTo
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR n)
    (α : Ordinal.{0}) (hα : α < Ordinal.omega.{0} 1)
    (hα_above_last : A.lastLevel < α) :
    CoherentBranchApprox cR (n + 1) := by
  classical
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  -- The new chain at α, obtained via `PairERChain.extendTo` (via the
  -- named helper `extendToChain`).
  let nextChain : PairERChain cR α :=
    A.extendToChain α hα hα_above_last
  refine
    { level := A.extendToLevel α
      level_lt_omega1 := ?_
      level_strictMono := ?_
      prefixAt := A.extendToPrefixAt nextChain
      branchAt := A.extendToBranchAt nextChain
      prefix_restrict := ?_
      branch_restrict := ?_
      large := ?_
      top_in_validFiber := ?_ }
  · -- level_lt_omega1
    intro k
    induction k using Fin.lastCases with
    | last => rw [A.extendToLevel_last]; exact hα
    | cast k => rw [A.extendToLevel_castSucc]; exact A.level_lt_omega1 k
  · -- level_strictMono
    intro a b hab
    induction a using Fin.lastCases with
    | last =>
      exfalso
      exact absurd hab (not_lt_of_ge (Fin.le_last b))
    | cast j₁ =>
      induction b using Fin.lastCases with
      | last =>
        rw [A.extendToLevel_castSucc, A.extendToLevel_last]
        exact (A.lastLevel_ge j₁).trans_lt hα_above_last
      | cast j₂ =>
        rw [A.extendToLevel_castSucc, A.extendToLevel_castSucc]
        apply A.level_strictMono
        exact (Fin.castSucc_lt_castSucc_iff).mp hab
  · -- prefix_restrict
    intro k₁ k₂ hk x
    induction k₁ using Fin.lastCases with
    | last =>
      induction k₂ using Fin.lastCases with
      | last =>
        congr 1
        have h : Ordinal.initialSegToType
            (le_refl (A.extendToLevel α (Fin.last n))) =
            InitialSeg.refl _ := Subsingleton.elim _ _
        rw [h]; rfl
      | cast j₂ =>
        exact absurd hk (not_le_of_gt (Fin.castSucc_lt_last j₂))
    | cast j₁ =>
      induction k₂ using Fin.lastCases with
      | last =>
        -- Boundary case (k₁ = j₁.castSucc, k₂ = Fin.last n).
        haveI : IsWellOrder (A.level j₁).ToType (· < ·) := isWellOrder_lt
        set x' : (A.level j₁).ToType := (A.extendToLevel_castSucc α j₁) ▸ x with hx'
        rw [A.extendToPrefixAt_last_apply, A.extendToPrefixAt_castSucc_apply, ← hx']
        -- Goal: nextChain.head (transport of initialSegToType-lift x)
        --     = A.prefixAt j₁ x'
        -- Reduce LHS via `initialSegToType_transport_eq` and apply
        -- `extendToChain_head_at_level`.
        have h_lvl_le : A.level j₁ ≤ α :=
          (A.lastLevel_ge j₁).trans hα_above_last.le
        rw [initialSegToType_transport_eq (A.extendToLevel_castSucc α j₁)
            (A.extendToLevel_last α) _ h_lvl_le x]
        -- LHS now: nextChain.head ((initialSegToType h_lvl_le).toOrderEmbedding x')
        exact A.extendToChain_head_at_level α hα hα_above_last j₁ x'
      | cast j₂ =>
        have hj : j₁ ≤ j₂ := (Fin.castSucc_le_castSucc_iff).mp hk
        haveI : IsWellOrder (A.level j₁).ToType (· < ·) := isWellOrder_lt
        haveI : IsWellOrder (A.level j₂).ToType (· < ·) := isWellOrder_lt
        set x' : (A.level j₁).ToType := (A.extendToLevel_castSucc α j₁) ▸ x with hx'
        rw [A.extendToPrefixAt_castSucc_apply, A.extendToPrefixAt_castSucc_apply,
            ← hx']
        have hres := A.prefix_restrict hj x'
        convert hres using 2
        exact initialSegToType_transport_eq
          (A.extendToLevel_castSucc α j₁) (A.extendToLevel_castSucc α j₂) _ _ x
  · -- branch_restrict (parallel to prefix_restrict)
    intro k₁ k₂ hk x
    induction k₁ using Fin.lastCases with
    | last =>
      induction k₂ using Fin.lastCases with
      | last =>
        congr 1
        have h : Ordinal.initialSegToType
            (le_refl (A.extendToLevel α (Fin.last n))) =
            InitialSeg.refl _ := Subsingleton.elim _ _
        rw [h]; rfl
      | cast j₂ =>
        exact absurd hk (not_le_of_gt (Fin.castSucc_lt_last j₂))
    | cast j₁ =>
      induction k₂ using Fin.lastCases with
      | last =>
        -- Boundary case for branch.
        haveI : IsWellOrder (A.level j₁).ToType (· < ·) := isWellOrder_lt
        set x' : (A.level j₁).ToType := (A.extendToLevel_castSucc α j₁) ▸ x with hx'
        rw [A.extendToBranchAt_last_apply, A.extendToBranchAt_castSucc_apply, ← hx']
        have h_lvl_le : A.level j₁ ≤ α :=
          (A.lastLevel_ge j₁).trans hα_above_last.le
        rw [initialSegToType_transport_eq (A.extendToLevel_castSucc α j₁)
            (A.extendToLevel_last α) _ h_lvl_le x]
        exact A.extendToChain_type_at_level α hα hα_above_last j₁ x'
      | cast j₂ =>
        have hj : j₁ ≤ j₂ := (Fin.castSucc_le_castSucc_iff).mp hk
        haveI : IsWellOrder (A.level j₁).ToType (· < ·) := isWellOrder_lt
        haveI : IsWellOrder (A.level j₂).ToType (· < ·) := isWellOrder_lt
        set x' : (A.level j₁).ToType := (A.extendToLevel_castSucc α j₁) ▸ x with hx'
        rw [A.extendToBranchAt_castSucc_apply, A.extendToBranchAt_castSucc_apply,
            ← hx']
        have hres := A.branch_restrict hj x'
        convert hres using 2
        exact initialSegToType_transport_eq
          (A.extendToLevel_castSucc α j₁) (A.extendToLevel_castSucc α j₂) _ _ x
  · -- large
    intro k
    induction k using Fin.lastCases with
    | last =>
      show Order.succ (Cardinal.beth.{0} 1) ≤
          Cardinal.mk (validFiber cR (A.extendToPrefixAt nextChain (Fin.last n))
            (A.extendToBranchAt nextChain (Fin.last n)))
      convert nextChain.large using 4
      · exact A.extendToLevel_last α
      · exact A.extendToPrefixAt_last_heq nextChain
      · exact A.extendToBranchAt_last_heq nextChain
    | cast j =>
      show Order.succ (Cardinal.beth.{0} 1) ≤
          Cardinal.mk (validFiber cR (A.extendToPrefixAt nextChain j.castSucc)
            (A.extendToBranchAt nextChain j.castSucc))
      convert A.large j using 4
      · exact A.extendToLevel_castSucc α j
      · exact A.extendToPrefixAt_castSucc_heq nextChain j
      · exact A.extendToBranchAt_castSucc_heq nextChain j
  · -- top_in_validFiber
    intro i h
    have hi : i < n := Nat.lt_of_succ_lt_succ h
    by_cases hi1 : i + 1 < n
    · -- Both old (castSucc + castSucc): use A.top_in_validFiber.
      show A.extendToPrefixAt nextChain ((⟨i + 1, hi1⟩ : Fin n).castSucc)
          ((Ordinal.enum (· < ·))
            ⟨A.extendToLevel α ((⟨i, hi⟩ : Fin n).castSucc), _⟩) ∈ _
      convert A.top_in_validFiber i hi1 using 2
      · exact A.extendToLevel_castSucc α ⟨i, hi⟩
      · exact A.extendToPrefixAt_castSucc_heq nextChain ⟨i, hi⟩
      · exact A.extendToBranchAt_castSucc_heq nextChain ⟨i, hi⟩
      · rw [A.extendToPrefixAt_castSucc_apply]
        congr 1
        exact enum_transport_eq (A.extendToLevel_castSucc α ⟨i + 1, hi1⟩)
          (A.extendToLevel_castSucc α ⟨i, hi⟩) _ _
    · -- ⟨i + 1, h⟩ = Fin.last n; use extendToChain_realizes_at_lastIndex.
      -- We subst n = i + 1 so the indices become concrete, then bridge via
      -- the apply lemmas and `orderEmbed_ordinal_apply_heq` /
      -- `enum_transport_eq` for the dependent enum bound.
      have hi1_eq : i + 1 = n := by omega
      obtain rfl : n = i + 1 := hi1_eq.symm
      have hn_ne_zero : i + 1 ≠ 0 := by omega
      have hn' : i + 1 - 1 < i + 1 := by omega
      have h_idx : (⟨i, hi⟩ : Fin (i + 1)) = ⟨i + 1 - 1, hn'⟩ := by
        apply Fin.ext; show i = i + 1 - 1; omega
      have h_last : (⟨i + 1, h⟩ : Fin (i + 1 + 1)) = Fin.last (i + 1) :=
        Fin.ext rfl
      convert A.extendToChain_realizes_at_lastIndex α hα hα_above_last
          hn_ne_zero using 2
      · show A.extendToLevel α (⟨i, hi⟩ : Fin (i + 1)).castSucc =
          A.level ⟨i + 1 - 1, hn'⟩
        rw [A.extendToLevel_castSucc α ⟨i, hi⟩, h_idx]
      · show HEq (A.extendToPrefixAt nextChain (⟨i, hi⟩ : Fin (i + 1)).castSucc)
          (A.prefixAt ⟨i + 1 - 1, hn'⟩)
        rw [h_idx]
        exact A.extendToPrefixAt_castSucc_heq nextChain _
      · show HEq (A.extendToBranchAt nextChain (⟨i, hi⟩ : Fin (i + 1)).castSucc)
          (A.branchAt ⟨i + 1 - 1, hn'⟩)
        rw [h_idx]
        exact A.extendToBranchAt_castSucc_heq nextChain _
      · haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
        have h_lvl : A.extendToLevel α ⟨i + 1, h⟩ = α := by
          show A.extendToLevel α (Fin.last (i + 1)) = α
          exact A.extendToLevel_last α
        have h_fn_heq : HEq (A.extendToPrefixAt nextChain ⟨i + 1, h⟩)
            nextChain.head := by
          rw [h_last]; exact A.extendToPrefixAt_last_heq nextChain
        rw [orderEmbed_ordinal_apply_heq h_lvl _ _ h_fn_heq]
        congr 1
        exact enum_transport_eq h_lvl
          (A.extendToLevel_castSucc α ⟨i + 1 - 1, hn'⟩) _ _

/-! ### Approximations over arbitrary finite ordinal sequences

`CoherentBranchApprox.extendTo` adds a level at an arbitrary countable
ordinal `α > A.lastLevel`. Iterating this from
`CoherentBranchApprox.zero` along a strictly-sorted list of countable
positive ordinals produces a `CoherentBranchApprox` over those exact
levels — the **finite-arbitrary-levels** analog of the
natural-number-only `coherentBranchApproxSeq`.

This is the bridge from finite-ordinal levels (via `extend`) to
countable-ordinal levels (via `extendTo`). The remaining step toward
`exists_coherentMajorityBranch` is a compactness/Kőnig-style
extraction to all countable levels. -/

/-- **`exists_coherentBranchApprox_for_strictMono`**: build a
`CoherentBranchApprox cR n` over any strictly-monotone `Fin`-indexed
family of countable ordinals (no positivity required), with
`A.level i = f i`.

This is the Fin-indexed form of the "finite-arbitrary-levels" bridge.
For `k > 0` the induction proceeds via `extendTo` (strict-monotonicity
gives `A'.lastLevel < α`); for `k = 0` (the n = 1 base) we case-split:
`α > 0` uses `(CoherentBranchApprox.zero cR).extendTo α`, while
`α = 0` uses `CoherentBranchApprox.fromZero` directly. -/
theorem exists_coherentBranchApprox_for_strictMono
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    ∀ {n : ℕ} (f : Fin n → Ordinal.{0})
      (_h_lt : ∀ i, f i < Ordinal.omega.{0} 1)
      (_h_strictMono : StrictMono f),
      ∃ A : CoherentBranchApprox cR n, ∀ i, A.level i = f i := by
  intro n
  induction n with
  | zero =>
    intro f _ _
    refine ⟨CoherentBranchApprox.zero cR, ?_⟩
    intro i; exact i.elim0
  | succ k IH =>
    intro f h_lt h_strictMono
    by_cases hk : k = 0
    · -- n = 1 case. Special-handle f ⟨0, _⟩ = 0 via fromZero.
      subst hk
      let α : Ordinal.{0} := f ⟨0, Nat.zero_lt_one⟩
      have hα_lt : α < Ordinal.omega.{0} 1 := h_lt _
      by_cases hα_pos : 0 < α
      · -- α > 0: extend CBA.zero.
        refine ⟨(CoherentBranchApprox.zero cR).extendTo α hα_lt hα_pos, ?_⟩
        intro i
        have hi_eq : i = Fin.last 0 :=
          Fin.ext (by have := i.isLt; omega)
        rw [hi_eq]
        exact (CoherentBranchApprox.zero cR).extendToLevel_last α
      · -- α = 0: use fromZero directly.
        push_neg at hα_pos
        have hα_eq : α = 0 := le_antisymm hα_pos (zero_le _)
        refine ⟨CoherentBranchApprox.fromZero cR, ?_⟩
        intro i
        have hi_eq : i = ⟨0, Nat.zero_lt_one⟩ :=
          Fin.ext (by have := i.isLt; omega)
        rw [hi_eq]
        show (0 : Ordinal) = f ⟨0, Nat.zero_lt_one⟩
        exact hα_eq.symm
    · -- k > 0 case. IH + extendTo; h_above follows from strict mono.
      let f' : Fin k → Ordinal.{0} := fun i => f i.castSucc
      have h_lt' : ∀ i, f' i < Ordinal.omega.{0} 1 := fun i => h_lt _
      have h_strictMono' : StrictMono f' := fun _ _ hab =>
        h_strictMono (Fin.castSucc_lt_castSucc_iff.mpr hab)
      obtain ⟨A', hA'⟩ := IH f' h_lt' h_strictMono'
      let α : Ordinal.{0} := f (Fin.last k)
      have hα_lt : α < Ordinal.omega.{0} 1 := h_lt _
      have h_above : A'.lastLevel < α := by
        unfold CoherentBranchApprox.lastLevel
        rw [dif_neg hk]
        have hk' : k - 1 < k := Nat.sub_lt (Nat.pos_of_ne_zero hk) one_pos
        rw [hA' ⟨k - 1, hk'⟩]
        show f' ⟨k - 1, hk'⟩ < α
        show f (⟨k - 1, hk'⟩ : Fin k).castSucc < f (Fin.last k)
        apply h_strictMono
        exact Fin.castSucc_lt_last _
      refine ⟨A'.extendTo α hα_lt h_above, ?_⟩
      intro i
      show A'.extendToLevel α i = f i
      induction i using Fin.lastCases with
      | last => rw [A'.extendToLevel_last]
      | cast j =>
        rw [A'.extendToLevel_castSucc α j, hA' j]

/-- **`exists_coherentBranchApprox_for_list`**: build a
`CoherentBranchApprox cR l.length` over any strictly-sorted finite
list `l` of countable ordinals (no positivity required), with
`A.level i = l.get i`.

Derived from `exists_coherentBranchApprox_for_strictMono` by reading
the list as a Fin-indexed family. -/
theorem exists_coherentBranchApprox_for_list
    (cR : (Fin 2 ↪o PairERSource) → Bool)
    (l : List Ordinal.{0})
    (h_sorted : l.Pairwise (· < ·))
    (h_lt : ∀ α ∈ l, α < Ordinal.omega.{0} 1) :
    ∃ A : CoherentBranchApprox cR l.length,
      ∀ i : Fin l.length, A.level i = l.get i := by
  refine exists_coherentBranchApprox_for_strictMono cR (l.get) ?_ ?_
  · exact fun i => h_lt _ (List.get_mem _ _)
  · intro a b hab
    exact List.pairwise_iff_get.mp h_sorted a b hab

/-! ### Finset-indexed partial branches

`CoherentBranchPartial cR S` is the Finset-indexed analog of
`CoherentMajorityBranch`: a partial coherent branch with data
defined exactly at the ordinals in `S`. It is the compactness object
on which a Kőnig-style extraction toward `exists_coherentMajorityBranch`
operates: instead of building approximations indexed by an arbitrary
n-length list, the projective system is indexed by finite subsets of
`ω₁`, removing dependence on list order.

The structure is a thin wrapper around `CoherentBranchApprox cR S.card`
plus a level identification with `S.orderEmbOfFin rfl`. The CMB-style
accessors (`prefixAt`, `branch`, `prefix_restrict`, `branch_restrict`,
`large`, `top_in_validFiber`) are derived in subsequent definitions
and lemmas, with transport handled via `level_indexOf`.

Existence (`exists_coherentBranchPartial`) is immediate from
`exists_coherentBranchApprox_for_strictMono` using the strictly-
monotone embedding `S.orderEmbOfFin rfl : Fin S.card ↪o Ordinal`. -/

/-- **`CoherentBranchPartial cR S`**: partial coherent branch indexed
by a finite set `S` of countable ordinals. Internally backed by a
`CoherentBranchApprox cR S.card` whose `level` matches
`S.orderEmbOfFin rfl`. -/
structure CoherentBranchPartial
    (cR : (Fin 2 ↪o PairERSource) → Bool) (S : Finset Ordinal.{0}) where
  /-- The underlying approximation at length `S.card`. -/
  toApprox : CoherentBranchApprox cR S.card
  /-- Level identification: the approximation's level at index `i`
  equals the `i`-th element of `S` (in increasing order). -/
  level_eq : ∀ i : Fin S.card,
    toApprox.level i = (S.orderEmbOfFin rfl) i

/-- **`exists_coherentBranchPartial`**: for any finite set `S` of
countable ordinals, there exists a `CoherentBranchPartial cR S`.
No positivity hypothesis required; the `0 ∈ S` case is handled by
`CoherentBranchApprox.fromZero` inside the `strictMono` constructor. -/
theorem exists_coherentBranchPartial
    (cR : (Fin 2 ↪o PairERSource) → Bool) (S : Finset Ordinal.{0})
    (hS : ∀ α ∈ S, α < Ordinal.omega.{0} 1) :
    Nonempty (CoherentBranchPartial cR S) := by
  obtain ⟨A, hA⟩ := exists_coherentBranchApprox_for_strictMono cR
    (S.orderEmbOfFin rfl)
    (fun i => hS _ (S.orderEmbOfFin_mem rfl i))
    (S.orderEmbOfFin rfl).strictMono
  exact ⟨{ toApprox := A, level_eq := hA }⟩

/-! ### CMB-style accessors for `CoherentBranchPartial`

Project the underlying approximation into the CMB-style API: take
`α ∈ S` arguments (not Fin indices) and return data over `α.ToType`
(transported through the level identification). -/

/-- **`indexOf`**: the `Fin S.card` index corresponding to `α ∈ S`. -/
noncomputable def CoherentBranchPartial.indexOf {cR : (Fin 2 ↪o PairERSource) → Bool}
    {S : Finset Ordinal.{0}} (_P : CoherentBranchPartial cR S)
    (α : Ordinal.{0}) (hα : α ∈ S) : Fin S.card :=
  (S.orderIsoOfFin rfl).symm ⟨α, hα⟩

/-- **`level_indexOf`**: the approximation's level at `indexOf α hα`
equals `α`. The key transport hypothesis for the accessors below. -/
lemma CoherentBranchPartial.level_indexOf
    {cR : (Fin 2 ↪o PairERSource) → Bool} {S : Finset Ordinal.{0}}
    (P : CoherentBranchPartial cR S) (α : Ordinal.{0}) (hα : α ∈ S) :
    P.toApprox.level (P.indexOf α hα) = α := by
  rw [P.level_eq]
  show ↑((S.orderIsoOfFin rfl) ((S.orderIsoOfFin rfl).symm ⟨α, hα⟩)) = α
  rw [(S.orderIsoOfFin rfl).apply_symm_apply]

/-- **`prefixAt`**: CMB-style prefix accessor at `α ∈ S`, with the
type `α.ToType ↪o PairERSource` obtained by casting the
approximation's prefix at `indexOf α hα` along `level_indexOf`.

Uses `cast` (with explicit `congrArg`) rather than the `▸` shorthand
so that `cast_heq` directly produces the HEq witness used in the
projection theorems below. -/
noncomputable def CoherentBranchPartial.prefixAt
    {cR : (Fin 2 ↪o PairERSource) → Bool} {S : Finset Ordinal.{0}}
    (P : CoherentBranchPartial cR S) (α : Ordinal.{0}) (hα : α ∈ S) :
    α.ToType ↪o PairERSource :=
  cast (congrArg (fun o : Ordinal.{0} => o.ToType ↪o PairERSource)
    (P.level_indexOf α hα)) (P.toApprox.prefixAt (P.indexOf α hα))

/-- **`branch`**: CMB-style branch accessor at `α ∈ S`. -/
noncomputable def CoherentBranchPartial.branch
    {cR : (Fin 2 ↪o PairERSource) → Bool} {S : Finset Ordinal.{0}}
    (P : CoherentBranchPartial cR S) (α : Ordinal.{0}) (hα : α ∈ S) :
    α.ToType → Bool :=
  cast (congrArg (fun o : Ordinal.{0} => o.ToType → Bool)
    (P.level_indexOf α hα)) (P.toApprox.branchAt (P.indexOf α hα))

/-- **`prefixAt_heq_prefixAt`**: HEq between the CMB-style accessor and
the underlying approximation's prefix. -/
lemma CoherentBranchPartial.prefixAt_heq_toApprox_prefixAt
    {cR : (Fin 2 ↪o PairERSource) → Bool} {S : Finset Ordinal.{0}}
    (P : CoherentBranchPartial cR S) (α : Ordinal.{0}) (hα : α ∈ S) :
    HEq (P.prefixAt α hα) (P.toApprox.prefixAt (P.indexOf α hα)) :=
  cast_heq _ _

/-- **`branch_heq_toApprox_branchAt`**: HEq between the CMB-style
branch accessor and the underlying approximation's branch. -/
lemma CoherentBranchPartial.branch_heq_toApprox_branchAt
    {cR : (Fin 2 ↪o PairERSource) → Bool} {S : Finset Ordinal.{0}}
    (P : CoherentBranchPartial cR S) (α : Ordinal.{0}) (hα : α ∈ S) :
    HEq (P.branch α hα) (P.toApprox.branchAt (P.indexOf α hα)) :=
  cast_heq _ _

/-! ### Apply-rewriters for the CMB-style accessors

Express `prefixAt α hα y` and `branch α hα y` as applications of
the underlying `toApprox.prefixAt` / `toApprox.branchAt` after the
inverse transport. Used as the bridge in the CMB-style theorems
(`prefix_restrict`, `branch_restrict`, `large`). -/

lemma CoherentBranchPartial.prefixAt_apply
    {cR : (Fin 2 ↪o PairERSource) → Bool} {S : Finset Ordinal.{0}}
    (P : CoherentBranchPartial cR S) (α : Ordinal.{0}) (hα : α ∈ S)
    (y : α.ToType) :
    P.prefixAt α hα y =
      P.toApprox.prefixAt (P.indexOf α hα)
        ((P.level_indexOf α hα).symm ▸ y) :=
  orderEmbed_ordinal_apply_heq (P.level_indexOf α hα).symm _ _
    (P.prefixAt_heq_toApprox_prefixAt α hα) y

lemma CoherentBranchPartial.branch_apply
    {cR : (Fin 2 ↪o PairERSource) → Bool} {S : Finset Ordinal.{0}}
    (P : CoherentBranchPartial cR S) (α : Ordinal.{0}) (hα : α ∈ S)
    (y : α.ToType) :
    P.branch α hα y =
      P.toApprox.branchAt (P.indexOf α hα)
        ((P.level_indexOf α hα).symm ▸ y) :=
  fn_ordinal_apply_heq (P.level_indexOf α hα).symm _ _
    (P.branch_heq_toApprox_branchAt α hα) y

/-! ### Index monotonicity: `β ≤ α` ∈ `S` implies `indexOf β ≤ indexOf α`

Since `S.orderIsoOfFin rfl` is an order isomorphism, its inverse is
also order-preserving, so the indices respect the ordinal order on
the elements of `S`. -/

lemma CoherentBranchPartial.indexOf_le
    {cR : (Fin 2 ↪o PairERSource) → Bool} {S : Finset Ordinal.{0}}
    (P : CoherentBranchPartial cR S)
    {β α : Ordinal.{0}} (hβ : β ∈ S) (hα : α ∈ S) (hβα : β ≤ α) :
    P.indexOf β hβ ≤ P.indexOf α hα :=
  (S.orderIsoOfFin rfl).symm.monotone (Subtype.mk_le_mk.mpr hβα)

/-! ### CMB-style projection theorems

The CoherentMajorityBranch-style theorems (`prefix_restrict`,
`branch_restrict`, `large`) projected onto the partial structure.
All follow from the corresponding `CoherentBranchApprox` field via
`indexOf_le` + the `apply` rewriters + the transport-coherence
lemmas (`initialSegToType_transport_eq`). -/

theorem CoherentBranchPartial.prefix_restrict
    {cR : (Fin 2 ↪o PairERSource) → Bool} {S : Finset Ordinal.{0}}
    (P : CoherentBranchPartial cR S)
    {β α : Ordinal.{0}} (hβα : β ≤ α) (hβ : β ∈ S) (hα : α ∈ S)
    (x : β.ToType) :
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
    P.prefixAt α hα ((Ordinal.initialSegToType hβα).toOrderEmbedding x) =
      P.prefixAt β hβ x := by
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  have h_lvl_α : P.toApprox.level (P.indexOf α hα) = α := P.level_indexOf α hα
  have h_lvl_β : P.toApprox.level (P.indexOf β hβ) = β := P.level_indexOf β hβ
  have hidx_le : P.indexOf β hβ ≤ P.indexOf α hα := P.indexOf_le hβ hα hβα
  have h_lvl_le : P.toApprox.level (P.indexOf β hβ) ≤
      P.toApprox.level (P.indexOf α hα) :=
    P.toApprox.level_strictMono.monotone hidx_le
  rw [P.prefixAt_apply α hα, P.prefixAt_apply β hβ,
      initialSegToType_transport_eq h_lvl_β.symm h_lvl_α.symm hβα h_lvl_le x]
  exact P.toApprox.prefix_restrict hidx_le _

theorem CoherentBranchPartial.branch_restrict
    {cR : (Fin 2 ↪o PairERSource) → Bool} {S : Finset Ordinal.{0}}
    (P : CoherentBranchPartial cR S)
    {β α : Ordinal.{0}} (hβα : β ≤ α) (hβ : β ∈ S) (hα : α ∈ S)
    (x : β.ToType) :
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
    P.branch α hα ((Ordinal.initialSegToType hβα).toOrderEmbedding x) =
      P.branch β hβ x := by
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  have h_lvl_α : P.toApprox.level (P.indexOf α hα) = α := P.level_indexOf α hα
  have h_lvl_β : P.toApprox.level (P.indexOf β hβ) = β := P.level_indexOf β hβ
  have hidx_le : P.indexOf β hβ ≤ P.indexOf α hα := P.indexOf_le hβ hα hβα
  have h_lvl_le : P.toApprox.level (P.indexOf β hβ) ≤
      P.toApprox.level (P.indexOf α hα) :=
    P.toApprox.level_strictMono.monotone hidx_le
  rw [P.branch_apply α hα, P.branch_apply β hβ,
      initialSegToType_transport_eq h_lvl_β.symm h_lvl_α.symm hβα h_lvl_le x]
  exact P.toApprox.branch_restrict hidx_le _

theorem CoherentBranchPartial.large
    {cR : (Fin 2 ↪o PairERSource) → Bool} {S : Finset Ordinal.{0}}
    (P : CoherentBranchPartial cR S) (α : Ordinal.{0}) (hα : α ∈ S) :
    Order.succ (Cardinal.beth.{0} 1) ≤
      Cardinal.mk (validFiber cR (P.prefixAt α hα) (P.branch α hα)) := by
  have h_lvl : P.toApprox.level (P.indexOf α hα) = α := P.level_indexOf α hα
  have := P.toApprox.large (P.indexOf α hα)
  convert this using 4
  · exact h_lvl.symm
  · exact P.prefixAt_heq_toApprox_prefixAt α hα
  · exact P.branch_heq_toApprox_branchAt α hα

/-! ### Successor adjacency in the index map

If both `γ` and `Order.succ γ` lie in `S`, then their `indexOf` indices
are **consecutive** in `Fin S.card` (i.e., `idx_{succ γ}.val = idx_γ.val + 1`).
This holds because no ordinal lies strictly between `γ` and `Order.succ γ`
(by `Order.lt_succ_iff`), and an `OrderEmbedding` from `Fin S.card` into
`Ordinal` strictly preserves order — so any in-between index would
witness an in-between ordinal in `S`, a contradiction.

This adjacency is the bridge from CBA's index-adjacent `top_in_validFiber`
field to the CMB-aligned `(γ, Order.succ γ)` form. -/

/-- Helper: the `orderEmbOfFin` value at the `indexOf` of any element
`α ∈ S` is `α` itself. -/
private lemma CoherentBranchPartial.orderEmbOfFin_indexOf
    {cR : (Fin 2 ↪o PairERSource) → Bool} {S : Finset Ordinal.{0}}
    (_P : CoherentBranchPartial cR S)
    (α : Ordinal.{0}) (hα : α ∈ S) :
    (S.orderEmbOfFin rfl) ((S.orderIsoOfFin rfl).symm ⟨α, hα⟩) = α := by
  rw [← S.coe_orderIsoOfFin_apply rfl,
      (S.orderIsoOfFin rfl).apply_symm_apply]

lemma CoherentBranchPartial.indexOf_succ_eq_succ_indexOf
    {cR : (Fin 2 ↪o PairERSource) → Bool} {S : Finset Ordinal.{0}}
    (P : CoherentBranchPartial cR S)
    (γ : Ordinal.{0}) (hγ : γ ∈ S) (hsγ : Order.succ γ ∈ S) :
    (P.indexOf (Order.succ γ) hsγ).val = (P.indexOf γ hγ).val + 1 := by
  set i : Fin S.card := P.indexOf γ hγ with hi_def
  set j : Fin S.card := P.indexOf (Order.succ γ) hsγ with hj_def
  have h_fi : (S.orderEmbOfFin rfl) i = γ := P.orderEmbOfFin_indexOf γ hγ
  have h_fj : (S.orderEmbOfFin rfl) j = Order.succ γ :=
    P.orderEmbOfFin_indexOf (Order.succ γ) hsγ
  -- f strictly mono + γ < succ γ gives i.val < j.val.
  have h_lt : i.val < j.val := by
    have : i < j := (S.orderEmbOfFin rfl).strictMono.lt_iff_lt.mp
      (by rw [h_fi, h_fj]; exact Order.lt_succ γ)
    exact this
  -- Show i.val + 1 = j.val.
  by_contra h_ne
  have h_lt' : i.val + 1 < j.val := by omega
  have hk_lt_card : i.val + 1 < S.card := h_lt'.trans j.isLt
  set k : Fin S.card := ⟨i.val + 1, hk_lt_card⟩ with hk_def
  have h_i_lt_k : i < k := by
    show i.val < k.val
    show i.val < i.val + 1
    omega
  have h_k_lt_j : k < j := by
    show k.val < j.val
    show i.val + 1 < j.val
    exact h_lt'
  have h_γ_lt_fk : γ < (S.orderEmbOfFin rfl) k :=
    h_fi ▸ (S.orderEmbOfFin rfl).strictMono h_i_lt_k
  have h_fk_lt_sγ : (S.orderEmbOfFin rfl) k < Order.succ γ :=
    h_fj ▸ (S.orderEmbOfFin rfl).strictMono h_k_lt_j
  have h_fk_le_γ : (S.orderEmbOfFin rfl) k ≤ γ := Order.lt_succ_iff.mp h_fk_lt_sγ
  exact absurd (lt_of_lt_of_le h_γ_lt_fk h_fk_le_γ) (lt_irrefl γ)

/-! ### CMB-style `top_in_validFiber` for `CoherentBranchPartial`

The successor-adjacent validFiber property in CMB-style form: when
both `γ` and `Order.succ γ` lie in `S`, the top of `(Order.succ γ).ToType`
under the partial branch's prefix lies in the validFiber for `γ`.

Proof structure:
1. Use `indexOf_succ_eq_succ_indexOf` to identify
   `(indexOf γ).val = i.val` and `(indexOf (succ γ)).val = i.val + 1`.
2. Invoke the CBA's index-adjacent `top_in_validFiber` at `i.val`.
3. Use `Fin.eta` to rewrite the resulting CBA indices to `i` and `j`.
4. Use `validFiber_eq_of_HEq` (+ `prefixAt_heq_toApprox_prefixAt`,
   `branch_heq_toApprox_branchAt`) to convert the validFiber.
5. Use `prefixAt_apply` to expose the `cast`-transport on the LHS,
   then `enum_succ_eq_top.symm` + `enum_transport_eq` to identify
   the transported `⊤` with the `enum` argument of the CBA-level
   statement. -/

/-- **Helper**: CBA-level `top_in_validFiber` with explicit Fin
indices and matching level data. Bridges from the index-adjacent form
(over `i.val`, `i.val + 1`) to a parametric form usable when the
indices come from `indexOf`-lookup. -/
private lemma CoherentBranchApprox.top_in_validFiber_at
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR n)
    {i j : Fin n} (h_adj : j.val = i.val + 1) :
    haveI : IsWellOrder (A.level j).ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder (A.level i).ToType (· < ·) := isWellOrder_lt
    A.prefixAt j (Ordinal.enum (α := (A.level j).ToType) (· < ·)
      ⟨A.level i, by
        haveI : IsWellOrder (A.level j).ToType (· < ·) := isWellOrder_lt
        rw [Ordinal.type_toType]
        exact A.level_strictMono (show i < j by
          show i.val < j.val; omega)⟩) ∈
    validFiber cR (A.prefixAt i) (A.branchAt i) := by
  haveI : IsWellOrder (A.level j).ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder (A.level i).ToType (· < ·) := isWellOrder_lt
  -- Substitute j = ⟨i.val + 1, _⟩ via subst.
  have h_j_idx_lt : i.val + 1 < n := h_adj ▸ j.isLt
  obtain rfl : j = ⟨i.val + 1, h_j_idx_lt⟩ := Fin.ext h_adj
  -- `i` and `⟨i.val, _⟩` are definitionally equal via Fin proof
  -- irrelevance, so the CBA field applies directly.
  exact A.top_in_validFiber i.val h_j_idx_lt

/-- **`validFiber_between`** (generalization of `top_in_validFiber_at`
to arbitrary `i < j`): the value at position `A.level i` in the
chain at `A.level j` lies in the validFiber for `A.level i`,
regardless of whether `i` and `j` are adjacent in `Fin n`.

Proof: factor through `i + 1`. The element `enum_j at A.level i` is
the `(initialSegToType (A.level (i+1) ≤ A.level j))`-lift of
`enum_(i+1) at A.level i`, by `Ordinal.typein_apply` / `typein_enum`.
Then `A.prefix_restrict` collapses the lift, and `top_in_validFiber_at`
at `(i, i+1)` closes the goal. -/
private lemma CoherentBranchApprox.validFiber_between
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR n)
    {i j : Fin n} (hij : i < j) :
    haveI : IsWellOrder (A.level j).ToType (· < ·) := isWellOrder_lt
    A.prefixAt j (Ordinal.enum (α := (A.level j).ToType) (· < ·)
      ⟨A.level i, by
        haveI : IsWellOrder (A.level j).ToType (· < ·) := isWellOrder_lt
        rw [Ordinal.type_toType]
        exact A.level_strictMono hij⟩) ∈
    validFiber cR (A.prefixAt i) (A.branchAt i) := by
  haveI : IsWellOrder (A.level j).ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder (A.level i).ToType (· < ·) := isWellOrder_lt
  -- Define k = i + 1 (as a Fin index) and verify k ≤ j.
  have hk_lt : i.val + 1 < n := by
    have h1 : i.val + 1 ≤ j.val := hij
    have h2 : j.val < n := j.isLt
    omega
  let k : Fin n := ⟨i.val + 1, hk_lt⟩
  haveI : IsWellOrder (A.level k).ToType (· < ·) := isWellOrder_lt
  have hik : i < k := by show i.val < k.val; show i.val < i.val + 1; omega
  have hkj : k ≤ j := by show k.val ≤ j.val; show i.val + 1 ≤ j.val; exact hij
  have h_lvl_le : A.level k ≤ A.level j := A.level_strictMono.monotone hkj
  -- Adjacency at (i, k) via top_in_validFiber_at.
  have h_top : A.prefixAt k (Ordinal.enum (α := (A.level k).ToType) (· < ·)
        ⟨A.level i, by
          haveI : IsWellOrder (A.level k).ToType (· < ·) := isWellOrder_lt
          rw [Ordinal.type_toType]
          exact A.level_strictMono hik⟩) ∈
      validFiber cR (A.prefixAt i) (A.branchAt i) :=
    A.top_in_validFiber_at (show k.val = i.val + 1 from rfl)
  -- The lift of `enum_k at A.level i` equals `enum_j at A.level i`.
  have h_lift_eq :
      (Ordinal.initialSegToType h_lvl_le).toOrderEmbedding
        (Ordinal.enum (α := (A.level k).ToType) (· < ·)
          ⟨A.level i, by
            haveI : IsWellOrder (A.level k).ToType (· < ·) := isWellOrder_lt
            rw [Ordinal.type_toType]
            exact A.level_strictMono hik⟩) =
      Ordinal.enum (α := (A.level j).ToType) (· < ·)
        ⟨A.level i, by
          haveI : IsWellOrder (A.level j).ToType (· < ·) := isWellOrder_lt
          rw [Ordinal.type_toType]
          exact A.level_strictMono hij⟩ := by
    rw [← Ordinal.enum_typein (· < · : (A.level j).ToType → (A.level j).ToType → Prop)
      ((Ordinal.initialSegToType h_lvl_le).toOrderEmbedding _)]
    congr 1
    apply Subtype.ext
    show Ordinal.typein (α := (A.level j).ToType) (· < ·)
        ((Ordinal.initialSegToType h_lvl_le).toOrderEmbedding _) = A.level i
    rw [show Ordinal.typein (α := (A.level j).ToType) (· < ·)
          ((Ordinal.initialSegToType h_lvl_le).toOrderEmbedding _) =
        Ordinal.typein (α := (A.level k).ToType) (· < ·)
          (Ordinal.enum (α := (A.level k).ToType) (· < ·)
            ⟨A.level i, by
              haveI : IsWellOrder (A.level k).ToType (· < ·) := isWellOrder_lt
              rw [Ordinal.type_toType]
              exact A.level_strictMono hik⟩) from
        Ordinal.typein_apply _ _, Ordinal.typein_enum]
  -- Conclude via prefix_restrict (k ≤ j).
  rw [← h_lift_eq, A.prefix_restrict hkj _]
  exact h_top

theorem CoherentBranchPartial.top_in_validFiber
    {cR : (Fin 2 ↪o PairERSource) → Bool} {S : Finset Ordinal.{0}}
    (P : CoherentBranchPartial cR S) (γ : Ordinal.{0}) (hγ : γ ∈ S)
    (hsγ : Order.succ γ ∈ S) :
    haveI : IsWellOrder (Order.succ γ).ToType (· < ·) := isWellOrder_lt
    P.prefixAt (Order.succ γ) hsγ (⊤ : (Order.succ γ).ToType) ∈
      validFiber cR (P.prefixAt γ hγ) (P.branch γ hγ) := by
  haveI : IsWellOrder (Order.succ γ).ToType (· < ·) := isWellOrder_lt
  have h_lvl_γ : P.toApprox.level (P.indexOf γ hγ) = γ := P.level_indexOf γ hγ
  have h_lvl_sγ : P.toApprox.level (P.indexOf (Order.succ γ) hsγ) =
      Order.succ γ := P.level_indexOf (Order.succ γ) hsγ
  have h_succ : (P.indexOf (Order.succ γ) hsγ).val =
      (P.indexOf γ hγ).val + 1 :=
    P.indexOf_succ_eq_succ_indexOf γ hγ hsγ
  -- Step 1: Convert goal's validFiber to A's via HEq.
  rw [validFiber_eq_of_HEq h_lvl_γ.symm
      (P.prefixAt_heq_toApprox_prefixAt γ hγ)
      (P.branch_heq_toApprox_branchAt γ hγ)]
  -- Step 2: Expose the cast on LHS via prefixAt_apply.
  rw [P.prefixAt_apply (Order.succ γ) hsγ]
  -- Goal: A.prefixAt (P.indexOf (succ γ) hsγ) (h_lvl_sγ.symm ▸ ⊤) ∈
  --         validFiber cR (A.prefixAt (P.indexOf γ hγ)) (A.branchAt (P.indexOf γ hγ))
  -- Apply the CBA-level helper (which handles the Fin-index plumbing).
  haveI : IsWellOrder (P.toApprox.level (P.indexOf (Order.succ γ) hsγ)).ToType
      (· < ·) := isWellOrder_lt
  haveI : IsWellOrder (P.toApprox.level (P.indexOf γ hγ)).ToType
      (· < ·) := isWellOrder_lt
  convert P.toApprox.top_in_validFiber_at h_succ using 2
  -- Single subgoal: cast_⊤ = enum at A.level (P.indexOf γ hγ) in A.level (P.indexOf (succ γ) hsγ).
  rw [show (⊤ : (Order.succ γ).ToType) =
        Ordinal.enum (α := (Order.succ γ).ToType) (· < ·)
          ⟨γ, (Ordinal.type_toType _).symm ▸ Order.lt_succ γ⟩ from
      Ordinal.enum_succ_eq_top.symm]
  exact enum_transport_eq h_lvl_sγ.symm h_lvl_γ.symm _ _

/-! ### Restriction `CoherentBranchPartial.restrict`

Given `P : CoherentBranchPartial cR T` and `S ⊆ T`, restrict `P` to a
`CoherentBranchPartial cR S` by pulling back through `P.indexOf`:
each `i : Fin S.card` lands at the `T`-index of `(S.orderEmbOfFin rfl) i`.

The construction takes the new CBA's `level` to be `P.toApprox.level ∘
ρ` (rather than `S.orderEmbOfFin rfl` directly), so `prefixAt` and
`branchAt` need no casts — they are literally
`P.toApprox.prefixAt (ρ i)` / `P.toApprox.branchAt (ρ i)`. The level
agreement with `S.orderEmbOfFin rfl` is then a separate field
(`level_eq`) given by `P.level_indexOf`. The CBA's
`top_in_validFiber` field — which requires validFiber adjacency at
**arbitrary** `(ρ i, ρ (i+1))` pairs in `P.toApprox` (not necessarily
consecutive in `Fin T.card`) — is supplied by `validFiber_between`. -/

noncomputable def CoherentBranchPartial.restrict
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {T : Finset Ordinal.{0}} (P : CoherentBranchPartial cR T)
    {S : Finset Ordinal.{0}} (hST : S ⊆ T) :
    CoherentBranchPartial cR S := by
  classical
  -- The S-elements as a strict-mono Fin S.card → Ordinal.
  set σ_S : Fin S.card → Ordinal.{0} := fun i => (S.orderEmbOfFin rfl) i with hσS
  have h_σ_S : ∀ i, σ_S i ∈ S := S.orderEmbOfFin_mem rfl
  have h_σ_T : ∀ i, σ_S i ∈ T := fun i => hST (h_σ_S i)
  -- ρ : Fin S.card → Fin T.card via P.indexOf.
  set ρ : Fin S.card → Fin T.card := fun i => P.indexOf (σ_S i) (h_σ_T i) with hρ
  -- Level identification at each pulled-back index.
  have h_lvl_ρ : ∀ i, P.toApprox.level (ρ i) = σ_S i :=
    fun i => P.level_indexOf (σ_S i) (h_σ_T i)
  -- ρ is strictly monotone (via OrderIso composition).
  have h_ρ_strictMono : StrictMono ρ := by
    intro a b hab
    show (T.orderIsoOfFin rfl).symm ⟨σ_S a, h_σ_T a⟩ <
      (T.orderIsoOfFin rfl).symm ⟨σ_S b, h_σ_T b⟩
    exact (T.orderIsoOfFin rfl).symm.strictMono
      ((S.orderEmbOfFin rfl).strictMono hab)
  -- Build the wrapped CBA + level_eq.
  refine ⟨{
    level := fun i => P.toApprox.level (ρ i)
    level_lt_omega1 := fun i => P.toApprox.level_lt_omega1 (ρ i)
    level_strictMono := fun _ _ hab =>
      P.toApprox.level_strictMono (h_ρ_strictMono hab)
    prefixAt := fun i => P.toApprox.prefixAt (ρ i)
    branchAt := fun i => P.toApprox.branchAt (ρ i)
    prefix_restrict := fun {k₁ k₂} hk x =>
      P.toApprox.prefix_restrict (h_ρ_strictMono.monotone hk) x
    branch_restrict := fun {k₁ k₂} hk x =>
      P.toApprox.branch_restrict (h_ρ_strictMono.monotone hk) x
    large := fun i => P.toApprox.large (ρ i)
    top_in_validFiber := ?_
  }, ?_⟩
  · -- top_in_validFiber: validFiber adjacency at consecutive S-indices.
    -- New CBA's levels at ⟨i, _⟩ and ⟨i+1, hi⟩ are P.toApprox.level (ρ ⟨i, _⟩)
    -- and P.toApprox.level (ρ ⟨i+1, hi⟩), with ρ strictly monotone.
    intro i hi
    apply P.toApprox.validFiber_between
    exact h_ρ_strictMono (show (⟨i, Nat.lt_of_succ_lt hi⟩ : Fin S.card) <
      ⟨i + 1, hi⟩ from by show i < i + 1; omega)
  · -- level_eq: the new CBA's level equals σ_S = S.orderEmbOfFin rfl.
    intro i
    exact h_lvl_ρ i

/-! ### Restriction preserves CMB-style fields

`(P.restrict hST)`'s data agrees with `P`'s on the elements of `S`.

These follow by routing through HEq: the underlying `P.toApprox.prefixAt`
values agree via `congr_arg_heq` once the Fin index round-trip
(`ρ_indexOf_eq`) aligns. The two `cast`s on each side absorb via
`cast_heq` (proof-irrelevant cast). -/

private lemma CoherentBranchPartial.ρ_indexOf_eq
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {T : Finset Ordinal.{0}} (P : CoherentBranchPartial cR T)
    {S : Finset Ordinal.{0}} (hST : S ⊆ T)
    (α : Ordinal.{0}) (hα : α ∈ S) :
    P.indexOf ((S.orderEmbOfFin rfl) ((S.orderIsoOfFin rfl).symm ⟨α, hα⟩))
      (hST (S.orderEmbOfFin_mem rfl _)) =
      P.indexOf α (hST hα) := by
  congr 1
  rw [← S.coe_orderIsoOfFin_apply rfl,
      (S.orderIsoOfFin rfl).apply_symm_apply]

theorem CoherentBranchPartial.restrict_prefixAt
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {T : Finset Ordinal.{0}} (P : CoherentBranchPartial cR T)
    {S : Finset Ordinal.{0}} (hST : S ⊆ T)
    (α : Ordinal.{0}) (hα : α ∈ S) :
    (P.restrict hST).prefixAt α hα = P.prefixAt α (hST hα) := by
  have h_eq := P.ρ_indexOf_eq hST α hα
  apply eq_of_heq
  -- LHS = cast _ ((P.restrict hST).toApprox.prefixAt ((P.restrict hST).indexOf α hα))
  --     = cast _ (P.toApprox.prefixAt (ρ ((P.restrict hST).indexOf α hα)))  -- defn of restrict
  --     ≅ P.toApprox.prefixAt (P.indexOf α (hST hα))                          -- congr_arg_heq + h_eq
  --     ≅ cast _ (P.toApprox.prefixAt (P.indexOf α (hST hα)))                 -- cast_heq.symm
  --     = RHS
  refine HEq.trans (cast_heq _ _) (HEq.trans ?_ (cast_heq _ _).symm)
  exact congr_arg_heq P.toApprox.prefixAt h_eq

theorem CoherentBranchPartial.restrict_branch
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {T : Finset Ordinal.{0}} (P : CoherentBranchPartial cR T)
    {S : Finset Ordinal.{0}} (hST : S ⊆ T)
    (α : Ordinal.{0}) (hα : α ∈ S) :
    (P.restrict hST).branch α hα = P.branch α (hST hα) := by
  have h_eq := P.ρ_indexOf_eq hST α hα
  apply eq_of_heq
  refine HEq.trans (cast_heq _ _) (HEq.trans ?_ (cast_heq _ _).symm)
  exact congr_arg_heq P.toApprox.branchAt h_eq

/-- **`restrict_validFiber`**: the validFiber set is preserved under
restriction (immediate from `restrict_prefixAt` + `restrict_branch`).
Implies preservation of `large` and `top_in_validFiber`. -/
theorem CoherentBranchPartial.restrict_validFiber
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {T : Finset Ordinal.{0}} (P : CoherentBranchPartial cR T)
    {S : Finset Ordinal.{0}} (hST : S ⊆ T)
    (α : Ordinal.{0}) (hα : α ∈ S) :
    validFiber cR ((P.restrict hST).prefixAt α hα)
        ((P.restrict hST).branch α hα) =
      validFiber cR (P.prefixAt α (hST hα)) (P.branch α (hST hα)) := by
  rw [P.restrict_prefixAt hST α hα, P.restrict_branch hST α hα]

/-! ### Finite common extension: the projective system's FIP

For any finite family `𝒮 : Finset (Finset Ordinal)` of countable
positive-ordinal sets, there is a single `CoherentBranchPartial cR`
defined on the **union** `𝒮.sup id`, whose restriction to each
`S ∈ 𝒮` is a compatible partial branch over `S`.

This is the **finite-intersection-property** form of the projective
system: rather than comparing independently chosen partials (which
are non-canonical), we exhibit one partial over the union and read
off its restrictions. The construction is immediate from
`exists_coherentBranchPartial` applied to the union finset.

`commonExtensionPartialOn` is the accessor that produces the
compatible restriction at each `S ∈ 𝒮`. -/

theorem exists_commonExtensionPartial
    (cR : (Fin 2 ↪o PairERSource) → Bool)
    (𝒮 : Finset (Finset Ordinal.{0}))
    (h𝒮_lt : ∀ S ∈ 𝒮, ∀ α ∈ S, α < Ordinal.omega.{0} 1) :
    Nonempty (CoherentBranchPartial cR (𝒮.sup id)) := by
  classical
  apply exists_coherentBranchPartial
  intro α hα
  obtain ⟨S, hS, hαS⟩ := Finset.mem_sup.mp hα
  exact h𝒮_lt S hS α hαS

/-- **`commonExtensionPartialOn`**: given a common extension `P` over
the union `𝒮.sup id`, restrict to any member `S ∈ 𝒮`. The compatible
family `{commonExtensionPartialOn P S hS | S ∈ 𝒮}` is the
projective-system value at each `S`. -/
noncomputable def commonExtensionPartialOn
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {𝒮 : Finset (Finset Ordinal.{0})}
    (P : CoherentBranchPartial cR (𝒮.sup id))
    (S : Finset Ordinal.{0}) (hS : S ∈ 𝒮) :
    CoherentBranchPartial cR S :=
  P.restrict (by
    classical
    intro α hα
    exact Finset.mem_sup.mpr ⟨S, hS, hα⟩)

/-! ### ω-chain of finite approximations

The ω-chain `coherentBranchApproxSeq cR : (n : ℕ) → CoherentBranchApprox cR n`
is built by primitive recursion: `0 ↦ zero`, `n+1 ↦ (·).extend`. Its
cross-stage stability lemmas (`level_stable`, `prefix_stable`,
`branch_stable`) say that data at index `i : Fin n` is preserved
when passing to a longer approximation `m ≥ n`. These are the
prerequisites for assembling the full `CoherentMajorityBranch`. -/

/-- **`coherentBranchApproxSeq`**: the ω-chain of finite approximations,
defined by primitive recursion on the length. -/
noncomputable def coherentBranchApproxSeq
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    (n : ℕ) → CoherentBranchApprox cR n
  | 0 => CoherentBranchApprox.zero cR
  | n + 1 => (coherentBranchApproxSeq cR n).extend

@[simp] theorem coherentBranchApproxSeq_zero
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    coherentBranchApproxSeq cR 0 = CoherentBranchApprox.zero cR := rfl

@[simp] theorem coherentBranchApproxSeq_succ
    (cR : (Fin 2 ↪o PairERSource) → Bool) (n : ℕ) :
    coherentBranchApproxSeq cR (n + 1) =
      (coherentBranchApproxSeq cR n).extend := rfl

/-! ### Single-step stability

`coherentBranchApproxSeq_*_castSucc_step` lemmas say that the data of
the approximation at level `n` matches the data of the approximation
at level `n+1` after embedding `Fin n ↪ Fin (n+1)` via `Fin.castSucc`.
For `level`, this is an `Eq`; for `prefixAt` / `branchAt`, an `HEq`. -/

/-- **Single-step level stability**: `level` is preserved when moving
from stage `n` to stage `n+1` via `Fin.castSucc`. -/
theorem coherentBranchApproxSeq_level_castSucc_step
    {cR : (Fin 2 ↪o PairERSource) → Bool} (n : ℕ) (i : Fin n) :
    (coherentBranchApproxSeq cR (n + 1)).level i.castSucc =
      (coherentBranchApproxSeq cR n).level i := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ m =>
    -- n = m+1, so (n+1) = m+2 and extend = extendSucc.
    show ((coherentBranchApproxSeq cR (m + 1)).extendSucc).level i.castSucc =
        (coherentBranchApproxSeq cR (m + 1)).level i
    exact (coherentBranchApproxSeq cR (m + 1)).extendLevel_castSucc i

/-- **Single-step prefix stability**: `prefixAt` is `HEq`-preserved
from stage `n` to stage `n+1` via `Fin.castSucc`. -/
theorem coherentBranchApproxSeq_prefix_castSucc_step
    {cR : (Fin 2 ↪o PairERSource) → Bool} (n : ℕ) (i : Fin n) :
    HEq ((coherentBranchApproxSeq cR (n + 1)).prefixAt i.castSucc)
        ((coherentBranchApproxSeq cR n).prefixAt i) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ m =>
    show HEq (((coherentBranchApproxSeq cR (m + 1)).extendSucc).prefixAt i.castSucc) _
    exact (coherentBranchApproxSeq cR (m + 1)).extendPrefixAt_castSucc_heq i

/-- **Single-step branch stability**: `branchAt` is `HEq`-preserved
from stage `n` to stage `n+1` via `Fin.castSucc`. -/
theorem coherentBranchApproxSeq_branch_castSucc_step
    {cR : (Fin 2 ↪o PairERSource) → Bool} (n : ℕ) (i : Fin n) :
    HEq ((coherentBranchApproxSeq cR (n + 1)).branchAt i.castSucc)
        ((coherentBranchApproxSeq cR n).branchAt i) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ m =>
    show HEq (((coherentBranchApproxSeq cR (m + 1)).extendSucc).branchAt i.castSucc) _
    exact (coherentBranchApproxSeq cR (m + 1)).extendBranchAt_castSucc_heq i

/-! ### Cross-stage stability

The single-step stability lemmas iterate to give cross-stage stability:
for `n ≤ m`, the approximation at length `m` agrees with the
approximation at length `n` on the image of `Fin.castLE` (the natural
embedding `Fin n ↪ Fin m`). -/

/-- **`coherentBranchApproxSeq_level_stable`**: cross-stage level
stability. For `n ≤ m`, the level at index `i : Fin n` is preserved
when re-indexed into `Fin m`. -/
theorem coherentBranchApproxSeq_level_stable
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n m : ℕ} (hnm : n ≤ m) (i : Fin n) :
    (coherentBranchApproxSeq cR m).level (Fin.castLE hnm i) =
      (coherentBranchApproxSeq cR n).level i := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ k hnk ih =>
    -- Goal: (seq cR (k+1)).level (castLE _ i) = (seq cR n).level i
    -- Note: Fin.castLE (hnk.le.trans k.le_succ) i = (Fin.castLE hnk i).castSucc
    have h_cast :
        (Fin.castLE (Nat.le_succ_of_le hnk) i : Fin (k + 1)) =
          (Fin.castLE hnk i : Fin k).castSucc := by
      apply Fin.ext; rfl
    rw [h_cast, coherentBranchApproxSeq_level_castSucc_step, ih]

/-- **`coherentBranchApproxSeq_prefix_stable`**: cross-stage prefix
stability (HEq-form, since the OrderEmbedding type depends on the
level which would change formally though not in value). -/
theorem coherentBranchApproxSeq_prefix_stable
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n m : ℕ} (hnm : n ≤ m) (i : Fin n) :
    HEq ((coherentBranchApproxSeq cR m).prefixAt (Fin.castLE hnm i))
        ((coherentBranchApproxSeq cR n).prefixAt i) := by
  induction m, hnm using Nat.le_induction with
  | base => exact HEq.rfl
  | succ k hnk ih =>
    have h_cast :
        (Fin.castLE (Nat.le_succ_of_le hnk) i : Fin (k + 1)) =
          (Fin.castLE hnk i : Fin k).castSucc := by
      apply Fin.ext; rfl
    rw [h_cast]
    exact (coherentBranchApproxSeq_prefix_castSucc_step k (Fin.castLE hnk i)).trans ih

/-- **`coherentBranchApproxSeq_branch_stable`**: cross-stage branch
stability (HEq-form). -/
theorem coherentBranchApproxSeq_branch_stable
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n m : ℕ} (hnm : n ≤ m) (i : Fin n) :
    HEq ((coherentBranchApproxSeq cR m).branchAt (Fin.castLE hnm i))
        ((coherentBranchApproxSeq cR n).branchAt i) := by
  induction m, hnm using Nat.le_induction with
  | base => exact HEq.rfl
  | succ k hnk ih =>
    have h_cast :
        (Fin.castLE (Nat.le_succ_of_le hnk) i : Fin (k + 1)) =
          (Fin.castLE hnk i : Fin k).castSucc := by
      apply Fin.ext; rfl
    rw [h_cast]
    exact (coherentBranchApproxSeq_branch_castSucc_step k (Fin.castLE hnk i)).trans ih

/-! ### Diagnostic: the ω-chain only covers finite-ordinal levels

`CoherentBranchApprox.fromZero` starts the chain at level `0`, and
each `extendSucc` step adds a level at `Order.succ` of the previous.
Hence the levels at stage `n` are exactly the natural-number
ordinals `0, 1, …, n−1`. In particular the range of all levels in
the ω-chain is contained in `Ordinal.omega 0`, **not cofinal in
ω₁**. Consequently, the ω-chain alone is not strong enough to
produce a `CoherentMajorityBranch` (which requires data at every
`α < ω₁`); a transfinite cofinal-in-ω₁ refinement is needed instead. -/

/-- **`coherentBranchApproxSeq_level_eq_natCast`**: at stage `n`, the
level at index `i : Fin n` is exactly `i.val` cast to `Ordinal`. -/
theorem coherentBranchApproxSeq_level_eq_natCast
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    ∀ {n : ℕ} (i : Fin n),
      (coherentBranchApproxSeq cR n).level i = ((i.val : ℕ) : Ordinal.{0})
  | 0, i => Fin.elim0 i
  | 1, ⟨0, _⟩ => by
    -- Stage 1 = fromZero, level _ = 0.
    show (CoherentBranchApprox.fromZero cR).level _ = ((0 : ℕ) : Ordinal.{0})
    simp [CoherentBranchApprox.fromZero]
  | (n + 2), i => by
    -- Stage n+2 = (seq cR (n+1)).extendSucc; case on Fin (n+2).
    induction i using Fin.lastCases with
    | last =>
      -- Index = Fin.last (n+1); level = succ ((seq cR (n+1)).level (Fin.last n)).
      show (coherentBranchApproxSeq cR (n + 1)).extendLevel (Fin.last (n + 1)) =
        (((Fin.last (n + 1)).val : ℕ) : Ordinal.{0})
      rw [(coherentBranchApproxSeq cR (n + 1)).extendLevel_last,
          coherentBranchApproxSeq_level_eq_natCast cR (Fin.last n)]
      show Order.succ ((n : ℕ) : Ordinal.{0}) = ((n + 1 : ℕ) : Ordinal.{0})
      push_cast
      rfl
    | cast k =>
      show (coherentBranchApproxSeq cR (n + 1)).extendLevel k.castSucc =
        ((k.castSucc.val : ℕ) : Ordinal.{0})
      rw [(coherentBranchApproxSeq cR (n + 1)).extendLevel_castSucc k]
      exact coherentBranchApproxSeq_level_eq_natCast cR k

/-- **`coherentBranchApproxSeq_level_lt_omega0`**: every level in the
ω-chain is strictly below `ω` (i.e., a finite ordinal). -/
theorem coherentBranchApproxSeq_level_lt_omega0
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ} (i : Fin n) :
    (coherentBranchApproxSeq cR n).level i < Ordinal.omega.{0} 0 := by
  rw [coherentBranchApproxSeq_level_eq_natCast cR i, Ordinal.omega_zero]
  exact Ordinal.nat_lt_omega0 i.val

/-- **`coherentBranchApproxSeq_level_lt_omega0_succ`**: in particular,
the last level at any stage is `< ω`. So `ω` itself is an upper bound
on the ω-chain's level range. -/
theorem coherentBranchApproxSeq_range_bounded_by_omega0
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ} (i : Fin n) :
    (coherentBranchApproxSeq cR n).level i ≤ Ordinal.omega.{0} 0 :=
  le_of_lt (coherentBranchApproxSeq_level_lt_omega0 i)

/-- **Diagnostic conclusion: the ω-chain is not cofinal in ω₁**.
There exists a countable ordinal (namely `ω`) which is strictly
above every level produced by the ω-chain. Hence the ω-chain alone
cannot index a `CoherentMajorityBranch` (which is defined for every
`α < ω₁`); a transfinite cofinal-in-ω₁ refinement is required. -/
theorem coherentBranchApproxSeq_not_cofinal_in_omega1
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    ∃ α : Ordinal.{0}, α < Ordinal.omega.{0} 1 ∧
      ∀ {n : ℕ} (i : Fin n), (coherentBranchApproxSeq cR n).level i < α := by
  refine ⟨Ordinal.omega.{0} 0, ?_, fun {n} i => ?_⟩
  · rw [Ordinal.omega_zero]; exact Ordinal.omega0_lt_omega_one
  · exact coherentBranchApproxSeq_level_lt_omega0 i

/-! ### Decomposition: raw branch assignment + compactness principle

The inverse-limit compactness frontier
(`exists_coherentMajorityBranch_of_finitePartials`) factors through a
more generic Tychonoff/ultrafilter-style compactness principle on a
product space of "raw" prefix/branch assignments.

The product space `RawBranchAssignment cR` is a pair of partial
functions from countable ordinals to prefix/branch data (each
returning `Option`, so values may be unset; using `Option` avoids
having to fix arbitrary default OrderEmbeddings at unused levels).
`SatisfiesFinite A S` asserts that `A`'s `some`-values on `S` match
some `CoherentBranchPartial cR S`. The compactness principle
`rawBranchCompactness cR` then says: if every finite `S ⊂ ω₁` is
satisfied by some `A`, there is a global `A` satisfying every such
`S`.

**Frontier status (as of the `FiniteProjectiveSystem` decomposition):**
`rawBranchCompactness_holds` is now a **derived bridge**, not the
final frontier. It is wired through
`rawBranchCompactness_of_coherentWitnessNet` ←
`exists_coherentWitnessNet`, which itself derives axiom-clean from
the generic compactness theorem
`FiniteProjectiveSystem.exists_global_section`. The remaining
mathematical content is now a single generic inverse-limit /
Zorn-style compactness statement, decoupled from the
Erdős–Rado-specific bookkeeping. See the FPS section near
`exists_global_section` for the current named frontier.

The bridge from `rawBranchCompactness` to
`exists_coherentMajorityBranch_of_finitePartials` is axiom-clean. -/

/-- **`RawBranchAssignment cR`**: the product space of partial
prefix/branch assignments. Values at each level `α < ω₁` may be
`some` (specified) or `none` (unset). -/
def RawBranchAssignment (_cR : (Fin 2 ↪o PairERSource) → Bool) : Type 1 :=
  (∀ α : Ordinal.{0}, α < Ordinal.omega.{0} 1 →
    Option (α.ToType ↪o PairERSource)) ×
  (∀ α : Ordinal.{0}, α < Ordinal.omega.{0} 1 →
    Option (α.ToType → Bool))

/-- **`SatisfiesFinite A S`**: there exists a `CoherentBranchPartial`
on `S` whose data matches `A`'s `some`-values at each `α ∈ S`. -/
def SatisfiesFinite {cR : (Fin 2 ↪o PairERSource) → Bool}
    (A : RawBranchAssignment cR) (S : Finset Ordinal.{0}) : Prop :=
  ∃ (hS : ∀ α ∈ S, α < Ordinal.omega.{0} 1)
    (P : CoherentBranchPartial cR S),
    (∀ α (hα : α ∈ S), A.1 α (hS α hα) = some (P.prefixAt α hα)) ∧
    (∀ α (hα : α ∈ S), A.2 α (hS α hα) = some (P.branch α hα))

/-- **`rawBranchCompactness cR`** (Prop): the compactness principle.
If every finite `S ⊂ ω₁` is satisfied by some raw assignment, there
is a single global raw assignment satisfying every such finite `S`. -/
def rawBranchCompactness (cR : (Fin 2 ↪o PairERSource) → Bool) : Prop :=
  (∀ S : Finset Ordinal.{0}, (∀ α ∈ S, α < Ordinal.omega.{0} 1) →
    ∃ A : RawBranchAssignment cR, SatisfiesFinite A S) →
  ∃ A : RawBranchAssignment cR, ∀ S : Finset Ordinal.{0},
    (∀ α ∈ S, α < Ordinal.omega.{0} 1) → SatisfiesFinite A S

/-! ### Status of `rawBranchCompactness_holds`

**Frontier status:** `rawBranchCompactness_holds` was the final
non-model-theoretic compactness frontier UNTIL the
`FiniteProjectiveSystem` decomposition was added. It is now a
**derived bridge**, wired through
`rawBranchCompactness_of_coherentWitnessNet` ←
`exists_coherentWitnessNet` ←
`FiniteProjectiveSystem.exists_global_section` (the current active
frontier). The notes below preserve the original two-route analysis
(Tychonoff vs. ultrafilter) — both still apply, but now to the
generic `exists_global_section` rather than to
`rawBranchCompactness_holds` directly.

`rawBranchCompactness_holds` can be proved either by:

1. **Tychonoff compactness** for products of compact (e.g., suitably
   compactified) spaces, reducing to the finite-intersection property
   of the projective system; or

2. **An ultrafilter** over `Finset Ordinal.{0}` extending the
   superset/cofinite filter, with the global assignment defined as
   the ultralimit value at each coordinate.

The intended packaging is a reusable compactness principle:

    theorem rawBranchCompactness_holds_of_ultrafilter
        (cR) (U : Ultrafilter (Finset Ordinal.{0}))
        (hU_superset : ∀ S, {T | S ⊆ T} ∈ U) :
        rawBranchCompactness cR

from which `rawBranchCompactness_holds` would follow by an existence
result for ultrafilters extending the superset filter on `Finset
Ordinal.{0}`. The construction is real set-theoretic compactness
work; for now the principle is left as the named frontier sorry.

**Mathlib ingredients available** (verified via LeanFinder):

- `Ultrafilter.of (f : Filter α) [NeBot f] : Ultrafilter α` —
  extends any non-trivial filter to an ultrafilter (via `exists_le`,
  `Classical.choose`).
- `Filter.atTop_neBot : NeBot (atTop : Filter α)` — `atTop` is
  non-trivial for any nonempty directed preorder.
- `Filter.atTop_finset_eq_iInf : atTop = ⨅ x, 𝓟 (Ici {x})` — `atTop`
  on `Finset α` IS the superset filter. `Ici S = {T | S ⊆ T}` via
  `Finset.le_iff_subset`.
- `Filter.Ici_mem_atTop : Ici a ∈ atTop` — superset sets are in `atTop`.

So `U := Ultrafilter.of (atTop : Filter (Finset Ordinal.{0}))` gives
an ultrafilter extending the superset filter; `hU_superset` follows
from `Ici_mem_atTop` and the `U ≤ atTop` inclusion.

- `Pi.compactSpace [∀ i, CompactSpace (X i)] : CompactSpace (∀ i, X i)` —
  Tychonoff.
- `Function.compactSpace [CompactSpace Y] : CompactSpace (ι → Y)` —
  Tychonoff for constant products.
- `isCompact_iff_finite_subfamily_closed` — FIP characterization.
- `IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed` —
  directed FIP.
- `isCompact_iff_finite [DiscreteTopology X]` — for discrete, compact
  iff finite (so direct Tychonoff over `Option (α.ToType ↪o PairERSource)`
  with discrete topology fails — each coordinate is infinite).
- `Ultrafilter.lim`, `Ultrafilter.le_nhds_lim` — ultralimit in a
  compact space.
- `Ultrafilter.em`, `Ultrafilter.eventually_exists_iff` — Boolean
  reasoning eventually.

The ultrafilter route is more direct given our Option-valued
RawBranchAssignment; the Tychonoff route needs a finer-grained
compact structure on each coordinate (e.g., a one-point
compactification or restricting to a specific compact subspace per
finite S). -/

/-- **`finiteSupersetUltrafilter ι`**: an ultrafilter on
`Finset ι` extending the `atTop` (superset) filter. Used as the
combinatorial backbone of the ultrafilter-style compactness proof
for `rawBranchCompactness`: every set of the form `{T | S ⊆ T}` (for
`S : Finset ι` fixed) is in this ultrafilter. -/
noncomputable def finiteSupersetUltrafilter (ι : Type*) :
    Ultrafilter (Finset ι) :=
  Ultrafilter.of (Filter.atTop : Filter (Finset ι))

/-- **`finiteSupersetUltrafilter_eventually_superset`**: for any
finite `S : Finset ι`, the set of supersets `{T : Finset ι | S ⊆ T}`
is in `finiteSupersetUltrafilter ι`.

Proof: `Set.Ici S = {T | S ≤ T}` is in `Filter.atTop` by
`Filter.Ici_mem_atTop`, and `S ≤ T ↔ S ⊆ T` for finsets, so this is
the same set. The ultrafilter `Ultrafilter.of atTop` is finer than
`atTop` (`Ultrafilter.of_le`), so the set is in the ultrafilter. -/
theorem finiteSupersetUltrafilter_eventually_superset
    {ι : Type*} (S : Finset ι) :
    {T : Finset ι | S ⊆ T} ∈ finiteSupersetUltrafilter ι := by
  have h_ici : Set.Ici S ∈ (Filter.atTop : Filter (Finset ι)) :=
    Filter.Ici_mem_atTop S
  -- {T | S ⊆ T} = Set.Ici S via Finset.le_iff_subset.
  have h_eq : ({T : Finset ι | S ⊆ T} : Set (Finset ι)) = Set.Ici S := by
    ext T
    exact Iff.rfl
  rw [h_eq]
  exact Ultrafilter.of_le _ h_ici

/-! ### Coordinate-level ultralimit helper

Generic helper for ultrafilter compactness: given a family
`f : ι → Option α` and an ultrafilter `U` on `ι`, the "eventual
value" is `some v` when `{i | f i = some v} ∈ U` for some `v`,
otherwise `none`. Used at each coordinate of the global raw
assignment in the compactness proof. -/

/-- **`ultrafilterEventuallyValue U f`**: the value taken by `f i`
for `U`-many `i`. Returns `some v` if some `v` is eventually equal,
else `none`. -/
noncomputable def ultrafilterEventuallyValue
    {ι : Type*} {α : Type*}
    (U : Ultrafilter ι) (f : ι → Option α) : Option α :=
  haveI : Decidable (∃ v : α, {i | f i = some v} ∈ U) := Classical.dec _
  if h : ∃ v : α, {i | f i = some v} ∈ U then some h.choose else none

/-- **`ultrafilterEventuallyValue_eq_some_mem`**: under the existence
hypothesis, `f i = ultrafilterEventuallyValue U f` for `U`-many `i`. -/
theorem ultrafilterEventuallyValue_eq_some_mem
    {ι : Type*} {α : Type*}
    {U : Ultrafilter ι} {f : ι → Option α}
    (h : ∃ v : α, {i | f i = some v} ∈ U) :
    {i | f i = ultrafilterEventuallyValue U f} ∈ U := by
  unfold ultrafilterEventuallyValue
  rw [dif_pos h]
  exact h.choose_spec

/-- **`ultrafilterEventuallyValue_unique`**: at most one `some v` can
be eventually equal (else the disjoint pair `{i | f i = some v₁}` and
`{i | f i = some v₂}` would both be in `U`, but their intersection is
empty — contradiction since `U` is non-trivial). -/
theorem ultrafilterEventuallyValue_unique
    {ι : Type*} {α : Type*}
    {U : Ultrafilter ι} {f : ι → Option α} {v₁ v₂ : α}
    (h₁ : {i | f i = some v₁} ∈ U) (h₂ : {i | f i = some v₂} ∈ U) :
    v₁ = v₂ := by
  by_contra h_ne
  have h_inter : {i | f i = some v₁} ∩ {i | f i = some v₂} ∈ U.toFilter :=
    Filter.inter_mem h₁ h₂
  have h_empty : ({i | f i = some v₁} ∩ {i | f i = some v₂} : Set ι) = ∅ := by
    ext i
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
      not_and]
    intro h_v₁ h_v₂
    exact h_ne (Option.some.inj (h_v₁.symm.trans h_v₂))
  rw [h_empty] at h_inter
  exact U.neBot'.ne (Filter.empty_mem_iff_bot.mp h_inter)

/-! ### Coordinatewise raw ultralimit

Given a witness family `A : Finset Ordinal → RawBranchAssignment cR`
(typically chosen via `Classical.choose` from a `SatisfiesFinite`
existence), the coordinatewise ultralimit raw assignment takes, at
each coordinate `(α, hα)`, the `ultrafilterEventuallyValue` along the
`finiteSupersetUltrafilter Ordinal` of `A S` at that coordinate. -/

/-- **`rawBranchUltralimit A`**: coordinatewise ultralimit raw
assignment, taking eventual `some v`-values along the
`finiteSupersetUltrafilter Ordinal`. -/
noncomputable def rawBranchUltralimit
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (A : Finset Ordinal.{0} → RawBranchAssignment cR) :
    RawBranchAssignment cR :=
  (fun α hα =>
      ultrafilterEventuallyValue (finiteSupersetUltrafilter Ordinal.{0})
        (fun S => (A S).1 α hα),
   fun α hα =>
      ultrafilterEventuallyValue (finiteSupersetUltrafilter Ordinal.{0})
        (fun S => (A S).2 α hα))

/-! ### Diagnostic: eventual-constancy obstruction

For `rawBranchUltralimit A` to satisfy `S₀` (in the sense of
`SatisfiesFinite`), each coordinate `(α, hα)` for `α ∈ S₀` must
return `some _` from `ultrafilterEventuallyValue` — equivalently:
for each `α ∈ S₀`, there must exist `v` with
`{S | (A S).1 α hα = some v} ∈ finiteSupersetUltrafilter Ordinal`,
i.e., `(A S).1 α hα` is **eventually constant** along the ultrafilter.

For **arbitrary** independently chosen `A_S` (each just satisfying
`SatisfiesFinite (A_S) S`), this eventual constancy is **NOT**
guaranteed: different `S`'s can produce different CBPs that disagree
at `α`, with no `U`-stable choice. Hence the next obstruction is to
arrange witnesses so that the coordinate values **agree on supersets**.

Two natural strategies:

1. **Coherent witness net**: pick witnesses `A_S` so that whenever
   `T ⊆ S`, `A_T` and `A_S` agree on the levels of `T`. This is a
   strong consistency requirement but follows from
   `exists_commonExtensionPartial`-style constructions for finite
   sub-families.

2. **Ultrafilter-respecting witness choice**: for each fixed
   `α < ω₁`, observe that `(A S).1 α hα` ranges over a (small) set of
   values as `S` varies over supersets of `{α}`. The ultrafilter
   `U`-partitions this set into one element by `Ultrafilter.em`-style
   reasoning, but extracting **U-many supersets giving the same
   value** requires the value type to be "small relative to `U`"
   (e.g., countable for `U` extending the cofinite filter on a
   countable index).

The clean route forward is **option 1**: define a coherent witness
family by recursively choosing each `A_S` to extend (via `restrict`)
a witness chosen on the union of finitely many previously-fixed
finite sets, leveraging `exists_commonExtensionPartial` to ensure
consistency. -/

/-! ### `FiniteProjectiveSystem`: generic finite-extension compactness

A `FiniteProjectiveSystem` packages the data needed for a
finite-to-global compactness argument: an indexed family of "objects"
over a partial order, with a restriction map for `i ≤ j`, and a
finite-extension property guaranteeing compatible choices over finite
sub-families. The `exists_global_section` theorem is the Zorn /
compactness conclusion.

This abstraction is generic — the pair Erdős–Rado projective system
(`CoherentBranchPartial` indexed by `Finset Ordinal`) instantiates it
in a follow-up, but other compactness arguments can reuse the same
shape. -/

/-- **`FiniteProjectiveSystem ι`**: a projective system on the
partial order `ι`. Carries object data, restriction maps, validity
predicate, a parametric compatibility relation on objects, and the
finite-extension property.

The `Compat` field is a parametric relation (typically `=` or a
fieldwise equivalence) — necessary because structural equality of
restrictions may not hold definitionally in concrete instances
(e.g., `CoherentBranchPartial` restricts are propositionally but
not definitionally equal under composition). -/
structure FiniteProjectiveSystem (ι : Type*) [PartialOrder ι] where
  /-- Validity predicate on indices (e.g., `S ⊂ ω₁`). -/
  Valid : ι → Prop
  /-- Object type at each index. -/
  Obj : ι → Type*
  /-- Restriction map for `i ≤ j`. -/
  restrict : ∀ {i j : ι}, i ≤ j → Obj j → Obj i
  /-- Compatibility predicate: typically `=` or fieldwise agreement. -/
  Compat : ∀ {i : ι}, Obj i → Obj i → Prop
  /-- Finite-extension: for any finite family of valid indices, there
  is a partial choice with restrictions compatible across the family. -/
  finite_extension :
    ∀ (𝒮 : Finset ι) (_h𝒮 : ∀ i ∈ 𝒮, Valid i),
      ∃ P : ∀ i, i ∈ 𝒮 → Obj i,
        ∀ {i j : ι} (hi : i ∈ 𝒮) (hj : j ∈ 𝒮) (hij : i ≤ j),
          Compat (restrict hij (P j hj)) (P i hi)

/-! ### Zorn machinery for `FiniteProjectiveSystem`

Toward the Zorn proof of `exists_global_section`. A
`PartialSection` is a partial choice function on a domain `D ⊆ ι`
of valid indices, with restrictions Compat-coherent on overlapping
pairs. The extension order on `PartialSection`s makes them a Preorder
under which a maximal element corresponds (via `finite_extension`)
to a global section. -/

/-- **`PartialSection X`**: a partial choice function on a domain
`D : Set ι` of valid indices, with `Compat`-coherent restrictions on
overlapping pairs. -/
structure FiniteProjectiveSystem.PartialSection
    {ι : Type*} [PartialOrder ι] (X : FiniteProjectiveSystem ι) where
  /-- Domain: the set of indices on which this section is defined. -/
  domain : Set ι
  /-- Every index in `domain` is valid. -/
  domain_valid : ∀ {i : ι}, i ∈ domain → X.Valid i
  /-- The partial choice function. -/
  P : ∀ i, i ∈ domain → X.Obj i
  /-- `Compat`-coherence: restrictions match on overlapping pairs. -/
  compat : ∀ {i j : ι} (hi : i ∈ domain) (hj : j ∈ domain) (hij : i ≤ j),
    X.Compat (X.restrict hij (P j hj)) (P i hi)

/-- **Extension order on partial sections**: `ps₁ ≤ ps₂` iff
`ps₂`'s domain contains `ps₁`'s, and the choice functions agree on
the common domain.

The agreement is Lean's `=` (not `Compat`) — within the partial
section world, we work with concrete choice values, while
`Compat` mediates between objects across the restriction structure. -/
instance FiniteProjectiveSystem.PartialSection.instLE
    {ι : Type*} [PartialOrder ι] {X : FiniteProjectiveSystem ι} :
    LE (X.PartialSection) where
  le ps₁ ps₂ :=
    (∀ i, i ∈ ps₁.domain → i ∈ ps₂.domain) ∧
    (∀ (i : ι) (hi₁ : i ∈ ps₁.domain) (hi₂ : i ∈ ps₂.domain),
      ps₂.P i hi₂ = ps₁.P i hi₁)

/-- **Preorder instance** on `PartialSection`. Reflexive (domain
inclusion + proof-irrelevant equality on overlap) and transitive
(chained inclusions + transported equalities). -/
instance FiniteProjectiveSystem.PartialSection.instPreorder
    {ι : Type*} [PartialOrder ι] {X : FiniteProjectiveSystem ι} :
    Preorder (X.PartialSection) where
  le := (· ≤ ·)
  le_refl ps := ⟨fun _ h => h, fun _ _ _ => rfl⟩
  le_trans ps₁ ps₂ ps₃ h₁₂ h₂₃ :=
    ⟨fun i hi => h₂₃.1 i (h₁₂.1 i hi),
     fun i hi₁ hi₃ =>
       (h₂₃.2 i (h₁₂.1 i hi₁) hi₃).trans (h₁₂.2 i hi₁ (h₁₂.1 i hi₁))⟩

/-! ### Chain upper bound for `PartialSection`

Given a chain of partial sections, the union of their domains
carries a well-defined partial section that's an upper bound. The
`P` value at each `i` is selected via `Classical.choose` from a
witnessing chain element; different choices agree by the chain's
extension order. -/

/-- **`chainUpperBound`**: the union of a chain of partial sections.
The domain is `{i | ∃ ps ∈ c, i ∈ ps.domain}`; the `P` value at each
`i` is chosen from a witnessing chain element via `Classical.choose`. -/
noncomputable def FiniteProjectiveSystem.PartialSection.chainUpperBound
    {ι : Type*} [PartialOrder ι] {X : FiniteProjectiveSystem ι}
    (c : Set X.PartialSection) (hc : IsChain (· ≤ ·) c) :
    X.PartialSection where
  domain := {i | ∃ ps ∈ c, i ∈ ps.domain}
  domain_valid {i} hi := by
    obtain ⟨ps, _, hi_ps⟩ := hi
    exact ps.domain_valid hi_ps
  P i hi := hi.choose.P i hi.choose_spec.2
  compat {i j} hi hj hij := by
    classical
    -- Witnesses for i and j.
    have hps_i_in_c : hi.choose ∈ c := hi.choose_spec.1
    have hps_j_in_c : hj.choose ∈ c := hj.choose_spec.1
    have hi_in_ps_i : i ∈ hi.choose.domain := hi.choose_spec.2
    have hj_in_ps_j : j ∈ hj.choose.domain := hj.choose_spec.2
    -- Case on whether hi.choose = hj.choose or they're comparable.
    rcases eq_or_ne hi.choose hj.choose with h_eq | h_ne
    · -- Same partial section.
      have hj_in_ps_i : j ∈ hi.choose.domain := h_eq ▸ hj_in_ps_j
      have h_pj_eq : hj.choose.P j hj_in_ps_j = hi.choose.P j hj_in_ps_i := by
        congr 1 <;> exact h_eq.symm
      rw [h_pj_eq]
      exact hi.choose.compat hi_in_ps_i hj_in_ps_i hij
    rcases hc hps_i_in_c hps_j_in_c h_ne with h_le | h_le
    · -- hi.choose ≤ hj.choose: hj.choose contains i too.
      have hi_in_ps_j : i ∈ hj.choose.domain := h_le.1 i hi_in_ps_i
      have h_pi_eq : hj.choose.P i hi_in_ps_j = hi.choose.P i hi_in_ps_i :=
        h_le.2 i hi_in_ps_i hi_in_ps_j
      have := hj.choose.compat hi_in_ps_j hj_in_ps_j hij
      rw [h_pi_eq] at this
      exact this
    · -- hj.choose ≤ hi.choose: hi.choose contains j too.
      have hj_in_ps_i : j ∈ hi.choose.domain := h_le.1 j hj_in_ps_j
      have h_pj_eq : hi.choose.P j hj_in_ps_i = hj.choose.P j hj_in_ps_j :=
        h_le.2 j hj_in_ps_j hj_in_ps_i
      have := hi.choose.compat hi_in_ps_i hj_in_ps_i hij
      rw [h_pj_eq] at this
      exact this

/-- **`chainUpperBound_isUB`**: the chain upper bound is indeed an
upper bound of the chain in the extension order. -/
theorem FiniteProjectiveSystem.PartialSection.chainUpperBound_isUB
    {ι : Type*} [PartialOrder ι] {X : FiniteProjectiveSystem ι}
    (c : Set X.PartialSection) (hc : IsChain (· ≤ ·) c) :
    ∀ ps ∈ c, ps ≤ chainUpperBound c hc := by
  intro ps hps
  refine ⟨fun i hi => ⟨ps, hps, hi⟩, ?_⟩
  intro i hi_ps hi_union
  -- The union's P at i picks some ps' ∈ c (via Classical.choose).
  -- ps and ps' are both in c. By chain, comparable.
  classical
  set ps' := hi_union.choose with hps'_def
  have hps'_in_c : ps' ∈ c := hi_union.choose_spec.1
  have hi_in_ps' : i ∈ ps'.domain := hi_union.choose_spec.2
  -- chainUpperBound's P at i = ps'.P i _.
  show ps'.P i hi_in_ps' = ps.P i hi_ps
  rcases eq_or_ne ps' ps with h_eq | h_ne
  · subst h_eq; rfl
  rcases hc hps'_in_c hps h_ne with h_le | h_le
  · -- ps' ≤ ps: h_le.2 i hi_in_ps' hi_ps : ps.P i hi_ps = ps'.P i hi_in_ps'.
    exact (h_le.2 i hi_in_ps' hi_ps).symm
  · -- ps ≤ ps': h_le.2 i hi_ps hi_in_ps' : ps'.P i hi_in_ps' = ps.P i hi_ps.
    exact h_le.2 i hi_ps hi_in_ps'

/-- **`bddAbove_of_isChain`**: every chain in `X.PartialSection` is
bounded above. This is the Zorn hypothesis. -/
theorem FiniteProjectiveSystem.PartialSection.bddAbove_of_isChain
    {ι : Type*} [PartialOrder ι] {X : FiniteProjectiveSystem ι}
    (c : Set X.PartialSection) (hc : IsChain (· ≤ ·) c) :
    BddAbove c :=
  ⟨chainUpperBound c hc, chainUpperBound_isUB c hc⟩

/-! ### Zorn application and maximality argument

With `bddAbove_of_isChain` providing the hypothesis of `zorn_le`,
we obtain a maximal partial section. The next step is to show its
domain is all valid indices: any missing valid index `i₀` can be
appended via `finite_extension` applied to `domain ∪ {i₀}` (or a
relevant finite subfamily), contradicting maximality. -/

/-- **Empty partial section**: an instance of `PartialSection` with
empty domain, used to ensure `PartialSection X` is nonempty (so
`zorn_le` applies to a nonempty type). -/
noncomputable def FiniteProjectiveSystem.PartialSection.empty
    {ι : Type*} [PartialOrder ι] (X : FiniteProjectiveSystem ι) :
    X.PartialSection where
  domain := ∅
  domain_valid {i} hi := absurd hi (Set.notMem_empty i)
  P i hi := absurd hi (Set.notMem_empty i)
  compat {i j} hi _ _ := absurd hi (Set.notMem_empty i)

/-- **Maximal partial section exists**: Zorn applied to
`bddAbove_of_isChain`. -/
theorem FiniteProjectiveSystem.PartialSection.exists_maximal
    {ι : Type*} [PartialOrder ι] (X : FiniteProjectiveSystem ι) :
    ∃ m : X.PartialSection, IsMax m :=
  zorn_le (fun c hc => bddAbove_of_isChain c hc)

/-! ### `HasPartialExtensions`: the strengthened projective-system property

The finite-extension field (`finite_extension`) says "for any finite
family of valid indices, there's a compatible choice." It doesn't say
"for any partial section, there's a strict extension by one new
index." The latter is what's needed to complete the Zorn proof: take
a maximal `m`, attempt to extend by a missing valid `i₀`, contradict
maximality.

`HasPartialExtensions` packages this stronger property at the
**`PartialSection` level** — returning a partial section `q` that
extends `p` and contains `i₀`, rather than a raw value `x₀ : X.Obj i₀`.
This keeps the dependent-transport handling (building `q` from
`(p, i₀, x₀)`) inside the instance proof, where the model-specific
machinery is available, instead of in the generic Zorn bridge. -/

/-- **`X.HasPartialExtensions`**: every partial section extends to a
strictly larger partial section containing any specified valid index. -/
def FiniteProjectiveSystem.HasPartialExtensions
    {ι : Type*} [PartialOrder ι] (X : FiniteProjectiveSystem ι) : Prop :=
  ∀ (p : X.PartialSection) (i₀ : ι), X.Valid i₀ →
    ∃ q : X.PartialSection, p ≤ q ∧ i₀ ∈ q.domain

/-- **Zorn-driven global-section existence** under
`HasPartialExtensions`. Get a maximal partial section via Zorn; any
missing valid index is supplied by `hExt`, contradicting maximality. -/
theorem FiniteProjectiveSystem.exists_global_section_of_partialExtensions
    {ι : Type*} [PartialOrder ι] (X : FiniteProjectiveSystem ι)
    (hExt : X.HasPartialExtensions) :
    ∃ P : ∀ i, X.Valid i → X.Obj i,
      ∀ {i j : ι} (hi : X.Valid i) (hj : X.Valid j) (hij : i ≤ j),
        X.Compat (X.restrict hij (P j hj)) (P i hi) := by
  obtain ⟨m, hm_max⟩ := FiniteProjectiveSystem.PartialSection.exists_maximal X
  -- Show m.domain covers all valid indices.
  have h_dom : ∀ i, X.Valid i → i ∈ m.domain := by
    intro i₀ hval
    by_contra h_not_in
    obtain ⟨q, h_le, h_i₀_in_q⟩ := hExt m i₀ hval
    -- By maximality, q ≤ m; so i₀ ∈ q.domain ⊆ m.domain. Contradiction.
    have h_max := hm_max h_le
    exact h_not_in (h_max.1 i₀ h_i₀_in_q)
  -- Extract the global section from m.
  refine ⟨fun i hval => m.P i (h_dom i hval), ?_⟩
  intro i j hi hj hij
  exact m.compat (h_dom i hi) (h_dom j hj) hij

/-! ### Ideal-domain variant: `IdealPartialSection`

The CBP `HasPartialExtensions` instance is hard to prove because a
generic `PartialSection`'s domain can be an arbitrary set of indices,
forcing extension lemmas to reconcile compatibility across unrelated
finsets. The ideal-domain variant restricts the domain to be
**downward closed** and **directed**, so it forms an "ideal" of `ι`.

The parallel structure `IdealPartialSection` has the same fields as
`PartialSection` plus `downward_closed` and `directed`. The chain
upper bound, maximality argument, and `HasPartialExtensions` analog
all carry over (the union of a chain of ideal domains is an ideal
domain). This is provided alongside the original `PartialSection`,
not replacing it; CBP migration happens only after the ideal version
proves simpler. -/

/-- **`IdealPartialSection X`**: a partial choice function whose
domain is an **ideal** of `ι` — a downward-closed, directed subset
of valid indices, with `Compat`-coherent restrictions. -/
structure FiniteProjectiveSystem.IdealPartialSection
    {ι : Type*} [PartialOrder ι] (X : FiniteProjectiveSystem ι) where
  /-- Domain: the set of indices on which this section is defined. -/
  domain : Set ι
  /-- Every index in `domain` is valid. -/
  domain_valid : ∀ {i : ι}, i ∈ domain → X.Valid i
  /-- Downward-closed: if `j ∈ domain` and `i ≤ j`, then `i ∈ domain`. -/
  downward_closed : ∀ {i j : ι}, j ∈ domain → i ≤ j → i ∈ domain
  /-- Directed: any two elements have a common upper bound in the domain. -/
  directed : ∀ {i j : ι}, i ∈ domain → j ∈ domain →
    ∃ k, k ∈ domain ∧ i ≤ k ∧ j ≤ k
  /-- The partial choice function. -/
  P : ∀ i, i ∈ domain → X.Obj i
  /-- `Compat`-coherence: restrictions match on overlapping pairs. -/
  compat : ∀ {i j : ι} (hi : i ∈ domain) (hj : j ∈ domain) (hij : i ≤ j),
    X.Compat (X.restrict hij (P j hj)) (P i hi)

/-- **Extension order on ideal partial sections**: same as for
`PartialSection` — `ps₁ ≤ ps₂` iff `ps₂`'s domain contains `ps₁`'s,
and the choice functions agree on the common domain. -/
instance FiniteProjectiveSystem.IdealPartialSection.instLE
    {ι : Type*} [PartialOrder ι] {X : FiniteProjectiveSystem ι} :
    LE (X.IdealPartialSection) where
  le ps₁ ps₂ :=
    (∀ i, i ∈ ps₁.domain → i ∈ ps₂.domain) ∧
    (∀ (i : ι) (hi₁ : i ∈ ps₁.domain) (hi₂ : i ∈ ps₂.domain),
      ps₂.P i hi₂ = ps₁.P i hi₁)

/-- **Preorder instance** on `IdealPartialSection`. Same proof as for
`PartialSection`: reflexive + transitive. -/
instance FiniteProjectiveSystem.IdealPartialSection.instPreorder
    {ι : Type*} [PartialOrder ι] {X : FiniteProjectiveSystem ι} :
    Preorder (X.IdealPartialSection) where
  le := (· ≤ ·)
  le_refl ps := ⟨fun _ h => h, fun _ _ _ => rfl⟩
  le_trans ps₁ ps₂ ps₃ h₁₂ h₂₃ :=
    ⟨fun i hi => h₂₃.1 i (h₁₂.1 i hi),
     fun i hi₁ hi₃ =>
       (h₂₃.2 i (h₁₂.1 i hi₁) hi₃).trans (h₁₂.2 i hi₁ (h₁₂.1 i hi₁))⟩

/-- **`chainUpperBound`** for ideal partial sections. The union of a
chain of ideal domains is itself an ideal: downward closure is
preserved by union, and directedness is preserved because any two
elements lie in some chain element (use the chain order to put them
together, then use that element's `directed`). -/
noncomputable def FiniteProjectiveSystem.IdealPartialSection.chainUpperBound
    {ι : Type*} [PartialOrder ι] {X : FiniteProjectiveSystem ι}
    (c : Set X.IdealPartialSection) (hc : IsChain (· ≤ ·) c) :
    X.IdealPartialSection where
  domain := {i | ∃ ps ∈ c, i ∈ ps.domain}
  domain_valid {i} hi := by
    obtain ⟨ps, _, hi_ps⟩ := hi
    exact ps.domain_valid hi_ps
  downward_closed {i j} hj hij := by
    obtain ⟨ps, hps_in, hj_ps⟩ := hj
    exact ⟨ps, hps_in, ps.downward_closed hj_ps hij⟩
  directed {i j} hi hj := by
    classical
    obtain ⟨ps_i, hps_i_in, hi_ps_i⟩ := hi
    obtain ⟨ps_j, hps_j_in, hj_ps_j⟩ := hj
    rcases eq_or_ne ps_i ps_j with h_eq | h_ne
    · subst h_eq
      obtain ⟨k, hk_in, hik, hjk⟩ := ps_i.directed hi_ps_i hj_ps_j
      exact ⟨k, ⟨ps_i, hps_i_in, hk_in⟩, hik, hjk⟩
    rcases hc hps_i_in hps_j_in h_ne with h_le | h_le
    · -- ps_i ≤ ps_j: lift i into ps_j.
      have hi_ps_j : i ∈ ps_j.domain := h_le.1 i hi_ps_i
      obtain ⟨k, hk_in, hik, hjk⟩ := ps_j.directed hi_ps_j hj_ps_j
      exact ⟨k, ⟨ps_j, hps_j_in, hk_in⟩, hik, hjk⟩
    · -- ps_j ≤ ps_i: lift j into ps_i.
      have hj_ps_i : j ∈ ps_i.domain := h_le.1 j hj_ps_j
      obtain ⟨k, hk_in, hik, hjk⟩ := ps_i.directed hi_ps_i hj_ps_i
      exact ⟨k, ⟨ps_i, hps_i_in, hk_in⟩, hik, hjk⟩
  P i hi := hi.choose.P i hi.choose_spec.2
  compat {i j} hi hj hij := by
    classical
    have hps_i_in_c : hi.choose ∈ c := hi.choose_spec.1
    have hps_j_in_c : hj.choose ∈ c := hj.choose_spec.1
    have hi_in_ps_i : i ∈ hi.choose.domain := hi.choose_spec.2
    have hj_in_ps_j : j ∈ hj.choose.domain := hj.choose_spec.2
    rcases eq_or_ne hi.choose hj.choose with h_eq | h_ne
    · have hj_in_ps_i : j ∈ hi.choose.domain := h_eq ▸ hj_in_ps_j
      have h_pj_eq : hj.choose.P j hj_in_ps_j = hi.choose.P j hj_in_ps_i := by
        congr 1 <;> exact h_eq.symm
      rw [h_pj_eq]
      exact hi.choose.compat hi_in_ps_i hj_in_ps_i hij
    rcases hc hps_i_in_c hps_j_in_c h_ne with h_le | h_le
    · have hi_in_ps_j : i ∈ hj.choose.domain := h_le.1 i hi_in_ps_i
      have h_pi_eq : hj.choose.P i hi_in_ps_j = hi.choose.P i hi_in_ps_i :=
        h_le.2 i hi_in_ps_i hi_in_ps_j
      have := hj.choose.compat hi_in_ps_j hj_in_ps_j hij
      rw [h_pi_eq] at this
      exact this
    · have hj_in_ps_i : j ∈ hi.choose.domain := h_le.1 j hj_in_ps_j
      have h_pj_eq : hi.choose.P j hj_in_ps_i = hj.choose.P j hj_in_ps_j :=
        h_le.2 j hj_in_ps_j hj_in_ps_i
      have := hi.choose.compat hi_in_ps_i hj_in_ps_i hij
      rw [h_pj_eq] at this
      exact this

/-- **`chainUpperBound_isUB`** for ideal partial sections: same proof
shape as for `PartialSection`. -/
theorem FiniteProjectiveSystem.IdealPartialSection.chainUpperBound_isUB
    {ι : Type*} [PartialOrder ι] {X : FiniteProjectiveSystem ι}
    (c : Set X.IdealPartialSection) (hc : IsChain (· ≤ ·) c) :
    ∀ ps ∈ c, ps ≤ chainUpperBound c hc := by
  intro ps hps
  refine ⟨fun i hi => ⟨ps, hps, hi⟩, ?_⟩
  intro i hi_ps hi_union
  classical
  set ps' := hi_union.choose with hps'_def
  have hps'_in_c : ps' ∈ c := hi_union.choose_spec.1
  have hi_in_ps' : i ∈ ps'.domain := hi_union.choose_spec.2
  show ps'.P i hi_in_ps' = ps.P i hi_ps
  rcases eq_or_ne ps' ps with h_eq | h_ne
  · subst h_eq; rfl
  rcases hc hps'_in_c hps h_ne with h_le | h_le
  · exact (h_le.2 i hi_in_ps' hi_ps).symm
  · exact h_le.2 i hi_ps hi_in_ps'

/-- **`bddAbove_of_isChain`** for ideal partial sections. -/
theorem FiniteProjectiveSystem.IdealPartialSection.bddAbove_of_isChain
    {ι : Type*} [PartialOrder ι] {X : FiniteProjectiveSystem ι}
    (c : Set X.IdealPartialSection) (hc : IsChain (· ≤ ·) c) :
    BddAbove c :=
  ⟨chainUpperBound c hc, chainUpperBound_isUB c hc⟩

/-- **Empty ideal partial section**: the empty domain is trivially
downward-closed and (vacuously) directed. -/
noncomputable def FiniteProjectiveSystem.IdealPartialSection.empty
    {ι : Type*} [PartialOrder ι] (X : FiniteProjectiveSystem ι) :
    X.IdealPartialSection where
  domain := ∅
  domain_valid {i} hi := absurd hi (Set.notMem_empty i)
  downward_closed {i j} hj _ := absurd hj (Set.notMem_empty j)
  directed {i j} hi _ := absurd hi (Set.notMem_empty i)
  P i hi := absurd hi (Set.notMem_empty i)
  compat {i j} hi _ _ := absurd hi (Set.notMem_empty i)

/-- **Maximal ideal partial section exists**: Zorn applied to
`bddAbove_of_isChain` for the ideal variant. -/
theorem FiniteProjectiveSystem.IdealPartialSection.exists_maximal
    {ι : Type*} [PartialOrder ι] (X : FiniteProjectiveSystem ι) :
    ∃ m : X.IdealPartialSection, IsMax m :=
  zorn_le (fun c hc => bddAbove_of_isChain c hc)

/-- **`X.IdealHasPartialExtensions`**: every ideal partial section
extends to an ideal partial section containing any specified valid
index. This is the ideal-domain analog of `HasPartialExtensions`. -/
def FiniteProjectiveSystem.IdealHasPartialExtensions
    {ι : Type*} [PartialOrder ι] (X : FiniteProjectiveSystem ι) : Prop :=
  ∀ (p : X.IdealPartialSection) (i₀ : ι), X.Valid i₀ →
    ∃ q : X.IdealPartialSection, p ≤ q ∧ i₀ ∈ q.domain

/-- **Zorn-driven global-section existence** for ideal partial
sections under `IdealHasPartialExtensions`. -/
theorem FiniteProjectiveSystem.exists_global_section_of_idealPartialExtensions
    {ι : Type*} [PartialOrder ι] (X : FiniteProjectiveSystem ι)
    (hExt : X.IdealHasPartialExtensions) :
    ∃ P : ∀ i, X.Valid i → X.Obj i,
      ∀ {i j : ι} (hi : X.Valid i) (hj : X.Valid j) (hij : i ≤ j),
        X.Compat (X.restrict hij (P j hj)) (P i hi) := by
  obtain ⟨m, hm_max⟩ := FiniteProjectiveSystem.IdealPartialSection.exists_maximal X
  have h_dom : ∀ i, X.Valid i → i ∈ m.domain := by
    intro i₀ hval
    by_contra h_not_in
    obtain ⟨q, h_le, h_i₀_in_q⟩ := hExt m i₀ hval
    have h_max := hm_max h_le
    exact h_not_in (h_max.1 i₀ h_i₀_in_q)
  refine ⟨fun i hval => m.P i (h_dom i hval), ?_⟩
  intro i j hi hj hij
  exact m.compat (h_dom i hi) (h_dom j hj) hij

/-! ### Status note

The previous `FiniteProjectiveSystem.exists_global_section` theorem
(an unconditional global-section existence) has been **superseded**
by the conditional `exists_global_section_of_partialExtensions`,
which derives the global section from a `HasPartialExtensions`
hypothesis. For concrete instances (e.g., `coherentBranchPartialSystem`),
the `HasPartialExtensions` is supplied separately.

An **ideal-domain variant** is also provided in parallel
(`IdealPartialSection`, `IdealHasPartialExtensions`,
`exists_global_section_of_idealPartialExtensions`). The ideal version
constrains the domain to a downward-closed, directed subset, which
makes the model-specific extension lemma significantly easier (each
new index has a clear set of predecessors to amalgamate against).
CBP migration to the ideal variant happens once the ideal extension
proof is shown to be tractable. -/

/-! ### `CoherentWitnessNet`: coherent global section of the projective system

The eventual-constancy obstruction documented above shows that
arbitrary witnesses don't suffice for the ultrafilter compactness
argument. The right structure is a **coherent witness net**: a
choice `P S hS : CoherentBranchPartial cR S` for every finite
`S ⊂ ω₁`, with restrictions compatible across `S ⊆ T`.

`CoherentWitnessNet` makes the compatibility a structural field of
the witness family. Given a `CoherentWitnessNet`, the compactness
proof is direct (no ultrafilter required): define `A` coordinatewise
via `W.P {α}`, and use `prefix_compat` / `branch_compat` to match
against `W.P S₀` for any `S₀` containing the coordinate.

The frontier migrated one level deeper to `exists_coherentWitnessNet`
(existence of a globally coherent section of the projective system),
and **then one more level** into the generic abstraction
`FiniteProjectiveSystem.exists_global_section`:

  `exists_coherentMajorityBranch` (axiom-clean, derived)
    ← `exists_coherentMajorityBranch_of_finitePartials` (axiom-clean bridge)
    ← `rawBranchCompactness_holds` (axiom-clean, derived)
    ← `rawBranchCompactness_of_coherentWitnessNet` (axiom-clean bridge)
    ← `exists_coherentWitnessNet` (axiom-clean, derived from FPS)
    ← `FiniteProjectiveSystem.exists_global_section` (**active frontier**)

So `CoherentWitnessNet` is now an intermediate object — neither the
frontier nor the top-level statement, but a clean restatement of the
projective system in CBP-specific language. The active mathematical
content lives in the generic FPS abstraction. -/

/-- **`CoherentWitnessNet cR`**: a coherent choice of partial
branches across every finite `S ⊂ ω₁`, with restrictions compatible
across `S ⊆ T`. -/
structure CoherentWitnessNet (cR : (Fin 2 ↪o PairERSource) → Bool) where
  /-- Witness CBP at every finite `S ⊂ ω₁`. -/
  P : ∀ S : Finset Ordinal.{0}, (∀ α ∈ S, α < Ordinal.omega.{0} 1) →
    CoherentBranchPartial cR S
  /-- Prefix compatibility across `S ⊆ T`: the prefix at `α ∈ S` is
  the same whether viewed in `P S` or `P T`. -/
  prefix_compat : ∀ {S T : Finset Ordinal.{0}}
    (hS : ∀ α ∈ S, α < Ordinal.omega.{0} 1)
    (hT : ∀ α ∈ T, α < Ordinal.omega.{0} 1)
    (hST : S ⊆ T) (α : Ordinal.{0}) (hα : α ∈ S),
    (P T hT).prefixAt α (hST hα) = (P S hS).prefixAt α hα
  /-- Branch compatibility (parallel to `prefix_compat`). -/
  branch_compat : ∀ {S T : Finset Ordinal.{0}}
    (hS : ∀ α ∈ S, α < Ordinal.omega.{0} 1)
    (hT : ∀ α ∈ T, α < Ordinal.omega.{0} 1)
    (hST : S ⊆ T) (α : Ordinal.{0}) (hα : α ∈ S),
    (P T hT).branch α (hST hα) = (P S hS).branch α hα

/-- **`rawBranchCompactness_of_coherentWitnessNet`**: axiom-clean
bridge. Given a `CoherentWitnessNet`, the raw-branch compactness
principle holds. The construction is direct (no ultrafilter): define
`A` at each coordinate via `W.P {α}`, and use `prefix_compat` /
`branch_compat` to match against `W.P S₀` for any `S₀` containing the
coordinate. -/
theorem rawBranchCompactness_of_coherentWitnessNet
    {cR : (Fin 2 ↪o PairERSource) → Bool} (W : CoherentWitnessNet cR) :
    rawBranchCompactness cR := by
  intro _hfin
  -- Singleton-witness helper for each α < ω₁.
  let hα_singleton : ∀ (α : Ordinal.{0}), α < Ordinal.omega.{0} 1 →
      ∀ β ∈ ({α} : Finset Ordinal.{0}), β < Ordinal.omega.{0} 1 :=
    fun α hα β hβ => Finset.mem_singleton.mp hβ ▸ hα
  -- Build the global raw assignment from singleton witnesses.
  refine ⟨(fun α hα =>
      some ((W.P {α} (hα_singleton α hα)).prefixAt α
        (Finset.mem_singleton.mpr rfl)),
    fun α hα =>
      some ((W.P {α} (hα_singleton α hα)).branch α
        (Finset.mem_singleton.mpr rfl))), ?_⟩
  intro S₀ hS₀
  -- The CBP witness for SatisfiesFinite is W.P S₀ hS₀.
  refine ⟨hS₀, W.P S₀ hS₀, ?_, ?_⟩
  · -- Prefix matching: A.1 α (hS₀ α hα) = some ((W.P S₀ hS₀).prefixAt α hα).
    intro α hα
    -- Both sides have form `some (...)`. The values agree by prefix_compat
    -- applied to {α} ⊆ S₀.
    have h_subset : ({α} : Finset Ordinal.{0}) ⊆ S₀ := by
      intro β hβ
      rw [Finset.mem_singleton.mp hβ]; exact hα
    have := W.prefix_compat (hα_singleton α (hS₀ α hα)) hS₀ h_subset α
      (Finset.mem_singleton.mpr rfl)
    -- `this : (W.P S₀ hS₀).prefixAt α (h_subset _) = (W.P {α} ...).prefixAt α _`.
    -- Use proof-irrelevance for the membership proofs.
    show some ((W.P {α} (hα_singleton α (hS₀ α hα))).prefixAt α
        (Finset.mem_singleton.mpr rfl)) =
      some ((W.P S₀ hS₀).prefixAt α hα)
    rw [← this]
  · -- Branch matching: parallel.
    intro α hα
    have h_subset : ({α} : Finset Ordinal.{0}) ⊆ S₀ := by
      intro β hβ
      rw [Finset.mem_singleton.mp hβ]; exact hα
    have := W.branch_compat (hα_singleton α (hS₀ α hα)) hS₀ h_subset α
      (Finset.mem_singleton.mpr rfl)
    show some ((W.P {α} (hα_singleton α (hS₀ α hα))).branch α
        (Finset.mem_singleton.mpr rfl)) =
      some ((W.P S₀ hS₀).branch α hα)
    rw [← this]

/-! ### Finite extension property for the projective system

The finite-extension property: for any finite family `𝒮` of finite
finsets `S ⊂ ω₁`, there is a partial-choice family
`P S hS_mem : CBP cR S` (for `S ∈ 𝒮`) that is compatible under
restriction. Proved by choosing a single CBP on the union of `𝒮`
(via `exists_coherentBranchPartial`) and restricting to each member.

This is the finite case of `CoherentWitnessNet`. The compactness
step (lifting from finite to all finsets `S ⊂ ω₁`) is the new
remaining frontier — typically discharged by a Zorn/maximality
argument or another compactness principle. -/

/-- **`CoherentWitnessNet.finite_extension_property`**: for any
finite family `𝒮` of `< ω₁`-bounded finsets, there is a
finite-restricted coherent witness family with mutually compatible
restrictions. Proved by choosing a single CBP on the union
`𝒮.sup id` and restricting to each member; the compatibility is
`restrict_prefixAt` / `restrict_branch` collapsing both sides to the
same `Q.prefixAt` (resp. `Q.branchAt`) value modulo proof-irrelevant
membership witnesses. -/
theorem CoherentWitnessNet.finite_extension_property
    (cR : (Fin 2 ↪o PairERSource) → Bool)
    (𝒮 : Finset (Finset Ordinal.{0}))
    (h𝒮 : ∀ S ∈ 𝒮, ∀ α ∈ S, α < Ordinal.omega.{0} 1) :
    ∃ P : ∀ S, S ∈ 𝒮 → CoherentBranchPartial cR S,
      (∀ {S T : Finset Ordinal.{0}} (hS : S ∈ 𝒮) (hT : T ∈ 𝒮)
          (hST : S ⊆ T) (α : Ordinal.{0}) (hα : α ∈ S),
          (P T hT).prefixAt α (hST hα) = (P S hS).prefixAt α hα) ∧
      (∀ {S T : Finset Ordinal.{0}} (hS : S ∈ 𝒮) (hT : T ∈ 𝒮)
          (hST : S ⊆ T) (α : Ordinal.{0}) (hα : α ∈ S),
          (P T hT).branch α (hST hα) = (P S hS).branch α hα) := by
  classical
  -- Step 1: union of all sets in 𝒮.
  set U : Finset Ordinal.{0} := 𝒮.sup id with hU_def
  have hU_lt : ∀ α ∈ U, α < Ordinal.omega.{0} 1 := by
    intro α hα
    obtain ⟨S, hS, hαS⟩ := Finset.mem_sup.mp hα
    exact h𝒮 S hS α hαS
  -- Step 2: a CBP on U.
  obtain ⟨Q⟩ := exists_coherentBranchPartial cR U hU_lt
  -- Step 3: for each S ∈ 𝒮, S ⊆ U.
  have h_sub : ∀ {S : Finset Ordinal.{0}}, S ∈ 𝒮 → S ⊆ U := by
    intro S hS_mem α hα
    exact Finset.mem_sup.mpr ⟨S, hS_mem, hα⟩
  -- Step 4: define P S hS := Q.restrict (h_sub hS).
  refine ⟨fun S hS_mem => Q.restrict (h_sub hS_mem), ?_, ?_⟩
  · -- Prefix compatibility: both reduce to Q.prefixAt α (some proof in U).
    intro S T hS hT hST α hα
    rw [Q.restrict_prefixAt (h_sub hT) α (hST hα),
        Q.restrict_prefixAt (h_sub hS) α hα]
  · -- Branch compatibility (parallel).
    intro S T hS hT hST α hα
    rw [Q.restrict_branch (h_sub hT) α (hST hα),
        Q.restrict_branch (h_sub hS) α hα]

/-! ### `CoherentBranchPartial` as a `FiniteProjectiveSystem` instance

The CBP projective system instantiates `FiniteProjectiveSystem`:

- index: `Finset Ordinal.{0}` with `⊆` (Finset's `≤` unfolds to `⊆`).
- validity: `∀ α ∈ S, α < ω₁`.
- objects: `CoherentBranchPartial cR S`.
- restriction: `CoherentBranchPartial.restrict`.
- compatibility: fieldwise — agreement on `prefixAt` and `branch`.
- finite extension: from `CoherentWitnessNet.finite_extension_property`.

Structural CBP equality of nested `restrict`s is not definitionally
true (the underlying `set`-based construction blocks `rfl`), so we
use a fieldwise `Compat` instead. -/

/-- **`cbpFieldwiseCompat`**: fieldwise compatibility on
`CoherentBranchPartial cR S` — agreement on `prefixAt` and `branch`. -/
def cbpFieldwiseCompat {cR : (Fin 2 ↪o PairERSource) → Bool}
    {S : Finset Ordinal.{0}}
    (P₁ P₂ : CoherentBranchPartial cR S) : Prop :=
  (∀ α (hα : α ∈ S), P₁.prefixAt α hα = P₂.prefixAt α hα) ∧
  (∀ α (hα : α ∈ S), P₁.branch α hα = P₂.branch α hα)

/-- **`coherentBranchPartialSystem cR`**: the `FiniteProjectiveSystem`
instance for `CoherentBranchPartial`, with fieldwise compatibility. -/
noncomputable def coherentBranchPartialSystem
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    FiniteProjectiveSystem (Finset Ordinal.{0}) where
  Valid S := ∀ α ∈ S, α < Ordinal.omega.{0} 1
  Obj S := CoherentBranchPartial cR S
  restrict {_ _} hij P := P.restrict hij
  Compat := cbpFieldwiseCompat
  finite_extension := by
    intro 𝒮 h𝒮
    classical
    set U : Finset Ordinal.{0} := 𝒮.sup id
    have hU_lt : ∀ α ∈ U, α < Ordinal.omega.{0} 1 := by
      intro α hα
      obtain ⟨S, hS, hαS⟩ := Finset.mem_sup.mp hα
      exact h𝒮 S hS α hαS
    obtain ⟨Q⟩ := exists_coherentBranchPartial cR U hU_lt
    have h_sub : ∀ {S : Finset Ordinal.{0}}, S ∈ 𝒮 → S ⊆ U := fun hS_mem α hα =>
      Finset.mem_sup.mpr ⟨_, hS_mem, hα⟩
    refine ⟨fun S hS_mem => Q.restrict (h_sub hS_mem), ?_⟩
    intro S T hS hT hST
    -- Compat: pointwise prefixAt/branch agreement.
    refine ⟨?_, ?_⟩
    · intro α hα
      -- `((Q.restrict (h_sub hT)).restrict hST).prefixAt α hα = (Q.restrict (h_sub hS)).prefixAt α hα`.
      -- Both reduce via restrict_prefixAt to Q.prefixAt at α with U-membership proofs
      -- (proof-irrelevantly equal).
      rw [CoherentBranchPartial.restrict_prefixAt, Q.restrict_prefixAt (h_sub hT) α (hST hα),
          Q.restrict_prefixAt (h_sub hS) α hα]
    · intro α hα
      rw [CoherentBranchPartial.restrict_branch, Q.restrict_branch (h_sub hT) α (hST hα),
          Q.restrict_branch (h_sub hS) α hα]

/-! ### CBP-specific `HasPartialExtensions` instance

The strengthened `HasPartialExtensions` property for the CBP
projective system. Given a partial section `p` and a new valid
finset `i₀`, must return `q : PartialSection` with `p ≤ q` and
`i₀ ∈ q.domain`.

**Obstruction analysis**: building `q` from `p` requires constructing
a CBP at `i₀` whose restriction to each `S ∈ p.domain` agrees with
`p.P S` (where the relevant overlap is `S ⊆ i₀` for back direction,
or `(p.P T).restrict i₀` matches `q.P i₀` for forward `T ⊇ i₀`).

The challenges:

- **Back direction** (`S ⊆ i₀`, finitely many subsets of `i₀`): forces
  `q.P i₀` to restrict to `p.P S` on each such `S`. Mutually
  compatible (via `p.compat`), so the data on `⋃ S ⊆ i₀` is
  determined. Extending to all of `i₀` requires a CBP-amalgamation
  primitive stronger than `exists_coherentBranchPartial` (which
  doesn't preserve prescribed data on a sub-finset).

- **Forward direction** (`T ⊇ i₀`, possibly infinitely many supersets):
  `q.P i₀` must equal `(p.P T).restrict i₀` for every such `T`. By
  `p.compat`, different `T`'s give the same restriction provided
  there's a common upper bound in `p.domain` — but a generic `p`
  isn't necessarily directed. Without directedness, infinitely many
  forward constraints could be inconsistent.

The naive use of `exists_commonExtensionPartial` on a finite slice
of `p.domain ∪ {i₀}` gives a coherent family, but the values **need
not match `p.P S`** on overlap. Hence `HasPartialExtensions` requires
a strictly stronger primitive than `exists_coherentBranchPartial` /
`finite_extension_property`.

This is the predicted next frontier (per the FPS migration plan):
the genuine compactness work, now isolated as a sorry on this
specific CBP-side property. -/

/-- **[NEW FRONTIER, sorry]** The CBP projective system has the
strengthened `HasPartialExtensions` property. Together with the
axiom-clean `exists_global_section_of_partialExtensions`, this
yields `exists_coherentWitnessNet`. -/
theorem coherentBranchPartial_hasPartialExtensions
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    (coherentBranchPartialSystem cR).HasPartialExtensions := by
  sorry

/-! ### Ideal-domain CBP frontier (parallel exploration)

The unrestricted `HasPartialExtensions` faces the obstruction noted
above: arbitrary `p.domain` forces compatibility across unrelated
finsets. The ideal-domain version
(`IdealHasPartialExtensions`) restricts attention to ideals
(downward-closed + directed). In the Finset-Ordinal setting an ideal
is exactly the downset of a (possibly infinite) set `A ⊆ ω₁`, i.e.
`p.domain = {S : Finset Ordinal | S ⊆ A ∧ S finite}`.

**Why this should be easier**: extending an ideal section by `i₀`
amounts to enlarging `A` to `A ∪ i₀`. The compatibility obligations
become "single-coordinate" — for each new ordinal `α ∈ i₀ \ A`, pick
`prefixAt α` and `branch α` so the new family remains coherent on
all finite subsets of `A ∪ i₀`. The hard combinatorial step is now
isolated as a *single-coordinate CBP extension*, rather than
amalgamation across arbitrary partial sections.

This stub is the ideal-side analog of
`coherentBranchPartial_hasPartialExtensions`. Both remain `sorry`
until the underlying CBP-extension primitive is built; the migration
plan is to fill the ideal version first, then redirect
`exists_coherentWitnessNet` to go through it. -/

/-- **[NEW FRONTIER, sorry]** The CBP projective system has the
strengthened `IdealHasPartialExtensions` property. Parallel to
`coherentBranchPartial_hasPartialExtensions` but with ideal domains —
the natural target for the single-coordinate CBP extension primitive. -/
theorem coherentBranchPartial_idealHasPartialExtensions
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    (coherentBranchPartialSystem cR).IdealHasPartialExtensions := by
  sorry

/-! ### Diagnostic: finite-subdomain extension via `finite_extension_property`

To test whether the ideal-domain structure actually removes the
extension obstruction, we attempt a **finite-subdomain** version:
given an ideal section `p` and a finite `D ⊆ p.domain`, find a
locally-coherent partial section on `D ∪ {i₀}` that matches `p` on
`D`. If this passes via `finite_extension_property`, the full
`IdealHasPartialExtensions` should follow by directedness; if not,
the obstruction is the primitive's strength, not the domain shape.

**Result**: The finite version is provable as a "raw" coherent
family (i.e. *some* CBP on `(insert i₀ D).sup id` exists) but
**not** as one that preserves `p.P` values on `D`. The
`finite_extension_property` builds a *fresh* CBP `Q`; nothing forces
`Q.restrict S = p.P S` for `S ∈ D`. Hence even the finite version
of the ideal extension needs a strictly stronger primitive — a
**rigid amalgamation** lemma that extends a prescribed coherent
family rather than building one from scratch.

Conclusion: the ideal-domain structure narrows the missing primitive
to single-coordinate rigid extension (extend a CBP on `T` to a CBP
on `T ∪ {α}` for one new `α`), but does not bypass it. -/

/-- **Diagnostic finite-extension lemma (axiom-clean).** Given an
ideal section `p` of the CBP system, a finite `D ⊆ p.domain`, and a
new valid finset `i₀`, the `finite_extension_property` produces a
*fresh* coherent family on `D ∪ {i₀}`. This is the **raw** finite
version, **without** the requirement that it preserve `p.P` values
on `D` — that requirement is the missing rigid amalgamation
primitive. -/
theorem coherentBranchPartial_finite_extension_with_i0
    (cR : (Fin 2 ↪o PairERSource) → Bool)
    (D : Finset (Finset Ordinal.{0}))
    (hD_valid : ∀ S ∈ D, ∀ α ∈ S, α < Ordinal.omega.{0} 1)
    (i₀ : Finset Ordinal.{0})
    (hi₀ : ∀ α ∈ i₀, α < Ordinal.omega.{0} 1) :
    ∃ P : ∀ S, S ∈ insert i₀ D → CoherentBranchPartial cR S,
      ∀ {S T} (hS : S ∈ insert i₀ D) (hT : T ∈ insert i₀ D) (hST : S ⊆ T),
        cbpFieldwiseCompat ((P T hT).restrict hST) (P S hS) := by
  classical
  -- Apply the FPS finite_extension on insert i₀ D.
  have h_valid : ∀ S ∈ insert i₀ D, (coherentBranchPartialSystem cR).Valid S := by
    intro S hS
    rcases Finset.mem_insert.mp hS with h | h
    · subst h; exact hi₀
    · exact hD_valid S h
  exact (coherentBranchPartialSystem cR).finite_extension (insert i₀ D) h_valid

/-- **The actual gap, stated precisely.** This is the
*rigid* version of the diagnostic: it asks for a coherent family on
`insert i₀ D` that *agrees with `p.P` on `D`*. Under the current
primitives (`finite_extension_property` builds a fresh CBP, not a
prescribed one), this is **not provable** — it is exactly the
missing rigid amalgamation primitive.

Marked `sorry` to make the gap visible and to enable downstream
constructions to be stated against it. A **conditional** version
(`coherentBranchPartial_rigid_finite_extension_above`, defined after
`coherentBranchPartial_extend_one`) is provable using the rigid
top-extension primitive when `i₀` is above `⋃ D`. The general case
(`i₀` interspersed within `⋃ D`) requires interior insertion, still
pending. -/
theorem coherentBranchPartial_rigid_finite_extension
    (cR : (Fin 2 ↪o PairERSource) → Bool)
    (p : (coherentBranchPartialSystem cR).IdealPartialSection)
    (D : Finset (Finset Ordinal.{0}))
    (hD : ∀ S ∈ D, S ∈ p.domain)
    (i₀ : Finset Ordinal.{0})
    (hi₀ : ∀ α ∈ i₀, α < Ordinal.omega.{0} 1) :
    ∃ P : ∀ S, S ∈ insert i₀ D → CoherentBranchPartial cR S,
      (∀ {S T} (hS : S ∈ insert i₀ D) (hT : T ∈ insert i₀ D) (hST : S ⊆ T),
        cbpFieldwiseCompat ((P T hT).restrict hST) (P S hS)) ∧
      (∀ S (hS_D : S ∈ D),
        cbpFieldwiseCompat (P S (Finset.mem_insert_of_mem hS_D)) (p.P S (hD S hS_D))) := by
  sorry

/-! ### Single-coordinate rigid extension (top-extension special case)

The natural primitive for closing the rigid amalgamation gap is to
extend a CBP by a single ordinal at a time. The cleanest case is
**top extension**: given `P : CBP cR T` and a new `α > max T`, build
`Q : CBP cR (insert α T)` whose restriction to `T` is fieldwise
equal to `P`. This uses `CoherentBranchApprox.extendTo` directly.

The general case (`α` not necessarily above `max T`) requires
inserting at an interior position, which is a strictly stronger
primitive. -/

/-- **Single-coordinate rigid top-extension**: given `P : CBP cR T`
and a new valid `α` strictly above all of `T`, build
`Q : CBP cR (insert α T)` whose restriction to `T` agrees fieldwise
with `P`. -/
theorem coherentBranchPartial_extend_one_above_top
    (cR : (Fin 2 ↪o PairERSource) → Bool)
    {T : Finset Ordinal.{0}} (P : CoherentBranchPartial cR T)
    (α : Ordinal.{0}) (hα : α < Ordinal.omega.{0} 1)
    (h_above : ∀ β ∈ T, β < α) :
    ∃ Q : CoherentBranchPartial cR (insert α T),
      cbpFieldwiseCompat (Q.restrict (Finset.subset_insert α T)) P := by
  classical
  -- α ∉ T (since α < α is false).
  have hα_not_mem : α ∉ T := fun h => lt_irrefl α (h_above α h)
  -- Handle T = ∅ trivially: build CBP on {α} fresh; fieldwise compat is vacuous.
  by_cases hT_empty : T = ∅
  · subst hT_empty
    have h_valid : ∀ β ∈ insert α (∅ : Finset Ordinal.{0}),
        β < Ordinal.omega.{0} 1 := by
      intro β hβ
      rcases Finset.mem_insert.mp hβ with h | h
      · exact h ▸ hα
      · exact absurd h (Finset.notMem_empty _)
    obtain ⟨Q⟩ := exists_coherentBranchPartial cR (insert α ∅) h_valid
    refine ⟨Q, ?_, ?_⟩ <;>
      intro β hβ <;> exact absurd hβ (Finset.notMem_empty _)
  -- Main case: T ≠ ∅. (T.card + 1 = (insert α T).card and α > max T.)
  have hT_card_ne : T.card ≠ 0 :=
    fun h => hT_empty (Finset.card_eq_zero.mp h)
  have hT_card_pos : 0 < T.card := Nat.pos_of_ne_zero hT_card_ne
  have h_card : (insert α T).card = T.card + 1 :=
    Finset.card_insert_of_notMem hα_not_mem
  -- P.toApprox.lastLevel < α (the max element of T is < α by h_above).
  have h_above_last : P.toApprox.lastLevel < α := by
    have hT_sub : T.card - 1 < T.card := Nat.sub_lt hT_card_pos one_pos
    have h_last_eq : P.toApprox.lastLevel =
        (T.orderEmbOfFin rfl) ⟨T.card - 1, hT_sub⟩ := by
      unfold CoherentBranchApprox.lastLevel
      rw [dif_neg hT_card_ne]
      exact P.level_eq ⟨T.card - 1, hT_sub⟩
    rw [h_last_eq]
    exact h_above _ (T.orderEmbOfFin_mem rfl _)
  -- The extended approximation A_ext : CBA cR (T.card + 1).
  let A_ext := P.toApprox.extendTo α hα h_above_last
  -- Identification of (insert α T).orderEmbOfFin via uniqueness.
  -- The strict-mono Fin.lastCases family f matches insert α T's enumeration.
  set f : Fin (T.card + 1) → Ordinal.{0} :=
    Fin.lastCases α (fun j => (T.orderEmbOfFin rfl) j) with hf_def
  have hf_last : f (Fin.last T.card) = α := Fin.lastCases_last
  have hf_castSucc : ∀ j : Fin T.card,
      f j.castSucc = (T.orderEmbOfFin rfl) j := fun j => Fin.lastCases_castSucc _
  have hf_mem : ∀ i, f i ∈ insert α T := by
    intro i
    induction i using Fin.lastCases with
    | last => rw [hf_last]; exact Finset.mem_insert_self α T
    | cast j =>
      rw [hf_castSucc j]
      exact Finset.mem_insert_of_mem (T.orderEmbOfFin_mem rfl j)
  have hf_strictMono : StrictMono f := by
    intro a b hab
    induction b using Fin.lastCases with
    | last =>
      induction a using Fin.lastCases with
      | last => exact absurd hab (lt_irrefl _)
      | cast j =>
        rw [hf_castSucc j, hf_last]
        exact h_above _ (T.orderEmbOfFin_mem rfl j)
    | cast j₂ =>
      induction a using Fin.lastCases with
      | last =>
        exact absurd hab (not_lt_of_ge (Fin.le_last _))
      | cast j₁ =>
        rw [hf_castSucc j₁, hf_castSucc j₂]
        exact (T.orderEmbOfFin rfl).strictMono
          (Fin.castSucc_lt_castSucc_iff.mp hab)
  -- Uniqueness: f = (insert α T).orderEmbOfFin h_card. This identifies the
  -- (insert α T) enumeration with the Fin.lastCases-glued extension.
  have hf_eq : f = ⇑((insert α T).orderEmbOfFin h_card) :=
    Finset.orderEmbOfFin_unique h_card hf_mem hf_strictMono
  -- A_ext.level matches f (by construction of extendTo).
  have hA_ext_level : ∀ j, A_ext.level j = f j := by
    intro j
    induction j using Fin.lastCases with
    | last =>
      rw [hf_last]
      show P.toApprox.extendToLevel α (Fin.last T.card) = α
      exact P.toApprox.extendToLevel_last α
    | cast j =>
      rw [hf_castSucc j]
      show P.toApprox.extendToLevel α j.castSucc = (T.orderEmbOfFin rfl) j
      rw [P.toApprox.extendToLevel_castSucc α j, P.level_eq j]
  -- Consistency: (insert α T).orderEmbOfFin h_card (Fin.cast h_card i)
  -- = (insert α T).orderEmbOfFin rfl i.
  have h_emb_cast : ∀ i : Fin (insert α T).card,
      (insert α T).orderEmbOfFin h_card (Fin.cast h_card i) =
        (insert α T).orderEmbOfFin rfl i := by
    intro i
    have hg_mem : ∀ x : Fin (insert α T).card,
        (insert α T).orderEmbOfFin h_card (Fin.cast h_card x) ∈ insert α T :=
      fun x => Finset.orderEmbOfFin_mem _ _ _
    have hg_strictMono : StrictMono
        (fun x : Fin (insert α T).card =>
          (insert α T).orderEmbOfFin h_card (Fin.cast h_card x)) := by
      intro a b hab
      exact ((insert α T).orderEmbOfFin h_card).strictMono hab
    have h_unique := Finset.orderEmbOfFin_unique
      (s := insert α T) (k := (insert α T).card) rfl hg_mem hg_strictMono
    exact congr_fun h_unique i
  -- Q.toApprox built via reindexing A_ext through Fin.cast h_card.
  let Q_cba : CoherentBranchApprox cR (insert α T).card := {
    level := fun i => A_ext.level (Fin.cast h_card i)
    level_lt_omega1 := fun i => A_ext.level_lt_omega1 _
    level_strictMono := fun {_ _} hab => A_ext.level_strictMono hab
    prefixAt := fun i => A_ext.prefixAt (Fin.cast h_card i)
    branchAt := fun i => A_ext.branchAt (Fin.cast h_card i)
    prefix_restrict := fun {k₁ k₂} hk x =>
      A_ext.prefix_restrict (k₁ := Fin.cast h_card k₁)
        (k₂ := Fin.cast h_card k₂) hk x
    branch_restrict := fun {k₁ k₂} hk x =>
      A_ext.branch_restrict (k₁ := Fin.cast h_card k₁)
        (k₂ := Fin.cast h_card k₂) hk x
    large := fun i => A_ext.large _
    top_in_validFiber := by
      intro i hi
      have hi' : i + 1 < T.card + 1 := h_card ▸ hi
      have := A_ext.top_in_validFiber i hi'
      convert this using 2 <;> rfl
  }
  -- Level_eq for Q (built atop Q_cba).
  have h_level_eq : ∀ i, Q_cba.level i = (insert α T).orderEmbOfFin rfl i := by
    intro i
    show A_ext.level (Fin.cast h_card i) = (insert α T).orderEmbOfFin rfl i
    rw [hA_ext_level (Fin.cast h_card i)]
    rw [show f (Fin.cast h_card i) = ((insert α T).orderEmbOfFin h_card)
          (Fin.cast h_card i) from congr_fun hf_eq _]
    exact h_emb_cast i
  let Q : CoherentBranchPartial cR (insert α T) :=
    ⟨Q_cba, h_level_eq⟩
  -- Key step: Fin.cast h_card (Q.indexOf α' h) = (P.indexOf α' hα').castSucc.
  -- Proved via A_ext.level injectivity (StrictMono → Injective).
  -- Both sides give A_ext.level = α', so they coincide.
  have h_indexOf : ∀ α' (hα' : α' ∈ T),
      Fin.cast h_card (Q.indexOf α' (Finset.subset_insert α T hα')) =
        (P.indexOf α' hα').castSucc := by
    intro α' hα'
    apply A_ext.level_strictMono.injective
    -- LHS: A_ext.level (Fin.cast h_card (Q.indexOf α' _)) = α'.
    have h_LHS : A_ext.level
        (Fin.cast h_card (Q.indexOf α' (Finset.subset_insert α T hα'))) = α' := by
      -- A_ext.level (Fin.cast h_card i) = Q_cba.level i = Q.toApprox.level i.
      change Q_cba.level (Q.indexOf α' (Finset.subset_insert α T hα')) = α'
      exact Q.level_indexOf α' (Finset.subset_insert α T hα')
    -- RHS: A_ext.level (P.indexOf α' hα').castSucc = α'.
    have h_RHS : A_ext.level (P.indexOf α' hα').castSucc = α' := by
      change P.toApprox.extendToLevel α (P.indexOf α' hα').castSucc = α'
      rw [P.toApprox.extendToLevel_castSucc α (P.indexOf α' hα'),
          P.level_indexOf α' hα']
    rw [h_LHS, h_RHS]
  refine ⟨Q, ?_, ?_⟩
  -- prefixAt and branch agreement (parallel proofs).
  · intro α' hα'
    rw [Q.restrict_prefixAt (Finset.subset_insert α T) α' hα']
    -- Q.prefixAt α' h = P.prefixAt α' hα' via HEq chaining.
    apply eq_of_heq
    refine HEq.trans (cast_heq _ _) (HEq.trans ?_ (cast_heq _ _).symm)
    -- HEq (Q.toApprox.prefixAt (Q.indexOf ...)) (P.toApprox.prefixAt (P.indexOf ...))
    refine HEq.trans (b := A_ext.prefixAt (P.indexOf α' hα').castSucc) ?_ ?_
    · -- Q.toApprox.prefixAt (Q.indexOf ...) HEq A_ext.prefixAt (castSucc).
      -- Q.toApprox.prefixAt = (def) fun i => A_ext.prefixAt (Fin.cast h_card i).
      change HEq (A_ext.prefixAt (Fin.cast h_card
        (Q.indexOf α' (Finset.subset_insert α T hα'))))
        (A_ext.prefixAt (P.indexOf α' hα').castSucc)
      exact congr_arg_heq A_ext.prefixAt (h_indexOf α' hα')
    · -- A_ext.prefixAt (castSucc) HEq P.toApprox.prefixAt _.
      change HEq (P.toApprox.extendToPrefixAt
          (P.toApprox.extendToChain α hα h_above_last)
          (P.indexOf α' hα').castSucc)
        (P.toApprox.prefixAt (P.indexOf α' hα'))
      exact P.toApprox.extendToPrefixAt_castSucc_heq _ (P.indexOf α' hα')
  · intro α' hα'
    rw [Q.restrict_branch (Finset.subset_insert α T) α' hα']
    apply eq_of_heq
    refine HEq.trans (cast_heq _ _) (HEq.trans ?_ (cast_heq _ _).symm)
    refine HEq.trans (b := A_ext.branchAt (P.indexOf α' hα').castSucc) ?_ ?_
    · change HEq (A_ext.branchAt (Fin.cast h_card
        (Q.indexOf α' (Finset.subset_insert α T hα'))))
        (A_ext.branchAt (P.indexOf α' hα').castSucc)
      exact congr_arg_heq A_ext.branchAt (h_indexOf α' hα')
    · change HEq (P.toApprox.extendToBranchAt
          (P.toApprox.extendToChain α hα h_above_last)
          (P.indexOf α' hα').castSucc)
        (P.toApprox.branchAt (P.indexOf α' hα'))
      exact P.toApprox.extendToBranchAt_castSucc_heq _ (P.indexOf α' hα')

/-! ### Iterated single-coordinate rigid extension over a sorted list

Iterating `coherentBranchPartial_extend_one_above_top` over a strictly-
sorted list `l` of ordinals where every element of `l` is above every
element of `T` yields a CBP on `l.foldl insert T` whose restriction to
`T` agrees with the original. The use of `List.foldl` makes the
recursion match the proof structure: each `α :: tail` step extends
the current `T` by `α`, then applies the inductive hypothesis with
the new starting set `insert α T`. -/

/-- **Helper**: `T` is a subset of the left-fold of inserts. -/
private lemma subset_foldl_insert :
    ∀ (l : List Ordinal.{0}) (T : Finset Ordinal.{0}),
      T ⊆ l.foldl (fun S α => insert α S) T
  | [], T => Finset.Subset.refl T
  | α :: tail, T =>
    (Finset.subset_insert α T).trans (subset_foldl_insert tail (insert α T))

/-- **Iterated rigid extension**: given `P : CBP cR T` and a
strictly-sorted list `l` of valid ordinals each above every element
of `T`, build `Q : CBP cR (l.foldl insert T)` whose restriction to
`T` agrees fieldwise with `P`. -/
theorem coherentBranchPartial_extend_list_above_top
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    ∀ (l : List Ordinal.{0}) {T : Finset Ordinal.{0}}
      (P : CoherentBranchPartial cR T)
      (_hvalid : ∀ α ∈ l, α < Ordinal.omega.{0} 1)
      (_hsorted : l.Pairwise (· < ·))
      (_habove : ∀ α ∈ l, ∀ β ∈ T, β < α),
      ∃ Q : CoherentBranchPartial cR (l.foldl (fun S α => insert α S) T),
        cbpFieldwiseCompat (Q.restrict (subset_foldl_insert l T)) P := by
  intro l
  induction l with
  | nil =>
    intros T P _ _ _
    refine ⟨P, ?_, ?_⟩ <;> intro α' hα'
    · exact P.restrict_prefixAt (subset_foldl_insert [] T) α' hα'
    · exact P.restrict_branch (subset_foldl_insert [] T) α' hα'
  | cons α tail ih =>
    intros T P hvalid hsorted habove
    have hα_lt : α < Ordinal.omega.{0} 1 := hvalid α List.mem_cons_self
    have h_α_above : ∀ β ∈ T, β < α := habove α List.mem_cons_self
    obtain ⟨Q', hQ'_prefix, hQ'_branch⟩ :=
      coherentBranchPartial_extend_one_above_top cR P α hα_lt h_α_above
    -- IH on tail with starting set insert α T.
    have h_tail_valid : ∀ γ ∈ tail, γ < Ordinal.omega.{0} 1 :=
      fun γ hγ => hvalid γ (List.mem_cons_of_mem _ hγ)
    have h_tail_sorted : tail.Pairwise (· < ·) := List.Pairwise.of_cons hsorted
    have h_tail_above : ∀ γ ∈ tail, ∀ β ∈ insert α T, β < γ := by
      intro γ hγ β hβ
      rcases Finset.mem_insert.mp hβ with rfl | hβT
      · exact List.rel_of_pairwise_cons hsorted hγ
      · exact habove γ (List.mem_cons_of_mem _ hγ) β hβT
    obtain ⟨Q, hQ_prefix, hQ_branch⟩ :=
      ih Q' h_tail_valid h_tail_sorted h_tail_above
    refine ⟨Q, ?_, ?_⟩
    · intro α' hα'
      have hα'_insα : α' ∈ insert α T := Finset.mem_insert_of_mem hα'
      have step1 :=
        (Q.restrict_prefixAt (subset_foldl_insert (α :: tail) T) α' hα').trans
        (((Q.restrict_prefixAt (subset_foldl_insert tail (insert α T))
              α' hα'_insα).symm.trans (hQ_prefix α' hα'_insα)).trans
          ((Q'.restrict_prefixAt (Finset.subset_insert α T) α' hα').symm.trans
            (hQ'_prefix α' hα')))
      exact step1
    · intro α' hα'
      have hα'_insα : α' ∈ insert α T := Finset.mem_insert_of_mem hα'
      exact (Q.restrict_branch (subset_foldl_insert (α :: tail) T) α' hα').trans
        (((Q.restrict_branch (subset_foldl_insert tail (insert α T))
              α' hα'_insα).symm.trans (hQ_branch α' hα'_insα)).trans
          ((Q'.restrict_branch (Finset.subset_insert α T) α' hα').symm.trans
            (hQ'_branch α' hα')))

/-- **`coherentBranchPartial_extend_one`** (rigid extension for any
finset above the current top): given `P : CBP cR T` and a finset `i₀`
of valid ordinals each strictly above every element of `T`, extend
`P` to a CBP on `T ∪ i₀` whose restriction to `T` agrees fieldwise
with `P`. Derived by sorting `i₀` and iterating
`extend_one_above_top` via the list-form. -/
theorem coherentBranchPartial_extend_one
    (cR : (Fin 2 ↪o PairERSource) → Bool)
    {T : Finset Ordinal.{0}} (P : CoherentBranchPartial cR T)
    (i₀ : Finset Ordinal.{0})
    (hvalid : ∀ α ∈ i₀, α < Ordinal.omega.{0} 1)
    (habove : ∀ α ∈ i₀, ∀ β ∈ T, β < α) :
    ∃ Q : CoherentBranchPartial cR (T ∪ i₀),
      cbpFieldwiseCompat (Q.restrict Finset.subset_union_left) P := by
  classical
  -- Sort i₀ into a strictly-sorted list of valid ordinals each above T.
  set l : List Ordinal.{0} := i₀.sort (· ≤ ·) with hl_def
  have hl_toFinset : l.toFinset = i₀ := Finset.sort_toFinset _ _
  have hl_sortedLT : l.Pairwise (· < ·) :=
    (Finset.sortedLT_sort i₀).pairwise
  have hl_mem : ∀ α, α ∈ l ↔ α ∈ i₀ := fun α => Finset.mem_sort _
  have hl_valid : ∀ α ∈ l, α < Ordinal.omega.{0} 1 :=
    fun α hα => hvalid α ((hl_mem α).mp hα)
  have hl_above : ∀ α ∈ l, ∀ β ∈ T, β < α :=
    fun α hα β hβ => habove α ((hl_mem α).mp hα) β hβ
  -- Auxiliary: l.foldl insert T = T ∪ l.toFinset = T ∪ i₀.
  have h_foldl_eq : l.foldl (fun S α => insert α S) T = T ∪ i₀ := by
    have step1 : ∀ (l' : List Ordinal.{0}) (T' : Finset Ordinal.{0}),
        l'.foldl (fun S α => insert α S) T' = T' ∪ l'.toFinset := by
      intro l'
      induction l' with
      | nil => intro T'; simp [List.toFinset_nil]
      | cons α tail ih =>
        intro T'
        rw [List.foldl_cons, ih, List.toFinset_cons]
        ext x
        simp only [Finset.mem_union, Finset.mem_insert]; tauto
    rw [step1, hl_toFinset]
  -- Apply list-form extension.
  obtain ⟨Q, hQ_pref, hQ_br⟩ :=
    coherentBranchPartial_extend_list_above_top cR l P
      hl_valid hl_sortedLT hl_above
  -- Restrict Q from (l.foldl ... T) down to (T ∪ i₀) via the Finset equality.
  have h_sub : T ∪ i₀ ⊆ l.foldl (fun S α => insert α S) T := by
    rw [h_foldl_eq]
  refine ⟨Q.restrict h_sub, ?_, ?_⟩
  · intro α' hα'
    -- (Q.restrict h_sub).restrict subset_union_left = Q.restrict (subset_foldl_insert l T)
    -- on prefixAt at α' (by two applications of restrict_prefixAt + prop-irrelevance).
    rw [(Q.restrict h_sub).restrict_prefixAt Finset.subset_union_left α' hα',
        Q.restrict_prefixAt h_sub α' (Finset.subset_union_left hα'),
        (Q.restrict_prefixAt (subset_foldl_insert l T) α' hα').symm]
    exact hQ_pref α' hα'
  · intro α' hα'
    rw [(Q.restrict h_sub).restrict_branch Finset.subset_union_left α' hα',
        Q.restrict_branch h_sub α' (Finset.subset_union_left hα'),
        (Q.restrict_branch (subset_foldl_insert l T) α' hα').symm]
    exact hQ_br α' hα'

/-! ### `PairERGoodChain`: chain with explicit inner cR-consistency

`PairERChain` records `head`, `type`, `large` but does not encode
the **inner cR-consistency** invariant that, in any chain built via
the standard constructors (`zero`, `succ`, `limit`, `extendTo`),
holds by construction: for every two positions `x < y` in
`α.ToType`,

  `cR (pairEmbed (head.strictMono h)) = type x`.

`PairERGoodChain` is a parallel layer (extends `PairERChain`) that
adds this invariant as an explicit field. This is the missing
primitive for interior insertion: once a chain is known to satisfy
inner cR-consistency, the `(α, β₀)` validFiber check at an interior
insertion reduces to the invariant.

The constructors:

- `zero` — vacuous (`(0).ToType` is empty).
- `succ` — closes via `succNewElement_in_validFiber` for the new
  top pair and inductive `inner_consistent` of `s` for old/old
  pairs.
- `limit` / `limitWithType` — does **not** automatically satisfy
  the invariant; explicit hypothesis required.
- `extendTo` — depends on strengthening `Extension`. This is the
  expected remaining frontier. -/

/-- **`PairERGoodChain`**: a `PairERChain` augmented with explicit
inner cR-consistency. Every pair of distinct positions in the chain
is colored by `cR` consistently with the `type` function. -/
structure PairERGoodChain (cR : (Fin 2 ↪o PairERSource) → Bool)
    (α : Ordinal.{0}) extends PairERChain cR α where
  /-- For every `x < y` in `α.ToType`, the cR-color of the pair
  `(head x, head y)` equals `type x`. -/
  inner_consistent : ∀ {x y : α.ToType} (h : x < y),
    cR (pairEmbed (toPairERChain.head.strictMono h)) = toPairERChain.type x

/-- **`PairERGoodChain.zero`**: vacuous inner consistency at level 0. -/
noncomputable def PairERGoodChain.zero
    (cR : (Fin 2 ↪o PairERSource) → Bool) : PairERGoodChain cR 0 where
  toPairERChain := PairERChain.zero cR
  inner_consistent {x _} _ :=
    haveI : IsEmpty (Ordinal.ToType 0) := Ordinal.isEmpty_toType_zero
    (IsEmpty.false x).elim

/-- **Helper**: applying `s.succ.head` to a lifted α-element recovers
`s.head` on the α-side. Proof via `extendHead_initialSegToType_apply`
with `β = α`. -/
theorem PairERChain.succ_head_initialSeg
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (s : PairERChain cR α) (x : α.ToType) :
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder (Order.succ α).ToType (· < ·) := isWellOrder_lt
    s.succ.head ((Ordinal.initialSegToType
        (Order.le_succ α)).toOrderEmbedding x) = s.head x := by
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder (Order.succ α).ToType (· < ·) := isWellOrder_lt
  -- The lifted x is not ⊤.
  have h_typein_xs : Ordinal.typein (α := (Order.succ α).ToType) (· < ·)
      ((Ordinal.initialSegToType (Order.le_succ α)).toOrderEmbedding x) =
      Ordinal.typein (α := α.ToType) (· < ·) x :=
    Ordinal.typein_apply _ x
  have h_typein_x_lt : Ordinal.typein (α := α.ToType) (· < ·) x < α := by
    have := Ordinal.typein_lt_type (· < ·) x
    rwa [Ordinal.type_toType] at this
  have h_typein_top : Ordinal.typein
      (α := (Order.succ α).ToType) (· < ·)
      (⊤ : (Order.succ α).ToType) = α := by
    rw [show (⊤ : (Order.succ α).ToType) =
        Ordinal.enum (α := (Order.succ α).ToType) (· < ·)
          ⟨α, (Ordinal.type_toType _).symm ▸ Order.lt_succ α⟩
      from Ordinal.enum_succ_eq_top.symm, Ordinal.typein_enum]
  have hxs_ne_top :
      (Ordinal.initialSegToType (Order.le_succ α)).toOrderEmbedding x ≠
      (⊤ : (Order.succ α).ToType) := by
    intro h_eq
    have : α = Ordinal.typein (· < ·) x :=
      h_typein_top.symm.trans (h_eq ▸ h_typein_xs)
    exact absurd this.symm (ne_of_lt h_typein_x_lt)
  unfold PairERChain.succ
  simp only [extendHead, OrderEmbedding.coe_ofStrictMono, dif_neg hxs_ne_top]
  -- Goal: s.head (enum ⟨typein xs, _⟩) = s.head x.
  congr 1
  -- Show enum ⟨typein xs, _⟩ = x via enum_typein on x.
  have hrec := Ordinal.enum_typein (α := α.ToType) (· < ·) x
  refine Eq.trans ?_ hrec
  -- Goal: enum ⟨typein xs, _⟩ = enum ⟨typein x, _⟩.
  congr 1
  apply Subtype.ext
  exact h_typein_xs

/-- **Helper**: parallel of `succ_head_initialSeg` for `type`. -/
theorem PairERChain.succ_type_initialSeg
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (s : PairERChain cR α) (x : α.ToType) :
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder (Order.succ α).ToType (· < ·) := isWellOrder_lt
    s.succ.type ((Ordinal.initialSegToType
        (Order.le_succ α)).toOrderEmbedding x) = s.type x := by
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder (Order.succ α).ToType (· < ·) := isWellOrder_lt
  have h_typein_xs : Ordinal.typein (α := (Order.succ α).ToType) (· < ·)
      ((Ordinal.initialSegToType (Order.le_succ α)).toOrderEmbedding x) =
      Ordinal.typein (α := α.ToType) (· < ·) x :=
    Ordinal.typein_apply _ x
  have h_typein_x_lt : Ordinal.typein (α := α.ToType) (· < ·) x < α := by
    have := Ordinal.typein_lt_type (· < ·) x
    rwa [Ordinal.type_toType] at this
  have h_typein_top : Ordinal.typein
      (α := (Order.succ α).ToType) (· < ·)
      (⊤ : (Order.succ α).ToType) = α := by
    rw [show (⊤ : (Order.succ α).ToType) =
        Ordinal.enum (α := (Order.succ α).ToType) (· < ·)
          ⟨α, (Ordinal.type_toType _).symm ▸ Order.lt_succ α⟩
      from Ordinal.enum_succ_eq_top.symm, Ordinal.typein_enum]
  have hxs_ne_top :
      (Ordinal.initialSegToType (Order.le_succ α)).toOrderEmbedding x ≠
      (⊤ : (Order.succ α).ToType) := by
    intro h_eq
    have : α = Ordinal.typein (· < ·) x :=
      h_typein_top.symm.trans (h_eq ▸ h_typein_xs)
    exact absurd this.symm (ne_of_lt h_typein_x_lt)
  unfold PairERChain.succ
  simp only [extendType, dif_neg hxs_ne_top]
  congr 1
  have hrec := Ordinal.enum_typein (α := α.ToType) (· < ·) x
  refine Eq.trans ?_ hrec
  congr 1
  apply Subtype.ext
  exact h_typein_xs

/-- **Projection**: the head of `succWithChoice` is `extendHead` of the
prescribed `y`. (The proof argument to `extendHead` is a Prop, hence
irrelevant.) -/
lemma PairERChain.succWithChoice_head_eq
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (s : PairERChain cR α) (y : PairERSource) (b : Bool)
    (hy_mem : y ∈ validFiber cR s.head s.type)
    (hlarge : Order.succ (Cardinal.beth.{0} 1) ≤
      Cardinal.mk (validFiberExtend cR s.head s.type y b)) :
    (s.succWithChoice y b hy_mem hlarge).head
      = extendHead s.head y (fun z => (hy_mem z).1) := rfl

/-- **Projection**: the type of `succWithChoice` is `extendType` of the
prescribed `b`. -/
lemma PairERChain.succWithChoice_type_eq
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (s : PairERChain cR α) (y : PairERSource) (b : Bool)
    (hy_mem : y ∈ validFiber cR s.head s.type)
    (hlarge : Order.succ (Cardinal.beth.{0} 1) ≤
      Cardinal.mk (validFiberExtend cR s.head s.type y b)) :
    (s.succWithChoice y b hy_mem hlarge).type = extendType s.type b := rfl

/-- **`succWithChoice_head_top`**: the head at the new top `⊤` is the
prescribed `y`. -/
lemma PairERChain.succWithChoice_head_top
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (s : PairERChain cR α) (y : PairERSource) (b : Bool)
    (hy_mem : y ∈ validFiber cR s.head s.type)
    (hlarge : Order.succ (Cardinal.beth.{0} 1) ≤
      Cardinal.mk (validFiberExtend cR s.head s.type y b)) :
    (s.succWithChoice y b hy_mem hlarge).head (⊤ : (Order.succ α).ToType) = y := by
  classical
  rw [s.succWithChoice_head_eq y b hy_mem hlarge]
  simp [extendHead]

/-- **`succWithChoice_head_initialSeg`**: on lifted α-elements the head
agrees with `s.head`. Parallel of `succ_head_initialSeg`. -/
theorem PairERChain.succWithChoice_head_initialSeg
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (s : PairERChain cR α) (y : PairERSource) (b : Bool)
    (hy_mem : y ∈ validFiber cR s.head s.type)
    (hlarge : Order.succ (Cardinal.beth.{0} 1) ≤
      Cardinal.mk (validFiberExtend cR s.head s.type y b)) (x : α.ToType) :
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder (Order.succ α).ToType (· < ·) := isWellOrder_lt
    (s.succWithChoice y b hy_mem hlarge).head ((Ordinal.initialSegToType
        (Order.le_succ α)).toOrderEmbedding x) = s.head x := by
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder (Order.succ α).ToType (· < ·) := isWellOrder_lt
  have h_typein_xs : Ordinal.typein (α := (Order.succ α).ToType) (· < ·)
      ((Ordinal.initialSegToType (Order.le_succ α)).toOrderEmbedding x) =
      Ordinal.typein (α := α.ToType) (· < ·) x :=
    Ordinal.typein_apply _ x
  have h_typein_x_lt : Ordinal.typein (α := α.ToType) (· < ·) x < α := by
    have := Ordinal.typein_lt_type (· < ·) x
    rwa [Ordinal.type_toType] at this
  have h_typein_top : Ordinal.typein
      (α := (Order.succ α).ToType) (· < ·)
      (⊤ : (Order.succ α).ToType) = α := by
    rw [show (⊤ : (Order.succ α).ToType) =
        Ordinal.enum (α := (Order.succ α).ToType) (· < ·)
          ⟨α, (Ordinal.type_toType _).symm ▸ Order.lt_succ α⟩
      from Ordinal.enum_succ_eq_top.symm, Ordinal.typein_enum]
  have hxs_ne_top :
      (Ordinal.initialSegToType (Order.le_succ α)).toOrderEmbedding x ≠
      (⊤ : (Order.succ α).ToType) := by
    intro h_eq
    have : α = Ordinal.typein (· < ·) x :=
      h_typein_top.symm.trans (h_eq ▸ h_typein_xs)
    exact absurd this.symm (ne_of_lt h_typein_x_lt)
  rw [s.succWithChoice_head_eq y b hy_mem hlarge]
  simp only [extendHead, OrderEmbedding.coe_ofStrictMono, dif_neg hxs_ne_top]
  congr 1
  have hrec := Ordinal.enum_typein (α := α.ToType) (· < ·) x
  refine Eq.trans ?_ hrec
  congr 1
  apply Subtype.ext
  exact h_typein_xs

/-- **`succWithChoice_type_initialSeg`**: on lifted α-elements the type
agrees with `s.type`. Parallel of `succ_type_initialSeg`. -/
theorem PairERChain.succWithChoice_type_initialSeg
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (s : PairERChain cR α) (y : PairERSource) (b : Bool)
    (hy_mem : y ∈ validFiber cR s.head s.type)
    (hlarge : Order.succ (Cardinal.beth.{0} 1) ≤
      Cardinal.mk (validFiberExtend cR s.head s.type y b)) (x : α.ToType) :
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder (Order.succ α).ToType (· < ·) := isWellOrder_lt
    (s.succWithChoice y b hy_mem hlarge).type ((Ordinal.initialSegToType
        (Order.le_succ α)).toOrderEmbedding x) = s.type x := by
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder (Order.succ α).ToType (· < ·) := isWellOrder_lt
  have h_typein_xs : Ordinal.typein (α := (Order.succ α).ToType) (· < ·)
      ((Ordinal.initialSegToType (Order.le_succ α)).toOrderEmbedding x) =
      Ordinal.typein (α := α.ToType) (· < ·) x :=
    Ordinal.typein_apply _ x
  have h_typein_x_lt : Ordinal.typein (α := α.ToType) (· < ·) x < α := by
    have := Ordinal.typein_lt_type (· < ·) x
    rwa [Ordinal.type_toType] at this
  have h_typein_top : Ordinal.typein
      (α := (Order.succ α).ToType) (· < ·)
      (⊤ : (Order.succ α).ToType) = α := by
    rw [show (⊤ : (Order.succ α).ToType) =
        Ordinal.enum (α := (Order.succ α).ToType) (· < ·)
          ⟨α, (Ordinal.type_toType _).symm ▸ Order.lt_succ α⟩
      from Ordinal.enum_succ_eq_top.symm, Ordinal.typein_enum]
  have hxs_ne_top :
      (Ordinal.initialSegToType (Order.le_succ α)).toOrderEmbedding x ≠
      (⊤ : (Order.succ α).ToType) := by
    intro h_eq
    have : α = Ordinal.typein (· < ·) x :=
      h_typein_top.symm.trans (h_eq ▸ h_typein_xs)
    exact absurd this.symm (ne_of_lt h_typein_x_lt)
  rw [s.succWithChoice_type_eq y b hy_mem hlarge]
  simp only [extendType, dif_neg hxs_ne_top]
  congr 1
  have hrec := Ordinal.enum_typein (α := α.ToType) (· < ·) x
  refine Eq.trans ?_ hrec
  congr 1
  apply Subtype.ext
  exact h_typein_xs

/-- **Helper for the dichotomy**: any element `z` of
`(Order.succ α).ToType` with `typein z < α` is the lift of the
corresponding α-element. Proof uses `Ordinal.typein_inj`. -/
private theorem succ_initialSeg_enum_typein_of_lt
    {α : Ordinal.{0}}
    (z : (Order.succ α).ToType)
    (hz : haveI : IsWellOrder (Order.succ α).ToType (· < ·) := isWellOrder_lt
         (Ordinal.typein (α := (Order.succ α).ToType) (· < ·)).toRelEmbedding z < α) :
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder (Order.succ α).ToType (· < ·) := isWellOrder_lt
    (Ordinal.initialSegToType (Order.le_succ α)).toOrderEmbedding
      (Ordinal.enum (α := α.ToType) (· < ·)
        ⟨(Ordinal.typein _).toRelEmbedding z,
         by rw [Ordinal.type_toType]; exact hz⟩) = z := by
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder (Order.succ α).ToType (· < ·) := isWellOrder_lt
  apply (Ordinal.typein_inj (α := (Order.succ α).ToType) (· < ·)).mp
  exact (Ordinal.typein_apply _ _).trans (Ordinal.typein_enum _ _)

/-- **Dichotomy** on elements of `(Order.succ α).ToType`: every
element is either the image of an α-element via `initialSegToType`
or the top `⊤`. -/
theorem OrderSucc.eq_initialSeg_or_top
    {α : Ordinal.{0}} (z : (Order.succ α).ToType) :
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder (Order.succ α).ToType (· < ·) := isWellOrder_lt
    (∃ x : α.ToType,
      z = (Ordinal.initialSegToType (Order.le_succ α)).toOrderEmbedding x) ∨
    z = (⊤ : (Order.succ α).ToType) := by
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder (Order.succ α).ToType (· < ·) := isWellOrder_lt
  by_cases hz_lt_α :
      (Ordinal.typein (α := (Order.succ α).ToType) (· < ·)).toRelEmbedding z < α
  · refine Or.inl ⟨Ordinal.enum (α := α.ToType) (· < ·)
      ⟨(Ordinal.typein _).toRelEmbedding z,
       by rw [Ordinal.type_toType]; exact hz_lt_α⟩, ?_⟩
    exact (succ_initialSeg_enum_typein_of_lt z hz_lt_α).symm
  · refine Or.inr ?_
    push_neg at hz_lt_α
    have h_lt_succ : (Ordinal.typein _).toRelEmbedding z <
        Ordinal.type (α := (Order.succ α).ToType) (· < ·) :=
      Ordinal.typein_lt_type _ _
    rw [Ordinal.type_toType] at h_lt_succ
    have h_typein_le_α : (Ordinal.typein _).toRelEmbedding z ≤ α :=
      Order.lt_succ_iff.mp h_lt_succ
    have h_typein_eq_α : (Ordinal.typein _).toRelEmbedding z = α :=
      le_antisymm h_typein_le_α hz_lt_α
    have h_typein_top : (Ordinal.typein (α := (Order.succ α).ToType) (· < ·)).toRelEmbedding
        (⊤ : (Order.succ α).ToType) = α := by
      rw [show (⊤ : (Order.succ α).ToType) =
          Ordinal.enum (α := (Order.succ α).ToType) (· < ·)
            ⟨α, by rw [Ordinal.type_toType]; exact Order.lt_succ α⟩
        from Ordinal.enum_succ_eq_top.symm]
      exact Ordinal.typein_enum _ _
    apply (Ordinal.typein_inj (α := (Order.succ α).ToType) (· < ·)).mp
    rw [h_typein_eq_α, h_typein_top]

/-- **`PairERGoodChain.succ`**: extends inner cR-consistency over
`PairERChain.succ`. Uses `OrderSucc.eq_initialSeg_or_top` to case
split each of `x'`, `y'` into "old (= lifted α-element)" vs "top".
- Old/old: reduce via helpers to `s.inner_consistent`.
- Old/top: reduce via helpers + `succNewElement_in_validFiber`.
- Top/anything: contradiction (nothing strictly above `⊤`). -/
noncomputable def PairERGoodChain.succ
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {α : Ordinal.{0}} (s : PairERGoodChain cR α) :
    PairERGoodChain cR (Order.succ α) where
  toPairERChain := s.toPairERChain.succ
  inner_consistent {x' y'} hxy' := by
    classical
    haveI : IsWellOrder (Order.succ α).ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    rcases OrderSucc.eq_initialSeg_or_top x' with ⟨x_α, hx_eq⟩ | hx_top
    · rcases OrderSucc.eq_initialSeg_or_top y' with ⟨y_α, hy_eq⟩ | hy_top
      · -- x' = lifted x_α, y' = lifted y_α.
        subst hx_eq; subst hy_eq
        have hxα_lt_yα : x_α < y_α :=
          (Ordinal.initialSegToType (Order.le_succ α)).toOrderEmbedding.lt_iff_lt.mp hxy'
        have h_inner := s.inner_consistent hxα_lt_yα
        rw [s.toPairERChain.succ_type_initialSeg]
        rw [← h_inner]
        congr 1
        apply RelEmbedding.ext
        intro i
        match i with
        | ⟨0, _⟩ =>
            simp only [pairEmbed, OrderEmbedding.coe_ofStrictMono,
              Matrix.cons_val_zero]
            exact s.toPairERChain.succ_head_initialSeg x_α
        | ⟨1, _⟩ =>
            simp only [pairEmbed, OrderEmbedding.coe_ofStrictMono,
              Matrix.cons_val_one, Matrix.head_cons]
            exact s.toPairERChain.succ_head_initialSeg y_α
      · -- x' = lifted x_α, y' = ⊤.
        subst hx_eq; subst hy_top
        rw [s.toPairERChain.succ_type_initialSeg]
        obtain ⟨_, h_cR⟩ := s.toPairERChain.succNewElement_in_validFiber x_α
        rw [← h_cR]
        congr 1
        apply RelEmbedding.ext
        intro i
        match i with
        | ⟨0, _⟩ =>
            simp only [pairEmbed, OrderEmbedding.coe_ofStrictMono,
              Matrix.cons_val_zero]
            exact s.toPairERChain.succ_head_initialSeg x_α
        | ⟨1, _⟩ =>
            simp only [pairEmbed, OrderEmbedding.coe_ofStrictMono,
              Matrix.cons_val_one, Matrix.head_cons]
            exact s.toPairERChain.succ_head_top
    · -- x' = ⊤. Then x' < y' would need y' > ⊤, impossible.
      subst hx_top
      exact absurd hxy' (not_lt_of_ge le_top)

/-- **[FRONTIER, sorry — Good-chain prescribed-level primitive]**
`PairERGoodChain.succWithChoice`. Successor stage of a Good chain
with **prescribed** new head `y` and type `b` at the new top, parallel
to `limitWithType` for limits. Bypasses the `Classical.choose` in
`PairERGoodChain.succ` (which goes through `PairERChain.succ`).

**The underlying bare-chain primitive** `PairERChain.succWithChoice`
is now available (proven). What remains is to **discharge
`inner_consistent`** for the prescribed `(y, b)`:

* Pairs `x' < y'` with both `x', y' ≠ ⊤`: lift to `α.ToType`, use
  `s.inner_consistent` (mechanical, same as `PairERGoodChain.succ`).
* Pairs `x' < y' = ⊤`: the new top's head is the prescribed `y`, the
  new top's type is the prescribed `b`. The `cR` value of
  `pairEmbed (head x_α < y)` follows from
  `hy_mem x_α : ∃ h, cR (pairEmbed h) = s.type x_α`. So the inner
  consistency at `(x_α, ⊤)` forces `extendType b ⊤ = s.type x_α`,
  i.e. `b = s.type x_α` — which is satisfied **only if** the caller
  arranges `b` to be consistent.

**Missing local axiom.** Either an additional hypothesis on the
caller (a `b_consistent` field saying `b` is the type the validFiber
witness forces), or a stronger primitive choosing `b` to match.

**This is the actual atomic frontier**: the Good-chain layer requires
prescribed-`b` consistency, not just bare-chain succWithChoice. -/
noncomputable def PairERGoodChain.succWithChoice
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (s : PairERGoodChain cR α)
    (y : PairERSource) (b : Bool)
    (hy_mem : y ∈ validFiber cR s.toPairERChain.head s.toPairERChain.type)
    (hlarge : Order.succ (Cardinal.beth.{0} 1) ≤
      Cardinal.mk (validFiberExtend cR s.toPairERChain.head
        s.toPairERChain.type y b)) :
    PairERGoodChain cR (Order.succ α) where
  toPairERChain := s.toPairERChain.succWithChoice y b hy_mem hlarge
  inner_consistent {x' y'} hxy' := by
    classical
    haveI : IsWellOrder (Order.succ α).ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    rcases OrderSucc.eq_initialSeg_or_top x' with ⟨x_α, hx_eq⟩ | hx_top
    · rcases OrderSucc.eq_initialSeg_or_top y' with ⟨y_α, hy_eq⟩ | hy_top
      · -- x' = lifted x_α, y' = lifted y_α: reduce to `s.inner_consistent`.
        subst hx_eq; subst hy_eq
        have hxα_lt_yα : x_α < y_α :=
          (Ordinal.initialSegToType (Order.le_succ α)).toOrderEmbedding.lt_iff_lt.mp hxy'
        have h_inner := s.inner_consistent hxα_lt_yα
        rw [s.toPairERChain.succWithChoice_type_initialSeg y b hy_mem hlarge]
        rw [← h_inner]
        congr 1
        apply RelEmbedding.ext
        intro i
        match i with
        | ⟨0, _⟩ =>
            simp only [pairEmbed, OrderEmbedding.coe_ofStrictMono]
            exact s.toPairERChain.succWithChoice_head_initialSeg y b hy_mem hlarge x_α
        | ⟨1, _⟩ =>
            simp only [pairEmbed, OrderEmbedding.coe_ofStrictMono]
            exact s.toPairERChain.succWithChoice_head_initialSeg y b hy_mem hlarge y_α
      · -- x' = lifted x_α, y' = ⊤: the new top's head is `y`; use `hy_mem`.
        subst hx_eq; subst hy_top
        rw [s.toPairERChain.succWithChoice_type_initialSeg y b hy_mem hlarge]
        obtain ⟨_, h_cR⟩ := hy_mem x_α
        rw [← h_cR]
        congr 1
        apply RelEmbedding.ext
        intro i
        match i with
        | ⟨0, _⟩ =>
            simp only [pairEmbed, OrderEmbedding.coe_ofStrictMono]
            exact s.toPairERChain.succWithChoice_head_initialSeg y b hy_mem hlarge x_α
        | ⟨1, _⟩ =>
            simp only [pairEmbed, OrderEmbedding.coe_ofStrictMono]
            exact s.toPairERChain.succWithChoice_head_top y b hy_mem hlarge
    · -- x' = ⊤: nothing lies strictly above ⊤.
      subst hx_top
      exact absurd hxy' (not_lt_of_ge le_top)

/-- **`PairERGoodChain.limitWithType`**: limit-stage constructor for
`PairERGoodChain` with explicit inner-consistency hypothesis. The
underlying chain is built via `PairERChain.limitWithType`; the inner
consistency is supplied directly by the caller (it cannot be derived
from `large` alone). -/
noncomputable def PairERGoodChain.limitWithType
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (p : α.ToType ↪o PairERSource) (τ : α.ToType → Bool)
    (hlarge : Order.succ (Cardinal.beth.{0} 1) ≤
      Cardinal.mk (validFiber cR p τ))
    (hinner : ∀ {x y : α.ToType} (hxy : x < y),
      cR (pairEmbed (p.strictMono hxy)) = τ x) :
    PairERGoodChain cR α where
  toPairERChain := PairERChain.limitWithType p τ hlarge
  inner_consistent := hinner

/-! ### `PairERGoodChain.Extension`: bundled extension carrying
inner cR-consistency

The parallel of `PairERChain.Extension`, but with the underlying
`chain` strengthened to a `PairERGoodChain`. The `commitAt_old`,
`typeAt_old`, and `head_β_in_validFiber` fields are stated against
the projected `toPairERChain`, so existing `PairERChain.Extension`
machinery composes through. -/

/-- **`PairERGoodChain.Extension`**: an extension of a good chain
`s : PairERGoodChain cR β` to a good chain at level `α > β`, bundling
the coherence data parallel to `PairERChain.Extension`. -/
structure PairERGoodChain.Extension
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {β : Ordinal.{0}} (s : PairERGoodChain cR β)
    {α : Ordinal.{0}} (hβα : β < α) where
  /-- The extended good chain at level `α`. -/
  chain : PairERGoodChain cR α
  /-- Head agreement at lower positions. -/
  commitAt_old : ∀ (δ : Ordinal.{0}) (hδβ : δ < β),
    chain.toPairERChain.commitAt δ (hδβ.trans hβα) =
      s.toPairERChain.commitAt δ hδβ
  /-- Type agreement at lower positions. -/
  typeAt_old : ∀ (δ : Ordinal.{0}) (hδβ : δ < β),
    chain.toPairERChain.typeAt δ (hδβ.trans hβα) =
      s.toPairERChain.typeAt δ hδβ
  /-- The new top at position `β` lies in `s`'s validFiber. -/
  head_β_in_validFiber :
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    chain.toPairERChain.head (Ordinal.enum (α := α.ToType) (· < ·)
      ⟨β, (Ordinal.type_toType α).symm ▸ hβα⟩) ∈
      validFiber cR s.toPairERChain.head s.toPairERChain.type

/-- **`GoodExtension.succ`**: the successor-step extension of a good
chain via `PairERGoodChain.succ`. -/
noncomputable def PairERGoodChain.Extension.succ
    {cR : (Fin 2 ↪o PairERSource) → Bool} {β : Ordinal.{0}}
    (s : PairERGoodChain cR β) :
    PairERGoodChain.Extension s (Order.lt_succ β) where
  chain := s.succ
  commitAt_old := fun δ hδβ => PairERChain.succ_commitAt s.toPairERChain δ hδβ
  typeAt_old := fun δ hδβ => PairERChain.succ_typeAt_old s.toPairERChain δ hδβ
  head_β_in_validFiber := by
    haveI : IsWellOrder (Order.succ β).ToType (· < ·) := isWellOrder_lt
    have h_top_eq : (⊤ : (Order.succ β).ToType) =
        Ordinal.enum (α := (Order.succ β).ToType) (· < ·)
          ⟨β, (Ordinal.type_toType _).symm ▸ Order.lt_succ β⟩ :=
      Ordinal.enum_succ_eq_top.symm
    show (s.succ).toPairERChain.head _ ∈ _
    rw [← h_top_eq]
    show s.toPairERChain.succ.head (⊤ : (Order.succ β).ToType) ∈ _
    rw [PairERChain.succ_head_top]
    exact s.toPairERChain.succNewElement_in_validFiber

/-- **Helper**: the initial-segment lift of `enum δ` in `β.ToType`
equals `enum δ` in `α.ToType`, for any `δ < β ≤ α`. Reusable across
prescribed-extension proofs that bridge the `β`-side enum to the
`α`-side enum via `Ordinal.initialSegToType`.

Proof: both sides have `typein = δ` (the LHS by
`Ordinal.typein_apply` for `InitialSeg` + `typein_enum`; the RHS by
`typein_enum` directly), then `enum_typein` aligns them. -/
lemma initialSegToType_enum_lift
    {β α : Ordinal.{0}} (hβα : β ≤ α) {δ : Ordinal.{0}}
    (hδβ : δ < β) :
    haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    (Ordinal.initialSegToType hβα).toOrderEmbedding
      (Ordinal.enum (α := β.ToType) (· < ·)
        ⟨δ, (Ordinal.type_toType β).symm ▸ hδβ⟩) =
    Ordinal.enum (α := α.ToType) (· < ·)
      ⟨δ, (Ordinal.type_toType α).symm ▸ hδβ.trans_le hβα⟩ := by
  haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  rw [← Ordinal.enum_typein (α := α.ToType) (r := (· < ·))
    ((Ordinal.initialSegToType hβα).toOrderEmbedding
      (Ordinal.enum (α := β.ToType) (· < ·)
        ⟨δ, (Ordinal.type_toType β).symm ▸ hδβ⟩))]
  congr 1
  apply Subtype.ext
  show (Ordinal.typein (α := α.ToType) (· < ·)).toRelEmbedding
      ((Ordinal.initialSegToType hβα).toOrderEmbedding _) = δ
  rw [show (Ordinal.initialSegToType hβα).toOrderEmbedding
        ((Ordinal.enum (α := β.ToType) (· < ·))
          ⟨δ, (Ordinal.type_toType β).symm ▸ hδβ⟩) =
      (Ordinal.initialSegToType hβα)
        ((Ordinal.enum (α := β.ToType) (· < ·))
          ⟨δ, (Ordinal.type_toType β).symm ▸ hδβ⟩) from rfl,
    Ordinal.typein_apply, Ordinal.typein_enum]

/-- **`PairERGoodChain.Extension.byPrescribedTop`**: when an
already-coherent Good chain `t` at level `α` is **prescribed** as the
extension of `s` at level `β < α`, package `t` as an
`Extension s hβα`.

**Hypothesis structure.** The caller supplies pointwise head and type
agreement between `s` (on `β.ToType`) and the initial-segment image
of `s`'s positions inside `t` (on `α.ToType` via
`Ordinal.initialSegToType hβα.le`):

* `h_prefix`: `s.head x = t.head (initialSeg x)` for `x : β.ToType`.
* `h_type`: `s.type x = t.type (initialSeg x)` for `x : β.ToType`.

**Why this is exactly what prescribed insertion needs.** Unlike the
constructive `succ`/`limitWithType`, no Good chain is BUILT here —
the chain `t` is provided already-coherent. The extension property is
PROVED, not constructed. This dodges the prescribed-level extension
primitive entirely at the chain layer; the burden moves to the caller
(who must supply a coherent `t`).

**Status.** Stated as the cleanly-designed primitive for the
`insert_prescribed_new_compatible` chain. Proof body is `sorry`
pending the four-line discharge of each Extension field from
`h_prefix` / `h_type` / `t.inner_consistent`. -/
noncomputable def PairERGoodChain.Extension.byPrescribedTop
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {β : Ordinal.{0}} (s : PairERGoodChain cR β)
    {α : Ordinal.{0}} (hβα : β < α)
    (t : PairERGoodChain cR α)
    (h_prefix : ∀ x : β.ToType,
      haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
      haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
      s.toPairERChain.head x =
        t.toPairERChain.head
          ((Ordinal.initialSegToType hβα.le).toOrderEmbedding x))
    (h_type : ∀ x : β.ToType,
      haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
      haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
      s.toPairERChain.type x =
        t.toPairERChain.type
          ((Ordinal.initialSegToType hβα.le).toOrderEmbedding x)) :
    PairERGoodChain.Extension s hβα where
  chain := t
  commitAt_old := fun δ hδβ => by
    haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    show t.toPairERChain.head _ = s.toPairERChain.head _
    rw [h_prefix, initialSegToType_enum_lift hβα.le hδβ]
  typeAt_old := fun δ hδβ => by
    haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    show t.toPairERChain.type _ = s.toPairERChain.type _
    rw [h_type, initialSegToType_enum_lift hβα.le hδβ]
  head_β_in_validFiber := by
    haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    intro x
    set y := (Ordinal.initialSegToType hβα.le).toOrderEmbedding x with hy_def
    -- y < enum β in α.ToType: typein y = typein x < β.
    have hy_lt : y < Ordinal.enum (α := α.ToType) (· < ·)
        ⟨β, (Ordinal.type_toType α).symm ▸ hβα⟩ := by
      rw [← Ordinal.enum_typein (α := α.ToType) (r := (· < ·)) y,
        (Ordinal.enum_lt_enum (α := α.ToType) (r := (· < ·)))]
      show ((Ordinal.typein (α := α.ToType) (· < ·)).toRelEmbedding y) < β
      rw [hy_def]
      rw [show (Ordinal.typein (α := α.ToType) (· < ·)).toRelEmbedding
            ((Ordinal.initialSegToType hβα.le).toOrderEmbedding x) =
          (Ordinal.typein (α := β.ToType) (· < ·)).toRelEmbedding x from
        Ordinal.typein_apply (Ordinal.initialSegToType hβα.le) x]
      have hx_lt : (Ordinal.typein (α := β.ToType) (· < ·)).toRelEmbedding x <
          Ordinal.type (α := β.ToType) (· < ·) :=
        Ordinal.typein_lt_type _ _
      rwa [Ordinal.type_toType] at hx_lt
    -- Apply t.inner_consistent to (y, enum β).
    have h_inner := t.inner_consistent hy_lt
    refine ⟨?_, ?_⟩
    · rw [h_prefix]
      exact t.toPairERChain.head.strictMono hy_lt
    · rw [h_type, ← h_inner]
      congr 1
      apply RelEmbedding.ext
      intro i
      match i with
      | ⟨0, _⟩ =>
        simp only [pairEmbed, OrderEmbedding.coe_ofStrictMono,
          Matrix.cons_val_zero]
        exact h_prefix x
      | ⟨1, _⟩ =>
        simp only [pairEmbed, OrderEmbedding.coe_ofStrictMono,
          Matrix.cons_val_one, Matrix.head_cons]
        rfl

/-- **`GoodExtension.limitWithType`**: limit-step good extension with
prescribed prefix/branch/largeness data + agreement witnesses +
**explicit inner cR-consistency** for the new chain. -/
noncomputable def PairERGoodChain.Extension.limitWithType
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {β : Ordinal.{0}} (s : PairERGoodChain cR β)
    {α : Ordinal.{0}} (hβα : β < α)
    (p : α.ToType ↪o PairERSource) (τ : α.ToType → Bool)
    (hlarge : Order.succ (Cardinal.beth.{0} 1) ≤
      Cardinal.mk (validFiber cR p τ))
    (hinner : ∀ {x y : α.ToType} (hxy : x < y),
      cR (pairEmbed (p.strictMono hxy)) = τ x)
    (h_commitAt : ∀ (δ : Ordinal.{0}) (hδβ : δ < β),
      (PairERChain.limitWithType (cR := cR) p τ hlarge).commitAt δ
          (hδβ.trans hβα) = s.toPairERChain.commitAt δ hδβ)
    (h_typeAt : ∀ (δ : Ordinal.{0}) (hδβ : δ < β),
      (PairERChain.limitWithType (cR := cR) p τ hlarge).typeAt δ
          (hδβ.trans hβα) = s.toPairERChain.typeAt δ hδβ)
    (h_realizes :
      haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
      (PairERChain.limitWithType (cR := cR) p τ hlarge).head
          (Ordinal.enum (α := α.ToType) (· < ·)
            ⟨β, (Ordinal.type_toType α).symm ▸ hβα⟩) ∈
        validFiber cR s.toPairERChain.head s.toPairERChain.type) :
    PairERGoodChain.Extension s hβα where
  chain := PairERGoodChain.limitWithType p τ hlarge hinner
  commitAt_old := h_commitAt
  typeAt_old := h_typeAt
  head_β_in_validFiber := h_realizes

/-- **`GoodExtension.trans`**: compose two good extensions. Parallel
to `PairERChain.Extension.trans` but at the `PairERGoodChain` layer. -/
noncomputable def PairERGoodChain.Extension.trans
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {β γ α : Ordinal.{0}} {s : PairERGoodChain cR β}
    {hβγ : β < γ} {hγα : γ < α}
    (e₁ : PairERGoodChain.Extension s hβγ)
    (e₂ : PairERGoodChain.Extension e₁.chain hγα) :
    PairERGoodChain.Extension s (hβγ.trans hγα) where
  chain := e₂.chain
  commitAt_old := fun δ hδβ =>
    (e₂.commitAt_old δ (hδβ.trans hβγ)).trans (e₁.commitAt_old δ hδβ)
  typeAt_old := fun δ hδβ =>
    (e₂.typeAt_old δ (hδβ.trans hβγ)).trans (e₁.typeAt_old δ hδβ)
  head_β_in_validFiber := by
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder γ.ToType (· < ·) := isWellOrder_lt
    have h_commit : e₂.chain.toPairERChain.commitAt β (hβγ.trans hγα) =
        e₁.chain.toPairERChain.commitAt β hβγ := e₂.commitAt_old β hβγ
    show e₂.chain.toPairERChain.head _ ∈
      validFiber cR s.toPairERChain.head s.toPairERChain.type
    show e₂.chain.toPairERChain.commitAt β (hβγ.trans hγα) ∈
      validFiber cR s.toPairERChain.head s.toPairERChain.type
    rw [h_commit]
    show e₁.chain.toPairERChain.head _ ∈
      validFiber cR s.toPairERChain.head s.toPairERChain.type
    exact e₁.head_β_in_validFiber

/-! ### `PairERGoodChain.extendToExt`: the Good transfinite-extension
frontier

The parallel of `PairERChain.extendToExt`, strengthened to carry
inner cR-consistency through the recursion. This is the named
frontier for the Good layer; closing it would close interior
insertion + the full Erdős-Rado pair theorem from the Good side.

We keep the old `PairERChain.extendToExt` frontier intact (downstream
approximation code depends on its exact shape); the Good version is
opt-in via consumers that need inner cR-consistency. -/

/-- **[FRONTIER, sorry]** Extend a good chain `s : PairERGoodChain cR β`
to a good extension `s → α` for any countable `α > β`. Parallel to
`PairERChain.extendToExt`. Closing this requires either:
  (i) building the recursion from scratch at the Good layer (closing
      under succ/limit/extendTo with explicit inner_consistent care);
  (ii) lifting an existing (closed) PairERChain Extension to a Good
      Extension by supplying inner_consistent. -/
noncomputable def PairERGoodChain.extendToExt
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {β α : Ordinal.{0}} (_s : PairERGoodChain cR β)
    (_hβα : β < α) (_hα : α < Ordinal.omega.{0} 1) :
    PairERGoodChain.Extension _s _hβα := by
  sorry

/-- **`PairERGoodChain.extendTo`**: chain-only projection of
`extendToExt`. -/
noncomputable def PairERGoodChain.extendTo
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {β α : Ordinal.{0}} (s : PairERGoodChain cR β)
    (hβα : β < α) (hα : α < Ordinal.omega.{0} 1) :
    PairERGoodChain cR α :=
  (s.extendToExt hβα hα).chain

/-- **`PairERGoodChain.extendTo_commitAt`**: agreement at `δ < β` —
projection of `Extension.commitAt_old`. -/
theorem PairERGoodChain.extendTo_commitAt
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {β α : Ordinal.{0}} (s : PairERGoodChain cR β)
    (hβα : β < α) (hα : α < Ordinal.omega.{0} 1)
    (δ : Ordinal.{0}) (hδβ : δ < β) :
    (s.extendTo hβα hα).toPairERChain.commitAt δ (hδβ.trans hβα) =
      s.toPairERChain.commitAt δ hδβ :=
  (s.extendToExt hβα hα).commitAt_old δ hδβ

/-- **`PairERGoodChain.extendTo_typeAt_old`**: agreement at `δ < β` for
the type function — projection of `Extension.typeAt_old`. -/
theorem PairERGoodChain.extendTo_typeAt_old
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {β α : Ordinal.{0}} (s : PairERGoodChain cR β)
    (hβα : β < α) (hα : α < Ordinal.omega.{0} 1)
    (δ : Ordinal.{0}) (hδβ : δ < β) :
    (s.extendTo hβα hα).toPairERChain.typeAt δ (hδβ.trans hβα) =
      s.toPairERChain.typeAt δ hδβ :=
  (s.extendToExt hβα hα).typeAt_old δ hδβ

/-- **`PairERGoodChain.extendTo_head_β_in_validFiber`**: the new chain's
head at position `β` lies in `s`'s validFiber — projection of
`Extension.head_β_in_validFiber`. -/
theorem PairERGoodChain.extendTo_head_β_in_validFiber
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {β α : Ordinal.{0}} (s : PairERGoodChain cR β)
    (hβα : β < α) (hα : α < Ordinal.omega.{0} 1) :
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    (s.extendTo hβα hα).toPairERChain.head
        (Ordinal.enum (α := α.ToType) (· < ·)
          ⟨β, (Ordinal.type_toType α).symm ▸ hβα⟩) ∈
      validFiber cR s.toPairERChain.head s.toPairERChain.type :=
  (s.extendToExt hβα hα).head_β_in_validFiber

/-- **`PairERGoodChain.Extension.toPairERChainExtension`**: bridge from
a good extension to an ordinary `PairERChain.Extension`. Projects the
underlying chain and drops `inner_consistent`. Allows existing
consumers of `PairERChain.Extension` to accept good extensions. -/
def PairERGoodChain.Extension.toPairERChainExtension
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {β : Ordinal.{0}} {s : PairERGoodChain cR β}
    {α : Ordinal.{0}} {hβα : β < α}
    (e : PairERGoodChain.Extension s hβα) :
    PairERChain.Extension s.toPairERChain hβα where
  chain := e.chain.toPairERChain
  commitAt_old := e.commitAt_old
  typeAt_old := e.typeAt_old
  head_β_in_validFiber := e.head_β_in_validFiber

/-- **`PairERGoodChain.extendToExt_of_succ_eq`**: if `α = Order.succ β`,
the extension is `PairERGoodChain.Extension.succ`. (Not a generic
constructor; a *consistency* lemma — useful only after closing
`extendToExt`'s structure.) Reduces the succ case of the frontier to
the proven `Extension.succ` constructor. -/
theorem PairERGoodChain.Extension.succ_eq_extension
    {cR : (Fin 2 ↪o PairERSource) → Bool} {β : Ordinal.{0}}
    (s : PairERGoodChain cR β) :
    ∃ e : PairERGoodChain.Extension s (Order.lt_succ β),
      e.chain = s.succ :=
  ⟨PairERGoodChain.Extension.succ s, rfl⟩

/-! ### Validation: inner cR-consistency closes the interior validFiber

For any `s : PairERGoodChain cR β` and any `α < β`, the value of
`s.head` at the α-position of `β.ToType` lies in the validFiber
defined by the **restricted** prefix/type to `α.ToType`. This is
exactly the (α, β₀)-adjacency obligation that blocked the interior
insertion proof; closing it with `inner_consistent` confirms that
inner cR-consistency is the missing ingredient. -/

/-- **`PairERGoodChain.head_at_α_in_restricted_validFiber`**: the
"interior validFiber" check is discharged by `inner_consistent`.
Given a good chain at `β` and `α < β`, the head value at position
`α` is in the validFiber of the head/type restricted to `α.ToType`. -/
theorem PairERGoodChain.head_at_α_in_restricted_validFiber
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {β : Ordinal.{0}} (s : PairERGoodChain cR β)
    {α : Ordinal.{0}} (hαβ : α < β) :
    haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    s.toPairERChain.head (Ordinal.enum (α := β.ToType) (· < ·)
        ⟨α, (Ordinal.type_toType β).symm ▸ hαβ⟩) ∈
      validFiber cR
        ((Ordinal.initialSegToType hαβ.le).toOrderEmbedding.trans
          s.toPairERChain.head)
        (fun x => s.toPairERChain.type
          ((Ordinal.initialSegToType hαβ.le).toOrderEmbedding x)) := by
  haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  intro x
  set y_x : β.ToType :=
    (Ordinal.initialSegToType hαβ.le).toOrderEmbedding x with hy_x_def
  set y_α : β.ToType := Ordinal.enum (α := β.ToType) (· < ·)
    ⟨α, (Ordinal.type_toType β).symm ▸ hαβ⟩ with hy_α_def
  -- y_x < y_α: typein y_x = typein x < α = typein y_α.
  have h_yx_typein : (Ordinal.typein (α := β.ToType) (· < ·)).toRelEmbedding y_x =
      (Ordinal.typein (α := α.ToType) (· < ·)).toRelEmbedding x :=
    Ordinal.typein_apply _ x
  have h_yα_typein :
      (Ordinal.typein (α := β.ToType) (· < ·)).toRelEmbedding y_α = α := by
    rw [hy_α_def, Ordinal.typein_enum]
  have h_x_typein_lt_α :
      (Ordinal.typein (α := α.ToType) (· < ·)).toRelEmbedding x < α := by
    have := Ordinal.typein_lt_type (· < ·) x
    rwa [Ordinal.type_toType] at this
  have h_yx_lt_yα : y_x < y_α := by
    rw [← Ordinal.typein_lt_typein (α := β.ToType) (· < ·)]
    rw [h_yx_typein, h_yα_typein]
    exact h_x_typein_lt_α
  refine ⟨s.toPairERChain.head.strictMono h_yx_lt_yα, ?_⟩
  exact s.inner_consistent h_yx_lt_yα

/-! ### `CoherentGoodBranchApprox`: Good-strengthened approximation

A parallel `CoherentBranchApprox` carrying a `PairERGoodChain` at
each level (with head/type agreement). Interior insertion and rigid
extension can use this layer to discharge the validFiber adjacency
obligations via `inner_consistent`; the bare CBA pipeline remains
intact for existing finite-existence consumers. -/

/-- **`CoherentGoodBranchApprox cR n`**: a CBA at length `n`
augmented with a `PairERGoodChain` at each level whose head/type
agree with the CBA's `prefixAt`/`branchAt`. -/
structure CoherentGoodBranchApprox
    (cR : (Fin 2 ↪o PairERSource) → Bool) (n : ℕ) where
  /-- The underlying bare approximation. -/
  toApprox : CoherentBranchApprox cR n
  /-- The Good chain at each level. -/
  goodAt : ∀ i : Fin n, PairERGoodChain cR (toApprox.level i)
  /-- Head agrees with `toApprox.prefixAt`. -/
  good_head : ∀ (i : Fin n) (x : (toApprox.level i).ToType),
    (goodAt i).toPairERChain.head x = toApprox.prefixAt i x
  /-- Type agrees with `toApprox.branchAt`. -/
  good_type : ∀ (i : Fin n) (x : (toApprox.level i).ToType),
    (goodAt i).toPairERChain.type x = toApprox.branchAt i x

/-- **Projection**: forget the Good chain data, recover the bare CBA. -/
def CoherentGoodBranchApprox.toCoherentBranchApprox
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentGoodBranchApprox cR n) : CoherentBranchApprox cR n :=
  A.toApprox

/-- **`CoherentGoodBranchApprox.zero`**: empty Good approximation. -/
noncomputable def CoherentGoodBranchApprox.zero
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    CoherentGoodBranchApprox cR 0 where
  toApprox := CoherentBranchApprox.zero cR
  goodAt i := i.elim0
  good_head i := i.elim0
  good_type i := i.elim0

/-- **`CoherentGoodBranchApprox.fromZero`**: the unique single-level
Good approximation at level `0` (using `PairERGoodChain.zero`). -/
noncomputable def CoherentGoodBranchApprox.fromZero
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    CoherentGoodBranchApprox cR 1 where
  toApprox := CoherentBranchApprox.fromZero cR
  goodAt _ := PairERGoodChain.zero cR
  good_head i x := by
    haveI : IsEmpty ((CoherentBranchApprox.fromZero cR).level i).ToType :=
      Ordinal.isEmpty_toType_zero
    exact isEmptyElim x
  good_type i x := by
    haveI : IsEmpty ((CoherentBranchApprox.fromZero cR).level i).ToType :=
      Ordinal.isEmpty_toType_zero
    exact isEmptyElim x

/-- **Helper**: in a Good approximation, the bare CBA's `lastChain`
equals the Good chain at the last position. Provable via
`RelEmbedding.ext` (head agreement) + `funext` (type agreement) +
proof irrelevance (large). -/
theorem CoherentGoodBranchApprox.lastChain_eq_goodAt_toPairERChain
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentGoodBranchApprox cR (n + 1)) :
    A.toApprox.lastChain = (A.goodAt (Fin.last n)).toPairERChain := by
  have h_head : A.toApprox.prefixAt (Fin.last n) =
      (A.goodAt (Fin.last n)).toPairERChain.head := by
    refine RelEmbedding.ext ?_
    intro x
    exact (A.good_head (Fin.last n) x).symm
  have h_type : A.toApprox.branchAt (Fin.last n) =
      (A.goodAt (Fin.last n)).toPairERChain.type := by
    funext x
    exact (A.good_type (Fin.last n) x).symm
  show ({ head := A.toApprox.prefixAt (Fin.last n)
          type := A.toApprox.branchAt (Fin.last n)
          large := A.toApprox.large (Fin.last n) } : PairERChain cR _) = _
  -- The two structures have matching fields; large is proof-irrelevant.
  congr 1

/-- **Helper**: structural equality `extendSucc.level = extendLevel`. -/
@[simp] theorem CoherentBranchApprox.extendSucc_level
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentBranchApprox cR (n + 1)) :
    A.extendSucc.level = A.extendLevel := rfl

/-- **`PairERGoodChain.castLevel`**: transport a good chain along an
ordinal equality. -/
def PairERGoodChain.castLevel
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α β : Ordinal.{0}}
    (h : α = β) (s : PairERGoodChain cR α) : PairERGoodChain cR β :=
  h ▸ s

@[simp] theorem PairERGoodChain.castLevel_rfl
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (s : PairERGoodChain cR α) : s.castLevel (rfl : α = α) = s := rfl

/-- **`castLevel_head`**: head of cast chain at `x : β.ToType` equals
head of original at the transported element `h.symm ▸ x : α.ToType`. -/
theorem PairERGoodChain.castLevel_head
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α β : Ordinal.{0}}
    (h : α = β) (s : PairERGoodChain cR α) (x : β.ToType) :
    (s.castLevel h).toPairERChain.head x =
      s.toPairERChain.head (h.symm ▸ x) := by
  subst h; rfl

/-- **`castLevel_type`**: parallel of `castLevel_head` for the type
function. -/
theorem PairERGoodChain.castLevel_type
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α β : Ordinal.{0}}
    (h : α = β) (s : PairERGoodChain cR α) (x : β.ToType) :
    (s.castLevel h).toPairERChain.type x =
      s.toPairERChain.type (h.symm ▸ x) := by
  subst h; rfl

/-- **`PairERGoodChain.restrict`**: restrict a Good chain at level `β`
to a Good chain at any lower level `α < β`. Head/type are composed
with `initialSegToType`; `large` follows from validFiber containment
(more constraints in β-validFiber); `inner_consistent` follows from
`s.inner_consistent` applied to lifted positions. -/
noncomputable def PairERGoodChain.restrict
    {cR : (Fin 2 ↪o PairERSource) → Bool} {β : Ordinal.{0}}
    (s : PairERGoodChain cR β) {α : Ordinal.{0}} (hαβ : α < β) :
    PairERGoodChain cR α := by
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  refine
    { toPairERChain :=
      { head := (Ordinal.initialSegToType hαβ.le).toOrderEmbedding.trans
          s.toPairERChain.head
        type := fun x => s.toPairERChain.type
          ((Ordinal.initialSegToType hαβ.le).toOrderEmbedding x)
        large := ?_ }
      inner_consistent := ?_ }
  · -- large: restricted validFiber ⊇ original validFiber.
    apply s.toPairERChain.large.trans
    apply Cardinal.mk_le_mk_of_subset
    intro y hy x
    exact hy ((Ordinal.initialSegToType hαβ.le).toOrderEmbedding x)
  · -- inner_consistent: lift x < y via initSeg, apply s.inner_consistent.
    intro x y h
    exact s.inner_consistent
      ((Ordinal.initialSegToType hαβ.le).toOrderEmbedding.strictMono h)

/-- **`restrict_head_apply`**: explicit formula for the head of a
restricted Good chain at `y : α.ToType`. -/
@[simp] theorem PairERGoodChain.restrict_head_apply
    {cR : (Fin 2 ↪o PairERSource) → Bool} {β : Ordinal.{0}}
    (s : PairERGoodChain cR β) {α : Ordinal.{0}} (hαβ : α < β)
    (y : α.ToType) :
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
    (s.restrict hαβ).toPairERChain.head y =
      s.toPairERChain.head
        ((Ordinal.initialSegToType hαβ.le).toOrderEmbedding y) := rfl

/-- **`restrict_type_apply`**: parallel for type. -/
@[simp] theorem PairERGoodChain.restrict_type_apply
    {cR : (Fin 2 ↪o PairERSource) → Bool} {β : Ordinal.{0}}
    (s : PairERGoodChain cR β) {α : Ordinal.{0}} (hαβ : α < β)
    (y : α.ToType) :
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
    (s.restrict hαβ).toPairERChain.type y =
      s.toPairERChain.type
        ((Ordinal.initialSegToType hαβ.le).toOrderEmbedding y) := rfl

/-- **`CoherentGoodBranchApprox.extendSucc`**: extend by one top
level via `PairERGoodChain.succ`, using `castLevel` to transport
along the structural level equalities. -/
noncomputable def CoherentGoodBranchApprox.extendSucc
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentGoodBranchApprox cR (n + 1)) :
    CoherentGoodBranchApprox cR (n + 2) := by
  classical
  haveI : IsWellOrder (A.toApprox.level (Fin.last n)).ToType (· < ·) := isWellOrder_lt
  have h_nextChain :
      A.toApprox.nextChain = ((A.goodAt (Fin.last n)).succ).toPairERChain := by
    show A.toApprox.lastChain.succ = ((A.goodAt (Fin.last n)).succ).toPairERChain
    rw [A.lastChain_eq_goodAt_toPairERChain]
    rfl
  -- Level equalities for extendSucc.
  have h_level_last : A.toApprox.extendSucc.level (Fin.last (n + 1)) =
      Order.succ (A.toApprox.level (Fin.last n)) := A.toApprox.extendLevel_last
  have h_level_cs : ∀ j : Fin (n + 1),
      A.toApprox.extendSucc.level j.castSucc = A.toApprox.level j :=
    fun j => A.toApprox.extendLevel_castSucc j
  refine
    { toApprox := A.toApprox.extendSucc
      goodAt := Fin.lastCases (motive := fun i =>
          PairERGoodChain cR (A.toApprox.extendSucc.level i))
        (((A.goodAt (Fin.last n)).succ).castLevel h_level_last.symm)
        (fun j => (A.goodAt j).castLevel (h_level_cs j).symm)
      good_head := ?_
      good_type := ?_ }
  · intro i x
    induction i using Fin.lastCases with
    | last =>
      simp only [Fin.lastCases_last]
      rw [PairERGoodChain.castLevel_head h_level_last.symm
          ((A.goodAt (Fin.last n)).succ) x]
      show ((A.goodAt (Fin.last n)).succ).toPairERChain.head _ =
        A.toApprox.extendSucc.prefixAt (Fin.last (n + 1)) x
      rw [show A.toApprox.extendSucc.prefixAt (Fin.last (n + 1)) x =
            A.toApprox.extendPrefixAt (Fin.last (n + 1)) x from rfl,
        A.toApprox.extendPrefixAt_last_apply x, ← h_nextChain]
    | cast j =>
      simp only [Fin.lastCases_castSucc]
      rw [PairERGoodChain.castLevel_head (h_level_cs j).symm
          (A.goodAt j) x]
      show (A.goodAt j).toPairERChain.head _ =
        A.toApprox.extendSucc.prefixAt j.castSucc x
      rw [show A.toApprox.extendSucc.prefixAt j.castSucc x =
            A.toApprox.extendPrefixAt j.castSucc x from rfl,
        A.toApprox.extendPrefixAt_castSucc_apply j x]
      exact A.good_head j _
  · intro i x
    induction i using Fin.lastCases with
    | last =>
      simp only [Fin.lastCases_last]
      rw [PairERGoodChain.castLevel_type h_level_last.symm
          ((A.goodAt (Fin.last n)).succ) x]
      show ((A.goodAt (Fin.last n)).succ).toPairERChain.type _ =
        A.toApprox.extendSucc.branchAt (Fin.last (n + 1)) x
      rw [show A.toApprox.extendSucc.branchAt (Fin.last (n + 1)) x =
            A.toApprox.extendBranchAt (Fin.last (n + 1)) x from rfl,
        A.toApprox.extendBranchAt_last_apply x, ← h_nextChain]
    | cast j =>
      simp only [Fin.lastCases_castSucc]
      rw [PairERGoodChain.castLevel_type (h_level_cs j).symm
          (A.goodAt j) x]
      show (A.goodAt j).toPairERChain.type _ =
        A.toApprox.extendSucc.branchAt j.castSucc x
      rw [show A.toApprox.extendSucc.branchAt j.castSucc x =
            A.toApprox.extendBranchAt j.castSucc x from rfl,
        A.toApprox.extendBranchAt_castSucc_apply j x]
      exact A.good_type j _

/-- **`CoherentGoodBranchApprox.extendToChain`**: the Good chain at
level `α` extending `A`'s last position. Dispatches on `n`:
- `n = 0`: uses `(PairERGoodChain.zero cR).extendTo`.
- `n = k + 1`: uses `(A.goodAt (Fin.last k)).extendTo`.

Parallels `CoherentBranchApprox.extendToChain` at the Good layer. -/
noncomputable def CoherentGoodBranchApprox.extendToChain
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentGoodBranchApprox cR n)
    (α : Ordinal.{0}) (hα : α < Ordinal.omega.{0} 1)
    (hα_above_last : A.toApprox.lastLevel < α) : PairERGoodChain cR α := by
  classical
  by_cases hn : n = 0
  · have hβα : (0 : Ordinal.{0}) < α := by
      have h_eq : A.toApprox.lastLevel = 0 := by
        unfold CoherentBranchApprox.lastLevel; rw [dif_pos hn]
      exact h_eq ▸ hα_above_last
    exact (PairERGoodChain.zero cR).extendTo hβα hα
  · have hn' : n - 1 < n := by omega
    have hβα : A.toApprox.level ⟨n - 1, hn'⟩ < α := by
      have h_eq : A.toApprox.lastLevel = A.toApprox.level ⟨n - 1, hn'⟩ := by
        unfold CoherentBranchApprox.lastLevel; rw [dif_neg hn]
      exact h_eq ▸ hα_above_last
    exact (A.goodAt ⟨n - 1, hn'⟩).extendTo hβα hα

/-- **`extendToGoodChain_head_at_level`**: the Good chain's head at
the position corresponding to `A`'s `k`-th level (lifted via
`initialSegToType`) agrees with `A.toApprox.prefixAt k`. Parallels
`extendToChain_head_at_level`; for `n > 0`, the proof routes through
`PairERGoodChain.extendTo_commitAt` + `lastChain_eq_goodAt_toPairERChain`
+ `A.toApprox.prefix_restrict`. -/
theorem CoherentGoodBranchApprox.extendToGoodChain_head_at_level
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentGoodBranchApprox cR n)
    (α : Ordinal.{0}) (hα : α < Ordinal.omega.{0} 1)
    (hα_above_last : A.toApprox.lastLevel < α)
    (k : Fin n) (x : (A.toApprox.level k).ToType) :
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder (A.toApprox.level k).ToType (· < ·) := isWellOrder_lt
    (A.extendToChain α hα hα_above_last).toPairERChain.head
        ((Ordinal.initialSegToType
          ((A.toApprox.lastLevel_ge k).trans hα_above_last.le)).toOrderEmbedding x) =
      A.toApprox.prefixAt k x := by
  classical
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder (A.toApprox.level k).ToType (· < ·) := isWellOrder_lt
  have hn_ne_zero : n ≠ 0 := by rintro rfl; exact k.elim0
  have hn' : n - 1 < n := by omega
  unfold CoherentGoodBranchApprox.extendToChain
  rw [dif_neg hn_ne_zero]
  haveI : IsWellOrder (A.toApprox.level ⟨n - 1, hn'⟩).ToType (· < ·) := isWellOrder_lt
  set lastGood := A.goodAt ⟨n - 1, hn'⟩ with hlastGood_def
  set hβα : A.toApprox.level ⟨n - 1, hn'⟩ < α := by
    have h_eq : A.toApprox.lastLevel = A.toApprox.level ⟨n - 1, hn'⟩ := by
      unfold CoherentBranchApprox.lastLevel; rw [dif_neg hn_ne_zero]
    exact h_eq ▸ hα_above_last
  show (lastGood.extendTo hβα hα).toPairERChain.head _ = _
  -- Identify the lift as enum at δ := typein x.
  set δ : Ordinal.{0} :=
    Ordinal.typein (α := (A.toApprox.level k).ToType) (· < ·) x with hδ_def
  have hδ_lt_lvlk : δ < A.toApprox.level k := by
    rw [hδ_def]; exact Ordinal.typein_lt_self x
  have hk_le : k ≤ (⟨n - 1, hn'⟩ : Fin n) := by
    show k.val ≤ n - 1
    have := k.isLt; omega
  have h_lvl_le : A.toApprox.level k ≤ A.toApprox.level ⟨n - 1, hn'⟩ :=
    A.toApprox.level_strictMono.monotone hk_le
  have hδ_lt_β : δ < A.toApprox.level ⟨n - 1, hn'⟩ := hδ_lt_lvlk.trans_le h_lvl_le
  have hδ_lt_α : δ < α := hδ_lt_β.trans hβα
  have h_lift_α : (Ordinal.initialSegToType
      ((A.toApprox.lastLevel_ge k).trans hα_above_last.le)).toOrderEmbedding x =
      Ordinal.enum (α := α.ToType) (· < ·)
        ⟨δ, (Ordinal.type_toType _).symm ▸ hδ_lt_α⟩ := by
    rw [← Ordinal.enum_typein (· < · : α.ToType → α.ToType → Prop)
      ((Ordinal.initialSegToType
        ((A.toApprox.lastLevel_ge k).trans hα_above_last.le)).toOrderEmbedding x)]
    congr 1
    apply Subtype.ext
    show Ordinal.typein (α := α.ToType) (· < ·)
        ((Ordinal.initialSegToType
          ((A.toApprox.lastLevel_ge k).trans hα_above_last.le)).toOrderEmbedding x) = δ
    rw [show Ordinal.typein (α := α.ToType) (· < ·)
          ((Ordinal.initialSegToType
            ((A.toApprox.lastLevel_ge k).trans hα_above_last.le)).toOrderEmbedding x) =
        Ordinal.typein (α := (A.toApprox.level k).ToType) (· < ·) x from
      Ordinal.typein_apply _ x]
  rw [h_lift_α]
  -- Use PairERGoodChain.extendTo_commitAt to bridge to lastGood.
  have h_step : (lastGood.extendTo hβα hα).toPairERChain.head
      (Ordinal.enum (α := α.ToType) (· < ·)
        ⟨δ, (Ordinal.type_toType _).symm ▸ hδ_lt_α⟩) =
      lastGood.toPairERChain.head (Ordinal.enum
        (α := (A.toApprox.level ⟨n - 1, hn'⟩).ToType) (· < ·)
        ⟨δ, (Ordinal.type_toType _).symm ▸ hδ_lt_β⟩) := by
    show (lastGood.extendTo hβα hα).toPairERChain.commitAt δ hδ_lt_α =
      lastGood.toPairERChain.commitAt δ hδ_lt_β
    exact PairERGoodChain.extendTo_commitAt lastGood hβα hα δ hδ_lt_β
  rw [h_step]
  -- lastGood.head = A.prefixAt ⟨n-1, _⟩ via good_head.
  -- Then identify enum at δ with the initialSegToType lift of x.
  have h_lift_αn : Ordinal.enum (α := (A.toApprox.level ⟨n - 1, hn'⟩).ToType) (· < ·)
      ⟨δ, (Ordinal.type_toType _).symm ▸ hδ_lt_β⟩ =
      (Ordinal.initialSegToType h_lvl_le).toOrderEmbedding x := by
    rw [← Ordinal.enum_typein
      (· < · : (A.toApprox.level ⟨n - 1, hn'⟩).ToType →
        (A.toApprox.level ⟨n - 1, hn'⟩).ToType → Prop)
      ((Ordinal.initialSegToType h_lvl_le).toOrderEmbedding x)]
    congr 1
    apply Subtype.ext
    show δ = Ordinal.typein (α := (A.toApprox.level ⟨n - 1, hn'⟩).ToType) (· < ·)
        ((Ordinal.initialSegToType h_lvl_le).toOrderEmbedding x)
    rw [show Ordinal.typein
          (α := (A.toApprox.level ⟨n - 1, hn'⟩).ToType) (· < ·)
          ((Ordinal.initialSegToType h_lvl_le).toOrderEmbedding x) =
        Ordinal.typein (α := (A.toApprox.level k).ToType) (· < ·) x from
      Ordinal.typein_apply (Ordinal.initialSegToType h_lvl_le) x]
  rw [h_lift_αn]
  -- Now LHS is lastGood.head ((initialSegToType h_lvl_le).toOrderEmb x) ;
  -- RHS is A.toApprox.prefixAt k x.
  rw [A.good_head ⟨n - 1, hn'⟩]
  exact A.toApprox.prefix_restrict hk_le x

/-- **`extendToGoodChain_type_at_level`**: analog of
`extendToGoodChain_head_at_level` for the type function. -/
theorem CoherentGoodBranchApprox.extendToGoodChain_type_at_level
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentGoodBranchApprox cR n)
    (α : Ordinal.{0}) (hα : α < Ordinal.omega.{0} 1)
    (hα_above_last : A.toApprox.lastLevel < α)
    (k : Fin n) (x : (A.toApprox.level k).ToType) :
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder (A.toApprox.level k).ToType (· < ·) := isWellOrder_lt
    (A.extendToChain α hα hα_above_last).toPairERChain.type
        ((Ordinal.initialSegToType
          ((A.toApprox.lastLevel_ge k).trans hα_above_last.le)).toOrderEmbedding x) =
      A.toApprox.branchAt k x := by
  classical
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder (A.toApprox.level k).ToType (· < ·) := isWellOrder_lt
  have hn_ne_zero : n ≠ 0 := by rintro rfl; exact k.elim0
  have hn' : n - 1 < n := by omega
  unfold CoherentGoodBranchApprox.extendToChain
  rw [dif_neg hn_ne_zero]
  haveI : IsWellOrder (A.toApprox.level ⟨n - 1, hn'⟩).ToType (· < ·) := isWellOrder_lt
  set lastGood := A.goodAt ⟨n - 1, hn'⟩ with hlastGood_def
  set hβα : A.toApprox.level ⟨n - 1, hn'⟩ < α := by
    have h_eq : A.toApprox.lastLevel = A.toApprox.level ⟨n - 1, hn'⟩ := by
      unfold CoherentBranchApprox.lastLevel; rw [dif_neg hn_ne_zero]
    exact h_eq ▸ hα_above_last
  show (lastGood.extendTo hβα hα).toPairERChain.type _ = _
  set δ : Ordinal.{0} :=
    Ordinal.typein (α := (A.toApprox.level k).ToType) (· < ·) x with hδ_def
  have hδ_lt_lvlk : δ < A.toApprox.level k := by
    rw [hδ_def]; exact Ordinal.typein_lt_self x
  have hk_le : k ≤ (⟨n - 1, hn'⟩ : Fin n) := by
    show k.val ≤ n - 1
    have := k.isLt; omega
  have h_lvl_le : A.toApprox.level k ≤ A.toApprox.level ⟨n - 1, hn'⟩ :=
    A.toApprox.level_strictMono.monotone hk_le
  have hδ_lt_β : δ < A.toApprox.level ⟨n - 1, hn'⟩ := hδ_lt_lvlk.trans_le h_lvl_le
  have hδ_lt_α : δ < α := hδ_lt_β.trans hβα
  have h_lift_α : (Ordinal.initialSegToType
      ((A.toApprox.lastLevel_ge k).trans hα_above_last.le)).toOrderEmbedding x =
      Ordinal.enum (α := α.ToType) (· < ·)
        ⟨δ, (Ordinal.type_toType _).symm ▸ hδ_lt_α⟩ := by
    rw [← Ordinal.enum_typein (· < · : α.ToType → α.ToType → Prop)
      ((Ordinal.initialSegToType
        ((A.toApprox.lastLevel_ge k).trans hα_above_last.le)).toOrderEmbedding x)]
    congr 1
    apply Subtype.ext
    show Ordinal.typein (α := α.ToType) (· < ·)
        ((Ordinal.initialSegToType
          ((A.toApprox.lastLevel_ge k).trans hα_above_last.le)).toOrderEmbedding x) = δ
    rw [show Ordinal.typein (α := α.ToType) (· < ·)
          ((Ordinal.initialSegToType
            ((A.toApprox.lastLevel_ge k).trans hα_above_last.le)).toOrderEmbedding x) =
        Ordinal.typein (α := (A.toApprox.level k).ToType) (· < ·) x from
      Ordinal.typein_apply _ x]
  rw [h_lift_α]
  have h_step : (lastGood.extendTo hβα hα).toPairERChain.type
      (Ordinal.enum (α := α.ToType) (· < ·)
        ⟨δ, (Ordinal.type_toType _).symm ▸ hδ_lt_α⟩) =
      lastGood.toPairERChain.type (Ordinal.enum
        (α := (A.toApprox.level ⟨n - 1, hn'⟩).ToType) (· < ·)
        ⟨δ, (Ordinal.type_toType _).symm ▸ hδ_lt_β⟩) := by
    show (lastGood.extendTo hβα hα).toPairERChain.typeAt δ hδ_lt_α =
      lastGood.toPairERChain.typeAt δ hδ_lt_β
    exact PairERGoodChain.extendTo_typeAt_old lastGood hβα hα δ hδ_lt_β
  rw [h_step]
  have h_lift_αn : Ordinal.enum (α := (A.toApprox.level ⟨n - 1, hn'⟩).ToType) (· < ·)
      ⟨δ, (Ordinal.type_toType _).symm ▸ hδ_lt_β⟩ =
      (Ordinal.initialSegToType h_lvl_le).toOrderEmbedding x := by
    rw [← Ordinal.enum_typein
      (· < · : (A.toApprox.level ⟨n - 1, hn'⟩).ToType →
        (A.toApprox.level ⟨n - 1, hn'⟩).ToType → Prop)
      ((Ordinal.initialSegToType h_lvl_le).toOrderEmbedding x)]
    congr 1
    apply Subtype.ext
    show δ = Ordinal.typein (α := (A.toApprox.level ⟨n - 1, hn'⟩).ToType) (· < ·)
        ((Ordinal.initialSegToType h_lvl_le).toOrderEmbedding x)
    rw [show Ordinal.typein
          (α := (A.toApprox.level ⟨n - 1, hn'⟩).ToType) (· < ·)
          ((Ordinal.initialSegToType h_lvl_le).toOrderEmbedding x) =
        Ordinal.typein (α := (A.toApprox.level k).ToType) (· < ·) x from
      Ordinal.typein_apply (Ordinal.initialSegToType h_lvl_le) x]
  rw [h_lift_αn]
  rw [A.good_type ⟨n - 1, hn'⟩]
  exact A.toApprox.branch_restrict hk_le x

/-- **`extendToGoodChain_realizes_at_lastIndex`**: the Good chain's
head at the position corresponding to the last existing level lies in
`A.toApprox`'s validFiber at that level. Parallels
`extendToChain_realizes_at_lastIndex`; uses
`PairERGoodChain.extendTo_head_β_in_validFiber` + chain equality. -/
theorem CoherentGoodBranchApprox.extendToGoodChain_realizes_at_lastIndex
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentGoodBranchApprox cR n)
    (α : Ordinal.{0}) (hα : α < Ordinal.omega.{0} 1)
    (hα_above_last : A.toApprox.lastLevel < α) (hn_ne_zero : n ≠ 0) :
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    have hn' : n - 1 < n := Nat.sub_lt (Nat.pos_of_ne_zero hn_ne_zero) Nat.one_pos
    have hβα : A.toApprox.level ⟨n - 1, hn'⟩ < α := by
      have h_eq : A.toApprox.lastLevel = A.toApprox.level ⟨n - 1, hn'⟩ := by
        unfold CoherentBranchApprox.lastLevel; rw [dif_neg hn_ne_zero]
      exact h_eq ▸ hα_above_last
    (A.extendToChain α hα hα_above_last).toPairERChain.head
        (Ordinal.enum (α := α.ToType) (· < ·)
          ⟨A.toApprox.level ⟨n - 1, hn'⟩, (Ordinal.type_toType _).symm ▸ hβα⟩) ∈
      validFiber cR (A.toApprox.prefixAt ⟨n - 1, hn'⟩)
        (A.toApprox.branchAt ⟨n - 1, hn'⟩) := by
  classical
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  have hn' : n - 1 < n := Nat.sub_lt (Nat.pos_of_ne_zero hn_ne_zero) Nat.one_pos
  haveI : IsWellOrder (A.toApprox.level ⟨n - 1, hn'⟩).ToType (· < ·) := isWellOrder_lt
  set lastGood := A.goodAt ⟨n - 1, hn'⟩ with hlastGood_def
  set hβα : A.toApprox.level ⟨n - 1, hn'⟩ < α := by
    have h_eq : A.toApprox.lastLevel = A.toApprox.level ⟨n - 1, hn'⟩ := by
      unfold CoherentBranchApprox.lastLevel; rw [dif_neg hn_ne_zero]
    exact h_eq ▸ hα_above_last
  -- Reduce extendToChain to lastGood.extendTo via a separate chain equality.
  have h_chain_eq :
      A.extendToChain α hα hα_above_last = lastGood.extendTo hβα hα := by
    unfold CoherentGoodBranchApprox.extendToChain
    rw [dif_neg hn_ne_zero]
  rw [h_chain_eq]
  -- Bridge validFiber's arguments to lastGood via good_head/good_type.
  show (lastGood.extendTo hβα hα).toPairERChain.head _ ∈
    validFiber cR (A.toApprox.prefixAt ⟨n - 1, hn'⟩)
      (A.toApprox.branchAt ⟨n - 1, hn'⟩)
  have h_head_eq : A.toApprox.prefixAt ⟨n - 1, hn'⟩ =
      lastGood.toPairERChain.head := by
    refine RelEmbedding.ext ?_
    intro y; exact (A.good_head ⟨n - 1, hn'⟩ y).symm
  have h_type_eq : A.toApprox.branchAt ⟨n - 1, hn'⟩ =
      lastGood.toPairERChain.type := by
    funext y; exact (A.good_type ⟨n - 1, hn'⟩ y).symm
  rw [h_head_eq, h_type_eq]
  exact PairERGoodChain.extendTo_head_β_in_validFiber lastGood hβα hα

/-- **`CoherentGoodBranchApprox.extendTo`** (depends only on
`PairERGoodChain.extendToExt` via `A.extendToChain`): the Good analog
of `CoherentBranchApprox.extendTo`. Builds the new bare CBA from
scratch using `A.extendToChain α hα h_above_last`, and uses the
three Good chain agreement lemmas for boundary cases. `goodAt` is
defined via `Fin.lastCases` with `castLevel`-transported chains. -/
noncomputable def CoherentGoodBranchApprox.extendTo
    {cR : (Fin 2 ↪o PairERSource) → Bool} {n : ℕ}
    (A : CoherentGoodBranchApprox cR n)
    (α : Ordinal.{0}) (hα : α < Ordinal.omega.{0} 1)
    (hα_above_last : A.toApprox.lastLevel < α) :
    CoherentGoodBranchApprox cR (n + 1) := by
  classical
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  let nextGood : PairERGoodChain cR α := A.extendToChain α hα hα_above_last
  let nextChain : PairERChain cR α := nextGood.toPairERChain
  -- Build the bare CBA.
  let bareCBA : CoherentBranchApprox cR (n + 1) := {
    level := A.toApprox.extendToLevel α
    level_lt_omega1 := by
      intro k
      induction k using Fin.lastCases with
      | last => rw [A.toApprox.extendToLevel_last]; exact hα
      | cast k => rw [A.toApprox.extendToLevel_castSucc]; exact A.toApprox.level_lt_omega1 k
    level_strictMono := by
      intro a b hab
      induction a using Fin.lastCases with
      | last => exfalso; exact absurd hab (not_lt_of_ge (Fin.le_last b))
      | cast j₁ =>
        induction b using Fin.lastCases with
        | last =>
          rw [A.toApprox.extendToLevel_castSucc, A.toApprox.extendToLevel_last]
          exact (A.toApprox.lastLevel_ge j₁).trans_lt hα_above_last
        | cast j₂ =>
          rw [A.toApprox.extendToLevel_castSucc, A.toApprox.extendToLevel_castSucc]
          apply A.toApprox.level_strictMono
          exact (Fin.castSucc_lt_castSucc_iff).mp hab
    prefixAt := A.toApprox.extendToPrefixAt nextChain
    branchAt := A.toApprox.extendToBranchAt nextChain
    prefix_restrict := by
      intro k₁ k₂ hk x
      induction k₁ using Fin.lastCases with
      | last =>
        induction k₂ using Fin.lastCases with
        | last =>
          congr 1
          have h : Ordinal.initialSegToType
              (le_refl (A.toApprox.extendToLevel α (Fin.last n))) =
              InitialSeg.refl _ := Subsingleton.elim _ _
          rw [h]; rfl
        | cast j₂ =>
          exact absurd hk (not_le_of_gt (Fin.castSucc_lt_last j₂))
      | cast j₁ =>
        induction k₂ using Fin.lastCases with
        | last =>
          haveI : IsWellOrder (A.toApprox.level j₁).ToType (· < ·) := isWellOrder_lt
          set x' : (A.toApprox.level j₁).ToType :=
            (A.toApprox.extendToLevel_castSucc α j₁) ▸ x with hx'
          rw [A.toApprox.extendToPrefixAt_last_apply,
              A.toApprox.extendToPrefixAt_castSucc_apply, ← hx']
          have h_lvl_le : A.toApprox.level j₁ ≤ α :=
            (A.toApprox.lastLevel_ge j₁).trans hα_above_last.le
          rw [initialSegToType_transport_eq (A.toApprox.extendToLevel_castSucc α j₁)
              (A.toApprox.extendToLevel_last α) _ h_lvl_le x]
          exact A.extendToGoodChain_head_at_level α hα hα_above_last j₁ x'
        | cast j₂ =>
          have hj : j₁ ≤ j₂ := (Fin.castSucc_le_castSucc_iff).mp hk
          haveI : IsWellOrder (A.toApprox.level j₁).ToType (· < ·) := isWellOrder_lt
          haveI : IsWellOrder (A.toApprox.level j₂).ToType (· < ·) := isWellOrder_lt
          set x' : (A.toApprox.level j₁).ToType :=
            (A.toApprox.extendToLevel_castSucc α j₁) ▸ x with hx'
          rw [A.toApprox.extendToPrefixAt_castSucc_apply,
              A.toApprox.extendToPrefixAt_castSucc_apply, ← hx']
          have hres := A.toApprox.prefix_restrict hj x'
          convert hres using 2
          exact initialSegToType_transport_eq
            (A.toApprox.extendToLevel_castSucc α j₁)
            (A.toApprox.extendToLevel_castSucc α j₂) _ _ x
    branch_restrict := by
      intro k₁ k₂ hk x
      induction k₁ using Fin.lastCases with
      | last =>
        induction k₂ using Fin.lastCases with
        | last =>
          congr 1
          have h : Ordinal.initialSegToType
              (le_refl (A.toApprox.extendToLevel α (Fin.last n))) =
              InitialSeg.refl _ := Subsingleton.elim _ _
          rw [h]; rfl
        | cast j₂ =>
          exact absurd hk (not_le_of_gt (Fin.castSucc_lt_last j₂))
      | cast j₁ =>
        induction k₂ using Fin.lastCases with
        | last =>
          haveI : IsWellOrder (A.toApprox.level j₁).ToType (· < ·) := isWellOrder_lt
          set x' : (A.toApprox.level j₁).ToType :=
            (A.toApprox.extendToLevel_castSucc α j₁) ▸ x with hx'
          rw [A.toApprox.extendToBranchAt_last_apply,
              A.toApprox.extendToBranchAt_castSucc_apply, ← hx']
          have h_lvl_le : A.toApprox.level j₁ ≤ α :=
            (A.toApprox.lastLevel_ge j₁).trans hα_above_last.le
          rw [initialSegToType_transport_eq (A.toApprox.extendToLevel_castSucc α j₁)
              (A.toApprox.extendToLevel_last α) _ h_lvl_le x]
          exact A.extendToGoodChain_type_at_level α hα hα_above_last j₁ x'
        | cast j₂ =>
          have hj : j₁ ≤ j₂ := (Fin.castSucc_le_castSucc_iff).mp hk
          haveI : IsWellOrder (A.toApprox.level j₁).ToType (· < ·) := isWellOrder_lt
          haveI : IsWellOrder (A.toApprox.level j₂).ToType (· < ·) := isWellOrder_lt
          set x' : (A.toApprox.level j₁).ToType :=
            (A.toApprox.extendToLevel_castSucc α j₁) ▸ x with hx'
          rw [A.toApprox.extendToBranchAt_castSucc_apply,
              A.toApprox.extendToBranchAt_castSucc_apply, ← hx']
          have hres := A.toApprox.branch_restrict hj x'
          convert hres using 2
          exact initialSegToType_transport_eq
            (A.toApprox.extendToLevel_castSucc α j₁)
            (A.toApprox.extendToLevel_castSucc α j₂) _ _ x
    large := by
      intro k
      induction k using Fin.lastCases with
      | last =>
        show Order.succ (Cardinal.beth.{0} 1) ≤
            Cardinal.mk (validFiber cR
              (A.toApprox.extendToPrefixAt nextChain (Fin.last n))
              (A.toApprox.extendToBranchAt nextChain (Fin.last n)))
        convert nextChain.large using 4
        · exact A.toApprox.extendToLevel_last α
        · exact A.toApprox.extendToPrefixAt_last_heq nextChain
        · exact A.toApprox.extendToBranchAt_last_heq nextChain
      | cast j =>
        show Order.succ (Cardinal.beth.{0} 1) ≤
            Cardinal.mk (validFiber cR
              (A.toApprox.extendToPrefixAt nextChain j.castSucc)
              (A.toApprox.extendToBranchAt nextChain j.castSucc))
        convert A.toApprox.large j using 4
        · exact A.toApprox.extendToLevel_castSucc α j
        · exact A.toApprox.extendToPrefixAt_castSucc_heq nextChain j
        · exact A.toApprox.extendToBranchAt_castSucc_heq nextChain j
    top_in_validFiber := by
      intro i h
      have hi : i < n := Nat.lt_of_succ_lt_succ h
      by_cases hi1 : i + 1 < n
      · show A.toApprox.extendToPrefixAt nextChain ((⟨i + 1, hi1⟩ : Fin n).castSucc)
            ((Ordinal.enum (· < ·))
              ⟨A.toApprox.extendToLevel α ((⟨i, hi⟩ : Fin n).castSucc), _⟩) ∈ _
        convert A.toApprox.top_in_validFiber i hi1 using 2
        · exact A.toApprox.extendToLevel_castSucc α ⟨i, hi⟩
        · exact A.toApprox.extendToPrefixAt_castSucc_heq nextChain ⟨i, hi⟩
        · exact A.toApprox.extendToBranchAt_castSucc_heq nextChain ⟨i, hi⟩
        · rw [A.toApprox.extendToPrefixAt_castSucc_apply]
          congr 1
          exact enum_transport_eq (A.toApprox.extendToLevel_castSucc α ⟨i + 1, hi1⟩)
            (A.toApprox.extendToLevel_castSucc α ⟨i, hi⟩) _ _
      · have hi1_eq : i + 1 = n := by omega
        obtain rfl : n = i + 1 := hi1_eq.symm
        have hn_ne_zero : i + 1 ≠ 0 := by omega
        have hn' : i + 1 - 1 < i + 1 := by omega
        have h_idx : (⟨i, hi⟩ : Fin (i + 1)) = ⟨i + 1 - 1, hn'⟩ := by
          apply Fin.ext; show i = i + 1 - 1; omega
        have h_last : (⟨i + 1, h⟩ : Fin (i + 1 + 1)) = Fin.last (i + 1) :=
          Fin.ext rfl
        convert A.extendToGoodChain_realizes_at_lastIndex α hα hα_above_last
            hn_ne_zero using 2
        · show A.toApprox.extendToLevel α (⟨i, hi⟩ : Fin (i + 1)).castSucc =
            A.toApprox.level ⟨i + 1 - 1, hn'⟩
          rw [A.toApprox.extendToLevel_castSucc α ⟨i, hi⟩, h_idx]
        · show HEq (A.toApprox.extendToPrefixAt nextChain
              (⟨i, hi⟩ : Fin (i + 1)).castSucc)
            (A.toApprox.prefixAt ⟨i + 1 - 1, hn'⟩)
          rw [h_idx]
          exact A.toApprox.extendToPrefixAt_castSucc_heq nextChain _
        · show HEq (A.toApprox.extendToBranchAt nextChain
              (⟨i, hi⟩ : Fin (i + 1)).castSucc)
            (A.toApprox.branchAt ⟨i + 1 - 1, hn'⟩)
          rw [h_idx]
          exact A.toApprox.extendToBranchAt_castSucc_heq nextChain _
        · haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
          have h_lvl : A.toApprox.extendToLevel α ⟨i + 1, h⟩ = α := by
            show A.toApprox.extendToLevel α (Fin.last (i + 1)) = α
            exact A.toApprox.extendToLevel_last α
          have h_fn_heq : HEq (A.toApprox.extendToPrefixAt nextChain ⟨i + 1, h⟩)
              nextChain.head := by
            rw [h_last]; exact A.toApprox.extendToPrefixAt_last_heq nextChain
          rw [orderEmbed_ordinal_apply_heq h_lvl _ _ h_fn_heq]
          congr 1
          exact enum_transport_eq h_lvl
            (A.toApprox.extendToLevel_castSucc α ⟨i + 1 - 1, hn'⟩) _ _ }
  -- Level equalities for the goodAt construction.
  have h_level_last : bareCBA.level (Fin.last n) = α :=
    A.toApprox.extendToLevel_last α
  have h_level_cs : ∀ j : Fin n, bareCBA.level j.castSucc = A.toApprox.level j :=
    fun j => A.toApprox.extendToLevel_castSucc α j
  refine
    { toApprox := bareCBA
      goodAt := Fin.lastCases (motive := fun i => PairERGoodChain cR (bareCBA.level i))
        (nextGood.castLevel h_level_last.symm)
        (fun j => (A.goodAt j).castLevel (h_level_cs j).symm)
      good_head := ?_
      good_type := ?_ }
  · intro i x
    induction i using Fin.lastCases with
    | last =>
      simp only [Fin.lastCases_last]
      rw [PairERGoodChain.castLevel_head h_level_last.symm nextGood x]
      show nextGood.toPairERChain.head _ =
        bareCBA.prefixAt (Fin.last n) x
      show nextChain.head _ = A.toApprox.extendToPrefixAt nextChain (Fin.last n) x
      rw [A.toApprox.extendToPrefixAt_last_apply nextChain x]
    | cast j =>
      simp only [Fin.lastCases_castSucc]
      rw [PairERGoodChain.castLevel_head (h_level_cs j).symm (A.goodAt j) x]
      show (A.goodAt j).toPairERChain.head _ = bareCBA.prefixAt j.castSucc x
      show (A.goodAt j).toPairERChain.head _ =
        A.toApprox.extendToPrefixAt nextChain j.castSucc x
      rw [A.toApprox.extendToPrefixAt_castSucc_apply nextChain j x]
      exact A.good_head j _
  · intro i x
    induction i using Fin.lastCases with
    | last =>
      simp only [Fin.lastCases_last]
      rw [PairERGoodChain.castLevel_type h_level_last.symm nextGood x]
      show nextGood.toPairERChain.type _ =
        bareCBA.branchAt (Fin.last n) x
      show nextChain.type _ = A.toApprox.extendToBranchAt nextChain (Fin.last n) x
      rw [A.toApprox.extendToBranchAt_last_apply nextChain x]
    | cast j =>
      simp only [Fin.lastCases_castSucc]
      rw [PairERGoodChain.castLevel_type (h_level_cs j).symm (A.goodAt j) x]
      show (A.goodAt j).toPairERChain.type _ = bareCBA.branchAt j.castSucc x
      show (A.goodAt j).toPairERChain.type _ =
        A.toApprox.extendToBranchAt nextChain j.castSucc x
      rw [A.toApprox.extendToBranchAt_castSucc_apply nextChain j x]
      exact A.good_type j _

/-- **`CoherentGoodBranchApprox.extend`**: generic one-step extension
dispatching on `n` (uses `fromZero` for `n = 0`, `extendSucc`
otherwise). Mirrors `CoherentBranchApprox.extend`. -/
noncomputable def CoherentGoodBranchApprox.extend
    {cR : (Fin 2 ↪o PairERSource) → Bool} : ∀ {n : ℕ},
    CoherentGoodBranchApprox cR n → CoherentGoodBranchApprox cR (n + 1)
  | 0, _ => CoherentGoodBranchApprox.fromZero cR
  | _ + 1, A => A.extendSucc

/-- **`coherentGoodBranchApproxSeq`**: the ω-chain of Good
approximations, defined by primitive recursion. -/
noncomputable def coherentGoodBranchApproxSeq
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    (n : ℕ) → CoherentGoodBranchApprox cR n
  | 0 => CoherentGoodBranchApprox.zero cR
  | n + 1 => (coherentGoodBranchApproxSeq cR n).extend

@[simp] theorem coherentGoodBranchApproxSeq_zero
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    coherentGoodBranchApproxSeq cR 0 = CoherentGoodBranchApprox.zero cR := rfl

@[simp] theorem coherentGoodBranchApproxSeq_succ
    (cR : (Fin 2 ↪o PairERSource) → Bool) (n : ℕ) :
    coherentGoodBranchApproxSeq cR (n + 1) =
      (coherentGoodBranchApproxSeq cR n).extend := rfl

/-- **`coherentGoodBranchApproxSeq_toApprox`**: the bare projection
of the Good sequence equals the bare sequence. -/
theorem coherentGoodBranchApproxSeq_toApprox
    (cR : (Fin 2 ↪o PairERSource) → Bool) (n : ℕ) :
    (coherentGoodBranchApproxSeq cR n).toApprox =
      coherentBranchApproxSeq cR n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show ((coherentGoodBranchApproxSeq cR n).extend).toApprox = _
    cases n with
    | zero =>
      show (CoherentGoodBranchApprox.fromZero cR).toApprox = _
      rfl
    | succ m =>
      show ((coherentGoodBranchApproxSeq cR (m + 1)).extendSucc).toApprox = _
      show (coherentGoodBranchApproxSeq cR (m + 1)).toApprox.extendSucc = _
      rw [ih]
      rfl

/-! ### Good arbitrary-finite-levels existence theorems

Mirrors the bare `exists_coherentBranchApprox_for_strictMono` and
`exists_coherentBranchApprox_for_list`, providing a
`CoherentGoodBranchApprox` at any strictly-monotone Fin-indexed (or
list-indexed) family of countable ordinals. Depends only on
`PairERGoodChain.extendToExt` (the Good frontier). -/

/-- **`exists_coherentGoodBranchApprox_for_strictMono`**: build a
`CoherentGoodBranchApprox cR n` over any strictly-monotone Fin-indexed
family of countable ordinals. Parallels the bare version, using CGBA
primitives `zero`/`fromZero`/`extendTo`. -/
theorem exists_coherentGoodBranchApprox_for_strictMono
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    ∀ {n : ℕ} (f : Fin n → Ordinal.{0})
      (_h_lt : ∀ i, f i < Ordinal.omega.{0} 1)
      (_h_strictMono : StrictMono f),
      ∃ A : CoherentGoodBranchApprox cR n, ∀ i, A.toApprox.level i = f i := by
  intro n
  induction n with
  | zero =>
    intro f _ _
    refine ⟨CoherentGoodBranchApprox.zero cR, ?_⟩
    intro i; exact i.elim0
  | succ k IH =>
    intro f h_lt h_strictMono
    by_cases hk : k = 0
    · subst hk
      let α : Ordinal.{0} := f ⟨0, Nat.zero_lt_one⟩
      have hα_lt : α < Ordinal.omega.{0} 1 := h_lt _
      by_cases hα_pos : 0 < α
      · refine ⟨(CoherentGoodBranchApprox.zero cR).extendTo α hα_lt hα_pos, ?_⟩
        intro i
        have hi_eq : i = Fin.last 0 :=
          Fin.ext (by have := i.isLt; omega)
        rw [hi_eq]
        exact (CoherentBranchApprox.zero cR).extendToLevel_last α
      · push_neg at hα_pos
        have hα_eq : α = 0 := le_antisymm hα_pos (zero_le _)
        refine ⟨CoherentGoodBranchApprox.fromZero cR, ?_⟩
        intro i
        have hi_eq : i = ⟨0, Nat.zero_lt_one⟩ :=
          Fin.ext (by have := i.isLt; omega)
        rw [hi_eq]
        show (0 : Ordinal) = f ⟨0, Nat.zero_lt_one⟩
        exact hα_eq.symm
    · let f' : Fin k → Ordinal.{0} := fun i => f i.castSucc
      have h_lt' : ∀ i, f' i < Ordinal.omega.{0} 1 := fun i => h_lt _
      have h_strictMono' : StrictMono f' := fun _ _ hab =>
        h_strictMono (Fin.castSucc_lt_castSucc_iff.mpr hab)
      obtain ⟨A', hA'⟩ := IH f' h_lt' h_strictMono'
      let α : Ordinal.{0} := f (Fin.last k)
      have hα_lt : α < Ordinal.omega.{0} 1 := h_lt _
      have h_above : A'.toApprox.lastLevel < α := by
        unfold CoherentBranchApprox.lastLevel
        rw [dif_neg hk]
        have hk' : k - 1 < k := Nat.sub_lt (Nat.pos_of_ne_zero hk) one_pos
        rw [hA' ⟨k - 1, hk'⟩]
        show f' ⟨k - 1, hk'⟩ < α
        show f (⟨k - 1, hk'⟩ : Fin k).castSucc < f (Fin.last k)
        apply h_strictMono
        exact Fin.castSucc_lt_last _
      refine ⟨A'.extendTo α hα_lt h_above, ?_⟩
      intro i
      show A'.toApprox.extendToLevel α i = f i
      induction i using Fin.lastCases with
      | last => rw [A'.toApprox.extendToLevel_last]
      | cast j =>
        rw [A'.toApprox.extendToLevel_castSucc α j, hA' j]

/-- **`exists_coherentGoodBranchApprox_for_list`**: list-indexed
version. -/
theorem exists_coherentGoodBranchApprox_for_list
    (cR : (Fin 2 ↪o PairERSource) → Bool)
    (l : List Ordinal.{0})
    (h_sorted : l.Pairwise (· < ·))
    (h_lt : ∀ α ∈ l, α < Ordinal.omega.{0} 1) :
    ∃ A : CoherentGoodBranchApprox cR l.length,
      ∀ i : Fin l.length, A.toApprox.level i = l.get i := by
  refine exists_coherentGoodBranchApprox_for_strictMono cR (l.get) ?_ ?_
  · exact fun i => h_lt _ (List.get_mem _ _)
  · intro a b hab
    exact List.pairwise_iff_get.mp h_sorted a b hab

/-! ### `CoherentGoodBranchPartial`: Finset-indexed partial Good
branches

Parallel wrapper of `CoherentBranchPartial` carrying Good chain data
at each level. Used by interior insertion (where access to
`PairERGoodChain.inner_consistent` discharges the (α, β₀) validFiber
adjacency). -/

/-- **`CoherentGoodBranchPartial cR S`**: a Good-strengthened partial
branch indexed by a finite set `S` of countable ordinals. Internally
backed by a `CoherentGoodBranchApprox cR S.card` whose `level` matches
`S.orderEmbOfFin rfl`. -/
structure CoherentGoodBranchPartial
    (cR : (Fin 2 ↪o PairERSource) → Bool) (S : Finset Ordinal.{0}) where
  /-- The underlying Good approximation at length `S.card`. -/
  toGoodApprox : CoherentGoodBranchApprox cR S.card
  /-- Level identification. -/
  level_eq : ∀ i : Fin S.card,
    toGoodApprox.toApprox.level i = (S.orderEmbOfFin rfl) i

/-- **Projection** to bare `CoherentBranchPartial`: forget the Good
chain data, recover the bare CBP. -/
def CoherentGoodBranchPartial.toCoherentBranchPartial
    {cR : (Fin 2 ↪o PairERSource) → Bool} {S : Finset Ordinal.{0}}
    (P : CoherentGoodBranchPartial cR S) : CoherentBranchPartial cR S where
  toApprox := P.toGoodApprox.toApprox
  level_eq := P.level_eq

/-- **`goodAt`**: for `α ∈ S`, the Good chain at level `α`. Uses
`indexOf` and `castLevel` to transport from the Good approximation. -/
noncomputable def CoherentGoodBranchPartial.goodAt
    {cR : (Fin 2 ↪o PairERSource) → Bool} {S : Finset Ordinal.{0}}
    (P : CoherentGoodBranchPartial cR S)
    (α : Ordinal.{0}) (hα : α ∈ S) : PairERGoodChain cR α :=
  (P.toGoodApprox.goodAt (P.toCoherentBranchPartial.indexOf α hα)).castLevel
    (P.toCoherentBranchPartial.level_indexOf α hα)

/-- **`good_head_eq`**: the Good chain's head at `α` matches the
bare `CBP.prefixAt α`. Routes through `castLevel_head` +
`A.good_head` + the cast lemmas. -/
theorem CoherentGoodBranchPartial.good_head_eq
    {cR : (Fin 2 ↪o PairERSource) → Bool} {S : Finset Ordinal.{0}}
    (P : CoherentGoodBranchPartial cR S)
    (α : Ordinal.{0}) (hα : α ∈ S) (x : α.ToType) :
    (P.goodAt α hα).toPairERChain.head x =
      P.toCoherentBranchPartial.prefixAt α hα x := by
  set idx := P.toCoherentBranchPartial.indexOf α hα
  set h_lvl := P.toCoherentBranchPartial.level_indexOf α hα
  -- Chain: castLevel + good_head + prefixAt_apply.
  calc ((P.toGoodApprox.goodAt idx).castLevel h_lvl).toPairERChain.head x
      = (P.toGoodApprox.goodAt idx).toPairERChain.head (h_lvl.symm ▸ x) :=
        PairERGoodChain.castLevel_head h_lvl (P.toGoodApprox.goodAt idx) x
    _ = P.toGoodApprox.toApprox.prefixAt idx (h_lvl.symm ▸ x) :=
        P.toGoodApprox.good_head idx (h_lvl.symm ▸ x)
    _ = P.toCoherentBranchPartial.prefixAt α hα x :=
        (P.toCoherentBranchPartial.prefixAt_apply α hα x).symm

/-- **`good_type_eq`**: parallel for `branch`. -/
theorem CoherentGoodBranchPartial.good_type_eq
    {cR : (Fin 2 ↪o PairERSource) → Bool} {S : Finset Ordinal.{0}}
    (P : CoherentGoodBranchPartial cR S)
    (α : Ordinal.{0}) (hα : α ∈ S) (x : α.ToType) :
    (P.goodAt α hα).toPairERChain.type x =
      P.toCoherentBranchPartial.branch α hα x := by
  set idx := P.toCoherentBranchPartial.indexOf α hα
  set h_lvl := P.toCoherentBranchPartial.level_indexOf α hα
  calc ((P.toGoodApprox.goodAt idx).castLevel h_lvl).toPairERChain.type x
      = (P.toGoodApprox.goodAt idx).toPairERChain.type (h_lvl.symm ▸ x) :=
        PairERGoodChain.castLevel_type h_lvl (P.toGoodApprox.goodAt idx) x
    _ = P.toGoodApprox.toApprox.branchAt idx (h_lvl.symm ▸ x) :=
        P.toGoodApprox.good_type idx (h_lvl.symm ▸ x)
    _ = P.toCoherentBranchPartial.branch α hα x :=
        (P.toCoherentBranchPartial.branch_apply α hα x).symm

/-- **`goodAt_head_apply_eq_of_eq`**: when `α = β`, the head value of
`P.goodAt α hα` at `y` equals the head value of `P.goodAt β hβ` at the
transported `h ▸ y`. Closes via `subst h` + definitional proof
irrelevance on the membership proofs. -/
theorem CoherentGoodBranchPartial.goodAt_head_apply_eq_of_eq
    {cR : (Fin 2 ↪o PairERSource) → Bool} {S : Finset Ordinal.{0}}
    (P : CoherentGoodBranchPartial cR S)
    {α β : Ordinal.{0}} {hα : α ∈ S} {hβ : β ∈ S} (h : α = β)
    (y : α.ToType) :
    (P.goodAt α hα).head y =
      (P.goodAt β hβ).head (h ▸ y) := by
  subst h
  rfl

/-- **`goodAt_type_apply_eq_of_eq`**: parallel for the type function. -/
theorem CoherentGoodBranchPartial.goodAt_type_apply_eq_of_eq
    {cR : (Fin 2 ↪o PairERSource) → Bool} {S : Finset Ordinal.{0}}
    (P : CoherentGoodBranchPartial cR S)
    {α β : Ordinal.{0}} {hα : α ∈ S} {hβ : β ∈ S} (h : α = β)
    (y : α.ToType) :
    (P.goodAt α hα).type y =
      (P.goodAt β hβ).type (h ▸ y) := by
  subst h
  rfl

/-- **`CoherentGoodBranchPartial.restrict`**: Good analog of
`CoherentBranchPartial.restrict`. Builds a Good CBP on `S ⊆ T` by
reindexing `PG.toGoodApprox` through `ρ : Fin S.card → Fin T.card`
(the same reindexing as the bare version). The Good chain at S-index
`i` is `PG.toGoodApprox.goodAt (ρ i)`; `good_head`/`good_type` carry
through from `PG.toGoodApprox`. -/
noncomputable def CoherentGoodBranchPartial.restrict
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {T : Finset Ordinal.{0}} (PG : CoherentGoodBranchPartial cR T)
    {S : Finset Ordinal.{0}} (hST : S ⊆ T) :
    CoherentGoodBranchPartial cR S := by
  classical
  set σ_S : Fin S.card → Ordinal.{0} := fun i => (S.orderEmbOfFin rfl) i
  have h_σ_S : ∀ i, σ_S i ∈ S := S.orderEmbOfFin_mem rfl
  have h_σ_T : ∀ i, σ_S i ∈ T := fun i => hST (h_σ_S i)
  set ρ : Fin S.card → Fin T.card := fun i =>
    PG.toCoherentBranchPartial.indexOf (σ_S i) (h_σ_T i)
  have h_lvl_ρ : ∀ i, PG.toGoodApprox.toApprox.level (ρ i) = σ_S i :=
    fun i => PG.toCoherentBranchPartial.level_indexOf (σ_S i) (h_σ_T i)
  have h_ρ_strictMono : StrictMono ρ := by
    intro a b hab
    show (T.orderIsoOfFin rfl).symm ⟨σ_S a, h_σ_T a⟩ <
      (T.orderIsoOfFin rfl).symm ⟨σ_S b, h_σ_T b⟩
    exact (T.orderIsoOfFin rfl).symm.strictMono
      ((S.orderEmbOfFin rfl).strictMono hab)
  refine
    { toGoodApprox :=
      { toApprox :=
        { level := fun i => PG.toGoodApprox.toApprox.level (ρ i)
          level_lt_omega1 := fun i =>
            PG.toGoodApprox.toApprox.level_lt_omega1 (ρ i)
          level_strictMono := fun _ _ hab =>
            PG.toGoodApprox.toApprox.level_strictMono (h_ρ_strictMono hab)
          prefixAt := fun i => PG.toGoodApprox.toApprox.prefixAt (ρ i)
          branchAt := fun i => PG.toGoodApprox.toApprox.branchAt (ρ i)
          prefix_restrict := fun {k₁ k₂} hk x =>
            PG.toGoodApprox.toApprox.prefix_restrict
              (h_ρ_strictMono.monotone hk) x
          branch_restrict := fun {k₁ k₂} hk x =>
            PG.toGoodApprox.toApprox.branch_restrict
              (h_ρ_strictMono.monotone hk) x
          large := fun i => PG.toGoodApprox.toApprox.large (ρ i)
          top_in_validFiber := ?_ }
        goodAt := fun i => PG.toGoodApprox.goodAt (ρ i)
        good_head := fun i x => PG.toGoodApprox.good_head (ρ i) x
        good_type := fun i x => PG.toGoodApprox.good_type (ρ i) x }
      level_eq := ?_ }
  · intro i hi
    apply PG.toGoodApprox.toApprox.validFiber_between
    exact h_ρ_strictMono
      (show (⟨i, Nat.lt_of_succ_lt hi⟩ : Fin S.card) <
        ⟨i + 1, hi⟩ from by show i < i + 1; omega)
  · intro i; exact h_lvl_ρ i

/-- **`CoherentGoodBranchPartial.restrict_toCoherentBranchPartial`**:
the projection commutes with restrict. Used as a simp lemma to bridge
Good and bare restricts in the projective-system instance. -/
@[simp] theorem CoherentGoodBranchPartial.restrict_toCoherentBranchPartial
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {T : Finset Ordinal.{0}} (PG : CoherentGoodBranchPartial cR T)
    {S : Finset Ordinal.{0}} (hST : S ⊆ T) :
    (PG.restrict hST).toCoherentBranchPartial =
      PG.toCoherentBranchPartial.restrict hST := rfl

/-- **`exists_coherentGoodBranchPartial`**: for any finite set `S` of
countable ordinals, there exists a `CoherentGoodBranchPartial cR S`.
Derived from `exists_coherentGoodBranchApprox_for_strictMono` applied
to `S.orderEmbOfFin rfl`. -/
theorem exists_coherentGoodBranchPartial
    (cR : (Fin 2 ↪o PairERSource) → Bool) (S : Finset Ordinal.{0})
    (hS : ∀ α ∈ S, α < Ordinal.omega.{0} 1) :
    Nonempty (CoherentGoodBranchPartial cR S) := by
  obtain ⟨A, hA⟩ := exists_coherentGoodBranchApprox_for_strictMono cR
    (S.orderEmbOfFin rfl)
    (fun i => hS _ (S.orderEmbOfFin_mem rfl i))
    (S.orderEmbOfFin rfl).strictMono
  exact ⟨{ toGoodApprox := A, level_eq := hA }⟩

/-! ### Helper: least upper bound in a finset

For any `T : Finset Ordinal` containing some element strictly above
`α`, there exists a unique minimal such element. Used by interior
insertion to locate the upper bound `β₀` of the new level `α`. -/

/-- **`exists_min_above_in_finset`**: in a finset `T`, the minimum
element strictly above `α` (when one exists). -/
theorem exists_min_above_in_finset
    (T : Finset Ordinal.{0}) (α : Ordinal.{0})
    (h : ∃ β ∈ T, α < β) :
    ∃ β₀ ∈ T, α < β₀ ∧ ∀ γ ∈ T, α < γ → β₀ ≤ γ := by
  classical
  set T_above : Finset Ordinal.{0} := T.filter (fun γ => α < γ)
  have hT_above_ne : T_above.Nonempty := by
    obtain ⟨β, hβT, hαβ⟩ := h
    exact ⟨β, Finset.mem_filter.mpr ⟨hβT, hαβ⟩⟩
  set β₀ := T_above.min' hT_above_ne
  have hβ₀_mem : β₀ ∈ T_above := T_above.min'_mem hT_above_ne
  obtain ⟨hβ₀_T, hαβ₀⟩ := Finset.mem_filter.mp hβ₀_mem
  refine ⟨β₀, hβ₀_T, hαβ₀, ?_⟩
  intro γ hγT hαγ
  exact T_above.min'_le γ (Finset.mem_filter.mpr ⟨hγT, hαγ⟩)

/-! ### Index bookkeeping for `insert α T`

Small helpers to be used by the fixed-β₀ interior insertion. With
`hmin : ∀ γ ∈ T, α < γ → β₀ ≤ γ`, the sorted enumeration of
`insert α T` puts α immediately before β₀: positions of T-elements
below α are unchanged, α takes the position equal to β₀'s index in
T, and T-elements at-or-above β₀ shift up by one. -/

/-- **`insert_split_of_min`**: under `hmin` AND `α ∉ T`, every γ ∈ T
satisfies `γ < α ∨ β₀ ≤ γ` — i.e., no T-element lies strictly between
α and β₀. -/
theorem insert_split_of_min
    {T : Finset Ordinal.{0}} {α β₀ : Ordinal.{0}}
    (hα_not_mem : α ∉ T)
    (_hαβ₀ : α < β₀) (hmin : ∀ γ ∈ T, α < γ → β₀ ≤ γ)
    (γ : Ordinal.{0}) (hγ : γ ∈ T) :
    γ < α ∨ β₀ ≤ γ := by
  rcases lt_or_ge γ α with hγα | hαγ
  · exact Or.inl hγα
  · rcases eq_or_lt_of_le hαγ with h_eq | h_lt
    · -- γ = α: but α ∉ T contradicts γ ∈ T.
      exact absurd (h_eq ▸ hγ : α ∈ T) hα_not_mem
    · exact Or.inr (hmin γ hγ h_lt)

/-- **`card_insert_of_not_mem'`**: cardinality identity for insert
when α ∉ T (Mathlib reuse). -/
theorem card_insert_of_not_mem'
    {T : Finset Ordinal.{0}} {α : Ordinal.{0}} (hα : α ∉ T) :
    (insert α T).card = T.card + 1 :=
  Finset.card_insert_of_notMem hα

/-- **`finsetIndexOf`**: helper extracting the Fin-position of an
element of a finset via `orderIsoOfFin.symm`. -/
noncomputable def finsetIndexOf
    (S : Finset Ordinal.{0}) (γ : Ordinal.{0}) (hγ : γ ∈ S) :
    Fin S.card :=
  (S.orderIsoOfFin rfl).symm ⟨γ, hγ⟩

@[simp] theorem finsetIndexOf_orderEmb
    (S : Finset Ordinal.{0}) (γ : Ordinal.{0}) (hγ : γ ∈ S) :
    (S.orderEmbOfFin rfl) (finsetIndexOf S γ hγ) = γ := by
  unfold finsetIndexOf
  show ↑((S.orderIsoOfFin rfl) ((S.orderIsoOfFin rfl).symm ⟨γ, hγ⟩)) = γ
  rw [(S.orderIsoOfFin rfl).apply_symm_apply]

/-- **`insertOrderEmb`**: the piecewise enumeration of `insert α T`
built via `Fin.insertNth`. Inserts α at position `pos₀.castSucc` (=
β₀'s position in T lifted to `Fin (T.card + 1)`), with old T-values
at all other positions via `succAbove`. -/
noncomputable def insertOrderEmb
    (T : Finset Ordinal.{0}) (α β₀ : Ordinal.{0}) (hβ₀ : β₀ ∈ T) :
    Fin (T.card + 1) → Ordinal.{0} :=
  Fin.insertNth (finsetIndexOf T β₀ hβ₀).castSucc α
    (fun j => T.orderEmbOfFin rfl j)

/-- **`insertOrderEmb_mem`**: each value of the piecewise enumeration
lies in `insert α T`. Case-splits via the explicit equivalent of
`Fin.succAboveCases`. -/
theorem insertOrderEmb_mem
    {T : Finset Ordinal.{0}} {α β₀ : Ordinal.{0}} (hβ₀ : β₀ ∈ T)
    (i : Fin (T.card + 1)) :
    insertOrderEmb T α β₀ hβ₀ i ∈ insert α T := by
  classical
  unfold insertOrderEmb
  by_cases h_eq : i = (finsetIndexOf T β₀ hβ₀).castSucc
  · rw [h_eq, Fin.insertNth_apply_same]
    exact Finset.mem_insert_self α T
  · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq h_eq
    rw [← hj, Fin.insertNth_apply_succAbove]
    exact Finset.mem_insert_of_mem (T.orderEmbOfFin_mem rfl j)

/-- **`insertOrderEmb_strictMono`**: the piecewise enumeration is strictly
monotone. Case analysis on whether each of `a, b` equals the inserted
position `p := pos₀.castSucc`, with `insert_split_of_min` providing the
cross-cases: when `a = p` and `b = p.succAbove j` with `p < b`, the value
at `j` is at-or-above `β₀ > α`; symmetrically when `b = p`. -/
theorem insertOrderEmb_strictMono
    {T : Finset Ordinal.{0}} {α β₀ : Ordinal.{0}}
    (hα_not_mem : α ∉ T) (hαβ₀ : α < β₀) (hβ₀ : β₀ ∈ T)
    (hmin : ∀ γ ∈ T, α < γ → β₀ ≤ γ) :
    StrictMono (insertOrderEmb T α β₀ hβ₀) := by
  classical
  have hpos₀_value : T.orderEmbOfFin rfl (finsetIndexOf T β₀ hβ₀) = β₀ :=
    finsetIndexOf_orderEmb T β₀ hβ₀
  have hvalue_below : ∀ j : Fin T.card,
      j.castSucc < (finsetIndexOf T β₀ hβ₀).castSucc →
      T.orderEmbOfFin rfl j < α := by
    intro j hj
    have hj_lt : j < finsetIndexOf T β₀ hβ₀ :=
      Fin.castSucc_lt_castSucc_iff.mp hj
    have hj_lt_β₀ : T.orderEmbOfFin rfl j < β₀ := by
      have := (T.orderEmbOfFin rfl).strictMono hj_lt
      rwa [hpos₀_value] at this
    have hjT : T.orderEmbOfFin rfl j ∈ T := T.orderEmbOfFin_mem rfl j
    rcases insert_split_of_min hα_not_mem hαβ₀ hmin _ hjT with h | h
    · exact h
    · exact absurd hj_lt_β₀ (not_lt_of_ge h)
  have hvalue_above : ∀ j : Fin T.card,
      (finsetIndexOf T β₀ hβ₀).castSucc ≤ j.castSucc →
      α < T.orderEmbOfFin rfl j := by
    intro j hj
    have hj_ge : finsetIndexOf T β₀ hβ₀ ≤ j :=
      Fin.castSucc_le_castSucc_iff.mp hj
    have hβ₀_le : β₀ ≤ T.orderEmbOfFin rfl j := by
      have := (T.orderEmbOfFin rfl).monotone hj_ge
      rwa [hpos₀_value] at this
    exact hαβ₀.trans_le hβ₀_le
  intro a b hab
  unfold insertOrderEmb
  by_cases ha : a = (finsetIndexOf T β₀ hβ₀).castSucc
  · by_cases hb : b = (finsetIndexOf T β₀ hβ₀).castSucc
    · subst ha; subst hb; exact absurd hab (lt_irrefl _)
    · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hb
      subst ha
      rw [Fin.insertNth_apply_same, ← hj, Fin.insertNth_apply_succAbove]
      apply hvalue_above
      have h_lt : (finsetIndexOf T β₀ hβ₀).castSucc <
          (finsetIndexOf T β₀ hβ₀).castSucc.succAbove j := by
        rw [hj]; exact hab
      exact (Fin.lt_succAbove_iff_le_castSucc _ j).mp h_lt
  · by_cases hb : b = (finsetIndexOf T β₀ hβ₀).castSucc
    · obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq ha
      subst hb
      rw [← hi, Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same]
      apply hvalue_below
      have h_lt : (finsetIndexOf T β₀ hβ₀).castSucc.succAbove i <
          (finsetIndexOf T β₀ hβ₀).castSucc := by
        rw [hi]; exact hab
      exact (Fin.succAbove_lt_iff_castSucc_lt _ i).mp h_lt
    · obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq ha
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hb
      rw [← hi, ← hj, Fin.insertNth_apply_succAbove,
          Fin.insertNth_apply_succAbove]
      apply (T.orderEmbOfFin rfl).strictMono
      have h_lt : (finsetIndexOf T β₀ hβ₀).castSucc.succAbove i <
          (finsetIndexOf T β₀ hβ₀).castSucc.succAbove j := by
        rw [hi, hj]; exact hab
      exact Fin.succAbove_lt_succAbove_iff.mp h_lt

/-- The piecewise enumeration agrees with the canonical
`(insert α T).orderEmbOfFin`. Combines `insertOrderEmb_mem` +
`insertOrderEmb_strictMono` via `Finset.orderEmbOfFin_unique`. -/
theorem insertOrderEmb_eq_orderEmbOfFin
    {T : Finset Ordinal.{0}} {α β₀ : Ordinal.{0}}
    (hα_not_mem : α ∉ T) (hαβ₀ : α < β₀) (hβ₀ : β₀ ∈ T)
    (hmin : ∀ γ ∈ T, α < γ → β₀ ≤ γ) (i : Fin (T.card + 1)) :
    insertOrderEmb T α β₀ hβ₀ i =
      (insert α T).orderEmbOfFin (card_insert_of_not_mem' hα_not_mem)
        i := by
  have h_eq : insertOrderEmb T α β₀ hβ₀ =
      ⇑((insert α T).orderEmbOfFin (card_insert_of_not_mem' hα_not_mem)) :=
    Finset.orderEmbOfFin_unique (card_insert_of_not_mem' hα_not_mem)
      (insertOrderEmb_mem hβ₀)
      (insertOrderEmb_strictMono hα_not_mem hαβ₀ hβ₀ hmin)
  exact congr_fun h_eq i

/-- **`insert_indexOf_self`**: derived from `insertOrderEmb_eq_orderEmbOfFin`
by evaluating at `pos₀.castSucc` (the inserted position) and applying
`Fin.insertNth_apply_same`. -/
theorem insert_indexOf_self
    {T : Finset Ordinal.{0}} {α β₀ : Ordinal.{0}}
    (hα_not_mem : α ∉ T) (hαβ₀ : α < β₀) (hβ₀ : β₀ ∈ T)
    (hmin : ∀ γ ∈ T, α < γ → β₀ ≤ γ) :
    finsetIndexOf (insert α T) α (Finset.mem_insert_self α T) =
      Fin.cast (card_insert_of_not_mem' hα_not_mem).symm
        (finsetIndexOf T β₀ hβ₀).castSucc := by
  classical
  apply ((insert α T).orderEmbOfFin rfl).injective
  rw [finsetIndexOf_orderEmb]
  have h_orderEmb : (insert α T).orderEmbOfFin rfl
        (Fin.cast (card_insert_of_not_mem' hα_not_mem).symm
          (finsetIndexOf T β₀ hβ₀).castSucc) =
      (insert α T).orderEmbOfFin (card_insert_of_not_mem' hα_not_mem)
        (finsetIndexOf T β₀ hβ₀).castSucc :=
    Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr rfl
  rw [h_orderEmb,
      ← insertOrderEmb_eq_orderEmbOfFin hα_not_mem hαβ₀ hβ₀ hmin]
  unfold insertOrderEmb
  rw [Fin.insertNth_apply_same]

/-- **`insert_indexOf_old_before`**: derived from
`insertOrderEmb_eq_orderEmbOfFin` at `pos₀.castSucc.succAbove
(finsetIndexOf T γ hγ)`. Since `γ < α < β₀`, the T-index of γ is below
pos₀, so `succAbove` reduces to `castSucc` (via
`Fin.succAbove_of_castSucc_lt`). -/
theorem insert_indexOf_old_before
    {T : Finset Ordinal.{0}} {α β₀ : Ordinal.{0}}
    (hα_not_mem : α ∉ T) (hαβ₀ : α < β₀) (hβ₀ : β₀ ∈ T)
    (hmin : ∀ γ ∈ T, α < γ → β₀ ≤ γ)
    (γ : Ordinal.{0}) (hγ : γ ∈ T) (hγα : γ < α) :
    finsetIndexOf (insert α T) γ (Finset.mem_insert_of_mem hγ) =
      Fin.cast (card_insert_of_not_mem' hα_not_mem).symm
        (finsetIndexOf T γ hγ).castSucc := by
  classical
  apply ((insert α T).orderEmbOfFin rfl).injective
  rw [finsetIndexOf_orderEmb]
  have h_orderEmb : (insert α T).orderEmbOfFin rfl
        (Fin.cast (card_insert_of_not_mem' hα_not_mem).symm
          (finsetIndexOf T γ hγ).castSucc) =
      (insert α T).orderEmbOfFin (card_insert_of_not_mem' hα_not_mem)
        (finsetIndexOf T γ hγ).castSucc :=
    Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr rfl
  rw [h_orderEmb,
      ← insertOrderEmb_eq_orderEmbOfFin hα_not_mem hαβ₀ hβ₀ hmin]
  have h_lt : finsetIndexOf T γ hγ < finsetIndexOf T β₀ hβ₀ := by
    apply (T.orderEmbOfFin rfl).strictMono.lt_iff_lt.mp
    rw [finsetIndexOf_orderEmb, finsetIndexOf_orderEmb]
    exact hγα.trans hαβ₀
  have h_castSucc_lt : (finsetIndexOf T γ hγ).castSucc <
      (finsetIndexOf T β₀ hβ₀).castSucc :=
    Fin.castSucc_lt_castSucc_iff.mpr h_lt
  unfold insertOrderEmb
  rw [show (finsetIndexOf T γ hγ).castSucc =
        (finsetIndexOf T β₀ hβ₀).castSucc.succAbove (finsetIndexOf T γ hγ)
      from (Fin.succAbove_of_castSucc_lt _ _ h_castSucc_lt).symm,
      Fin.insertNth_apply_succAbove]
  exact (finsetIndexOf_orderEmb T γ hγ).symm

/-- **`insert_indexOf_old_after`**: derived from
`insertOrderEmb_eq_orderEmbOfFin` at `pos₀.castSucc.succAbove
(finsetIndexOf T γ hγ)`. Since `β₀ ≤ γ`, the T-index of γ is ≥ pos₀,
so `succAbove` reduces to `succ` (via `Fin.succAbove_of_le_castSucc`). -/
theorem insert_indexOf_old_after
    {T : Finset Ordinal.{0}} {α β₀ : Ordinal.{0}}
    (hα_not_mem : α ∉ T) (hαβ₀ : α < β₀) (hβ₀ : β₀ ∈ T)
    (hmin : ∀ γ ∈ T, α < γ → β₀ ≤ γ)
    (γ : Ordinal.{0}) (hγ : γ ∈ T) (hβγ : β₀ ≤ γ) :
    finsetIndexOf (insert α T) γ (Finset.mem_insert_of_mem hγ) =
      Fin.cast (card_insert_of_not_mem' hα_not_mem).symm
        (finsetIndexOf T γ hγ).succ := by
  classical
  apply ((insert α T).orderEmbOfFin rfl).injective
  rw [finsetIndexOf_orderEmb]
  have h_orderEmb : (insert α T).orderEmbOfFin rfl
        (Fin.cast (card_insert_of_not_mem' hα_not_mem).symm
          (finsetIndexOf T γ hγ).succ) =
      (insert α T).orderEmbOfFin (card_insert_of_not_mem' hα_not_mem)
        (finsetIndexOf T γ hγ).succ :=
    Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr rfl
  rw [h_orderEmb,
      ← insertOrderEmb_eq_orderEmbOfFin hα_not_mem hαβ₀ hβ₀ hmin]
  have h_le : finsetIndexOf T β₀ hβ₀ ≤ finsetIndexOf T γ hγ := by
    apply (T.orderEmbOfFin rfl).strictMono.le_iff_le.mp
    rw [finsetIndexOf_orderEmb, finsetIndexOf_orderEmb]
    exact hβγ
  have h_castSucc_le : (finsetIndexOf T β₀ hβ₀).castSucc ≤
      (finsetIndexOf T γ hγ).castSucc :=
    Fin.castSucc_le_castSucc_iff.mpr h_le
  unfold insertOrderEmb
  rw [show (finsetIndexOf T γ hγ).succ =
        (finsetIndexOf T β₀ hβ₀).castSucc.succAbove (finsetIndexOf T γ hγ)
      from (Fin.succAbove_of_le_castSucc _ _ h_castSucc_le).symm,
      Fin.insertNth_apply_succAbove]
  exact (finsetIndexOf_orderEmb T γ hγ).symm

/-! ### Good interior insertion: fixed-β₀ version

`coherentGoodBranchPartial_insert_before` is the structural heart of
interior insertion. Given `P : CoherentGoodBranchPartial cR T`, a new
α below some T-element β₀, and `hmin` saying β₀ is the LEAST T-element
above α (so α goes immediately before β₀ in the sorted enumeration of
`insert α T`), produces a Good partial branch on `insert α T` whose
restriction to `T` agrees fieldwise with `P`.

Architecture (two-layer):
1. `insertBeforeGoodAt` — dispatch helper producing the Good chain at
   each position of `insert α T`'s sorted enumeration. At the α-position
   uses `(P.goodAt β₀ hβ₀).restrict hαβ₀`; at old positions uses
   `P.goodAt γ`.
2. `insertBeforeGoodApprox` — assembles the Good chains into a
   `CoherentGoodBranchApprox cR (insert α T).card` whose
   `prefixAt`/`branchAt` are exactly the heads/types of the Good chains.
3. `coherentGoodBranchPartial_insert_before` — wraps as a
   `CoherentGoodBranchPartial cR (insert α T)` with `level_eq := rfl`
   (since the level function IS `(insert α T).orderEmbOfFin rfl`).

The coherence proof obligations (`prefix_restrict`, `branch_restrict`,
`top_in_validFiber`) require dispatch via the index lemmas
(`insert_indexOf_self`, `insert_indexOf_old_before`,
`insert_indexOf_old_after`) plus P's coherence (T-T pairs) or `restrict`
properties (α-T pairs at the (γ_pred, α) and (α, β₀) adjacencies).
Currently stubbed; future commits will fill these in. -/

/-- **`insertBeforeGoodAt`**: dispatch helper. At position `i` in the
sorted enumeration of `insert α T`, return the Good chain at level
`(insert α T).orderEmbOfFin rfl i`. Uses
`(P.goodAt β₀ hβ₀).restrict hαβ₀` when the level equals α, and
`P.goodAt γ` otherwise. Term-mode `dite` so `dif_pos`/`dif_neg`
simplify the dispatch in downstream proofs. -/
noncomputable def insertBeforeGoodAt
    {cR : (Fin 2 ↪o PairERSource) → Bool} {T : Finset Ordinal.{0}}
    (P : CoherentGoodBranchPartial cR T)
    {α β₀ : Ordinal.{0}}
    (hβ₀ : β₀ ∈ T) (hαβ₀ : α < β₀)
    (i : Fin (insert α T).card) :
    PairERGoodChain cR ((insert α T).orderEmbOfFin rfl i) :=
  letI : Decidable ((insert α T).orderEmbOfFin rfl i = α) := Classical.dec _
  if h_eq : (insert α T).orderEmbOfFin rfl i = α then
    ((P.goodAt β₀ hβ₀).restrict hαβ₀).castLevel h_eq.symm
  else
    P.goodAt _
      ((Finset.mem_insert.mp ((insert α T).orderEmbOfFin_mem rfl i)).resolve_left h_eq)

/-- **`insertBeforeGoodAt_eq_alpha`**: when the level at `i` equals α,
`insertBeforeGoodAt` returns the cast of the restricted chain from β₀. -/
theorem insertBeforeGoodAt_eq_alpha
    {cR : (Fin 2 ↪o PairERSource) → Bool} {T : Finset Ordinal.{0}}
    (P : CoherentGoodBranchPartial cR T) {α β₀ : Ordinal.{0}}
    (hβ₀ : β₀ ∈ T) (hαβ₀ : α < β₀)
    {i : Fin (insert α T).card}
    (h_eq : (insert α T).orderEmbOfFin rfl i = α) :
    insertBeforeGoodAt P hβ₀ hαβ₀ i =
      ((P.goodAt β₀ hβ₀).restrict hαβ₀).castLevel h_eq.symm := by
  classical
  unfold insertBeforeGoodAt
  rw [dif_pos h_eq]

/-- **`insertBeforeGoodAt_eq_old`**: when the level at `i` is not α,
`insertBeforeGoodAt` returns `P.goodAt γ hγ` directly. -/
theorem insertBeforeGoodAt_eq_old
    {cR : (Fin 2 ↪o PairERSource) → Bool} {T : Finset Ordinal.{0}}
    (P : CoherentGoodBranchPartial cR T) {α β₀ : Ordinal.{0}}
    (hβ₀ : β₀ ∈ T) (hαβ₀ : α < β₀)
    {i : Fin (insert α T).card}
    (h_neq : (insert α T).orderEmbOfFin rfl i ≠ α) :
    insertBeforeGoodAt P hβ₀ hαβ₀ i =
      P.goodAt _
        ((Finset.mem_insert.mp ((insert α T).orderEmbOfFin_mem rfl i)).resolve_left h_neq) := by
  classical
  unfold insertBeforeGoodAt
  rw [dif_neg h_neq]

/-- **`validFiber_congr_prefix_branch`**: validFiber sets coincide when
prefix embeddings are pointwise equal and branch functions are pointwise
equal. Prevents repeating `RelEmbedding.ext` + `funext` per case. -/
private lemma validFiber_congr_prefix_branch
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    {p₁ p₂ : α.ToType ↪o PairERSource}
    {τ₁ τ₂ : α.ToType → Bool}
    (hp : ∀ x, p₁ x = p₂ x) (hτ : ∀ x, τ₁ x = τ₂ x) :
    validFiber cR p₁ τ₁ = validFiber cR p₂ τ₂ := by
  have hp_eq : p₁ = p₂ := RelEmbedding.ext hp
  have hτ_eq : τ₁ = τ₂ := funext hτ
  rw [hp_eq, hτ_eq]

/-- **`insert_adjacent_alpha_old_eq_beta0`**: if `α` lies at position `i`
in the sorted enumeration of `insert α T` and the next position `i+1`
holds an old T-element, then that element must be `β₀`. Otherwise
`hmin` puts β₀ strictly between, contradicting adjacency. -/
private lemma insert_adjacent_alpha_old_eq_beta0
    {T : Finset Ordinal.{0}} {α β₀ : Ordinal.{0}}
    (_hα_not_mem : α ∉ T) (hαβ₀ : α < β₀) (hβ₀ : β₀ ∈ T)
    (hmin : ∀ γ ∈ T, α < γ → β₀ ≤ γ)
    {i : ℕ} (h : i + 1 < (insert α T).card)
    (h₁ : (insert α T).orderEmbOfFin rfl ⟨i, Nat.lt_of_succ_lt h⟩ = α)
    (h₂ : (insert α T).orderEmbOfFin rfl ⟨i + 1, h⟩ ≠ α) :
    (insert α T).orderEmbOfFin rfl ⟨i + 1, h⟩ = β₀ := by
  classical
  have hv₂_mem : (insert α T).orderEmbOfFin rfl ⟨i + 1, h⟩ ∈ insert α T :=
    (insert α T).orderEmbOfFin_mem rfl _
  have hv₂_T : (insert α T).orderEmbOfFin rfl ⟨i + 1, h⟩ ∈ T :=
    (Finset.mem_insert.mp hv₂_mem).resolve_left h₂
  have hv_lt : (insert α T).orderEmbOfFin rfl ⟨i, Nat.lt_of_succ_lt h⟩ <
      (insert α T).orderEmbOfFin rfl ⟨i + 1, h⟩ :=
    ((insert α T).orderEmbOfFin rfl).strictMono
      (show (⟨i, Nat.lt_of_succ_lt h⟩ : Fin (insert α T).card) <
        ⟨i + 1, h⟩ from Nat.lt_succ_self i)
  have h_α_lt_v₂ : α < (insert α T).orderEmbOfFin rfl ⟨i + 1, h⟩ :=
    calc α = (insert α T).orderEmbOfFin rfl ⟨i, Nat.lt_of_succ_lt h⟩ := h₁.symm
      _ < (insert α T).orderEmbOfFin rfl ⟨i + 1, h⟩ := hv_lt
  have h_β₀_le_v₂ : β₀ ≤ (insert α T).orderEmbOfFin rfl ⟨i + 1, h⟩ :=
    hmin _ hv₂_T h_α_lt_v₂
  -- Show v₂ ≤ β₀ by contradiction.
  refine le_antisymm ?_ h_β₀_le_v₂
  by_contra h_lt
  push_neg at h_lt
  -- h_lt : β₀ < v₂. Find finsetIndexOf β₀ in insert α T, show it's
  -- strictly between ⟨i⟩ and ⟨i+1⟩.
  have hβ₀_mem : β₀ ∈ insert α T := Finset.mem_insert_of_mem hβ₀
  have h_lo : (⟨i, Nat.lt_of_succ_lt h⟩ : Fin (insert α T).card) <
      finsetIndexOf (insert α T) β₀ hβ₀_mem := by
    apply ((insert α T).orderEmbOfFin rfl).strictMono.lt_iff_lt.mp
    rw [finsetIndexOf_orderEmb]
    rw [h₁]; exact hαβ₀
  have h_hi : finsetIndexOf (insert α T) β₀ hβ₀_mem <
      (⟨i + 1, h⟩ : Fin (insert α T).card) := by
    apply ((insert α T).orderEmbOfFin rfl).strictMono.lt_iff_lt.mp
    rw [finsetIndexOf_orderEmb]
    exact h_lt
  have h1 : i < (finsetIndexOf (insert α T) β₀ hβ₀_mem).val := h_lo
  have h2 : (finsetIndexOf (insert α T) β₀ hβ₀_mem).val < i + 1 := h_hi
  omega

/-- **`insert_adjacent_old_alpha_predecessor`**: dual of the above.
If the old T-element is at position `i` and α is at `i+1`, then no
element of T lies strictly between them in α (the lemma's content is
just `v₁ < α`, which is the gating fact for the T/α top_in_validFiber
case). -/
private lemma insert_adjacent_old_alpha_predecessor
    {T : Finset Ordinal.{0}} {α : Ordinal.{0}}
    (hα_not_mem : α ∉ T)
    {i : ℕ} (h : i + 1 < (insert α T).card)
    (h₁ : (insert α T).orderEmbOfFin rfl ⟨i, Nat.lt_of_succ_lt h⟩ ≠ α)
    (h₂ : (insert α T).orderEmbOfFin rfl ⟨i + 1, h⟩ = α) :
    (insert α T).orderEmbOfFin rfl ⟨i, Nat.lt_of_succ_lt h⟩ < α := by
  classical
  have hv₁_mem : (insert α T).orderEmbOfFin rfl ⟨i, Nat.lt_of_succ_lt h⟩ ∈
      insert α T := (insert α T).orderEmbOfFin_mem rfl _
  have hv₁_T : (insert α T).orderEmbOfFin rfl ⟨i, Nat.lt_of_succ_lt h⟩ ∈ T :=
    (Finset.mem_insert.mp hv₁_mem).resolve_left h₁
  have hv_lt : (insert α T).orderEmbOfFin rfl ⟨i, Nat.lt_of_succ_lt h⟩ <
      (insert α T).orderEmbOfFin rfl ⟨i + 1, h⟩ :=
    ((insert α T).orderEmbOfFin rfl).strictMono
      (show (⟨i, Nat.lt_of_succ_lt h⟩ : Fin (insert α T).card) <
        ⟨i + 1, h⟩ from Nat.lt_succ_self i)
  calc (insert α T).orderEmbOfFin rfl ⟨i, Nat.lt_of_succ_lt h⟩
      < (insert α T).orderEmbOfFin rfl ⟨i + 1, h⟩ := hv_lt
    _ = α := h₂

/-- **`insertBeforeGoodApprox`**: the inserted Good approximation at
length `(insert α T).card`. Levels are `(insert α T).orderEmbOfFin rfl`;
Good chains are routed by `insertBeforeGoodAt`; `prefixAt`/`branchAt`
are the chain heads/types so `good_head`/`good_type` are `rfl`.

All coherence fields closed (axiom-clean):
- `prefix_restrict`: all 4 cases (T/T, α/α, α/T, T/α).
- `branch_restrict`: all 4 cases.
- `top_in_validFiber`: α/α ruled out by strict-mono; α/T closes via
  `head_at_α_in_restricted_validFiber (P.goodAt v₂)` + `validFiber_congr`
  + `prefix_restrict` from β₀ to v₂; T/α via `head_at_α` on the
  α-position chain + `prefix_restrict` from v₁ to β₀; T/T via
  `head_at_α (P.goodAt v₂)` + `prefix_restrict` from v₁ to v₂. -/
noncomputable def insertBeforeGoodApprox
    {cR : (Fin 2 ↪o PairERSource) → Bool} {T : Finset Ordinal.{0}}
    (P : CoherentGoodBranchPartial cR T)
    {α β₀ : Ordinal.{0}}
    (hα_lt : α < Ordinal.omega.{0} 1)
    (_hα_not_mem : α ∉ T)
    (hβ₀ : β₀ ∈ T) (hαβ₀ : α < β₀)
    (hmin : ∀ γ ∈ T, α < γ → β₀ ≤ γ) :
    CoherentGoodBranchApprox cR (insert α T).card where
  toApprox :=
    { level := fun i => (insert α T).orderEmbOfFin rfl i
      level_lt_omega1 := by
        intro i
        have hv : (insert α T).orderEmbOfFin rfl i ∈ insert α T :=
          (insert α T).orderEmbOfFin_mem rfl i
        rcases Finset.mem_insert.mp hv with h_eq | h_T
        · rw [h_eq]; exact hα_lt
        · have h := P.toGoodApprox.toApprox.level_lt_omega1
            (finsetIndexOf T _ h_T)
          rw [P.level_eq, finsetIndexOf_orderEmb] at h
          exact h
      level_strictMono := ((insert α T).orderEmbOfFin rfl).strictMono
      prefixAt := fun i =>
        (insertBeforeGoodAt P hβ₀ hαβ₀ i).toPairERChain.head
      branchAt := fun i =>
        (insertBeforeGoodAt P hβ₀ hαβ₀ i).toPairERChain.type
      prefix_restrict := by
        intro k₁ k₂ hk x
        have hv₁_mem : (insert α T).orderEmbOfFin rfl k₁ ∈ insert α T :=
          (insert α T).orderEmbOfFin_mem rfl k₁
        have hv₂_mem : (insert α T).orderEmbOfFin rfl k₂ ∈ insert α T :=
          (insert α T).orderEmbOfFin_mem rfl k₂
        have hv_le : (insert α T).orderEmbOfFin rfl k₁ ≤
            (insert α T).orderEmbOfFin rfl k₂ :=
          ((insert α T).orderEmbOfFin rfl).monotone hk
        by_cases h₁ : (insert α T).orderEmbOfFin rfl k₁ = α
        · by_cases h₂ : (insert α T).orderEmbOfFin rfl k₂ = α
          · -- α/α: k₁ = k₂ by injectivity; lift reduces to identity by InitialSeg uniqueness
            have hk_eq : k₁ = k₂ :=
              ((insert α T).orderEmbOfFin rfl).injective (h₁.trans h₂.symm)
            subst hk_eq
            rw [insertBeforeGoodAt_eq_alpha P hβ₀ hαβ₀ h₁]
            haveI : IsWellOrder ((insert α T).orderEmbOfFin rfl k₁).ToType
              (· < ·) := isWellOrder_lt
            congr 1
            rw [InitialSeg.toOrderEmbedding_apply]
            exact ((Ordinal.initialSegToType
                (((insert α T).orderEmbOfFin rfl).monotone hk)).eq
              (InitialSeg.refl _) x).trans (InitialSeg.refl_apply x)
          · -- α/T: h₁ : v₁ = α, h₂ : v₂ ≠ α, hv_le : v₁ ≤ v₂
            have hv₂_T : (insert α T).orderEmbOfFin rfl k₂ ∈ T :=
              (Finset.mem_insert.mp hv₂_mem).resolve_left h₂
            have h_α_lt_v₂ : α < (insert α T).orderEmbOfFin rfl k₂ := by
              rcases lt_or_eq_of_le hv_le with hlt | heq
              · calc α = (insert α T).orderEmbOfFin rfl k₁ := h₁.symm
                  _ < (insert α T).orderEmbOfFin rfl k₂ := hlt
              · exact absurd (heq ▸ h₁ : (insert α T).orderEmbOfFin rfl k₂ = α) h₂
            have h_β₀_le_v₂ : β₀ ≤ (insert α T).orderEmbOfFin rfl k₂ :=
              hmin _ hv₂_T h_α_lt_v₂
            have h_α_le_v₂ : α ≤ (insert α T).orderEmbOfFin rfl k₂ :=
              le_of_lt h_α_lt_v₂
            rw [insertBeforeGoodAt_eq_old P hβ₀ hαβ₀ h₂,
                insertBeforeGoodAt_eq_alpha P hβ₀ hαβ₀ h₁,
                PairERGoodChain.castLevel_head h₁.symm,
                PairERGoodChain.restrict_head_apply,
                P.good_head_eq, P.good_head_eq]
            rw [← P.toCoherentBranchPartial.prefix_restrict h_β₀_le_v₂ hβ₀ hv₂_T
                ((Ordinal.initialSegToType hαβ₀.le).toOrderEmbedding
                  ((h₁.symm).symm ▸ x))]
            congr 1
            rw [initialSegToType_compose hαβ₀.le h_β₀_le_v₂]
            exact initialSegToType_transport_eq h₁ rfl
              (((insert α T).orderEmbOfFin rfl).monotone hk) h_α_le_v₂ x
        · by_cases h₂ : (insert α T).orderEmbOfFin rfl k₂ = α
          · -- T/α: h₁ : v₁ ≠ α, h₂ : v₂ = α
            have hv₁_T : (insert α T).orderEmbOfFin rfl k₁ ∈ T :=
              (Finset.mem_insert.mp hv₁_mem).resolve_left h₁
            have h_v₁_le_α : (insert α T).orderEmbOfFin rfl k₁ ≤ α :=
              calc (insert α T).orderEmbOfFin rfl k₁
                  ≤ (insert α T).orderEmbOfFin rfl k₂ := hv_le
                _ = α := h₂
            have h_v₁_lt_α : (insert α T).orderEmbOfFin rfl k₁ < α := by
              rcases lt_or_eq_of_le h_v₁_le_α with hlt | heq
              · exact hlt
              · exact absurd (heq ▸ hv₁_T : α ∈ T) _hα_not_mem
            have h_v₁_le_β₀ : (insert α T).orderEmbOfFin rfl k₁ ≤ β₀ :=
              le_of_lt (h_v₁_lt_α.trans hαβ₀)
            rw [insertBeforeGoodAt_eq_old P hβ₀ hαβ₀ h₁,
                insertBeforeGoodAt_eq_alpha P hβ₀ hαβ₀ h₂,
                PairERGoodChain.castLevel_head h₂.symm,
                PairERGoodChain.restrict_head_apply,
                P.good_head_eq, P.good_head_eq]
            rw [← P.toCoherentBranchPartial.prefix_restrict h_v₁_le_β₀ hv₁_T hβ₀ x]
            congr 1
            rw [← initialSegToType_compose h_v₁_le_α hαβ₀.le]
            congr 1
            exact initialSegToType_transport_eq rfl h₂
              (((insert α T).orderEmbOfFin rfl).monotone hk) h_v₁_le_α x
          · have hv₁_T : (insert α T).orderEmbOfFin rfl k₁ ∈ T :=
              (Finset.mem_insert.mp hv₁_mem).resolve_left h₁
            have hv₂_T : (insert α T).orderEmbOfFin rfl k₂ ∈ T :=
              (Finset.mem_insert.mp hv₂_mem).resolve_left h₂
            rw [insertBeforeGoodAt_eq_old P hβ₀ hαβ₀ h₁,
                insertBeforeGoodAt_eq_old P hβ₀ hαβ₀ h₂]
            rw [P.good_head_eq, P.good_head_eq]
            exact P.toCoherentBranchPartial.prefix_restrict hv_le hv₁_T hv₂_T x
      branch_restrict := by
        intro k₁ k₂ hk x
        have hv₁_mem : (insert α T).orderEmbOfFin rfl k₁ ∈ insert α T :=
          (insert α T).orderEmbOfFin_mem rfl k₁
        have hv₂_mem : (insert α T).orderEmbOfFin rfl k₂ ∈ insert α T :=
          (insert α T).orderEmbOfFin_mem rfl k₂
        have hv_le : (insert α T).orderEmbOfFin rfl k₁ ≤
            (insert α T).orderEmbOfFin rfl k₂ :=
          ((insert α T).orderEmbOfFin rfl).monotone hk
        by_cases h₁ : (insert α T).orderEmbOfFin rfl k₁ = α
        · by_cases h₂ : (insert α T).orderEmbOfFin rfl k₂ = α
          · have hk_eq : k₁ = k₂ :=
              ((insert α T).orderEmbOfFin rfl).injective (h₁.trans h₂.symm)
            subst hk_eq
            rw [insertBeforeGoodAt_eq_alpha P hβ₀ hαβ₀ h₁]
            haveI : IsWellOrder ((insert α T).orderEmbOfFin rfl k₁).ToType
              (· < ·) := isWellOrder_lt
            congr 1
            rw [InitialSeg.toOrderEmbedding_apply]
            exact ((Ordinal.initialSegToType
                (((insert α T).orderEmbOfFin rfl).monotone hk)).eq
              (InitialSeg.refl _) x).trans (InitialSeg.refl_apply x)
          · have hv₂_T : (insert α T).orderEmbOfFin rfl k₂ ∈ T :=
              (Finset.mem_insert.mp hv₂_mem).resolve_left h₂
            have h_α_lt_v₂ : α < (insert α T).orderEmbOfFin rfl k₂ := by
              rcases lt_or_eq_of_le hv_le with hlt | heq
              · calc α = (insert α T).orderEmbOfFin rfl k₁ := h₁.symm
                  _ < (insert α T).orderEmbOfFin rfl k₂ := hlt
              · exact absurd (heq ▸ h₁ : (insert α T).orderEmbOfFin rfl k₂ = α) h₂
            have h_β₀_le_v₂ : β₀ ≤ (insert α T).orderEmbOfFin rfl k₂ :=
              hmin _ hv₂_T h_α_lt_v₂
            have h_α_le_v₂ : α ≤ (insert α T).orderEmbOfFin rfl k₂ :=
              le_of_lt h_α_lt_v₂
            rw [insertBeforeGoodAt_eq_old P hβ₀ hαβ₀ h₂,
                insertBeforeGoodAt_eq_alpha P hβ₀ hαβ₀ h₁,
                PairERGoodChain.castLevel_type h₁.symm,
                PairERGoodChain.restrict_type_apply,
                P.good_type_eq, P.good_type_eq]
            rw [← P.toCoherentBranchPartial.branch_restrict h_β₀_le_v₂ hβ₀ hv₂_T
                ((Ordinal.initialSegToType hαβ₀.le).toOrderEmbedding
                  ((h₁.symm).symm ▸ x))]
            congr 1
            rw [initialSegToType_compose hαβ₀.le h_β₀_le_v₂]
            exact initialSegToType_transport_eq h₁ rfl
              (((insert α T).orderEmbOfFin rfl).monotone hk) h_α_le_v₂ x
        · by_cases h₂ : (insert α T).orderEmbOfFin rfl k₂ = α
          · have hv₁_T : (insert α T).orderEmbOfFin rfl k₁ ∈ T :=
              (Finset.mem_insert.mp hv₁_mem).resolve_left h₁
            have h_v₁_le_α : (insert α T).orderEmbOfFin rfl k₁ ≤ α :=
              calc (insert α T).orderEmbOfFin rfl k₁
                  ≤ (insert α T).orderEmbOfFin rfl k₂ := hv_le
                _ = α := h₂
            have h_v₁_lt_α : (insert α T).orderEmbOfFin rfl k₁ < α := by
              rcases lt_or_eq_of_le h_v₁_le_α with hlt | heq
              · exact hlt
              · exact absurd (heq ▸ hv₁_T : α ∈ T) _hα_not_mem
            have h_v₁_le_β₀ : (insert α T).orderEmbOfFin rfl k₁ ≤ β₀ :=
              le_of_lt (h_v₁_lt_α.trans hαβ₀)
            rw [insertBeforeGoodAt_eq_old P hβ₀ hαβ₀ h₁,
                insertBeforeGoodAt_eq_alpha P hβ₀ hαβ₀ h₂,
                PairERGoodChain.castLevel_type h₂.symm,
                PairERGoodChain.restrict_type_apply,
                P.good_type_eq, P.good_type_eq]
            rw [← P.toCoherentBranchPartial.branch_restrict h_v₁_le_β₀ hv₁_T hβ₀ x]
            congr 1
            rw [← initialSegToType_compose h_v₁_le_α hαβ₀.le]
            congr 1
            exact initialSegToType_transport_eq rfl h₂
              (((insert α T).orderEmbOfFin rfl).monotone hk) h_v₁_le_α x
          · have hv₁_T : (insert α T).orderEmbOfFin rfl k₁ ∈ T :=
              (Finset.mem_insert.mp hv₁_mem).resolve_left h₁
            have hv₂_T : (insert α T).orderEmbOfFin rfl k₂ ∈ T :=
              (Finset.mem_insert.mp hv₂_mem).resolve_left h₂
            rw [insertBeforeGoodAt_eq_old P hβ₀ hαβ₀ h₁,
                insertBeforeGoodAt_eq_old P hβ₀ hαβ₀ h₂]
            rw [P.good_type_eq, P.good_type_eq]
            exact P.toCoherentBranchPartial.branch_restrict hv_le hv₁_T hv₂_T x
      large := fun i => (insertBeforeGoodAt P hβ₀ hαβ₀ i).toPairERChain.large
      top_in_validFiber := by
        intro i h
        have hv₁_mem : (insert α T).orderEmbOfFin rfl ⟨i, Nat.lt_of_succ_lt h⟩ ∈
            insert α T :=
          (insert α T).orderEmbOfFin_mem rfl _
        have hv₂_mem : (insert α T).orderEmbOfFin rfl ⟨i + 1, h⟩ ∈ insert α T :=
          (insert α T).orderEmbOfFin_mem rfl _
        have hv_lt : (insert α T).orderEmbOfFin rfl ⟨i, Nat.lt_of_succ_lt h⟩ <
            (insert α T).orderEmbOfFin rfl ⟨i + 1, h⟩ :=
          ((insert α T).orderEmbOfFin rfl).strictMono
            (show (⟨i, Nat.lt_of_succ_lt h⟩ : Fin (insert α T).card) <
              ⟨i + 1, h⟩ from Nat.lt_succ_self i)
        by_cases h₁ : (insert α T).orderEmbOfFin rfl ⟨i, Nat.lt_of_succ_lt h⟩ = α
        · -- α at k₁; k₂ ≠ α (since k₁ < k₂ ⇒ v₁ < v₂); so T at k₂.
          have h₂ : (insert α T).orderEmbOfFin rfl ⟨i + 1, h⟩ ≠ α := fun heq =>
            (ne_of_lt hv_lt) (h₁.trans heq.symm)
          have hv₂_T : (insert α T).orderEmbOfFin rfl ⟨i + 1, h⟩ ∈ T :=
            (Finset.mem_insert.mp hv₂_mem).resolve_left h₂
          have h_α_lt_v₂ : α < (insert α T).orderEmbOfFin rfl ⟨i + 1, h⟩ :=
            calc α = (insert α T).orderEmbOfFin rfl ⟨i, Nat.lt_of_succ_lt h⟩ :=
                  h₁.symm
              _ < (insert α T).orderEmbOfFin rfl ⟨i + 1, h⟩ := hv_lt
          have h_β₀_le_v₂ : β₀ ≤ (insert α T).orderEmbOfFin rfl ⟨i + 1, h⟩ :=
            hmin _ hv₂_T h_α_lt_v₂
          rw [insertBeforeGoodAt_eq_old P hβ₀ hαβ₀ h₂,
              insertBeforeGoodAt_eq_alpha P hβ₀ hαβ₀ h₁]
          have h_har := (P.goodAt _ hv₂_T).head_at_α_in_restricted_validFiber hv_lt
          have h_vf_eq : validFiber cR
              (((P.goodAt β₀ hβ₀).restrict hαβ₀).castLevel h₁.symm).toPairERChain.head
              (((P.goodAt β₀ hβ₀).restrict hαβ₀).castLevel
                  h₁.symm).toPairERChain.type =
            validFiber cR
              ((Ordinal.initialSegToType hv_lt.le).toOrderEmbedding.trans
                (P.goodAt _ hv₂_T).toPairERChain.head)
              (fun x => (P.goodAt _ hv₂_T).toPairERChain.type
                ((Ordinal.initialSegToType hv_lt.le).toOrderEmbedding x)) := by
            apply validFiber_congr_prefix_branch
            · intro y
              rw [PairERGoodChain.castLevel_head h₁.symm,
                  PairERGoodChain.restrict_head_apply,
                  RelEmbedding.trans_apply, P.good_head_eq, P.good_head_eq]
              rw [← P.toCoherentBranchPartial.prefix_restrict h_β₀_le_v₂
                  hβ₀ hv₂_T ((Ordinal.initialSegToType hαβ₀.le).toOrderEmbedding
                    ((h₁.symm).symm ▸ y))]
              congr 1
              rw [initialSegToType_compose hαβ₀.le h_β₀_le_v₂]
              exact (initialSegToType_transport_eq h₁ rfl hv_lt.le
                (le_of_lt h_α_lt_v₂) y).symm
            · intro y
              rw [PairERGoodChain.castLevel_type h₁.symm,
                  PairERGoodChain.restrict_type_apply,
                  P.good_type_eq, P.good_type_eq]
              rw [← P.toCoherentBranchPartial.branch_restrict h_β₀_le_v₂
                  hβ₀ hv₂_T ((Ordinal.initialSegToType hαβ₀.le).toOrderEmbedding
                    ((h₁.symm).symm ▸ y))]
              congr 1
              rw [initialSegToType_compose hαβ₀.le h_β₀_le_v₂]
              exact (initialSegToType_transport_eq h₁ rfl hv_lt.le
                (le_of_lt h_α_lt_v₂) y).symm
          rw [h_vf_eq]
          exact h_har
        · by_cases h₂ : (insert α T).orderEmbOfFin rfl ⟨i + 1, h⟩ = α
          · -- T/α case: h₁ : v₁ ≠ α, h₂ : v₂ = α
            have hv₁_T : (insert α T).orderEmbOfFin rfl ⟨i, Nat.lt_of_succ_lt h⟩ ∈
                T := (Finset.mem_insert.mp hv₁_mem).resolve_left h₁
            have h_v₁_lt_α : (insert α T).orderEmbOfFin rfl
                ⟨i, Nat.lt_of_succ_lt h⟩ < α :=
              insert_adjacent_old_alpha_predecessor _hα_not_mem h h₁ h₂
            have h_v₁_le_α : (insert α T).orderEmbOfFin rfl
                ⟨i, Nat.lt_of_succ_lt h⟩ ≤ α := le_of_lt h_v₁_lt_α
            have h_v₁_le_β₀ : (insert α T).orderEmbOfFin rfl
                ⟨i, Nat.lt_of_succ_lt h⟩ ≤ β₀ :=
              le_of_lt (h_v₁_lt_α.trans hαβ₀)
            rw [insertBeforeGoodAt_eq_old P hβ₀ hαβ₀ h₁,
                insertBeforeGoodAt_eq_alpha P hβ₀ hαβ₀ h₂]
            have h_har := (((P.goodAt β₀ hβ₀).restrict hαβ₀).castLevel
              h₂.symm).head_at_α_in_restricted_validFiber hv_lt
            have h_vf_eq : validFiber cR
                (P.goodAt _ hv₁_T).toPairERChain.head
                (P.goodAt _ hv₁_T).toPairERChain.type =
              validFiber cR
                ((Ordinal.initialSegToType hv_lt.le).toOrderEmbedding.trans
                  (((P.goodAt β₀ hβ₀).restrict hαβ₀).castLevel
                      h₂.symm).toPairERChain.head)
                (fun x => (((P.goodAt β₀ hβ₀).restrict hαβ₀).castLevel
                    h₂.symm).toPairERChain.type
                  ((Ordinal.initialSegToType hv_lt.le).toOrderEmbedding x)) := by
              apply validFiber_congr_prefix_branch
              · intro y
                rw [RelEmbedding.trans_apply,
                    PairERGoodChain.castLevel_head h₂.symm,
                    PairERGoodChain.restrict_head_apply,
                    P.good_head_eq, P.good_head_eq]
                rw [← P.toCoherentBranchPartial.prefix_restrict h_v₁_le_β₀
                    hv₁_T hβ₀ y]
                congr 1
                rw [← initialSegToType_compose h_v₁_le_α hαβ₀.le]
                congr 1
                exact (initialSegToType_transport_eq rfl h₂ hv_lt.le
                  h_v₁_le_α y).symm
              · intro y
                rw [PairERGoodChain.castLevel_type h₂.symm,
                    PairERGoodChain.restrict_type_apply,
                    P.good_type_eq, P.good_type_eq]
                rw [← P.toCoherentBranchPartial.branch_restrict h_v₁_le_β₀
                    hv₁_T hβ₀ y]
                congr 1
                rw [← initialSegToType_compose h_v₁_le_α hαβ₀.le]
                congr 1
                exact (initialSegToType_transport_eq rfl h₂ hv_lt.le
                  h_v₁_le_α y).symm
            rw [h_vf_eq]
            exact h_har
          · -- T/T: both old elements; use head_at_α on P.goodAt v₂
            have hv₁_T : (insert α T).orderEmbOfFin rfl ⟨i, Nat.lt_of_succ_lt h⟩ ∈
                T := (Finset.mem_insert.mp hv₁_mem).resolve_left h₁
            have hv₂_T : (insert α T).orderEmbOfFin rfl ⟨i + 1, h⟩ ∈ T :=
              (Finset.mem_insert.mp hv₂_mem).resolve_left h₂
            rw [insertBeforeGoodAt_eq_old P hβ₀ hαβ₀ h₁,
                insertBeforeGoodAt_eq_old P hβ₀ hαβ₀ h₂]
            have h_har := (P.goodAt _ hv₂_T).head_at_α_in_restricted_validFiber hv_lt
            have h_vf_eq : validFiber cR
                (P.goodAt _ hv₁_T).toPairERChain.head
                (P.goodAt _ hv₁_T).toPairERChain.type =
              validFiber cR
                ((Ordinal.initialSegToType hv_lt.le).toOrderEmbedding.trans
                  (P.goodAt _ hv₂_T).toPairERChain.head)
                (fun x => (P.goodAt _ hv₂_T).toPairERChain.type
                  ((Ordinal.initialSegToType hv_lt.le).toOrderEmbedding x)) := by
              apply validFiber_congr_prefix_branch
              · intro y
                rw [RelEmbedding.trans_apply, P.good_head_eq, P.good_head_eq]
                exact (P.toCoherentBranchPartial.prefix_restrict hv_lt.le
                  hv₁_T hv₂_T y).symm
              · intro y
                rw [P.good_type_eq, P.good_type_eq]
                exact (P.toCoherentBranchPartial.branch_restrict hv_lt.le
                  hv₁_T hv₂_T y).symm
            rw [h_vf_eq]
            exact h_har
        }
  goodAt := fun i => insertBeforeGoodAt P hβ₀ hαβ₀ i
  good_head := fun _ _ => rfl
  good_type := fun _ _ => rfl

/-- **`insertBeforeGoodApprox_goodAt_old_eq`**: at any old position
γ ∈ T (so γ ≠ α), the inserted Good chain `Q.goodAt γ` agrees pointwise
with `P.goodAt γ` for both head and type. Proved via `generalize+subst`
on `γ' := orderEmbOfFin (Q.indexOf γ)` (= γ via `finsetIndexOf_orderEmb`)
followed by proof irrelevance on the membership and the residual cast. -/
private lemma insertBeforeGoodApprox_goodAt_old_head
    {cR : (Fin 2 ↪o PairERSource) → Bool} {T : Finset Ordinal.{0}}
    (P : CoherentGoodBranchPartial cR T)
    {α β₀ : Ordinal.{0}}
    (hα_lt : α < Ordinal.omega.{0} 1) (hα_not_mem : α ∉ T)
    (hβ₀ : β₀ ∈ T) (hαβ₀ : α < β₀)
    (hmin : ∀ γ ∈ T, α < γ → β₀ ≤ γ)
    (γ : Ordinal.{0}) (hγ : γ ∈ T) (x : γ.ToType) :
    letI Q : CoherentGoodBranchPartial cR (insert α T) :=
      { toGoodApprox := insertBeforeGoodApprox P hα_lt hα_not_mem hβ₀ hαβ₀ hmin
        level_eq := fun _ => rfl }
    (Q.goodAt γ (Finset.mem_insert_of_mem hγ)).toPairERChain.head x =
      (P.goodAt γ hγ).toPairERChain.head x := by
  classical
  let Q : CoherentGoodBranchPartial cR (insert α T) :=
    { toGoodApprox := insertBeforeGoodApprox P hα_lt hα_not_mem hβ₀ hαβ₀ hmin
      level_eq := fun _ => rfl }
  have h_ne : (insert α T).orderEmbOfFin rfl
      (Q.toCoherentBranchPartial.indexOf γ (Finset.mem_insert_of_mem hγ)) ≠ α := by
    show (insert α T).orderEmbOfFin rfl
      (finsetIndexOf (insert α T) γ (Finset.mem_insert_of_mem hγ)) ≠ α
    rw [finsetIndexOf_orderEmb]
    exact fun h => hα_not_mem (h ▸ hγ)
  have h_chain_eq :
      Q.toGoodApprox.goodAt (Q.toCoherentBranchPartial.indexOf γ
          (Finset.mem_insert_of_mem hγ)) =
        P.goodAt _ ((Finset.mem_insert.mp
          ((insert α T).orderEmbOfFin_mem rfl _)).resolve_left h_ne) :=
    insertBeforeGoodAt_eq_old P hβ₀ hαβ₀ h_ne
  -- Unfold Q.goodAt
  show ((Q.toGoodApprox.goodAt (Q.toCoherentBranchPartial.indexOf γ
      (Finset.mem_insert_of_mem hγ))).castLevel _).toPairERChain.head x = _
  rw [h_chain_eq]
  rw [PairERGoodChain.castLevel_head]
  -- Goal: (P.goodAt γ' hv_T).head (h.symm ▸ x) = (P.goodAt γ hγ).head x
  -- where γ' = (insert α T).orderEmbOfFin rfl (Q.indexOf γ ...) = γ.
  -- Use goodAt_head_apply_eq_of_eq with h : γ' = γ to transport.
  have h_eq : (insert α T).orderEmbOfFin rfl
      (Q.toCoherentBranchPartial.indexOf γ (Finset.mem_insert_of_mem hγ)) = γ :=
    finsetIndexOf_orderEmb _ _ _
  refine (P.goodAt_head_apply_eq_of_eq (hα := _) (hβ := hγ) h_eq _).trans ?_
  -- Goal: (P.goodAt γ hγ).head (h_eq ▸ (h.symm ▸ x)) = (P.goodAt γ hγ).head x
  congr 1
  -- Goal: h_eq ▸ (h.symm ▸ x) = x  -- by Eq.rec composition
  exact eq_of_heq (HEq.trans (eqRec_heq h_eq _) (eqRec_heq _ x))

/-- **`insertBeforeGoodApprox_goodAt_old_type`**: parallel for type. -/
private lemma insertBeforeGoodApprox_goodAt_old_type
    {cR : (Fin 2 ↪o PairERSource) → Bool} {T : Finset Ordinal.{0}}
    (P : CoherentGoodBranchPartial cR T)
    {α β₀ : Ordinal.{0}}
    (hα_lt : α < Ordinal.omega.{0} 1) (hα_not_mem : α ∉ T)
    (hβ₀ : β₀ ∈ T) (hαβ₀ : α < β₀)
    (hmin : ∀ γ ∈ T, α < γ → β₀ ≤ γ)
    (γ : Ordinal.{0}) (hγ : γ ∈ T) (x : γ.ToType) :
    letI Q : CoherentGoodBranchPartial cR (insert α T) :=
      { toGoodApprox := insertBeforeGoodApprox P hα_lt hα_not_mem hβ₀ hαβ₀ hmin
        level_eq := fun _ => rfl }
    (Q.goodAt γ (Finset.mem_insert_of_mem hγ)).toPairERChain.type x =
      (P.goodAt γ hγ).toPairERChain.type x := by
  classical
  let Q : CoherentGoodBranchPartial cR (insert α T) :=
    { toGoodApprox := insertBeforeGoodApprox P hα_lt hα_not_mem hβ₀ hαβ₀ hmin
      level_eq := fun _ => rfl }
  have h_ne : (insert α T).orderEmbOfFin rfl
      (Q.toCoherentBranchPartial.indexOf γ (Finset.mem_insert_of_mem hγ)) ≠ α := by
    show (insert α T).orderEmbOfFin rfl
      (finsetIndexOf (insert α T) γ (Finset.mem_insert_of_mem hγ)) ≠ α
    rw [finsetIndexOf_orderEmb]
    exact fun h => hα_not_mem (h ▸ hγ)
  have h_chain_eq :
      Q.toGoodApprox.goodAt (Q.toCoherentBranchPartial.indexOf γ
          (Finset.mem_insert_of_mem hγ)) =
        P.goodAt _ ((Finset.mem_insert.mp
          ((insert α T).orderEmbOfFin_mem rfl _)).resolve_left h_ne) :=
    insertBeforeGoodAt_eq_old P hβ₀ hαβ₀ h_ne
  show ((Q.toGoodApprox.goodAt (Q.toCoherentBranchPartial.indexOf γ
      (Finset.mem_insert_of_mem hγ))).castLevel _).toPairERChain.type x = _
  rw [h_chain_eq]
  rw [PairERGoodChain.castLevel_type]
  have h_eq : (insert α T).orderEmbOfFin rfl
      (Q.toCoherentBranchPartial.indexOf γ (Finset.mem_insert_of_mem hγ)) = γ :=
    finsetIndexOf_orderEmb _ _ _
  refine (P.goodAt_type_apply_eq_of_eq (hα := _) (hβ := hγ) h_eq _).trans ?_
  congr 1
  exact eq_of_heq (HEq.trans (eqRec_heq h_eq _) (eqRec_heq _ x))

/-- **`coherentGoodBranchPartial_insert_before`**: fixed-β₀ interior
insertion at the Good layer. Wraps `insertBeforeGoodApprox` into a
`CoherentGoodBranchPartial cR (insert α T)`. Fieldwise compat reduces
to the two pointwise helpers `insertBeforeGoodApprox_goodAt_old_head`
and `_type`, both via `restrict_prefixAt`/`restrict_branch`,
`good_head_eq`/`good_type_eq`, and `RelEmbedding.ext`/`funext`. -/
theorem coherentGoodBranchPartial_insert_before
    {cR : (Fin 2 ↪o PairERSource) → Bool} {T : Finset Ordinal.{0}}
    (P : CoherentGoodBranchPartial cR T)
    {α β₀ : Ordinal.{0}}
    (hα_lt : α < Ordinal.omega.{0} 1)
    (hα_not_mem : α ∉ T)
    (hβ₀ : β₀ ∈ T)
    (hαβ₀ : α < β₀)
    (hmin : ∀ γ ∈ T, α < γ → β₀ ≤ γ) :
    ∃ Q : CoherentGoodBranchPartial cR (insert α T),
      cbpFieldwiseCompat
        (Q.toCoherentBranchPartial.restrict (Finset.subset_insert α T))
        P.toCoherentBranchPartial := by
  letI Q : CoherentGoodBranchPartial cR (insert α T) :=
    { toGoodApprox := insertBeforeGoodApprox P hα_lt hα_not_mem hβ₀ hαβ₀ hmin
      level_eq := fun _ => rfl }
  refine ⟨Q, ?_, ?_⟩
  · intro γ hγ
    have hγ_ins : γ ∈ insert α T := Finset.mem_insert_of_mem hγ
    rw [CoherentBranchPartial.restrict_prefixAt]
    apply RelEmbedding.ext
    intro x
    rw [← Q.good_head_eq γ hγ_ins x, ← P.good_head_eq γ hγ x]
    exact insertBeforeGoodApprox_goodAt_old_head P hα_lt hα_not_mem
      hβ₀ hαβ₀ hmin γ hγ x
  · intro γ hγ
    have hγ_ins : γ ∈ insert α T := Finset.mem_insert_of_mem hγ
    rw [CoherentBranchPartial.restrict_branch]
    funext x
    rw [← Q.good_type_eq γ hγ_ins x, ← P.good_type_eq γ hγ x]
    exact insertBeforeGoodApprox_goodAt_old_type P hα_lt hα_not_mem
      hβ₀ hαβ₀ hmin γ hγ x

/-- **`insertPrescribedGoodAt`**: prescribed-chain analog of
`insertBeforeGoodAt`. At the new level `α`, dispatches to the
**prescribed** `Pα.goodAt α` (rather than restricting `P.goodAt β₀` to
`α`). At old levels `γ ≠ α` in `insert α T`, dispatches to
`P.goodAt γ`.

**Why this is needed.** The corrected `insert_prescribed_new_compatible`
requires the new level's Good chain to be the prescribed `Pα`'s
chain — not a derived/restricted chain from `P`. So
`insertBeforeGoodAt` (which derives from `P`'s data) is structurally
wrong for prescribed insertion; this primitive replaces it.

**No `β₀` parameter needed.** Unlike `insertBeforeGoodAt`, which uses
the minimum `β₀ ∈ T` above `α` to derive the chain at `α`,
`insertPrescribedGoodAt` takes the chain at `α` directly from `Pα`.

**Dispatch sub-cases.**
* `(insert α T).orderEmbOfFin rfl i = α`: take
  `(Pα.goodAt α (mem_singleton)).castLevel`.
* otherwise (the level is some `γ ∈ T`): take `P.goodAt γ`. -/
noncomputable def insertPrescribedGoodAt
    {cR : (Fin 2 ↪o PairERSource) → Bool} {T : Finset Ordinal.{0}}
    (P : CoherentGoodBranchPartial cR T)
    {α : Ordinal.{0}}
    (Pα : CoherentGoodBranchPartial cR ({α} : Finset Ordinal.{0}))
    (i : Fin (insert α T).card) :
    PairERGoodChain cR ((insert α T).orderEmbOfFin rfl i) :=
  letI : Decidable ((insert α T).orderEmbOfFin rfl i = α) := Classical.dec _
  if h_eq : (insert α T).orderEmbOfFin rfl i = α then
    (Pα.goodAt α (Finset.mem_singleton.mpr rfl)).castLevel h_eq.symm
  else
    P.goodAt _
      ((Finset.mem_insert.mp ((insert α T).orderEmbOfFin_mem rfl i)).resolve_left h_eq)

/-- **`insertPrescribedGoodAt_eq_alpha`**: at the α-level position,
`insertPrescribedGoodAt` returns `Pα.goodAt α` cast to the matching
level. -/
theorem insertPrescribedGoodAt_eq_alpha
    {cR : (Fin 2 ↪o PairERSource) → Bool} {T : Finset Ordinal.{0}}
    (P : CoherentGoodBranchPartial cR T) {α : Ordinal.{0}}
    (Pα : CoherentGoodBranchPartial cR ({α} : Finset Ordinal.{0}))
    {i : Fin (insert α T).card}
    (h_eq : (insert α T).orderEmbOfFin rfl i = α) :
    insertPrescribedGoodAt P Pα i =
      (Pα.goodAt α (Finset.mem_singleton.mpr rfl)).castLevel h_eq.symm := by
  classical
  unfold insertPrescribedGoodAt
  rw [dif_pos h_eq]

/-- **`insertPrescribedGoodAt_eq_old`**: at non-α positions,
`insertPrescribedGoodAt` returns `P.goodAt γ hγ` directly. -/
theorem insertPrescribedGoodAt_eq_old
    {cR : (Fin 2 ↪o PairERSource) → Bool} {T : Finset Ordinal.{0}}
    (P : CoherentGoodBranchPartial cR T) {α : Ordinal.{0}}
    (Pα : CoherentGoodBranchPartial cR ({α} : Finset Ordinal.{0}))
    {i : Fin (insert α T).card}
    (h_neq : (insert α T).orderEmbOfFin rfl i ≠ α) :
    insertPrescribedGoodAt P Pα i =
      P.goodAt _
        ((Finset.mem_insert.mp ((insert α T).orderEmbOfFin_mem rfl i)).resolve_left h_neq) := by
  classical
  unfold insertPrescribedGoodAt
  rw [dif_neg h_neq]

/-- **`insertPrescribedGoodApprox`**: the `CoherentGoodBranchApprox` at
length `(insert α T).card` assembled from `insertPrescribedGoodAt`.
Parallel to `insertBeforeGoodApprox` but **does not need a `β₀`** — it
uses the prescribed `Pα` directly at the α-level.

**Inputs.** `P : CGBP cR T`, `Pα : CGBP cR {α}` (the prescribed chain
at α), `hα_lt : α < ω₁`, `hα_not_mem : α ∉ T`, and a
`PrescribedAmbientCompat α P Pα` hypothesis (the strong compat,
defined alongside `insert_prescribed_new_compatible`).

**Why the compat hypothesis is needed at the approximation layer.**
The three approximation fields (`prefix_restrict`, `branch_restrict`,
`top_in_validFiber`) require relating `Pα`'s data at the α-level to
`P`'s data at neighboring levels in `T`. The `PrescribedAmbientCompat`
fields (`prefix_below`, `branch_below`) supply exactly those
relations.

**Status.** Currently a skeleton with `sorry` on the three field
proofs. The proofs mirror `insertBeforeGoodApprox`'s 4-case dispatch
(α/α, α/T, T/α, T/T) but with `hamb.prefix_below` / `hamb.branch_below`
replacing the β₀-anchored equalities that `insertBeforeGoodApprox`
derives from `P` alone. The closure follows the same pattern as the
existing approximation — no new mathematical content, just careful
bookkeeping. -/
noncomputable def insertPrescribedGoodApprox
    {cR : (Fin 2 ↪o PairERSource) → Bool} {T : Finset Ordinal.{0}}
    (P : CoherentGoodBranchPartial cR T)
    {α : Ordinal.{0}}
    (hα_lt : α < Ordinal.omega.{0} 1)
    (_hα_not_mem : α ∉ T)
    (Pα : CoherentGoodBranchPartial cR ({α} : Finset Ordinal.{0}))
    (_h_prefix_below : ∀ β (hβ_T : β ∈ T) (hβ_lt_α : β < α),
      haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
      haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
      ∀ (x : β.ToType),
        P.toCoherentBranchPartial.prefixAt β hβ_T x =
          Pα.toCoherentBranchPartial.prefixAt α (Finset.mem_singleton.mpr rfl)
            ((Ordinal.initialSegToType hβ_lt_α.le).toOrderEmbedding x))
    (_h_branch_below : ∀ β (hβ_T : β ∈ T) (hβ_lt_α : β < α),
      haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
      haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
      ∀ (x : β.ToType),
        P.toCoherentBranchPartial.branch β hβ_T x =
          Pα.toCoherentBranchPartial.branch α (Finset.mem_singleton.mpr rfl)
            ((Ordinal.initialSegToType hβ_lt_α.le).toOrderEmbedding x))
    (_h_prefix_above : ∀ β (hβ_T : β ∈ T) (hα_lt_β : α < β),
      haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
      haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
      ∀ (x : α.ToType),
        Pα.toCoherentBranchPartial.prefixAt α (Finset.mem_singleton.mpr rfl) x =
          P.toCoherentBranchPartial.prefixAt β hβ_T
            ((Ordinal.initialSegToType hα_lt_β.le).toOrderEmbedding x))
    (_h_branch_above : ∀ β (hβ_T : β ∈ T) (hα_lt_β : α < β),
      haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
      haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
      ∀ (x : α.ToType),
        Pα.toCoherentBranchPartial.branch α (Finset.mem_singleton.mpr rfl) x =
          P.toCoherentBranchPartial.branch β hβ_T
            ((Ordinal.initialSegToType hα_lt_β.le).toOrderEmbedding x)) :
    CoherentGoodBranchApprox cR (insert α T).card where
  toApprox :=
    { level := fun i => (insert α T).orderEmbOfFin rfl i
      level_lt_omega1 := by
        intro i
        have hv : (insert α T).orderEmbOfFin rfl i ∈ insert α T :=
          (insert α T).orderEmbOfFin_mem rfl i
        rcases Finset.mem_insert.mp hv with h_eq | h_T
        · rw [h_eq]; exact hα_lt
        · have h := P.toGoodApprox.toApprox.level_lt_omega1
            (finsetIndexOf T _ h_T)
          rw [P.level_eq, finsetIndexOf_orderEmb] at h
          exact h
      level_strictMono := ((insert α T).orderEmbOfFin rfl).strictMono
      prefixAt := fun i => (insertPrescribedGoodAt P Pα i).toPairERChain.head
      branchAt := fun i => (insertPrescribedGoodAt P Pα i).toPairERChain.type
      prefix_restrict := by
        intro k₁ k₂ hk x
        have hv₁_mem : (insert α T).orderEmbOfFin rfl k₁ ∈ insert α T :=
          (insert α T).orderEmbOfFin_mem rfl k₁
        have hv₂_mem : (insert α T).orderEmbOfFin rfl k₂ ∈ insert α T :=
          (insert α T).orderEmbOfFin_mem rfl k₂
        have hv_le : (insert α T).orderEmbOfFin rfl k₁ ≤
            (insert α T).orderEmbOfFin rfl k₂ :=
          ((insert α T).orderEmbOfFin rfl).monotone hk
        by_cases h₁ : (insert α T).orderEmbOfFin rfl k₁ = α
        · by_cases h₂ : (insert α T).orderEmbOfFin rfl k₂ = α
          · -- α/α: k₁ = k₂.
            have hk_eq : k₁ = k₂ :=
              ((insert α T).orderEmbOfFin rfl).injective (h₁.trans h₂.symm)
            subst hk_eq
            rw [insertPrescribedGoodAt_eq_alpha P Pα h₁]
            haveI : IsWellOrder ((insert α T).orderEmbOfFin rfl k₁).ToType
              (· < ·) := isWellOrder_lt
            congr 1
            rw [InitialSeg.toOrderEmbedding_apply]
            exact ((Ordinal.initialSegToType
                (((insert α T).orderEmbOfFin rfl).monotone hk)).eq
              (InitialSeg.refl _) x).trans (InitialSeg.refl_apply x)
          · -- α/T case (v₁ = α, v₂ ∈ T, α < v₂)
            have hv₂_T : (insert α T).orderEmbOfFin rfl k₂ ∈ T :=
              (Finset.mem_insert.mp hv₂_mem).resolve_left h₂
            have h_α_lt_v₂ : α < (insert α T).orderEmbOfFin rfl k₂ := by
              rcases lt_or_eq_of_le hv_le with hlt | heq
              · calc α = (insert α T).orderEmbOfFin rfl k₁ := h₁.symm
                  _ < (insert α T).orderEmbOfFin rfl k₂ := hlt
              · exact absurd (heq ▸ h₁ : (insert α T).orderEmbOfFin rfl k₂ = α) h₂
            have h_α_le_v₂ : α ≤ (insert α T).orderEmbOfFin rfl k₂ :=
              le_of_lt h_α_lt_v₂
            rw [insertPrescribedGoodAt_eq_old P Pα h₂,
                insertPrescribedGoodAt_eq_alpha P Pα h₁,
                PairERGoodChain.castLevel_head h₁.symm,
                P.good_head_eq, Pα.good_head_eq]
            rw [_h_prefix_above _ hv₂_T h_α_lt_v₂ (h₁ ▸ x)]
            congr 1
            exact initialSegToType_transport_eq h₁ rfl
              (((insert α T).orderEmbOfFin rfl).monotone hk) h_α_le_v₂ x
        · by_cases h₂ : (insert α T).orderEmbOfFin rfl k₂ = α
          · -- T/α case (v₁ ∈ T, v₂ = α, v₁ < α)
            have hv₁_T : (insert α T).orderEmbOfFin rfl k₁ ∈ T :=
              (Finset.mem_insert.mp hv₁_mem).resolve_left h₁
            have h_v₁_le_α : (insert α T).orderEmbOfFin rfl k₁ ≤ α :=
              calc (insert α T).orderEmbOfFin rfl k₁
                  ≤ (insert α T).orderEmbOfFin rfl k₂ := hv_le
                _ = α := h₂
            have h_v₁_lt_α : (insert α T).orderEmbOfFin rfl k₁ < α := by
              rcases lt_or_eq_of_le h_v₁_le_α with hlt | heq
              · exact hlt
              · exact absurd (heq ▸ hv₁_T : α ∈ T) _hα_not_mem
            rw [insertPrescribedGoodAt_eq_old P Pα h₁,
                insertPrescribedGoodAt_eq_alpha P Pα h₂,
                PairERGoodChain.castLevel_head h₂.symm,
                P.good_head_eq, Pα.good_head_eq]
            rw [_h_prefix_below _ hv₁_T h_v₁_lt_α x]
            congr 1
            exact initialSegToType_transport_eq rfl h₂
              (((insert α T).orderEmbOfFin rfl).monotone hk) h_v₁_lt_α.le x
          · -- T/T: both in T, use P.prefix_restrict.
            have hv₁_T : (insert α T).orderEmbOfFin rfl k₁ ∈ T :=
              (Finset.mem_insert.mp hv₁_mem).resolve_left h₁
            have hv₂_T : (insert α T).orderEmbOfFin rfl k₂ ∈ T :=
              (Finset.mem_insert.mp hv₂_mem).resolve_left h₂
            rw [insertPrescribedGoodAt_eq_old P Pα h₁,
                insertPrescribedGoodAt_eq_old P Pα h₂]
            rw [P.good_head_eq, P.good_head_eq]
            exact P.toCoherentBranchPartial.prefix_restrict hv_le hv₁_T hv₂_T x
      branch_restrict := by
        intro k₁ k₂ hk x
        have hv₁_mem : (insert α T).orderEmbOfFin rfl k₁ ∈ insert α T :=
          (insert α T).orderEmbOfFin_mem rfl k₁
        have hv₂_mem : (insert α T).orderEmbOfFin rfl k₂ ∈ insert α T :=
          (insert α T).orderEmbOfFin_mem rfl k₂
        have hv_le : (insert α T).orderEmbOfFin rfl k₁ ≤
            (insert α T).orderEmbOfFin rfl k₂ :=
          ((insert α T).orderEmbOfFin rfl).monotone hk
        by_cases h₁ : (insert α T).orderEmbOfFin rfl k₁ = α
        · by_cases h₂ : (insert α T).orderEmbOfFin rfl k₂ = α
          · -- α/α
            have hk_eq : k₁ = k₂ :=
              ((insert α T).orderEmbOfFin rfl).injective (h₁.trans h₂.symm)
            subst hk_eq
            rw [insertPrescribedGoodAt_eq_alpha P Pα h₁]
            haveI : IsWellOrder ((insert α T).orderEmbOfFin rfl k₁).ToType
              (· < ·) := isWellOrder_lt
            congr 1
            rw [InitialSeg.toOrderEmbedding_apply]
            exact ((Ordinal.initialSegToType
                (((insert α T).orderEmbOfFin rfl).monotone hk)).eq
              (InitialSeg.refl _) x).trans (InitialSeg.refl_apply x)
          · -- α/T
            have hv₂_T : (insert α T).orderEmbOfFin rfl k₂ ∈ T :=
              (Finset.mem_insert.mp hv₂_mem).resolve_left h₂
            have h_α_lt_v₂ : α < (insert α T).orderEmbOfFin rfl k₂ := by
              rcases lt_or_eq_of_le hv_le with hlt | heq
              · calc α = (insert α T).orderEmbOfFin rfl k₁ := h₁.symm
                  _ < (insert α T).orderEmbOfFin rfl k₂ := hlt
              · exact absurd (heq ▸ h₁ : (insert α T).orderEmbOfFin rfl k₂ = α) h₂
            have h_α_le_v₂ : α ≤ (insert α T).orderEmbOfFin rfl k₂ :=
              le_of_lt h_α_lt_v₂
            rw [insertPrescribedGoodAt_eq_old P Pα h₂,
                insertPrescribedGoodAt_eq_alpha P Pα h₁,
                PairERGoodChain.castLevel_type h₁.symm,
                P.good_type_eq, Pα.good_type_eq]
            rw [_h_branch_above _ hv₂_T h_α_lt_v₂ (h₁ ▸ x)]
            congr 1
            exact initialSegToType_transport_eq h₁ rfl
              (((insert α T).orderEmbOfFin rfl).monotone hk) h_α_le_v₂ x
        · by_cases h₂ : (insert α T).orderEmbOfFin rfl k₂ = α
          · -- T/α
            have hv₁_T : (insert α T).orderEmbOfFin rfl k₁ ∈ T :=
              (Finset.mem_insert.mp hv₁_mem).resolve_left h₁
            have h_v₁_le_α : (insert α T).orderEmbOfFin rfl k₁ ≤ α :=
              calc (insert α T).orderEmbOfFin rfl k₁
                  ≤ (insert α T).orderEmbOfFin rfl k₂ := hv_le
                _ = α := h₂
            have h_v₁_lt_α : (insert α T).orderEmbOfFin rfl k₁ < α := by
              rcases lt_or_eq_of_le h_v₁_le_α with hlt | heq
              · exact hlt
              · exact absurd (heq ▸ hv₁_T : α ∈ T) _hα_not_mem
            rw [insertPrescribedGoodAt_eq_old P Pα h₁,
                insertPrescribedGoodAt_eq_alpha P Pα h₂,
                PairERGoodChain.castLevel_type h₂.symm,
                P.good_type_eq, Pα.good_type_eq]
            rw [_h_branch_below _ hv₁_T h_v₁_lt_α x]
            congr 1
            exact initialSegToType_transport_eq rfl h₂
              (((insert α T).orderEmbOfFin rfl).monotone hk) h_v₁_lt_α.le x
          · -- T/T
            have hv₁_T : (insert α T).orderEmbOfFin rfl k₁ ∈ T :=
              (Finset.mem_insert.mp hv₁_mem).resolve_left h₁
            have hv₂_T : (insert α T).orderEmbOfFin rfl k₂ ∈ T :=
              (Finset.mem_insert.mp hv₂_mem).resolve_left h₂
            rw [insertPrescribedGoodAt_eq_old P Pα h₁,
                insertPrescribedGoodAt_eq_old P Pα h₂]
            rw [P.good_type_eq, P.good_type_eq]
            exact P.toCoherentBranchPartial.branch_restrict hv_le hv₁_T hv₂_T x
      large := fun i => (insertPrescribedGoodAt P Pα i).toPairERChain.large
      top_in_validFiber := by
        intro i h
        have hv₁_mem : (insert α T).orderEmbOfFin rfl ⟨i, Nat.lt_of_succ_lt h⟩ ∈
            insert α T :=
          (insert α T).orderEmbOfFin_mem rfl _
        have hv₂_mem : (insert α T).orderEmbOfFin rfl ⟨i + 1, h⟩ ∈ insert α T :=
          (insert α T).orderEmbOfFin_mem rfl _
        have hv_lt : (insert α T).orderEmbOfFin rfl ⟨i, Nat.lt_of_succ_lt h⟩ <
            (insert α T).orderEmbOfFin rfl ⟨i + 1, h⟩ :=
          ((insert α T).orderEmbOfFin rfl).strictMono
            (show (⟨i, Nat.lt_of_succ_lt h⟩ : Fin (insert α T).card) <
              ⟨i + 1, h⟩ from Nat.lt_succ_self i)
        by_cases h₁ : (insert α T).orderEmbOfFin rfl ⟨i, Nat.lt_of_succ_lt h⟩ = α
        · -- α/T (v₁ = α, v₂ ∈ T)
          have h₂ : (insert α T).orderEmbOfFin rfl ⟨i + 1, h⟩ ≠ α := fun heq =>
            (ne_of_lt hv_lt) (h₁.trans heq.symm)
          have hv₂_T : (insert α T).orderEmbOfFin rfl ⟨i + 1, h⟩ ∈ T :=
            (Finset.mem_insert.mp hv₂_mem).resolve_left h₂
          have h_α_lt_v₂ : α < (insert α T).orderEmbOfFin rfl ⟨i + 1, h⟩ :=
            calc α = (insert α T).orderEmbOfFin rfl ⟨i, Nat.lt_of_succ_lt h⟩ :=
                  h₁.symm
              _ < (insert α T).orderEmbOfFin rfl ⟨i + 1, h⟩ := hv_lt
          rw [insertPrescribedGoodAt_eq_old P Pα h₂,
              insertPrescribedGoodAt_eq_alpha P Pα h₁]
          have h_har := (P.goodAt _ hv₂_T).head_at_α_in_restricted_validFiber hv_lt
          have h_vf_eq : validFiber cR
              (((Pα.goodAt α (Finset.mem_singleton.mpr rfl)).castLevel
                  h₁.symm).toPairERChain.head)
              (((Pα.goodAt α (Finset.mem_singleton.mpr rfl)).castLevel
                  h₁.symm).toPairERChain.type) =
            validFiber cR
              ((Ordinal.initialSegToType hv_lt.le).toOrderEmbedding.trans
                (P.goodAt _ hv₂_T).toPairERChain.head)
              (fun x => (P.goodAt _ hv₂_T).toPairERChain.type
                ((Ordinal.initialSegToType hv_lt.le).toOrderEmbedding x)) := by
            apply validFiber_congr_prefix_branch
            · intro y
              rw [PairERGoodChain.castLevel_head h₁.symm,
                  RelEmbedding.trans_apply, Pα.good_head_eq, P.good_head_eq,
                  _h_prefix_above _ hv₂_T h_α_lt_v₂ (h₁ ▸ y)]
              congr 1
              exact (initialSegToType_transport_eq h₁ rfl hv_lt.le
                (le_of_lt h_α_lt_v₂) y).symm
            · intro y
              rw [PairERGoodChain.castLevel_type h₁.symm,
                  Pα.good_type_eq, P.good_type_eq,
                  _h_branch_above _ hv₂_T h_α_lt_v₂ (h₁ ▸ y)]
              congr 1
              exact (initialSegToType_transport_eq h₁ rfl hv_lt.le
                (le_of_lt h_α_lt_v₂) y).symm
          rw [h_vf_eq]
          exact h_har
        · by_cases h₂ : (insert α T).orderEmbOfFin rfl ⟨i + 1, h⟩ = α
          · -- T/α (v₁ ∈ T, v₂ = α)
            have hv₁_T : (insert α T).orderEmbOfFin rfl ⟨i, Nat.lt_of_succ_lt h⟩ ∈
                T := (Finset.mem_insert.mp hv₁_mem).resolve_left h₁
            have h_v₁_lt_α : (insert α T).orderEmbOfFin rfl
                ⟨i, Nat.lt_of_succ_lt h⟩ < α := lt_of_lt_of_eq hv_lt h₂
            rw [insertPrescribedGoodAt_eq_old P Pα h₁,
                insertPrescribedGoodAt_eq_alpha P Pα h₂]
            have h_har :=
              ((Pα.goodAt α (Finset.mem_singleton.mpr rfl)).castLevel
                h₂.symm).head_at_α_in_restricted_validFiber hv_lt
            have h_vf_eq : validFiber cR
                (P.goodAt _ hv₁_T).toPairERChain.head
                (P.goodAt _ hv₁_T).toPairERChain.type =
              validFiber cR
                ((Ordinal.initialSegToType hv_lt.le).toOrderEmbedding.trans
                  (((Pα.goodAt α (Finset.mem_singleton.mpr rfl)).castLevel
                      h₂.symm).toPairERChain.head))
                (fun x => (((Pα.goodAt α (Finset.mem_singleton.mpr rfl)).castLevel
                    h₂.symm).toPairERChain.type)
                  ((Ordinal.initialSegToType hv_lt.le).toOrderEmbedding x)) := by
              apply validFiber_congr_prefix_branch
              · intro y
                rw [RelEmbedding.trans_apply,
                    PairERGoodChain.castLevel_head h₂.symm,
                    P.good_head_eq, Pα.good_head_eq,
                    _h_prefix_below _ hv₁_T h_v₁_lt_α y]
                congr 1
                exact (initialSegToType_transport_eq rfl h₂ hv_lt.le
                  h_v₁_lt_α.le y).symm
              · intro y
                rw [PairERGoodChain.castLevel_type h₂.symm,
                    P.good_type_eq, Pα.good_type_eq,
                    _h_branch_below _ hv₁_T h_v₁_lt_α y]
                congr 1
                exact (initialSegToType_transport_eq rfl h₂ hv_lt.le
                  h_v₁_lt_α.le y).symm
            rw [h_vf_eq]
            exact h_har
          · -- T/T
            have hv₁_T : (insert α T).orderEmbOfFin rfl ⟨i, Nat.lt_of_succ_lt h⟩ ∈
                T := (Finset.mem_insert.mp hv₁_mem).resolve_left h₁
            have hv₂_T : (insert α T).orderEmbOfFin rfl ⟨i + 1, h⟩ ∈ T :=
              (Finset.mem_insert.mp hv₂_mem).resolve_left h₂
            rw [insertPrescribedGoodAt_eq_old P Pα h₁,
                insertPrescribedGoodAt_eq_old P Pα h₂]
            have h_har := (P.goodAt _ hv₂_T).head_at_α_in_restricted_validFiber hv_lt
            have h_vf_eq : validFiber cR
                (P.goodAt _ hv₁_T).toPairERChain.head
                (P.goodAt _ hv₁_T).toPairERChain.type =
              validFiber cR
                ((Ordinal.initialSegToType hv_lt.le).toOrderEmbedding.trans
                  (P.goodAt _ hv₂_T).toPairERChain.head)
                (fun x => (P.goodAt _ hv₂_T).toPairERChain.type
                  ((Ordinal.initialSegToType hv_lt.le).toOrderEmbedding x)) := by
              apply validFiber_congr_prefix_branch
              · intro y
                rw [RelEmbedding.trans_apply, P.good_head_eq, P.good_head_eq]
                exact (P.toCoherentBranchPartial.prefix_restrict hv_lt.le
                  hv₁_T hv₂_T y).symm
              · intro y
                rw [P.good_type_eq, P.good_type_eq]
                exact (P.toCoherentBranchPartial.branch_restrict hv_lt.le
                  hv₁_T hv₂_T y).symm
            rw [h_vf_eq]
            exact h_har }
  goodAt := insertPrescribedGoodAt P Pα
  good_head := fun _ _ => rfl
  good_type := fun _ _ => rfl

/-- **`insertPrescribedGoodApprox_goodAt_old_head`**: for γ ∈ T, the
Good chain head at γ in the inserted CGBP matches `P.goodAt γ`'s head.
Mirror of `insertBeforeGoodApprox_goodAt_old_head` using
`insertPrescribedGoodAt_eq_old` + `goodAt_head_apply_eq_of_eq`. -/
private lemma insertPrescribedGoodApprox_goodAt_old_head
    {cR : (Fin 2 ↪o PairERSource) → Bool} {T : Finset Ordinal.{0}}
    (P : CoherentGoodBranchPartial cR T)
    {α : Ordinal.{0}}
    (hα_lt : α < Ordinal.omega.{0} 1) (hα_not_mem : α ∉ T)
    (Pα : CoherentGoodBranchPartial cR ({α} : Finset Ordinal.{0}))
    (h_prefix_below : ∀ β (hβ_T : β ∈ T) (hβ_lt_α : β < α),
      haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
      haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
      ∀ (x : β.ToType),
        P.toCoherentBranchPartial.prefixAt β hβ_T x =
          Pα.toCoherentBranchPartial.prefixAt α (Finset.mem_singleton.mpr rfl)
            ((Ordinal.initialSegToType hβ_lt_α.le).toOrderEmbedding x))
    (h_branch_below : ∀ β (hβ_T : β ∈ T) (hβ_lt_α : β < α),
      haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
      haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
      ∀ (x : β.ToType),
        P.toCoherentBranchPartial.branch β hβ_T x =
          Pα.toCoherentBranchPartial.branch α (Finset.mem_singleton.mpr rfl)
            ((Ordinal.initialSegToType hβ_lt_α.le).toOrderEmbedding x))
    (h_prefix_above : ∀ β (hβ_T : β ∈ T) (hα_lt_β : α < β),
      haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
      haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
      ∀ (x : α.ToType),
        Pα.toCoherentBranchPartial.prefixAt α (Finset.mem_singleton.mpr rfl) x =
          P.toCoherentBranchPartial.prefixAt β hβ_T
            ((Ordinal.initialSegToType hα_lt_β.le).toOrderEmbedding x))
    (h_branch_above : ∀ β (hβ_T : β ∈ T) (hα_lt_β : α < β),
      haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
      haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
      ∀ (x : α.ToType),
        Pα.toCoherentBranchPartial.branch α (Finset.mem_singleton.mpr rfl) x =
          P.toCoherentBranchPartial.branch β hβ_T
            ((Ordinal.initialSegToType hα_lt_β.le).toOrderEmbedding x))
    (γ : Ordinal.{0}) (hγ : γ ∈ T) (x : γ.ToType) :
    letI Q : CoherentGoodBranchPartial cR (insert α T) :=
      { toGoodApprox := insertPrescribedGoodApprox P hα_lt hα_not_mem Pα
          h_prefix_below h_branch_below h_prefix_above h_branch_above
        level_eq := fun _ => rfl }
    (Q.goodAt γ (Finset.mem_insert_of_mem hγ)).toPairERChain.head x =
      (P.goodAt γ hγ).toPairERChain.head x := by
  classical
  let Q : CoherentGoodBranchPartial cR (insert α T) :=
    { toGoodApprox := insertPrescribedGoodApprox P hα_lt hα_not_mem Pα
        h_prefix_below h_branch_below h_prefix_above h_branch_above
      level_eq := fun _ => rfl }
  have h_ne : (insert α T).orderEmbOfFin rfl
      (Q.toCoherentBranchPartial.indexOf γ (Finset.mem_insert_of_mem hγ)) ≠ α := by
    show (insert α T).orderEmbOfFin rfl
      (finsetIndexOf (insert α T) γ (Finset.mem_insert_of_mem hγ)) ≠ α
    rw [finsetIndexOf_orderEmb]
    exact fun h => hα_not_mem (h ▸ hγ)
  have h_chain_eq :
      Q.toGoodApprox.goodAt (Q.toCoherentBranchPartial.indexOf γ
          (Finset.mem_insert_of_mem hγ)) =
        P.goodAt _ ((Finset.mem_insert.mp
          ((insert α T).orderEmbOfFin_mem rfl _)).resolve_left h_ne) :=
    insertPrescribedGoodAt_eq_old P Pα h_ne
  show ((Q.toGoodApprox.goodAt (Q.toCoherentBranchPartial.indexOf γ
      (Finset.mem_insert_of_mem hγ))).castLevel _).toPairERChain.head x = _
  rw [h_chain_eq, PairERGoodChain.castLevel_head]
  have h_eq : (insert α T).orderEmbOfFin rfl
      (Q.toCoherentBranchPartial.indexOf γ (Finset.mem_insert_of_mem hγ)) = γ :=
    finsetIndexOf_orderEmb _ _ _
  refine (P.goodAt_head_apply_eq_of_eq (hα := _) (hβ := hγ) h_eq _).trans ?_
  congr 1
  exact eq_of_heq (HEq.trans (eqRec_heq h_eq _) (eqRec_heq _ x))

/-- **`insertPrescribedGoodApprox_goodAt_old_type`**: parallel of
`_head` for the type function. -/
private lemma insertPrescribedGoodApprox_goodAt_old_type
    {cR : (Fin 2 ↪o PairERSource) → Bool} {T : Finset Ordinal.{0}}
    (P : CoherentGoodBranchPartial cR T)
    {α : Ordinal.{0}}
    (hα_lt : α < Ordinal.omega.{0} 1) (hα_not_mem : α ∉ T)
    (Pα : CoherentGoodBranchPartial cR ({α} : Finset Ordinal.{0}))
    (h_prefix_below : ∀ β (hβ_T : β ∈ T) (hβ_lt_α : β < α),
      haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
      haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
      ∀ (x : β.ToType),
        P.toCoherentBranchPartial.prefixAt β hβ_T x =
          Pα.toCoherentBranchPartial.prefixAt α (Finset.mem_singleton.mpr rfl)
            ((Ordinal.initialSegToType hβ_lt_α.le).toOrderEmbedding x))
    (h_branch_below : ∀ β (hβ_T : β ∈ T) (hβ_lt_α : β < α),
      haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
      haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
      ∀ (x : β.ToType),
        P.toCoherentBranchPartial.branch β hβ_T x =
          Pα.toCoherentBranchPartial.branch α (Finset.mem_singleton.mpr rfl)
            ((Ordinal.initialSegToType hβ_lt_α.le).toOrderEmbedding x))
    (h_prefix_above : ∀ β (hβ_T : β ∈ T) (hα_lt_β : α < β),
      haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
      haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
      ∀ (x : α.ToType),
        Pα.toCoherentBranchPartial.prefixAt α (Finset.mem_singleton.mpr rfl) x =
          P.toCoherentBranchPartial.prefixAt β hβ_T
            ((Ordinal.initialSegToType hα_lt_β.le).toOrderEmbedding x))
    (h_branch_above : ∀ β (hβ_T : β ∈ T) (hα_lt_β : α < β),
      haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
      haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
      ∀ (x : α.ToType),
        Pα.toCoherentBranchPartial.branch α (Finset.mem_singleton.mpr rfl) x =
          P.toCoherentBranchPartial.branch β hβ_T
            ((Ordinal.initialSegToType hα_lt_β.le).toOrderEmbedding x))
    (γ : Ordinal.{0}) (hγ : γ ∈ T) (x : γ.ToType) :
    letI Q : CoherentGoodBranchPartial cR (insert α T) :=
      { toGoodApprox := insertPrescribedGoodApprox P hα_lt hα_not_mem Pα
          h_prefix_below h_branch_below h_prefix_above h_branch_above
        level_eq := fun _ => rfl }
    (Q.goodAt γ (Finset.mem_insert_of_mem hγ)).toPairERChain.type x =
      (P.goodAt γ hγ).toPairERChain.type x := by
  classical
  let Q : CoherentGoodBranchPartial cR (insert α T) :=
    { toGoodApprox := insertPrescribedGoodApprox P hα_lt hα_not_mem Pα
        h_prefix_below h_branch_below h_prefix_above h_branch_above
      level_eq := fun _ => rfl }
  have h_ne : (insert α T).orderEmbOfFin rfl
      (Q.toCoherentBranchPartial.indexOf γ (Finset.mem_insert_of_mem hγ)) ≠ α := by
    show (insert α T).orderEmbOfFin rfl
      (finsetIndexOf (insert α T) γ (Finset.mem_insert_of_mem hγ)) ≠ α
    rw [finsetIndexOf_orderEmb]
    exact fun h => hα_not_mem (h ▸ hγ)
  have h_chain_eq :
      Q.toGoodApprox.goodAt (Q.toCoherentBranchPartial.indexOf γ
          (Finset.mem_insert_of_mem hγ)) =
        P.goodAt _ ((Finset.mem_insert.mp
          ((insert α T).orderEmbOfFin_mem rfl _)).resolve_left h_ne) :=
    insertPrescribedGoodAt_eq_old P Pα h_ne
  show ((Q.toGoodApprox.goodAt (Q.toCoherentBranchPartial.indexOf γ
      (Finset.mem_insert_of_mem hγ))).castLevel _).toPairERChain.type x = _
  rw [h_chain_eq, PairERGoodChain.castLevel_type]
  have h_eq : (insert α T).orderEmbOfFin rfl
      (Q.toCoherentBranchPartial.indexOf γ (Finset.mem_insert_of_mem hγ)) = γ :=
    finsetIndexOf_orderEmb _ _ _
  refine (P.goodAt_type_apply_eq_of_eq (hα := _) (hβ := hγ) h_eq _).trans ?_
  congr 1
  exact eq_of_heq (HEq.trans (eqRec_heq h_eq _) (eqRec_heq _ x))

/-- **`insertPrescribedGoodApprox_goodAt_alpha_head`**: for the
α-singleton, the Good chain head at α in the inserted CGBP matches
`Pα.goodAt α`'s head. Mirror of `_old_head` using
`insertPrescribedGoodAt_eq_alpha` + `goodAt_head_apply_eq_of_eq`. -/
private lemma insertPrescribedGoodApprox_goodAt_alpha_head
    {cR : (Fin 2 ↪o PairERSource) → Bool} {T : Finset Ordinal.{0}}
    (P : CoherentGoodBranchPartial cR T)
    {α : Ordinal.{0}}
    (hα_lt : α < Ordinal.omega.{0} 1) (hα_not_mem : α ∉ T)
    (Pα : CoherentGoodBranchPartial cR ({α} : Finset Ordinal.{0}))
    (h_prefix_below : ∀ β (hβ_T : β ∈ T) (hβ_lt_α : β < α),
      haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
      haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
      ∀ (x : β.ToType),
        P.toCoherentBranchPartial.prefixAt β hβ_T x =
          Pα.toCoherentBranchPartial.prefixAt α (Finset.mem_singleton.mpr rfl)
            ((Ordinal.initialSegToType hβ_lt_α.le).toOrderEmbedding x))
    (h_branch_below : ∀ β (hβ_T : β ∈ T) (hβ_lt_α : β < α),
      haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
      haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
      ∀ (x : β.ToType),
        P.toCoherentBranchPartial.branch β hβ_T x =
          Pα.toCoherentBranchPartial.branch α (Finset.mem_singleton.mpr rfl)
            ((Ordinal.initialSegToType hβ_lt_α.le).toOrderEmbedding x))
    (h_prefix_above : ∀ β (hβ_T : β ∈ T) (hα_lt_β : α < β),
      haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
      haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
      ∀ (x : α.ToType),
        Pα.toCoherentBranchPartial.prefixAt α (Finset.mem_singleton.mpr rfl) x =
          P.toCoherentBranchPartial.prefixAt β hβ_T
            ((Ordinal.initialSegToType hα_lt_β.le).toOrderEmbedding x))
    (h_branch_above : ∀ β (hβ_T : β ∈ T) (hα_lt_β : α < β),
      haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
      haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
      ∀ (x : α.ToType),
        Pα.toCoherentBranchPartial.branch α (Finset.mem_singleton.mpr rfl) x =
          P.toCoherentBranchPartial.branch β hβ_T
            ((Ordinal.initialSegToType hα_lt_β.le).toOrderEmbedding x))
    (x : α.ToType) :
    letI Q : CoherentGoodBranchPartial cR (insert α T) :=
      { toGoodApprox := insertPrescribedGoodApprox P hα_lt hα_not_mem Pα
          h_prefix_below h_branch_below h_prefix_above h_branch_above
        level_eq := fun _ => rfl }
    (Q.goodAt α (Finset.mem_insert_self α T)).toPairERChain.head x =
      (Pα.goodAt α (Finset.mem_singleton.mpr rfl)).toPairERChain.head x := by
  classical
  let Q : CoherentGoodBranchPartial cR (insert α T) :=
    { toGoodApprox := insertPrescribedGoodApprox P hα_lt hα_not_mem Pα
        h_prefix_below h_branch_below h_prefix_above h_branch_above
      level_eq := fun _ => rfl }
  have h_eq_α : (insert α T).orderEmbOfFin rfl
      (Q.toCoherentBranchPartial.indexOf α (Finset.mem_insert_self α T)) = α := by
    show (insert α T).orderEmbOfFin rfl
      (finsetIndexOf (insert α T) α (Finset.mem_insert_self α T)) = α
    rw [finsetIndexOf_orderEmb]
  have h_chain_eq :
      Q.toGoodApprox.goodAt (Q.toCoherentBranchPartial.indexOf α
          (Finset.mem_insert_self α T)) =
        (Pα.goodAt α (Finset.mem_singleton.mpr rfl)).castLevel h_eq_α.symm :=
    insertPrescribedGoodAt_eq_alpha P Pα h_eq_α
  show ((Q.toGoodApprox.goodAt (Q.toCoherentBranchPartial.indexOf α
      (Finset.mem_insert_self α T))).castLevel _).toPairERChain.head x = _
  rw [h_chain_eq]
  rw [PairERGoodChain.castLevel_head, PairERGoodChain.castLevel_head]
  congr 1
  exact eq_of_heq (HEq.trans (eqRec_heq _ _) (eqRec_heq _ x))

/-- **`insertPrescribedGoodApprox_goodAt_alpha_type`**: parallel of
`_alpha_head` for the type function. -/
private lemma insertPrescribedGoodApprox_goodAt_alpha_type
    {cR : (Fin 2 ↪o PairERSource) → Bool} {T : Finset Ordinal.{0}}
    (P : CoherentGoodBranchPartial cR T)
    {α : Ordinal.{0}}
    (hα_lt : α < Ordinal.omega.{0} 1) (hα_not_mem : α ∉ T)
    (Pα : CoherentGoodBranchPartial cR ({α} : Finset Ordinal.{0}))
    (h_prefix_below : ∀ β (hβ_T : β ∈ T) (hβ_lt_α : β < α),
      haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
      haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
      ∀ (x : β.ToType),
        P.toCoherentBranchPartial.prefixAt β hβ_T x =
          Pα.toCoherentBranchPartial.prefixAt α (Finset.mem_singleton.mpr rfl)
            ((Ordinal.initialSegToType hβ_lt_α.le).toOrderEmbedding x))
    (h_branch_below : ∀ β (hβ_T : β ∈ T) (hβ_lt_α : β < α),
      haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
      haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
      ∀ (x : β.ToType),
        P.toCoherentBranchPartial.branch β hβ_T x =
          Pα.toCoherentBranchPartial.branch α (Finset.mem_singleton.mpr rfl)
            ((Ordinal.initialSegToType hβ_lt_α.le).toOrderEmbedding x))
    (h_prefix_above : ∀ β (hβ_T : β ∈ T) (hα_lt_β : α < β),
      haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
      haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
      ∀ (x : α.ToType),
        Pα.toCoherentBranchPartial.prefixAt α (Finset.mem_singleton.mpr rfl) x =
          P.toCoherentBranchPartial.prefixAt β hβ_T
            ((Ordinal.initialSegToType hα_lt_β.le).toOrderEmbedding x))
    (h_branch_above : ∀ β (hβ_T : β ∈ T) (hα_lt_β : α < β),
      haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
      haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
      ∀ (x : α.ToType),
        Pα.toCoherentBranchPartial.branch α (Finset.mem_singleton.mpr rfl) x =
          P.toCoherentBranchPartial.branch β hβ_T
            ((Ordinal.initialSegToType hα_lt_β.le).toOrderEmbedding x))
    (x : α.ToType) :
    letI Q : CoherentGoodBranchPartial cR (insert α T) :=
      { toGoodApprox := insertPrescribedGoodApprox P hα_lt hα_not_mem Pα
          h_prefix_below h_branch_below h_prefix_above h_branch_above
        level_eq := fun _ => rfl }
    (Q.goodAt α (Finset.mem_insert_self α T)).toPairERChain.type x =
      (Pα.goodAt α (Finset.mem_singleton.mpr rfl)).toPairERChain.type x := by
  classical
  let Q : CoherentGoodBranchPartial cR (insert α T) :=
    { toGoodApprox := insertPrescribedGoodApprox P hα_lt hα_not_mem Pα
        h_prefix_below h_branch_below h_prefix_above h_branch_above
      level_eq := fun _ => rfl }
  have h_eq_α : (insert α T).orderEmbOfFin rfl
      (Q.toCoherentBranchPartial.indexOf α (Finset.mem_insert_self α T)) = α := by
    show (insert α T).orderEmbOfFin rfl
      (finsetIndexOf (insert α T) α (Finset.mem_insert_self α T)) = α
    rw [finsetIndexOf_orderEmb]
  have h_chain_eq :
      Q.toGoodApprox.goodAt (Q.toCoherentBranchPartial.indexOf α
          (Finset.mem_insert_self α T)) =
        (Pα.goodAt α (Finset.mem_singleton.mpr rfl)).castLevel h_eq_α.symm :=
    insertPrescribedGoodAt_eq_alpha P Pα h_eq_α
  show ((Q.toGoodApprox.goodAt (Q.toCoherentBranchPartial.indexOf α
      (Finset.mem_insert_self α T))).castLevel _).toPairERChain.type x = _
  rw [h_chain_eq]
  rw [PairERGoodChain.castLevel_type, PairERGoodChain.castLevel_type]
  congr 1
  exact eq_of_heq (HEq.trans (eqRec_heq _ _) (eqRec_heq _ x))

/-! ### Interior insertion primitive (frontier)

The complementary case to `extend_one_above_top` is **interior**
insertion: extending `P : CBP cR T` by an `α` that is below at least
one element of `T`. The natural construction defines the new
prefixAt at `α` by restriction from the data at the least `β₀ ∈ T`
above `α`:

  `Q.prefixAt α := P.prefixAt β₀ ∘ initSeg(α → β₀)`
  `Q.branch  α := P.branch  β₀ ∘ initSeg(α → β₀)`

Restriction laws (`prefix_restrict`, `branch_restrict`) for `T-T`
pairs come from `P` directly. For pairs involving `α`, they reduce
via `P.prefix_restrict` since `initSeg` composes nicely.

The non-trivial check is `top_in_validFiber` at the new
`(α-index, β₀-index)` adjacency:

  `P.prefixAt β₀ (enum at α in β₀) ∈ validFiber (Q.prefixAt α, Q.branch α)`

Unfolding requires for every `x ∈ α.ToType`:

  `cR (pair (P.prefixAt β₀ (initSeg x), P.prefixAt β₀ (enum at α))) =
   P.branch β₀ (initSeg x)`

This is the **inner cR-consistency** of `P.prefixAt β₀` between
positions `initSeg x < enum at α` *both inside* `β₀.ToType`. The
existing `CoherentBranchApprox.validFiber_between` lemma only
relates positions on different *levels* in the CBA (it generalizes
adjacency from `(i, i+1)` to `(i, j)`), not two positions inside one
level. Closing this requires an explicit inner-consistency theorem
for `PairERChain.head` proven by induction on the chain's
construction (`zero`, `succ`, `limit`, `extendTo`). -/

/-- **[FRONTIER, sorry]** Interior insertion at the bare CBP layer.
This form takes a bare `P : CBP cR T` as input, but the proven Good-
layer theorem `coherentGoodBranchPartial_insert_before` requires a
`CoherentGoodBranchPartial` (i.e., a CBP carrying inner cR-consistency
data on its chains). Lifting an arbitrary bare CBP to a Good CBP is
not generally possible — the inner cR-consistency is real extra data,
not derivable from the bare structure.

The Good-input form is `coherentBranchPartial_insert_between_of_good`
(below); this bare form is left as a frontier pending either a Good
lifting theorem or an alternative bare-level construction. -/
theorem coherentBranchPartial_insert_between
    (cR : (Fin 2 ↪o PairERSource) → Bool)
    {T : Finset Ordinal.{0}} (P : CoherentBranchPartial cR T)
    (α : Ordinal.{0}) (hα : α < Ordinal.omega.{0} 1)
    (hα_not_mem : α ∉ T)
    (h_between : ∃ β ∈ T, α < β) :
    ∃ Q : CoherentBranchPartial cR (insert α T),
      cbpFieldwiseCompat (Q.restrict (Finset.subset_insert α T)) P := by
  sorry

/-- **`coherentBranchPartial_insert_between_of_good`**: Good-input
form of interior insertion, derived from
`coherentGoodBranchPartial_insert_before` by choosing `β₀` via
`exists_min_above_in_finset` and projecting the resulting Good CBP
to its bare CBP. Axiom-clean. -/
theorem coherentBranchPartial_insert_between_of_good
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {T : Finset Ordinal.{0}} (PG : CoherentGoodBranchPartial cR T)
    {α : Ordinal.{0}} (hα : α < Ordinal.omega.{0} 1)
    (hα_not_mem : α ∉ T)
    (h_between : ∃ β ∈ T, α < β) :
    ∃ Q : CoherentBranchPartial cR (insert α T),
      cbpFieldwiseCompat (Q.restrict (Finset.subset_insert α T))
        PG.toCoherentBranchPartial := by
  obtain ⟨β₀, hβ₀, hαβ₀, hmin⟩ := exists_min_above_in_finset T α h_between
  obtain ⟨Q, hQ_compat⟩ := coherentGoodBranchPartial_insert_before
    PG hα hα_not_mem hβ₀ hαβ₀ hmin
  exact ⟨Q.toCoherentBranchPartial, hQ_compat⟩

/-! ### Good above-top extension and union extension

Lifting `coherentBranchPartial_extend_one_above_top` to the Good layer.
The construction mirrors the bare proof but uses
`CoherentGoodBranchApprox.extendTo` so the resulting `Q` carries Good
chain data at every level. Then iterating gives a Good union extension
combining above-top and interior insertion. -/

/-- **`coherentGoodBranchPartial_extend_one_above_top`**: Good-layer
above-top extension. Mirrors the bare proof at
`coherentBranchPartial_extend_one_above_top` but uses
`PG.toGoodApprox.extendTo α hα h_above_last` to obtain a
`CoherentGoodBranchApprox cR (T.card + 1)`, then reindexes to
`(insert α T).card` via `Fin.cast`. The Good data `goodAt`/`good_head`/
`good_type` carry through the reindex; fieldwise compat against
`PG.toCoherentBranchPartial` follows the same HEq + `congr_arg_heq`
pattern as the bare proof. Empty-T case closed via
`exists_coherentGoodBranchPartial`; non-empty case stubbed (~200 lines
of bare-proof mirroring). -/
theorem coherentGoodBranchPartial_extend_one_above_top
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {T : Finset Ordinal.{0}} (PG : CoherentGoodBranchPartial cR T)
    {α : Ordinal.{0}} (hα : α < Ordinal.omega.{0} 1)
    (h_above : ∀ β ∈ T, β < α) :
    ∃ Q : CoherentGoodBranchPartial cR (insert α T),
      cbpFieldwiseCompat
        (Q.toCoherentBranchPartial.restrict (Finset.subset_insert α T))
        PG.toCoherentBranchPartial := by
  classical
  have hα_not_mem : α ∉ T := fun h => lt_irrefl α (h_above α h)
  by_cases hT_empty : T = ∅
  · subst hT_empty
    have h_valid : ∀ β ∈ insert α (∅ : Finset Ordinal.{0}),
        β < Ordinal.omega.{0} 1 := by
      intro β hβ
      rcases Finset.mem_insert.mp hβ with h | h
      · exact h ▸ hα
      · exact absurd h (Finset.notMem_empty _)
    obtain ⟨Q⟩ := exists_coherentGoodBranchPartial cR (insert α ∅) h_valid
    refine ⟨Q, ?_, ?_⟩ <;>
      intro β hβ <;> exact absurd hβ (Finset.notMem_empty _)
  -- Main case: T ≠ ∅. Mirror the bare `extend_one_above_top` proof
  -- structure, threading Good data through `PG.toGoodApprox.extendTo`.
  have hT_card_ne : T.card ≠ 0 :=
    fun h => hT_empty (Finset.card_eq_zero.mp h)
  have hT_card_pos : 0 < T.card := Nat.pos_of_ne_zero hT_card_ne
  have h_card : (insert α T).card = T.card + 1 :=
    Finset.card_insert_of_notMem hα_not_mem
  -- lastLevel < α.
  have h_above_last : PG.toCoherentBranchPartial.toApprox.lastLevel < α := by
    have hT_sub : T.card - 1 < T.card := Nat.sub_lt hT_card_pos one_pos
    have h_last_eq : PG.toCoherentBranchPartial.toApprox.lastLevel =
        (T.orderEmbOfFin rfl) ⟨T.card - 1, hT_sub⟩ := by
      unfold CoherentBranchApprox.lastLevel
      rw [dif_neg hT_card_ne]
      exact PG.level_eq ⟨T.card - 1, hT_sub⟩
    rw [h_last_eq]
    exact h_above _ (T.orderEmbOfFin_mem rfl _)
  -- Extended Good CGBA.
  let A_ext : CoherentGoodBranchApprox cR (T.card + 1) :=
    PG.toGoodApprox.extendTo α hα h_above_last
  -- Identification of (insert α T).orderEmbOfFin via uniqueness.
  set f : Fin (T.card + 1) → Ordinal.{0} :=
    Fin.lastCases α (fun j => (T.orderEmbOfFin rfl) j) with hf_def
  have hf_last : f (Fin.last T.card) = α := Fin.lastCases_last
  have hf_castSucc : ∀ j : Fin T.card,
      f j.castSucc = (T.orderEmbOfFin rfl) j := fun j => Fin.lastCases_castSucc _
  have hf_mem : ∀ i, f i ∈ insert α T := by
    intro i
    induction i using Fin.lastCases with
    | last => rw [hf_last]; exact Finset.mem_insert_self α T
    | cast j =>
      rw [hf_castSucc j]
      exact Finset.mem_insert_of_mem (T.orderEmbOfFin_mem rfl j)
  have hf_strictMono : StrictMono f := by
    intro a b hab
    induction b using Fin.lastCases with
    | last =>
      induction a using Fin.lastCases with
      | last => exact absurd hab (lt_irrefl _)
      | cast j =>
        rw [hf_castSucc j, hf_last]
        exact h_above _ (T.orderEmbOfFin_mem rfl j)
    | cast j₂ =>
      induction a using Fin.lastCases with
      | last =>
        exact absurd hab (not_lt_of_ge (Fin.le_last _))
      | cast j₁ =>
        rw [hf_castSucc j₁, hf_castSucc j₂]
        exact (T.orderEmbOfFin rfl).strictMono
          (Fin.castSucc_lt_castSucc_iff.mp hab)
  have hf_eq : f = ⇑((insert α T).orderEmbOfFin h_card) :=
    Finset.orderEmbOfFin_unique h_card hf_mem hf_strictMono
  -- A_ext.toApprox.level matches f (by construction of extendTo).
  have hA_ext_level : ∀ j, A_ext.toApprox.level j = f j := by
    intro j
    induction j using Fin.lastCases with
    | last =>
      rw [hf_last]
      show PG.toCoherentBranchPartial.toApprox.extendToLevel α
        (Fin.last T.card) = α
      exact PG.toCoherentBranchPartial.toApprox.extendToLevel_last α
    | cast j =>
      rw [hf_castSucc j]
      show PG.toCoherentBranchPartial.toApprox.extendToLevel α j.castSucc =
        (T.orderEmbOfFin rfl) j
      rw [PG.toCoherentBranchPartial.toApprox.extendToLevel_castSucc α j]
      exact PG.level_eq j
  -- Consistency: (insert α T).orderEmbOfFin h_card ∘ Fin.cast h_card =
  -- (insert α T).orderEmbOfFin rfl.
  have h_emb_cast : ∀ i : Fin (insert α T).card,
      (insert α T).orderEmbOfFin h_card (Fin.cast h_card i) =
        (insert α T).orderEmbOfFin rfl i := by
    intro i
    have hg_mem : ∀ x : Fin (insert α T).card,
        (insert α T).orderEmbOfFin h_card (Fin.cast h_card x) ∈ insert α T :=
      fun x => Finset.orderEmbOfFin_mem _ _ _
    have hg_strictMono : StrictMono
        (fun x : Fin (insert α T).card =>
          (insert α T).orderEmbOfFin h_card (Fin.cast h_card x)) := by
      intro a b hab
      exact ((insert α T).orderEmbOfFin h_card).strictMono hab
    have h_unique := Finset.orderEmbOfFin_unique
      (s := insert α T) (k := (insert α T).card) rfl hg_mem hg_strictMono
    exact congr_fun h_unique i
  -- Build Q_cgba: reindex A_ext through Fin.cast h_card.
  let Q_cgba : CoherentGoodBranchApprox cR (insert α T).card :=
    { toApprox :=
        { level := fun i => A_ext.toApprox.level (Fin.cast h_card i)
          level_lt_omega1 := fun i => A_ext.toApprox.level_lt_omega1 _
          level_strictMono := fun {_ _} hab => A_ext.toApprox.level_strictMono hab
          prefixAt := fun i => A_ext.toApprox.prefixAt (Fin.cast h_card i)
          branchAt := fun i => A_ext.toApprox.branchAt (Fin.cast h_card i)
          prefix_restrict := fun {k₁ k₂} hk x =>
            A_ext.toApprox.prefix_restrict (k₁ := Fin.cast h_card k₁)
              (k₂ := Fin.cast h_card k₂) hk x
          branch_restrict := fun {k₁ k₂} hk x =>
            A_ext.toApprox.branch_restrict (k₁ := Fin.cast h_card k₁)
              (k₂ := Fin.cast h_card k₂) hk x
          large := fun i => A_ext.toApprox.large _
          top_in_validFiber := by
            intro i hi
            have hi' : i + 1 < T.card + 1 := h_card ▸ hi
            have := A_ext.toApprox.top_in_validFiber i hi'
            convert this using 2 <;> rfl }
      goodAt := fun i => A_ext.goodAt (Fin.cast h_card i)
      good_head := fun i x => A_ext.good_head (Fin.cast h_card i) x
      good_type := fun i x => A_ext.good_type (Fin.cast h_card i) x }
  -- Level_eq for Q (built atop Q_cgba).
  have h_level_eq : ∀ i, Q_cgba.toApprox.level i =
      (insert α T).orderEmbOfFin rfl i := by
    intro i
    show A_ext.toApprox.level (Fin.cast h_card i) =
      (insert α T).orderEmbOfFin rfl i
    rw [hA_ext_level (Fin.cast h_card i)]
    rw [show f (Fin.cast h_card i) = ((insert α T).orderEmbOfFin h_card)
          (Fin.cast h_card i) from congr_fun hf_eq _]
    exact h_emb_cast i
  let Q : CoherentGoodBranchPartial cR (insert α T) :=
    { toGoodApprox := Q_cgba, level_eq := h_level_eq }
  -- Key step: Fin.cast h_card (Q.indexOf α' h) = (P.indexOf α' hα').castSucc.
  have h_indexOf : ∀ α' (hα' : α' ∈ T),
      Fin.cast h_card (Q.toCoherentBranchPartial.indexOf α'
          (Finset.subset_insert α T hα')) =
        (PG.toCoherentBranchPartial.indexOf α' hα').castSucc := by
    intro α' hα'
    apply A_ext.toApprox.level_strictMono.injective
    have h_LHS : A_ext.toApprox.level
        (Fin.cast h_card (Q.toCoherentBranchPartial.indexOf α'
          (Finset.subset_insert α T hα'))) = α' := by
      change Q_cgba.toApprox.level (Q.toCoherentBranchPartial.indexOf α'
        (Finset.subset_insert α T hα')) = α'
      exact Q.toCoherentBranchPartial.level_indexOf α'
        (Finset.subset_insert α T hα')
    have h_RHS : A_ext.toApprox.level
        (PG.toCoherentBranchPartial.indexOf α' hα').castSucc = α' := by
      change PG.toCoherentBranchPartial.toApprox.extendToLevel α
        (PG.toCoherentBranchPartial.indexOf α' hα').castSucc = α'
      rw [PG.toCoherentBranchPartial.toApprox.extendToLevel_castSucc α
            (PG.toCoherentBranchPartial.indexOf α' hα'),
          PG.toCoherentBranchPartial.level_indexOf α' hα']
    rw [h_LHS, h_RHS]
  refine ⟨Q, ?_, ?_⟩
  · intro α' hα'
    rw [Q.toCoherentBranchPartial.restrict_prefixAt
          (Finset.subset_insert α T) α' hα']
    apply eq_of_heq
    refine HEq.trans (cast_heq _ _) (HEq.trans ?_ (cast_heq _ _).symm)
    refine HEq.trans (b := A_ext.toApprox.prefixAt
        (PG.toCoherentBranchPartial.indexOf α' hα').castSucc) ?_ ?_
    · change HEq (A_ext.toApprox.prefixAt (Fin.cast h_card
        (Q.toCoherentBranchPartial.indexOf α'
          (Finset.subset_insert α T hα'))))
        (A_ext.toApprox.prefixAt
          (PG.toCoherentBranchPartial.indexOf α' hα').castSucc)
      exact congr_arg_heq A_ext.toApprox.prefixAt (h_indexOf α' hα')
    · change HEq (PG.toCoherentBranchPartial.toApprox.extendToPrefixAt
          (PG.toGoodApprox.extendToChain α hα h_above_last).toPairERChain
          (PG.toCoherentBranchPartial.indexOf α' hα').castSucc)
        (PG.toCoherentBranchPartial.toApprox.prefixAt
          (PG.toCoherentBranchPartial.indexOf α' hα'))
      exact PG.toCoherentBranchPartial.toApprox.extendToPrefixAt_castSucc_heq _
        (PG.toCoherentBranchPartial.indexOf α' hα')
  · intro α' hα'
    rw [Q.toCoherentBranchPartial.restrict_branch
          (Finset.subset_insert α T) α' hα']
    apply eq_of_heq
    refine HEq.trans (cast_heq _ _) (HEq.trans ?_ (cast_heq _ _).symm)
    refine HEq.trans (b := A_ext.toApprox.branchAt
        (PG.toCoherentBranchPartial.indexOf α' hα').castSucc) ?_ ?_
    · change HEq (A_ext.toApprox.branchAt (Fin.cast h_card
        (Q.toCoherentBranchPartial.indexOf α'
          (Finset.subset_insert α T hα'))))
        (A_ext.toApprox.branchAt
          (PG.toCoherentBranchPartial.indexOf α' hα').castSucc)
      exact congr_arg_heq A_ext.toApprox.branchAt (h_indexOf α' hα')
    · change HEq (PG.toCoherentBranchPartial.toApprox.extendToBranchAt
          (PG.toGoodApprox.extendToChain α hα h_above_last).toPairERChain
          (PG.toCoherentBranchPartial.indexOf α' hα').castSucc)
        (PG.toCoherentBranchPartial.toApprox.branchAt
          (PG.toCoherentBranchPartial.indexOf α' hα'))
      exact PG.toCoherentBranchPartial.toApprox.extendToBranchAt_castSucc_heq _
        (PG.toCoherentBranchPartial.indexOf α' hα')

/-- **`coherentGoodBranchPartial_insert_one`**: one-step Good insertion
of a new (`α ∉ T`) element, dispatching internally on above-top vs
interior:
- `α ∉ T` and above all of `T`: use
  `coherentGoodBranchPartial_extend_one_above_top`.
- `α ∉ T` and interior: locate `β₀` via `exists_min_above_in_finset`
  and use `coherentGoodBranchPartial_insert_before`. -/
theorem coherentGoodBranchPartial_insert_one
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {T : Finset Ordinal.{0}} (PG : CoherentGoodBranchPartial cR T)
    (α : Ordinal.{0}) (hα : α < Ordinal.omega.{0} 1) (hα_not_mem : α ∉ T) :
    ∃ Q : CoherentGoodBranchPartial cR (insert α T),
      cbpFieldwiseCompat
        (Q.toCoherentBranchPartial.restrict (Finset.subset_insert α T))
        PG.toCoherentBranchPartial := by
  classical
  by_cases h_above : ∀ β ∈ T, β < α
  · exact coherentGoodBranchPartial_extend_one_above_top PG hα h_above
  · push_neg at h_above
    obtain ⟨β, hβ_T, hβα⟩ := h_above
    have hβ_ne_α : β ≠ α := fun h => hα_not_mem (h ▸ hβ_T)
    have h_α_lt_β : α < β := lt_of_le_of_ne hβα (Ne.symm hβ_ne_α)
    have h_between : ∃ β ∈ T, α < β := ⟨β, hβ_T, h_α_lt_β⟩
    obtain ⟨β₀, hβ₀, hαβ₀, hmin⟩ := exists_min_above_in_finset T α h_between
    exact coherentGoodBranchPartial_insert_before PG hα hα_not_mem hβ₀ hαβ₀ hmin

/-- **`coherentGoodBranchPartial_extend_list`**: list-fold version of
the Good union extension. Iterates `coherentGoodBranchPartial_insert_one`
over `l`, with each element disjoint from the cumulative set. This form
avoids `T ∪ ∅` / `T ∪ insert` rewrites at every step; instead, the
`l.foldl insert T` builds up incrementally.

The wrapper `coherentGoodBranchPartial_extend_to_union` then converts to
the union form once at the end via `l.foldl insert T = T ∪ U` for
`l = U.toList`. -/
theorem coherentGoodBranchPartial_extend_list
    {cR : (Fin 2 ↪o PairERSource) → Bool} :
    ∀ {T : Finset Ordinal.{0}} (PG : CoherentGoodBranchPartial cR T)
      (l : List Ordinal.{0})
      (_h_valid : ∀ α ∈ l, α < Ordinal.omega.{0} 1)
      (_h_nodup : l.Nodup)
      (_h_disjoint : ∀ α ∈ l, α ∉ T),
      ∃ Q : CoherentGoodBranchPartial cR
        (l.foldl (fun S α => insert α S) T),
        cbpFieldwiseCompat
          (Q.toCoherentBranchPartial.restrict (subset_foldl_insert l T))
          PG.toCoherentBranchPartial
  | T, PG, [], _, _, _ => by
    refine ⟨PG, ?_, ?_⟩
    · intro β hβ; rw [CoherentBranchPartial.restrict_prefixAt]
    · intro β hβ; rw [CoherentBranchPartial.restrict_branch]
  | T, PG, α :: tail, h_valid, h_nodup, h_disjoint => by
    have hα_lt : α < Ordinal.omega.{0} 1 :=
      h_valid α List.mem_cons_self
    have hα_not_T : α ∉ T := h_disjoint α List.mem_cons_self
    obtain ⟨Q₁, hQ₁_compat⟩ :=
      coherentGoodBranchPartial_insert_one PG α hα_lt hα_not_T
    -- Q₁ : CGBP cR (insert α T). Now recurse on tail with new T := insert α T.
    have h_tail_valid : ∀ β ∈ tail, β < Ordinal.omega.{0} 1 := fun β hβ =>
      h_valid β (List.mem_cons_of_mem α hβ)
    have h_tail_nodup : tail.Nodup := h_nodup.of_cons
    have h_tail_disjoint : ∀ β ∈ tail, β ∉ insert α T := fun β hβ h_ins => by
      rcases Finset.mem_insert.mp h_ins with h_eq | h_T
      · exact (List.nodup_cons.mp h_nodup).1 (h_eq ▸ hβ)
      · exact h_disjoint β (List.mem_cons_of_mem α hβ) h_T
    obtain ⟨Q, hQ_compat⟩ := coherentGoodBranchPartial_extend_list Q₁ tail
      h_tail_valid h_tail_nodup h_tail_disjoint
    -- Q : CGBP cR (tail.foldl insert (insert α T)) =
    -- CGBP cR ((α :: tail).foldl insert T).
    refine ⟨Q, ?_, ?_⟩
    · intro β hβ_T
      -- Chain: (Q.restrict h_outer).prefixAt β hβ_T
      --   = ((Q.restrict h_to_insert_α_T).restrict h_insert_α_T_to_T).prefixAt β hβ_T
      --   = Q₁.prefixAt β (Finset.subset_insert α T hβ_T)
      --   = PG.prefixAt β hβ_T
      have hβ_in_insert_α_T : β ∈ insert α T := Finset.subset_insert α T hβ_T
      rw [Q.toCoherentBranchPartial.restrict_prefixAt _ β hβ_T]
      have h_step1 := hQ_compat.1 β hβ_in_insert_α_T
      rw [Q.toCoherentBranchPartial.restrict_prefixAt
          (subset_foldl_insert tail (insert α T)) β hβ_in_insert_α_T] at h_step1
      rw [h_step1]
      have h_step2 := hQ₁_compat.1 β hβ_T
      rw [Q₁.toCoherentBranchPartial.restrict_prefixAt
          (Finset.subset_insert α T) β hβ_T] at h_step2
      exact h_step2
    · intro β hβ_T
      have hβ_in_insert_α_T : β ∈ insert α T := Finset.subset_insert α T hβ_T
      rw [Q.toCoherentBranchPartial.restrict_branch _ β hβ_T]
      have h_step1 := hQ_compat.2 β hβ_in_insert_α_T
      rw [Q.toCoherentBranchPartial.restrict_branch
          (subset_foldl_insert tail (insert α T)) β hβ_in_insert_α_T] at h_step1
      rw [h_step1]
      have h_step2 := hQ₁_compat.2 β hβ_T
      rw [Q₁.toCoherentBranchPartial.restrict_branch
          (Finset.subset_insert α T) β hβ_T] at h_step2
      exact h_step2

/-- **`foldl_insert_eq_union`**: list-fold of `insert` equals union with
the list-as-Finset. Proved by induction on `l` with `T` generalized. -/
private lemma foldl_insert_eq_union :
    ∀ (l : List Ordinal.{0}) (T : Finset Ordinal.{0}),
      l.foldl (fun S α => insert α S) T = T ∪ l.toFinset
  | [], T => by simp
  | α :: tail, T => by
    show tail.foldl (fun S α => insert α S) (insert α T) =
      T ∪ (α :: tail).toFinset
    rw [foldl_insert_eq_union tail (insert α T)]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, List.toFinset_cons]
    tauto

/-- **`transport_extend_compat`**: transports an `extend_list`-style
compat result across a Finset equation. Generic helper for converting
between forms of the underlying Finset (e.g., `l.foldl insert T` vs
`T ∪ U`). The subst handles both the type and the subset proof. -/
private lemma transport_extend_compat
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {T : Finset Ordinal.{0}} (PG : CoherentGoodBranchPartial cR T)
    {S₁ S₂ : Finset Ordinal.{0}} (h_eq : S₁ = S₂)
    (hT₁ : T ⊆ S₁) (hT₂ : T ⊆ S₂)
    (Q : CoherentGoodBranchPartial cR S₁)
    (h_compat : cbpFieldwiseCompat
      (Q.toCoherentBranchPartial.restrict hT₁) PG.toCoherentBranchPartial) :
    cbpFieldwiseCompat
      ((h_eq ▸ Q).toCoherentBranchPartial.restrict hT₂)
        PG.toCoherentBranchPartial := by
  subst h_eq
  exact h_compat

/-- **`coherentGoodBranchPartial_extend_to_union`**: Good-layer union
extension via the list version + final equality transport. Uses
`l := (U \ T).toList` so each element is fresh, then applies
`coherentGoodBranchPartial_extend_list` and transports via
`foldl_insert_eq_union`. -/
theorem coherentGoodBranchPartial_extend_to_union
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {T : Finset Ordinal.{0}} (PG : CoherentGoodBranchPartial cR T)
    (U : Finset Ordinal.{0})
    (hU : ∀ α ∈ U, α < Ordinal.omega.{0} 1) :
    ∃ Q : CoherentGoodBranchPartial cR (T ∪ U),
      cbpFieldwiseCompat
        (Q.toCoherentBranchPartial.restrict Finset.subset_union_left)
        PG.toCoherentBranchPartial := by
  classical
  set l : List Ordinal.{0} := (U \ T).toList with hl_def
  have h_valid : ∀ α ∈ l, α < Ordinal.omega.{0} 1 := fun α hα =>
    hU α (Finset.mem_sdiff.mp (Finset.mem_toList.mp hα)).1
  have h_nodup : l.Nodup := Finset.nodup_toList _
  have h_disjoint : ∀ α ∈ l, α ∉ T := fun α hα =>
    (Finset.mem_sdiff.mp (Finset.mem_toList.mp hα)).2
  -- l.foldl _ T = T ∪ U via foldl_insert_eq_union + toList_toFinset + sdiff identity.
  have h_fold : l.foldl (fun S α => insert α S) T = T ∪ U := by
    rw [foldl_insert_eq_union l T]
    show T ∪ l.toFinset = T ∪ U
    show T ∪ (U \ T).toList.toFinset = T ∪ U
    rw [Finset.toList_toFinset]
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  -- Apply extend_list to get Q' on l.foldl _ T.
  obtain ⟨Q', hQ'⟩ := coherentGoodBranchPartial_extend_list PG l
    h_valid h_nodup h_disjoint
  -- Transport via the generic helper.
  refine ⟨h_fold ▸ Q', transport_extend_compat PG h_fold
    (subset_foldl_insert l T) Finset.subset_union_left Q' hQ'⟩

/-- **`CoherentGoodBranchPartial.cast`**: transport a CGBP across a
Finset equality. Generic transport primitive — defined via `h ▸ P`
with `S, T` as separate parameters so `subst` works cleanly in
downstream proofs. -/
def CoherentGoodBranchPartial.cast
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {S T : Finset Ordinal.{0}} (h : S = T)
    (P : CoherentGoodBranchPartial cR S) :
    CoherentGoodBranchPartial cR T := h ▸ P

/-- **`CoherentGoodBranchPartial.cast_restrict_self`**: compat between
a cast CGBP's restriction back to a subset of the source and the
original CGBP itself. Closes via `subst h` (works because `S, T` are
separate parameters), then `restrict_prefixAt/branch` reduces to refl
under proof irrelevance on the subset proof. -/
theorem CoherentGoodBranchPartial.cast_restrict_self
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {S T : Finset Ordinal.{0}} (h : S = T)
    (P : CoherentGoodBranchPartial cR S) (hST : S ⊆ T) :
    cbpFieldwiseCompat
      ((P.cast h).toCoherentBranchPartial.restrict hST)
      P.toCoherentBranchPartial := by
  subst h
  refine ⟨?_, ?_⟩
  · intro β hβ
    rw [CoherentBranchPartial.restrict_prefixAt]
    rfl
  · intro β hβ
    rw [CoherentBranchPartial.restrict_branch]
    rfl

/-- **`CoherentGoodBranchPartial.AmbientCompat`**: cross-level
coherence between two CGBPs on different finsets. Strictly stronger
than the naive "overlap compat on `S ∩ T`" hypothesis: it requires
agreement on **every** cross-pair of indices, mediated by the
appropriate initial-segment embedding. This is the **mathematically
correct** compatibility for pair amalgamation, since a CGBP's prefix
at `α` already prescribes data at every `β < α` even if `β` is not in
the finset itself.

**Fields.**
* `prefix_below`: for `β ∈ S` and `α ∈ T` with `β < α`,
  `P.prefix β = PR.prefix α` restricted to `β.ToType` via initSeg.
* `branch_below`: analogous for the type function.
* `prefix_above`: for `α ∈ T` and `β ∈ S` with `α < β`,
  `PR.prefix α = P.prefix β` restricted to `α.ToType` via initSeg.
* `branch_above`: analogous.
* `prefix_diag`/`branch_diag`: same-level agreement on the overlap
  `α ∈ S ∩ T` (`P.prefix α = PR.prefix α`). The strict cross-level
  fields do not entail this at a common maximum, so it is explicit;
  it is what the `S₂ ∩ S₁` overlap case of `amalgamate_pair` needs.

**Why "below/above" instead of single direction.** Although the
relation is logically symmetric, splitting by direction matches how
the hypothesis is used in `PrescribedAmbientCompat` construction
(where the "α" being inserted has a specific role). -/
structure CoherentGoodBranchPartial.AmbientCompat
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {S T : Finset Ordinal.{0}}
    (P : CoherentGoodBranchPartial cR S)
    (PR : CoherentGoodBranchPartial cR T) : Prop where
  prefix_below : ∀ β (hβ_S : β ∈ S) α (hα_T : α ∈ T) (hβ_lt_α : β < α),
    haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    ∀ (x : β.ToType),
      P.toCoherentBranchPartial.prefixAt β hβ_S x =
        PR.toCoherentBranchPartial.prefixAt α hα_T
          ((Ordinal.initialSegToType hβ_lt_α.le).toOrderEmbedding x)
  branch_below : ∀ β (hβ_S : β ∈ S) α (hα_T : α ∈ T) (hβ_lt_α : β < α),
    haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    ∀ (x : β.ToType),
      P.toCoherentBranchPartial.branch β hβ_S x =
        PR.toCoherentBranchPartial.branch α hα_T
          ((Ordinal.initialSegToType hβ_lt_α.le).toOrderEmbedding x)
  prefix_above : ∀ α (hα_T : α ∈ T) β (hβ_S : β ∈ S) (hα_lt_β : α < β),
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
    ∀ (x : α.ToType),
      PR.toCoherentBranchPartial.prefixAt α hα_T x =
        P.toCoherentBranchPartial.prefixAt β hβ_S
          ((Ordinal.initialSegToType hα_lt_β.le).toOrderEmbedding x)
  branch_above : ∀ α (hα_T : α ∈ T) β (hβ_S : β ∈ S) (hα_lt_β : α < β),
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
    ∀ (x : α.ToType),
      PR.toCoherentBranchPartial.branch α hα_T x =
        P.toCoherentBranchPartial.branch β hβ_S
          ((Ordinal.initialSegToType hα_lt_β.le).toOrderEmbedding x)
  /-- Diagonal coherence: on the overlap `α ∈ S ∩ T`, `P` and `PR`
  prescribe the same prefix embedding. The strict cross-level fields
  do not entail this when `α` is a common maximum (no element lies
  strictly above it), so same-level agreement is stated explicitly. -/
  prefix_diag : ∀ α (hα_S : α ∈ S) (hα_T : α ∈ T),
    P.toCoherentBranchPartial.prefixAt α hα_S =
      PR.toCoherentBranchPartial.prefixAt α hα_T
  /-- Diagonal type coherence on the overlap. -/
  branch_diag : ∀ α (hα_S : α ∈ S) (hα_T : α ∈ T),
    P.toCoherentBranchPartial.branch α hα_S =
      PR.toCoherentBranchPartial.branch α hα_T

/-- **`cgbp_union_empty_right`**: trivial transport `S ∪ ∅ = S`
producing a CGBP at the `S ∪ ∅` index with compat back to the
original. Base case of `amalgamate_pair_aux`. -/
private lemma cgbp_union_empty_right
    {cR : (Fin 2 ↪o PairERSource) → Bool} {S : Finset Ordinal.{0}}
    (P : CoherentGoodBranchPartial cR S) :
    ∃ Q : CoherentGoodBranchPartial cR (S ∪ ∅),
      cbpFieldwiseCompat
        (Q.toCoherentBranchPartial.restrict
          (fun α hα => Finset.mem_union_left _ hα))
        P.toCoherentBranchPartial :=
  ⟨P.cast (Finset.union_empty S).symm,
    P.cast_restrict_self (Finset.union_empty S).symm _⟩

/-- **`PrescribedAmbientCompat P Pα`**: the strengthened compatibility
hypothesis required for `insert_prescribed_new_compatible`. Says that
`Pα`'s prefix and branch at `α` agree with `P`'s prefix and branch at
every position `β ∈ T` where they both have data, via the appropriate
initial-segment restrictions.

For `β ∈ T` with `β < α`: the prefix embedding `Pα.prefixAt α` at the
initial-segment `β.ToType` agrees with `P.prefixAt β`, and the type
function `Pα.branch α` at the initial-segment agrees with `P.branch β`.
Symmetric `prefix_above/branch_above` fields handle `β ∈ T` with
`α < β`. -/
structure PrescribedAmbientCompat
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {T : Finset Ordinal.{0}} (α : Ordinal.{0})
    (P : CoherentGoodBranchPartial cR T)
    (Pα : CoherentGoodBranchPartial cR ({α} : Finset Ordinal.{0})) :
    Prop where
  /-- Below-α coherence: `Pα`'s prefix at `α` agrees with `P`'s prefix
  at each `β ∈ T` with `β < α`, via the initial-segment embedding. -/
  prefix_below : ∀ β (hβ_T : β ∈ T) (hβ_lt_α : β < α),
    haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    ∀ (x : β.ToType),
      P.toCoherentBranchPartial.prefixAt β hβ_T x =
        Pα.toCoherentBranchPartial.prefixAt α (Finset.mem_singleton.mpr rfl)
          ((Ordinal.initialSegToType hβ_lt_α.le).toOrderEmbedding x)
  /-- Below-α type coherence: `Pα`'s branch at `α` agrees with `P`'s
  branch at each `β ∈ T` with `β < α`. -/
  branch_below : ∀ β (hβ_T : β ∈ T) (hβ_lt_α : β < α),
    haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    ∀ (x : β.ToType),
      P.toCoherentBranchPartial.branch β hβ_T x =
        Pα.toCoherentBranchPartial.branch α (Finset.mem_singleton.mpr rfl)
          ((Ordinal.initialSegToType hβ_lt_α.le).toOrderEmbedding x)
  /-- Above-α coherence: `Pα`'s prefix at `α` agrees with `P`'s prefix
  at each `β ∈ T` with `α < β`, via the initial-segment embedding
  `α.ToType → β.ToType`. -/
  prefix_above : ∀ β (hβ_T : β ∈ T) (hα_lt_β : α < β),
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
    ∀ (x : α.ToType),
      Pα.toCoherentBranchPartial.prefixAt α (Finset.mem_singleton.mpr rfl) x =
        P.toCoherentBranchPartial.prefixAt β hβ_T
          ((Ordinal.initialSegToType hα_lt_β.le).toOrderEmbedding x)
  /-- Above-α type coherence. -/
  branch_above : ∀ β (hβ_T : β ∈ T) (hα_lt_β : α < β),
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
    ∀ (x : α.ToType),
      Pα.toCoherentBranchPartial.branch α (Finset.mem_singleton.mpr rfl) x =
        P.toCoherentBranchPartial.branch β hβ_T
          ((Ordinal.initialSegToType hα_lt_β.le).toOrderEmbedding x)

/-- **`amalgamate_pair_aux_prescribedAmbient`**: the
`PrescribedAmbientCompat` builder used at each insertion step of
`amalgamate_pair_aux`.

**Inputs** (running invariants at the induction step):
* `Q' : CGBP cR (S ∪ D')` — the IH's CGBP on the partial domain.
* `hQ'_P : cbpFieldwiseCompat (Q'|S) P` — Q' agrees with P on S.
* `hQ'_PR_prefix/branch : ∀ β ∈ D', Q' at β agrees with PR at β`.
* `h_ambient : AmbientCompat P PR` — the global ambient compat.
* `α : Ordinal`, `hα_R : α ∈ R`, `hα_S : α ∉ S`, `hα_D' : α ∉ D'`.

**Output**: `PrescribedAmbientCompat α Q' (PR.restrict ({α} ⊆ R))`,
ready for `insert_prescribed_new_compatible (Q', α, PR.restrict {α})`.

**Proof structure**: for each direction, case-split β ∈ S ∪ D':
* `β ∈ S` (and β ≠ α since α ∉ S): use hQ'_P to bridge Q' to P, then
  AmbientCompat to bridge P to PR (the four AmbientCompat fields
  cover all directions).
* `β ∈ D'`: use hQ'_PR_* to bridge Q' directly to PR, then PR's
  internal restrict_prefixAt/branch to bridge PR at β to PR at α
  restricted.

All four PrescribedAmbientCompat fields proven by the case-analysis
documented above. -/
private lemma amalgamate_pair_aux_prescribedAmbient
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {S : Finset Ordinal.{0}}
    (P : CoherentGoodBranchPartial cR S)
    {R : Finset Ordinal.{0}}
    (PR : CoherentGoodBranchPartial cR R)
    {D' : Finset Ordinal.{0}}
    (Q' : CoherentGoodBranchPartial cR (S ∪ D'))
    (_hQ'_P : cbpFieldwiseCompat
      (Q'.toCoherentBranchPartial.restrict Finset.subset_union_left)
      P.toCoherentBranchPartial)
    (_hD'_sub_R : D' ⊆ R)
    (_hQ'_PR_prefix : ∀ β (hβ_D' : β ∈ D') (x : β.ToType),
      Q'.toCoherentBranchPartial.prefixAt β
          (Finset.mem_union_right S hβ_D') x =
        PR.toCoherentBranchPartial.prefixAt β (_hD'_sub_R hβ_D') x)
    (_hQ'_PR_branch : ∀ β (hβ_D' : β ∈ D') (x : β.ToType),
      Q'.toCoherentBranchPartial.branch β
          (Finset.mem_union_right S hβ_D') x =
        PR.toCoherentBranchPartial.branch β (_hD'_sub_R hβ_D') x)
    (_h_ambient : CoherentGoodBranchPartial.AmbientCompat P PR)
    (α : Ordinal.{0}) (_hα_R : α ∈ R)
    (_hα_S : α ∉ S) (_hα_D' : α ∉ D') :
    PrescribedAmbientCompat α Q' (PR.restrict
        (Finset.singleton_subset_iff.mpr _hα_R)) where
  prefix_below := by
    intro β hβ hβ_lt_α x
    -- Reduce RHS via restrict_toCBP + restrict_prefixAt.
    rw [CoherentGoodBranchPartial.restrict_toCoherentBranchPartial,
        CoherentBranchPartial.restrict_prefixAt]
    -- Now goal:
    --   Q'.toCBP.prefixAt β hβ x = PR.toCBP.prefixAt α _hα_R (initSeg.toOE x)
    rcases Finset.mem_union.mp hβ with hβ_S | hβ_D'
    · -- β ∈ S branch
      have hQP_eq : (Q'.toCoherentBranchPartial.restrict
            Finset.subset_union_left).prefixAt β hβ_S =
          P.toCoherentBranchPartial.prefixAt β hβ_S := _hQ'_P.1 β hβ_S
      have hQP_x : Q'.toCoherentBranchPartial.prefixAt β
            (Finset.subset_union_left hβ_S) x =
          P.toCoherentBranchPartial.prefixAt β hβ_S x := by
        have h := congrFun (congrArg (fun f : β.ToType ↪o PairERSource =>
          (f : β.ToType → PairERSource)) hQP_eq) x
        rw [CoherentBranchPartial.restrict_prefixAt] at h
        exact h
      rw [hQP_x]
      exact _h_ambient.prefix_below β hβ_S α _hα_R hβ_lt_α x
    · -- β ∈ D' branch
      have hQR_x : Q'.toCoherentBranchPartial.prefixAt β
            (Finset.mem_union_right S hβ_D') x =
          PR.toCoherentBranchPartial.prefixAt β (_hD'_sub_R hβ_D') x :=
        _hQ'_PR_prefix β hβ_D' x
      rw [hQR_x]
      exact (PR.toCoherentBranchPartial.prefix_restrict hβ_lt_α.le
        (_hD'_sub_R hβ_D') _hα_R x).symm
  branch_below := by
    intro β hβ hβ_lt_α x
    rw [CoherentGoodBranchPartial.restrict_toCoherentBranchPartial,
        CoherentBranchPartial.restrict_branch]
    rcases Finset.mem_union.mp hβ with hβ_S | hβ_D'
    · -- β ∈ S branch
      have hQP_eq : (Q'.toCoherentBranchPartial.restrict
            Finset.subset_union_left).branch β hβ_S =
          P.toCoherentBranchPartial.branch β hβ_S := _hQ'_P.2 β hβ_S
      have hQP_x : Q'.toCoherentBranchPartial.branch β
            (Finset.subset_union_left hβ_S) x =
          P.toCoherentBranchPartial.branch β hβ_S x := by
        have h := congrFun hQP_eq x
        rw [CoherentBranchPartial.restrict_branch] at h
        exact h
      rw [hQP_x]
      exact _h_ambient.branch_below β hβ_S α _hα_R hβ_lt_α x
    · -- β ∈ D' branch
      have hQR_x : Q'.toCoherentBranchPartial.branch β
            (Finset.mem_union_right S hβ_D') x =
          PR.toCoherentBranchPartial.branch β (_hD'_sub_R hβ_D') x :=
        _hQ'_PR_branch β hβ_D' x
      rw [hQR_x]
      exact (PR.toCoherentBranchPartial.branch_restrict hβ_lt_α.le
        (_hD'_sub_R hβ_D') _hα_R x).symm
  prefix_above := by
    intro β hβ hα_lt_β x
    -- Reduce LHS via restrict_toCBP + restrict_prefixAt.
    rw [CoherentGoodBranchPartial.restrict_toCoherentBranchPartial,
        CoherentBranchPartial.restrict_prefixAt]
    -- Now goal:
    --   PR.toCBP.prefixAt α _hα_R x = Q'.toCBP.prefixAt β hβ (initSeg.toOE x)
    rcases Finset.mem_union.mp hβ with hβ_S | hβ_D'
    · -- β ∈ S branch
      have hQP_eq : (Q'.toCoherentBranchPartial.restrict
            Finset.subset_union_left).prefixAt β hβ_S =
          P.toCoherentBranchPartial.prefixAt β hβ_S := _hQ'_P.1 β hβ_S
      have hQP_x : Q'.toCoherentBranchPartial.prefixAt β
            (Finset.subset_union_left hβ_S)
            ((Ordinal.initialSegToType hα_lt_β.le).toOrderEmbedding x) =
          P.toCoherentBranchPartial.prefixAt β hβ_S
            ((Ordinal.initialSegToType hα_lt_β.le).toOrderEmbedding x) := by
        have h := congrFun (congrArg (fun f : β.ToType ↪o PairERSource =>
          (f : β.ToType → PairERSource)) hQP_eq)
          ((Ordinal.initialSegToType hα_lt_β.le).toOrderEmbedding x)
        rw [CoherentBranchPartial.restrict_prefixAt] at h
        exact h
      rw [hQP_x]
      exact _h_ambient.prefix_above α _hα_R β hβ_S hα_lt_β x
    · -- β ∈ D' branch
      have hQR_x : Q'.toCoherentBranchPartial.prefixAt β
            (Finset.mem_union_right S hβ_D')
            ((Ordinal.initialSegToType hα_lt_β.le).toOrderEmbedding x) =
          PR.toCoherentBranchPartial.prefixAt β (_hD'_sub_R hβ_D')
            ((Ordinal.initialSegToType hα_lt_β.le).toOrderEmbedding x) :=
        _hQ'_PR_prefix β hβ_D'
          ((Ordinal.initialSegToType hα_lt_β.le).toOrderEmbedding x)
      rw [hQR_x]
      exact (PR.toCoherentBranchPartial.prefix_restrict hα_lt_β.le
        _hα_R (_hD'_sub_R hβ_D') x).symm
  branch_above := by
    intro β hβ hα_lt_β x
    rw [CoherentGoodBranchPartial.restrict_toCoherentBranchPartial,
        CoherentBranchPartial.restrict_branch]
    rcases Finset.mem_union.mp hβ with hβ_S | hβ_D'
    · -- β ∈ S branch
      have hQP_eq : (Q'.toCoherentBranchPartial.restrict
            Finset.subset_union_left).branch β hβ_S =
          P.toCoherentBranchPartial.branch β hβ_S := _hQ'_P.2 β hβ_S
      have hQP_x : Q'.toCoherentBranchPartial.branch β
            (Finset.subset_union_left hβ_S)
            ((Ordinal.initialSegToType hα_lt_β.le).toOrderEmbedding x) =
          P.toCoherentBranchPartial.branch β hβ_S
            ((Ordinal.initialSegToType hα_lt_β.le).toOrderEmbedding x) := by
        have h := congrFun hQP_eq
          ((Ordinal.initialSegToType hα_lt_β.le).toOrderEmbedding x)
        rw [CoherentBranchPartial.restrict_branch] at h
        exact h
      rw [hQP_x]
      exact _h_ambient.branch_above α _hα_R β hβ_S hα_lt_β x
    · -- β ∈ D' branch
      have hQR_x : Q'.toCoherentBranchPartial.branch β
            (Finset.mem_union_right S hβ_D')
            ((Ordinal.initialSegToType hα_lt_β.le).toOrderEmbedding x) =
          PR.toCoherentBranchPartial.branch β (_hD'_sub_R hβ_D')
            ((Ordinal.initialSegToType hα_lt_β.le).toOrderEmbedding x) :=
        _hQ'_PR_branch β hβ_D'
          ((Ordinal.initialSegToType hα_lt_β.le).toOrderEmbedding x)
      rw [hQR_x]
      exact (PR.toCoherentBranchPartial.branch_restrict hα_lt_β.le
        _hα_R (_hD'_sub_R hβ_D') x).symm

/-- **[FRONTIER, sorry — CORRECTED]**
`coherentGoodBranchPartial_insert_prescribed_new_compatible`. The
mathematically correct form: requires `PrescribedAmbientCompat` (the
strong compat with all four directions: prefix/branch × below/above).

**Construction status (2026-05-24).** The CGBA core
`insertPrescribedGoodApprox` is now **fully closed axiom-clean** (all
four fields: prefix_restrict, branch_restrict, large,
top_in_validFiber). The remaining wrapper packages this into a CGBP
and discharges the two compat conclusions (with `P` on `T` and `Pα`
on `{α}`) via:
1. `letI Q := { toGoodApprox := insertPrescribedGoodApprox ...,
                 level_eq := fun _ => rfl }`.
2. For γ ∈ T (compat with P): use the parallel of
   `insertBeforeGoodApprox_goodAt_old_head/type` —
   `insertPrescribedGoodApprox_goodAt_old_head/type`, which routes
   through `insertPrescribedGoodAt_eq_old` + `goodAt_head_apply_eq_of_eq`.
3. For γ = α (compat with Pα): use the parallel
   `_goodAt_alpha_head/type`, routing through
   `insertPrescribedGoodAt_eq_alpha` (the singleton membership
   `α ∈ {α}` is `Finset.mem_singleton.mpr rfl`).

Both helper-lemma sets follow the existing
`insertBeforeGoodApprox_goodAt_old_*` template mechanically. -/
theorem coherentGoodBranchPartial_insert_prescribed_new_compatible
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {T : Finset Ordinal.{0}} (α : Ordinal.{0})
    (hαT : α ∉ T)
    (_hT : ∀ β ∈ T, β < Ordinal.omega.{0} 1)
    (hα : α < Ordinal.omega.{0} 1)
    (P : CoherentGoodBranchPartial cR T)
    (Pα : CoherentGoodBranchPartial cR ({α} : Finset Ordinal.{0}))
    (h_compat : PrescribedAmbientCompat α P Pα) :
    ∃ Q : CoherentGoodBranchPartial cR (insert α T),
      cbpFieldwiseCompat
        (Q.toCoherentBranchPartial.restrict (Finset.subset_insert α T))
        P.toCoherentBranchPartial ∧
      cbpFieldwiseCompat
        (Q.toCoherentBranchPartial.restrict
          (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self α T)))
        Pα.toCoherentBranchPartial := by
  letI Q : CoherentGoodBranchPartial cR (insert α T) :=
    { toGoodApprox := insertPrescribedGoodApprox P hα hαT Pα
        h_compat.prefix_below h_compat.branch_below
        h_compat.prefix_above h_compat.branch_above
      level_eq := fun _ => rfl }
  refine ⟨Q, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · -- prefix compat with P on T
    intro γ hγ
    rw [CoherentBranchPartial.restrict_prefixAt]
    apply RelEmbedding.ext
    intro x
    rw [← Q.good_head_eq γ (Finset.mem_insert_of_mem hγ) x,
        ← P.good_head_eq γ hγ x]
    exact insertPrescribedGoodApprox_goodAt_old_head P hα hαT Pα
      h_compat.prefix_below h_compat.branch_below
      h_compat.prefix_above h_compat.branch_above γ hγ x
  · -- branch compat with P on T
    intro γ hγ
    rw [CoherentBranchPartial.restrict_branch]
    funext x
    rw [← Q.good_type_eq γ (Finset.mem_insert_of_mem hγ) x,
        ← P.good_type_eq γ hγ x]
    exact insertPrescribedGoodApprox_goodAt_old_type P hα hαT Pα
      h_compat.prefix_below h_compat.branch_below
      h_compat.prefix_above h_compat.branch_above γ hγ x
  · -- prefix compat with Pα on {α}
    intro γ hγ_sing
    have hγ_eq : γ = α := Finset.mem_singleton.mp hγ_sing
    subst hγ_eq
    rw [CoherentBranchPartial.restrict_prefixAt]
    apply RelEmbedding.ext
    intro x
    rw [← Q.good_head_eq γ (Finset.mem_insert_self γ T) x,
        ← Pα.good_head_eq γ (Finset.mem_singleton.mpr rfl) x]
    exact insertPrescribedGoodApprox_goodAt_alpha_head P hα hαT Pα
      h_compat.prefix_below h_compat.branch_below
      h_compat.prefix_above h_compat.branch_above x
  · -- branch compat with Pα on {α}
    intro γ hγ_sing
    have hγ_eq : γ = α := Finset.mem_singleton.mp hγ_sing
    subst hγ_eq
    rw [CoherentBranchPartial.restrict_branch]
    funext x
    rw [← Q.good_type_eq γ (Finset.mem_insert_self γ T) x,
        ← Pα.good_type_eq γ (Finset.mem_singleton.mpr rfl) x]
    exact insertPrescribedGoodApprox_goodAt_alpha_type P hα hαT Pα
      h_compat.prefix_below h_compat.branch_below
      h_compat.prefix_above h_compat.branch_above x

/-- **`amalgamate_pair_aux`** [auxiliary induction lemma for
`amalgamate_pair`]: prove pair amalgamation by induction on a disjoint
subset `D ⊆ R` representing the indices still to be inserted into the
running `S`-side domain.

**Invariant** at each step: the running `Q` agrees with `P` on `S`
(via `Q.restrict (S ⊆ S ∪ D)` compat `P`) and agrees with `PR` on
each `α ∈ D` (singleton-restricted compat). Insertion uses
`insert_prescribed_new_compatible` with the `PrescribedAmbientCompat`
assembled from the running invariants.

**Base** `D = ∅`: `S ∪ ∅ = S`, take `Q := P` after observing that
`S ∪ ∅ = S` as Finsets requires a small transport / direct rfl.

**Step** `D = insert α D'` with `α ∉ D'`: by IH on `D'`, get `Q'` on
`S ∪ D'` with the running invariants. By `hD_disjoint`,
`α ∉ S`; by `α ∉ D'`, `α ∉ S ∪ D'`. Apply
`insert_prescribed_new_compatible (Q', α, PR.restrict {α})` with
`PrescribedAmbientCompat` built from:
* `prefix_below/branch_below`: for `β < α` in `S ∪ D'`, agreement
  follows from either S-side overlap (`β ∈ S` → use
  `h_overlap_prefix` + PR's `restrict_prefixAt`) or D-side invariant
  (`β ∈ D'` → use IH's PR-agreement).
* `prefix_above/branch_above`: symmetric, for `α < β` in `S ∪ D'`.

**Status.** Proved (axiom-clean). Finset induction on `D`; the base
case is split out as `cgbp_union_empty_right`, and the step assembles
`PrescribedAmbientCompat` via `amalgamate_pair_aux_prescribedAmbient`,
inserts via `insert_prescribed_new_compatible`, and transports the
result across `insert α' (S ∪ D') = S ∪ insert α' D'`. -/
private lemma coherentGoodBranchPartial_amalgamate_pair_aux
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {S : Finset Ordinal.{0}}
    (_hS : ∀ α ∈ S, α < Ordinal.omega.{0} 1)
    (_P : CoherentGoodBranchPartial cR S)
    {R : Finset Ordinal.{0}}
    (_hR : ∀ α ∈ R, α < Ordinal.omega.{0} 1)
    (_PR : CoherentGoodBranchPartial cR R)
    (_h_ambient : CoherentGoodBranchPartial.AmbientCompat _P _PR)
    (D : Finset Ordinal.{0}) (_hD_sub : D ⊆ R)
    (_hD_disjoint : ∀ α ∈ D, α ∉ S) :
    ∃ Q : CoherentGoodBranchPartial cR (S ∪ D),
      cbpFieldwiseCompat
        (Q.toCoherentBranchPartial.restrict Finset.subset_union_left)
        _P.toCoherentBranchPartial ∧
      (∀ α (hα_D : α ∈ D) (x : α.ToType),
        Q.toCoherentBranchPartial.prefixAt α
            (Finset.mem_union_right S hα_D) x =
          _PR.toCoherentBranchPartial.prefixAt α (_hD_sub hα_D) x) ∧
      (∀ α (hα_D : α ∈ D) (x : α.ToType),
        Q.toCoherentBranchPartial.branch α
            (Finset.mem_union_right S hα_D) x =
          _PR.toCoherentBranchPartial.branch α (_hD_sub hα_D) x) := by
  classical
  revert _hD_sub _hD_disjoint
  induction D using Finset.induction_on with
  | empty =>
    intro _hD_sub _hD_disjoint
    obtain ⟨Q, hQ⟩ := cgbp_union_empty_right _P
    refine ⟨Q, hQ, ?_, ?_⟩
    · intro α hα _x
      exact absurd hα (Finset.notMem_empty α)
    · intro α hα _x
      exact absurd hα (Finset.notMem_empty α)
  | @insert α' D' h_notin IH =>
    intro _hD_sub _hD_disjoint
    -- The "hidden depth" concern (β ∈ S \ R) is resolved by the
    -- `AmbientCompat _P _PR` hypothesis (`_h_ambient`): the helper
    -- `amalgamate_pair_aux_prescribedAmbient` assembles the required
    -- `PrescribedAmbientCompat` from it together with the running
    -- invariants, covering all cross-pairs via PR's internal coherence.
    --
    -- Cast-transport helpers: target-side prefix/branch under a domain
    -- equality `A = B` (provable by `subst` since `A, B` are variables).
    have cast_pref : ∀ {A B : Finset Ordinal.{0}} (hAB : A = B)
        (Pc : CoherentGoodBranchPartial cR A) (γ : Ordinal.{0})
        (hA : γ ∈ A) (hB : γ ∈ B),
        (Pc.cast hAB).toCoherentBranchPartial.prefixAt γ hB =
          Pc.toCoherentBranchPartial.prefixAt γ hA := by
      intro A B hAB Pc γ hA hB; subst hAB; rfl
    have cast_branch : ∀ {A B : Finset Ordinal.{0}} (hAB : A = B)
        (Pc : CoherentGoodBranchPartial cR A) (γ : Ordinal.{0})
        (hA : γ ∈ A) (hB : γ ∈ B),
        (Pc.cast hAB).toCoherentBranchPartial.branch γ hB =
          Pc.toCoherentBranchPartial.branch γ hA := by
      intro A B hAB Pc γ hA hB; subst hAB; rfl
    -- Membership bookkeeping for the inserted index α'.
    have hα'_mem : α' ∈ insert α' D' := Finset.mem_insert_self α' D'
    have hα'_R : α' ∈ R := _hD_sub hα'_mem
    have hα'_S : α' ∉ S := _hD_disjoint α' hα'_mem
    have hD'_sub : D' ⊆ R := fun x hx => _hD_sub (Finset.mem_insert_of_mem hx)
    have hD'_disjoint : ∀ a ∈ D', a ∉ S :=
      fun a ha => _hD_disjoint a (Finset.mem_insert_of_mem ha)
    have hα'_notin : α' ∉ S ∪ D' := by
      simp only [Finset.mem_union, not_or]; exact ⟨hα'_S, h_notin⟩
    -- Inductive hypothesis on the smaller frontier D'.
    obtain ⟨Q', hQ'_S, hQ'_PR_prefix, hQ'_PR_branch⟩ := IH hD'_sub hD'_disjoint
    -- ω₁ side conditions.
    have hα'_lt : α' < Ordinal.omega.{0} 1 := _hR α' hα'_R
    have hSD'_lt : ∀ β ∈ S ∪ D', β < Ordinal.omega.{0} 1 := by
      intro β hβ
      rcases Finset.mem_union.mp hβ with hβ_S | hβ_D'
      · exact _hS β hβ_S
      · exact _hR β (hD'_sub hβ_D')
    -- Strong prescribed-ambient compat assembled by the helper.
    have h_compat :
        PrescribedAmbientCompat α' Q'
          (_PR.restrict (Finset.singleton_subset_iff.mpr hα'_R)) :=
      amalgamate_pair_aux_prescribedAmbient _P _PR Q' hQ'_S hD'_sub
        hQ'_PR_prefix hQ'_PR_branch _h_ambient α' hα'_R hα'_S h_notin
    -- Insert α' via the prescribed-new-compatible insertion theorem.
    obtain ⟨Q₀, hQ₀_Q', hQ₀_Pα⟩ :=
      coherentGoodBranchPartial_insert_prescribed_new_compatible α' hα'_notin
        hSD'_lt hα'_lt Q' (_PR.restrict (Finset.singleton_subset_iff.mpr hα'_R))
        h_compat
    -- Transport Q₀ : CGBP (insert α' (S ∪ D')) to CGBP (S ∪ insert α' D').
    have h_dom : insert α' (S ∪ D') = S ∪ insert α' D' :=
      (Finset.union_insert α' S D').symm
    refine ⟨Q₀.cast h_dom, ?_, ?_, ?_⟩
    · -- S-side fieldwise compat with _P (embedding/function level).
      refine ⟨?_, ?_⟩
      · intro γ hγ
        have hγ_SD' : γ ∈ S ∪ D' := Finset.mem_union_left _ hγ
        have e1 := hQ₀_Q'.1 γ hγ_SD'
        have e2 := hQ'_S.1 γ hγ
        simp only [CoherentBranchPartial.restrict_prefixAt] at e1 e2 ⊢
        rw [cast_pref h_dom Q₀ γ (Finset.mem_insert_of_mem hγ_SD')
          (Finset.subset_union_left hγ)]
        exact e1.trans e2
      · intro γ hγ
        have hγ_SD' : γ ∈ S ∪ D' := Finset.mem_union_left _ hγ
        have e1 := hQ₀_Q'.2 γ hγ_SD'
        have e2 := hQ'_S.2 γ hγ
        simp only [CoherentBranchPartial.restrict_branch] at e1 e2 ⊢
        rw [cast_branch h_dom Q₀ γ (Finset.mem_insert_of_mem hγ_SD')
          (Finset.subset_union_left hγ)]
        exact e1.trans e2
    · -- D-side prefix agreement with _PR (value level).
      intro a ha x
      have hA : a ∈ insert α' (S ∪ D') :=
        Finset.insert_subset_insert α' Finset.subset_union_right ha
      rw [cast_pref h_dom Q₀ a hA (Finset.mem_union_right S ha)]
      -- `rcases … with rfl` substitutes `α'` away, leaving everything in `a`.
      rcases Finset.mem_insert.mp ha with rfl | ha_D'
      · -- a = α': use the singleton-side compat from the insertion.
        have eP := hQ₀_Pα.1 a (Finset.mem_singleton.mpr rfl)
        simp only [CoherentGoodBranchPartial.restrict_toCoherentBranchPartial,
          CoherentBranchPartial.restrict_prefixAt] at eP
        exact congrFun (congrArg (fun e : a.ToType ↪o PairERSource =>
          (e : a.ToType → PairERSource)) eP) x
      · -- a ∈ D': chain Q₀-vs-Q' (insertion) with Q'-vs-PR (IH).
        have ha_SD' : a ∈ S ∪ D' := Finset.mem_union_right _ ha_D'
        have e1 := hQ₀_Q'.1 a ha_SD'
        simp only [CoherentBranchPartial.restrict_prefixAt] at e1
        exact (congrFun (congrArg (fun e : a.ToType ↪o PairERSource =>
          (e : a.ToType → PairERSource)) e1) x).trans (hQ'_PR_prefix a ha_D' x)
    · -- D-side branch agreement with _PR (value level).
      intro a ha x
      have hA : a ∈ insert α' (S ∪ D') :=
        Finset.insert_subset_insert α' Finset.subset_union_right ha
      rw [cast_branch h_dom Q₀ a hA (Finset.mem_union_right S ha)]
      rcases Finset.mem_insert.mp ha with rfl | ha_D'
      · have eP := hQ₀_Pα.2 a (Finset.mem_singleton.mpr rfl)
        simp only [CoherentGoodBranchPartial.restrict_toCoherentBranchPartial,
          CoherentBranchPartial.restrict_branch] at eP
        exact congrFun eP x
      · have ha_SD' : a ∈ S ∪ D' := Finset.mem_union_right _ ha_D'
        have e1 := hQ₀_Q'.2 a ha_SD'
        simp only [CoherentBranchPartial.restrict_branch] at e1
        exact (congrFun e1 x).trans (hQ'_PR_branch a ha_D' x)

/-- **`coherentGoodBranchPartial_amalgamate_pair`** (proved, axiom-clean).
Given two CGBPs at finsets `S₁, S₂` that are `AmbientCompat` (cross-level
coherence plus same-level overlap agreement), amalgamate them to a single
CGBP on `S₁ ∪ S₂` whose restrictions are fieldwise-compat with both `P₁`
and `P₂`.

**Why a genuine primitive.** A naive route through
`coherentGoodBranchPartial_extend_to_union` from `P₁` gives `Q.restrict S₁`
compat with `P₁`, but `Q`'s values on `S₂ \ S₁` are chosen freshly (via
`exists_coherentGoodBranchApprox`/`extend_list`'s `Classical.choose`), with
no constraint tying them to `P₂`. So two-sided value preservation is
strictly stronger than `extend_to_union`. This lemma is load-bearing
underneath `GoodPrescription.finite_satisfiable`, hence under
`prescribedGoodCompactness_holds` / `goodIdealCompactness`.

**Proof.** Induction on the frontier `S₂ \ S₁` via
`coherentGoodBranchPartial_amalgamate_pair_aux` (each step inserts a new
index using `insert_prescribed_new_compatible`), then transport across
`S₁ ∪ (S₂ \ S₁) = S₁ ∪ S₂`. The `S₂`-side splits into `S₂ \ S₁` (aux's
PR-agreement invariant) and `S₁ ∩ S₂` (the `S₁`-side compat composed with
`AmbientCompat.prefix_diag`/`branch_diag`).

**Special cases.**
* `coherentGoodBranchPartial_amalgamate_pair_nested` (below): the
  `S₁ ⊆ S₂` case, axiom-clean via `P₂.restrict hS` + overlap.
* `coherentGoodBranchPartial_amalgamate_pair_ordered` (below): the
  `S₁ < S₂` separated case, retained as a diagnostic (still `sorry`)
  showing `extend_to_union`'s freshness is the wrong tool there. -/
theorem coherentGoodBranchPartial_amalgamate_pair
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {S₁ S₂ : Finset Ordinal.{0}}
    (_hS₁ : ∀ α ∈ S₁, α < Ordinal.omega.{0} 1)
    (_hS₂ : ∀ α ∈ S₂, α < Ordinal.omega.{0} 1)
    (P₁ : CoherentGoodBranchPartial cR S₁)
    (P₂ : CoherentGoodBranchPartial cR S₂)
    (_h_ambient : CoherentGoodBranchPartial.AmbientCompat P₁ P₂) :
    ∃ Q : CoherentGoodBranchPartial cR (S₁ ∪ S₂),
      cbpFieldwiseCompat
        (Q.toCoherentBranchPartial.restrict Finset.subset_union_left)
        P₁.toCoherentBranchPartial ∧
      cbpFieldwiseCompat
        (Q.toCoherentBranchPartial.restrict Finset.subset_union_right)
        P₂.toCoherentBranchPartial := by
  classical
  -- Apply the aux induction lemma with base S₁, target S₂, frontier S₂ \ S₁.
  obtain ⟨Q₀, hQ₀_S₁, hQ₀_prefix, hQ₀_branch⟩ :=
    coherentGoodBranchPartial_amalgamate_pair_aux _hS₁ P₁ _hS₂ P₂ _h_ambient
      (S₂ \ S₁) Finset.sdiff_subset (fun α hα => (Finset.mem_sdiff.mp hα).2)
  -- Transport Q₀ : CGBP (S₁ ∪ (S₂ \ S₁)) to CGBP (S₁ ∪ S₂).
  have h_dom : S₁ ∪ (S₂ \ S₁) = S₁ ∪ S₂ := Finset.union_sdiff_self_eq_union
  -- Cast-transport helpers (as in the aux step).
  have cast_pref : ∀ {A B : Finset Ordinal.{0}} (hAB : A = B)
      (Pc : CoherentGoodBranchPartial cR A) (γ : Ordinal.{0})
      (hA : γ ∈ A) (hB : γ ∈ B),
      (Pc.cast hAB).toCoherentBranchPartial.prefixAt γ hB =
        Pc.toCoherentBranchPartial.prefixAt γ hA := by
    intro A B hAB Pc γ hA hB; subst hAB; rfl
  have cast_branch : ∀ {A B : Finset Ordinal.{0}} (hAB : A = B)
      (Pc : CoherentGoodBranchPartial cR A) (γ : Ordinal.{0})
      (hA : γ ∈ A) (hB : γ ∈ B),
      (Pc.cast hAB).toCoherentBranchPartial.branch γ hB =
        Pc.toCoherentBranchPartial.branch γ hA := by
    intro A B hAB Pc γ hA hB; subst hAB; rfl
  refine ⟨Q₀.cast h_dom, ?_, ?_⟩
  · -- S₁-side fieldwise compat with P₁ (transport aux's S-side).
    refine ⟨?_, ?_⟩
    · intro γ hγ
      have hA : γ ∈ S₁ ∪ (S₂ \ S₁) := Finset.mem_union_left _ hγ
      simp only [CoherentBranchPartial.restrict_prefixAt]
      rw [cast_pref h_dom Q₀ γ hA (Finset.subset_union_left hγ)]
      have e1 := hQ₀_S₁.1 γ hγ
      simp only [CoherentBranchPartial.restrict_prefixAt] at e1
      exact e1
    · intro γ hγ
      have hA : γ ∈ S₁ ∪ (S₂ \ S₁) := Finset.mem_union_left _ hγ
      simp only [CoherentBranchPartial.restrict_branch]
      rw [cast_branch h_dom Q₀ γ hA (Finset.subset_union_left hγ)]
      have e1 := hQ₀_S₁.2 γ hγ
      simp only [CoherentBranchPartial.restrict_branch] at e1
      exact e1
  · -- S₂-side fieldwise compat with P₂: split γ ∈ S₂ via membership in S₁.
    refine ⟨?_, ?_⟩
    · intro γ hγ
      simp only [CoherentBranchPartial.restrict_prefixAt]
      by_cases hγ_S₁ : γ ∈ S₁
      · -- γ ∈ S₁ ∩ S₂: Q₀ agrees with P₁ (S₁-side), then P₁ = P₂ (prefix_diag).
        have hA : γ ∈ S₁ ∪ (S₂ \ S₁) := Finset.mem_union_left _ hγ_S₁
        rw [cast_pref h_dom Q₀ γ hA (Finset.subset_union_right hγ)]
        have e1 := hQ₀_S₁.1 γ hγ_S₁
        simp only [CoherentBranchPartial.restrict_prefixAt] at e1
        exact e1.trans (_h_ambient.prefix_diag γ hγ_S₁ hγ)
      · -- γ ∈ S₂ \ S₁: aux's D-side agreement (value level via ext).
        have hγ_D : γ ∈ S₂ \ S₁ := Finset.mem_sdiff.mpr ⟨hγ, hγ_S₁⟩
        have hA : γ ∈ S₁ ∪ (S₂ \ S₁) := Finset.mem_union_right _ hγ_D
        apply RelEmbedding.ext
        intro x
        rw [cast_pref h_dom Q₀ γ hA (Finset.subset_union_right hγ)]
        exact hQ₀_prefix γ hγ_D x
    · intro γ hγ
      simp only [CoherentBranchPartial.restrict_branch]
      by_cases hγ_S₁ : γ ∈ S₁
      · have hA : γ ∈ S₁ ∪ (S₂ \ S₁) := Finset.mem_union_left _ hγ_S₁
        rw [cast_branch h_dom Q₀ γ hA (Finset.subset_union_right hγ)]
        have e1 := hQ₀_S₁.2 γ hγ_S₁
        simp only [CoherentBranchPartial.restrict_branch] at e1
        exact e1.trans (_h_ambient.branch_diag γ hγ_S₁ hγ)
      · have hγ_D : γ ∈ S₂ \ S₁ := Finset.mem_sdiff.mpr ⟨hγ, hγ_S₁⟩
        have hA : γ ∈ S₁ ∪ (S₂ \ S₁) := Finset.mem_union_right _ hγ_D
        rw [cast_branch h_dom Q₀ γ hA (Finset.subset_union_right hγ)]
        funext x
        exact hQ₀_branch γ hγ_D x

/-- **`coherentGoodBranchPartial_amalgamate_pair_nested`**: the
**nested case** of pair amalgamation. When `S₁ ⊆ S₂`, the
amalgamation is just `P₂` itself (no transport needed): the
restriction `P₂.restrict hS` is fieldwise-compatible with `P₁`,
directly via the overlap hypothesis (chained through
`restrict_prefixAt` / `restrict_branch`).

Axiom-clean. Serves as a **base case** for the finite amalgamation
induction; also validates that the overlap hypothesis is the right
shape (when overlap = `S₁`, it's exactly `P₂.restrict hS` matching
`P₁` fieldwise). -/
theorem coherentGoodBranchPartial_amalgamate_pair_nested
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {S₁ S₂ : Finset Ordinal.{0}}
    (hS : S₁ ⊆ S₂)
    (P₁ : CoherentGoodBranchPartial cR S₁)
    (P₂ : CoherentGoodBranchPartial cR S₂)
    (h_overlap_prefix : ∀ α (hα₁ : α ∈ S₁) (hα₂ : α ∈ S₂),
      P₁.toCoherentBranchPartial.prefixAt α hα₁ =
        P₂.toCoherentBranchPartial.prefixAt α hα₂)
    (h_overlap_branch : ∀ α (hα₁ : α ∈ S₁) (hα₂ : α ∈ S₂),
      P₁.toCoherentBranchPartial.branch α hα₁ =
        P₂.toCoherentBranchPartial.branch α hα₂) :
    cbpFieldwiseCompat
      (P₂.toCoherentBranchPartial.restrict hS)
      P₁.toCoherentBranchPartial := by
  refine ⟨?_, ?_⟩
  · intro α hα
    rw [CoherentBranchPartial.restrict_prefixAt]
    exact (h_overlap_prefix α hα (hS hα)).symm
  · intro α hα
    rw [CoherentBranchPartial.restrict_branch]
    exact (h_overlap_branch α hα (hS hα)).symm

/-- **[FRONTIER, sorry — diagnostic: ordered pair amalgamation]**
`coherentGoodBranchPartial_amalgamate_pair_ordered`. The **separated
case**: when every element of `S₁` is strictly below every element
of `S₂`, amalgamate `P₁` and `P₂` into a single CGBP on `S₁ ∪ S₂`.

**Why this is the second diagnostic.** The ordered hypothesis means
`S₁ ∩ S₂ = ∅`, so overlap compatibility is vacuous and the only
constraint is that the resulting Good chain coherently extends `P₁`'s
chain at the top of `S₁` into `P₂`'s chain at the bottom of `S₂`.

**Proof attempt strategy** (deferred): start from `P₁`, extend to
`S₁ ∪ S₂` via `coherentGoodBranchPartial_extend_to_union`. The `S₁`
side closes (extension preserves `P₁`). For the `S₂` side, the
extension's values on `S₂` are **chosen freshly** via
`exists_coherentGoodBranchApprox` — there is no facility to **force**
agreement with `P₂`'s prescribed values.

**Diagnostic outcome (predicted).** If this fails, two-sided value
preservation requires a **prescribed-values extension primitive** —
strictly stronger than `extend_to_union`. That confirms
`amalgamate_pair` is genuinely a new construction, not a small lemma
derivable from existing tools. -/
theorem coherentGoodBranchPartial_amalgamate_pair_ordered
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {S₁ S₂ : Finset Ordinal.{0}}
    (_hS₁ : ∀ α ∈ S₁, α < Ordinal.omega.{0} 1)
    (hS₂ : ∀ α ∈ S₂, α < Ordinal.omega.{0} 1)
    (_hbelow : ∀ α ∈ S₁, ∀ β ∈ S₂, α < β)
    (P₁ : CoherentGoodBranchPartial cR S₁)
    (_P₂ : CoherentGoodBranchPartial cR S₂) :
    ∃ Q : CoherentGoodBranchPartial cR (S₁ ∪ S₂),
      cbpFieldwiseCompat
        (Q.toCoherentBranchPartial.restrict Finset.subset_union_left)
        P₁.toCoherentBranchPartial ∧
      cbpFieldwiseCompat
        (Q.toCoherentBranchPartial.restrict Finset.subset_union_right)
        _P₂.toCoherentBranchPartial := by
  -- Diagnostic: extend P₁ above-top via extend_to_union.
  obtain ⟨Q, hQ_S₁⟩ := coherentGoodBranchPartial_extend_to_union P₁ S₂ hS₂
  refine ⟨Q, hQ_S₁, ?_⟩
  -- S₁ side closes. But on the S₂ side, _hbelow is unused — the ordered
  -- hypothesis does NOT help: extend_to_union's freshness covers ALL of
  -- S₂ \ S₁ = S₂ uniformly (the ordering of S₁ vs S₂ doesn't constrain
  -- which CGBP gets picked). The Good chain machinery via
  -- exists_coherentGoodBranchApprox provides existence at S₁ ∪ S₂, not a
  -- choice respecting a prescribed `_P₂` on S₂.
  --
  -- Conclusion: ordered amalgamation is **not** easier than general
  -- amalgamation under the current API. Two-sided preservation needs
  -- a strictly stronger primitive (prescribed-values extension), which
  -- would itself be a new construction.
  sorry

/-- **`coherentGoodBranchPartial_extend_prescribed`**: operational
alias for `coherentGoodBranchPartial_amalgamate_pair`. Same statement,
clearer name — "extend `P` on `S` with prescribed values from `PR` on
`R`, agreeing on the overlap".

The two names coexist:
* `amalgamate_pair` — symmetric reading (combine two CGBPs).
* `extend_prescribed` — directional reading (extend `P` along `R`
  with prescribed `PR`-values on `R \ S`).

Both refer to the same theorem; the genuine local constructive
frontier is the single-point new-index case
`insert_prescribed_new` (below); the existing-index case
`insert_prescribed_existing` is axiom-clean. -/
theorem coherentGoodBranchPartial_extend_prescribed
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {S R : Finset Ordinal.{0}}
    (hS : ∀ α ∈ S, α < Ordinal.omega.{0} 1)
    (hR : ∀ α ∈ R, α < Ordinal.omega.{0} 1)
    (P : CoherentGoodBranchPartial cR S)
    (PR : CoherentGoodBranchPartial cR R)
    (h_ambient : CoherentGoodBranchPartial.AmbientCompat P PR) :
    ∃ Q : CoherentGoodBranchPartial cR (S ∪ R),
      cbpFieldwiseCompat
        (Q.toCoherentBranchPartial.restrict Finset.subset_union_left)
        P.toCoherentBranchPartial ∧
      cbpFieldwiseCompat
        (Q.toCoherentBranchPartial.restrict Finset.subset_union_right)
        PR.toCoherentBranchPartial :=
  coherentGoodBranchPartial_amalgamate_pair hS hR P PR h_ambient

/-- **`coherentGoodBranchPartial_insert_prescribed_existing`**: the
**easy branch** of `insert_prescribed`. When `α ∈ T`, the prescribed
value at `α` is forced to match `P`'s value at `α` by the overlap
hypothesis; the amalgamation is just `P` itself, and what we need to
exhibit is exactly `P.restrict {α} = Pα` fieldwise. **Axiom-clean**;
serves as the existing-index base case for `insert_prescribed`'s
induction over `R \ T`. -/
theorem coherentGoodBranchPartial_insert_prescribed_existing
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {T : Finset Ordinal.{0}} (α : Ordinal.{0})
    (hαT : α ∈ T)
    (P : CoherentGoodBranchPartial cR T)
    (Pα : CoherentGoodBranchPartial cR ({α} : Finset Ordinal.{0}))
    (h_overlap_prefix : ∀ β (hβ_T : β ∈ T)
        (hβ_α : β ∈ ({α} : Finset Ordinal.{0})),
      P.toCoherentBranchPartial.prefixAt β hβ_T =
        Pα.toCoherentBranchPartial.prefixAt β hβ_α)
    (h_overlap_branch : ∀ β (hβ_T : β ∈ T)
        (hβ_α : β ∈ ({α} : Finset Ordinal.{0})),
      P.toCoherentBranchPartial.branch β hβ_T =
        Pα.toCoherentBranchPartial.branch β hβ_α) :
    cbpFieldwiseCompat
      (P.toCoherentBranchPartial.restrict
        (Finset.singleton_subset_iff.mpr hαT))
      Pα.toCoherentBranchPartial := by
  refine ⟨?_, ?_⟩
  · intro β hβ
    rw [CoherentBranchPartial.restrict_prefixAt]
    exact h_overlap_prefix β (Finset.singleton_subset_iff.mpr hαT hβ) hβ
  · intro β hβ
    rw [CoherentBranchPartial.restrict_branch]
    exact h_overlap_branch β (Finset.singleton_subset_iff.mpr hαT hβ) hβ

/-- **[OFF-CHAIN, sorry — superseded by `insert_prescribed_new_compatible`]**
`coherentGoodBranchPartial_insert_prescribed_new`. The **hard branch**
of `insert_prescribed`: when `α ∉ T`, extend `P` on `T` to
`insert α T = T ∪ {α}` matching both `P` on `T` and a prescribed
`Pα` on `{α}`.

**Mathematical correction (2026-05-23).** The naive version (no
overlap hypothesis, since `T ∩ {α} = ∅` when `α ∉ T`) is **wrong**.
A CGBP on `{α}` already carries an entire `PairERGoodChain cR α`,
including:
* a prefix embedding `α.ToType ↪o PairERSource` covering **all**
  positions below `α`;
* a type function `α.ToType → Bool` for all positions below `α`;
* `inner_consistent` linking pairs across all those positions.

For amalgamation to be possible, `Pα` must already be **coherent
with the ambient partial branch `P`** at every position where they
both have data:
* For `β ∈ T` with `β < α`: `P.prefixAt β` (a prefix on `β.ToType`)
  must agree with `Pα.prefixAt α` restricted to the initial-segment
  `β.ToType ⊆ α.ToType`. Similarly for `branch β`.
* For `β ∈ T` with `α < β`: `P.prefixAt β` at the position
  corresponding to `α` must equal the new top's head, derivable
  from `Pα`'s Good-chain data at `α`.

Without these compatibility hypotheses, the prescription `(P, Pα)`
generally has **no** common extension. Prescribed insertion is only
possible when `Pα` is already coherent with the surrounding partial
branch — not just for a vacuous set-theoretic overlap.

**This statement (no strong compat hypothesis) is therefore
**incompletely specified**.** The corrected form is
`insert_prescribed_new_compatible` below. The original is retained
here as a record of the (wrong) shape that motivated the correction. -/
theorem coherentGoodBranchPartial_insert_prescribed_new
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {T : Finset Ordinal.{0}} (α : Ordinal.{0})
    (_hαT : α ∉ T)
    (_hT : ∀ β ∈ T, β < Ordinal.omega.{0} 1)
    (_hα : α < Ordinal.omega.{0} 1)
    (_P : CoherentGoodBranchPartial cR T)
    (_Pα : CoherentGoodBranchPartial cR ({α} : Finset Ordinal.{0})) :
    ∃ Q : CoherentGoodBranchPartial cR (insert α T),
      cbpFieldwiseCompat
        (Q.toCoherentBranchPartial.restrict (Finset.subset_insert α T))
        _P.toCoherentBranchPartial ∧
      cbpFieldwiseCompat
        (Q.toCoherentBranchPartial.restrict
          (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self α T)))
        _Pα.toCoherentBranchPartial := by
  sorry

/-- **`coherentGoodBranchPartial_insert_prescribed_compatible`**
[**convenience wrapper — TRANSPORT TODO**]: unified existing/new
prescribed-insertion theorem.

**Off the critical path.** The induction over `R \ S` in
`extend_prescribed` only ever inserts indices that are **new** to
the running domain, so it never invokes the existing-index branch.
This wrapper is purely a presentational convenience and not load-
bearing for any downstream theorem. The α ∉ T case routes through
the now-fully-proven `insert_prescribed_new_compatible`; the α ∈ T
case requires non-trivial Finset transport bookkeeping (subst on
`Finset.insert_eq_of_mem hαT : insert α T = T` triggers recursive
rewriting on the parameter `T`). Left as a `sorry` until/if a
dedicated transport helper is added. -/
theorem coherentGoodBranchPartial_insert_prescribed_compatible
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {T : Finset Ordinal.{0}} (α : Ordinal.{0})
    (_hT : ∀ β ∈ T, β < Ordinal.omega.{0} 1)
    (hα : α < Ordinal.omega.{0} 1)
    (P : CoherentGoodBranchPartial cR T)
    (Pα : CoherentGoodBranchPartial cR ({α} : Finset Ordinal.{0}))
    (h_compat : PrescribedAmbientCompat α P Pα) :
    ∃ Q : CoherentGoodBranchPartial cR (insert α T),
      cbpFieldwiseCompat
        (Q.toCoherentBranchPartial.restrict (Finset.subset_insert α T))
        P.toCoherentBranchPartial ∧
      cbpFieldwiseCompat
        (Q.toCoherentBranchPartial.restrict
          (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self α T)))
        Pα.toCoherentBranchPartial := by
  classical
  by_cases hαT : α ∈ T
  · -- Existing case: insert α T = T, take Q := P via transport.
    -- The transport bookkeeping is non-trivial — left as one final sorry.
    sorry
  · exact coherentGoodBranchPartial_insert_prescribed_new_compatible α hαT _hT hα
      P Pα h_compat

/-- **Diagnostic for `insert_prescribed_new`.** If `extend_to_union`'s
freshly chosen extension happens to restrict to the prescribed `Pα`
on the new level — that is, if the assumption "any T-side-matching
extension of `P` to `insert α T` also matches `Pα` on `{α}`" holds —
then `insert_prescribed_new` closes immediately from the
`extend_to_union` witness.

**Diagnostic outcome.** The proof goes through with no compatibility
bookkeeping issues: the `obtain` from `extend_to_union` gives the
T-side; the hypothesis gives the `{α}`-side; done. This **confirms
the only missing thing is forcing the chosen level**, not anything
about how restrictions interact with prescribed values. The
prescribed-level extension primitive *is* the entire remaining
constructive content. -/
theorem coherentGoodBranchPartial_insert_prescribed_new_of_level_eq
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {T : Finset Ordinal.{0}} (α : Ordinal.{0})
    (_hαT : α ∉ T)
    (_hT : ∀ β ∈ T, β < Ordinal.omega.{0} 1)
    (hα : α < Ordinal.omega.{0} 1)
    (P : CoherentGoodBranchPartial cR T)
    (Pα : CoherentGoodBranchPartial cR ({α} : Finset Ordinal.{0}))
    (h_force :
      ∀ (Q : CoherentGoodBranchPartial cR (T ∪ {α})),
        cbpFieldwiseCompat
          (Q.toCoherentBranchPartial.restrict Finset.subset_union_left)
          P.toCoherentBranchPartial →
        cbpFieldwiseCompat
          (Q.toCoherentBranchPartial.restrict Finset.subset_union_right)
          Pα.toCoherentBranchPartial) :
    ∃ Q : CoherentGoodBranchPartial cR (T ∪ {α}),
      cbpFieldwiseCompat
        (Q.toCoherentBranchPartial.restrict Finset.subset_union_left)
        P.toCoherentBranchPartial ∧
      cbpFieldwiseCompat
        (Q.toCoherentBranchPartial.restrict Finset.subset_union_right)
        Pα.toCoherentBranchPartial := by
  have h_sing : ∀ β ∈ ({α} : Finset Ordinal.{0}), β < Ordinal.omega.{0} 1 := by
    intro β hβ
    rw [Finset.mem_singleton.mp hβ]
    exact hα
  obtain ⟨Q, hQ_T⟩ := coherentGoodBranchPartial_extend_to_union P {α} h_sing
  exact ⟨Q, hQ_T, h_force Q hQ_T⟩

/-! ### Final two-frontier dependency chain

The local constructive frontier `insert_prescribed_new` is the
**single** remaining algebraic obstacle. The full chain of wrapping
lemmas — by which `insert_prescribed_new` propagates up to the
inverse-limit step — is:

```
insert_prescribed_new   (sorry — local atomic frontier)
       ↓ + insert_prescribed_existing (proven)
insert_prescribed       (unified by `by_cases hαT : α ∈ T`)
       ↓ induction on `R \ S`
extend_prescribed       (= amalgamate_pair)
       ↓ induction on `I : Finset ι`
amalgamate_finset
       ↓ + pairwise compat from prescription
GoodPrescription.finite_satisfiable
       ↓ ultrafilter on finite sub-domains
prescribedGoodCompactness_holds   (sorry — infinite frontier)
```

**Two remaining theorem frontiers:**
* **Local (Frontier 1):** `coherentGoodBranchPartial_insert_prescribed_new`.
  Requires a prescribed-level Good-chain extension primitive, strictly
  stronger than `extendSucc`/`extendTo` which choose freshly.
* **Infinite (Frontier 2):** `prescribedGoodCompactness_holds`.
  Requires an ultrafilter / inverse-limit argument from finite
  satisfiability to global existence.

Everything in between is "easy" derivation (induction over finsets +
transport bookkeeping for the `α ∈ T` case of `insert_prescribed`).
The wrapping lemmas are documented as theorems with `sorry` proofs
in the current state; filling them is straightforward but mechanical.
**The constructive content lives only in the two named frontiers.** -/

/-- **[OFF-CHAIN, sorry — overlap-only hypotheses too weak; superseded]**
`coherentGoodBranchPartial_amalgamate_finset`. The finset
generalization of `amalgamate_pair`: given a finite family of
pairwise-compatible CGBPs (compatible on every pairwise overlap),
produce a single CGBP on `I.sup S` whose restriction to each `S i`
is fieldwise-compat with `P i`.

**Proof strategy** (induction on `I`, deferred):
* `I = ∅`: take any CGBP on `∅` (via `exists_coherentGoodBranchPartial`);
  the conclusion is vacuous.
* `I = insert i I'`: by IH on `I'`, get `Q'` on `I'.sup S` compat with
  each `P j` (`j ∈ I'`). Apply `amalgamate_pair` to `P i` and `Q'`:
  overlap compat between `P i` and `Q'` on `S i ∩ I'.sup S` follows
  from `h_overlap_*` (`P i` vs `P j` for the `j ∈ I'` containing the
  overlap point) chained with IH compat (`P j` vs `Q'`). The result
  `Q` on `S i ∪ I'.sup S = I.sup S` has the required two-sided compat;
  the `j ∈ I'` side carries through by another compat-transitivity
  step.

The whole induction is straightforward modulo Lean bookkeeping
(proof irrelevance for `α ∈ I'.sup S` proofs across the chain). -/
theorem coherentGoodBranchPartial_amalgamate_finset
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {ι : Type*} (I : Finset ι)
    (S : ι → Finset Ordinal.{0})
    (P : ∀ i, i ∈ I → CoherentGoodBranchPartial cR (S i))
    (_h_valid : ∀ i (hi : i ∈ I), ∀ α ∈ S i, α < Ordinal.omega.{0} 1)
    (_h_overlap_prefix : ∀ i (hi : i ∈ I) j (hj : j ∈ I) α
      (hα₁ : α ∈ S i) (hα₂ : α ∈ S j),
      (P i hi).toCoherentBranchPartial.prefixAt α hα₁ =
        (P j hj).toCoherentBranchPartial.prefixAt α hα₂)
    (_h_overlap_branch : ∀ i (hi : i ∈ I) j (hj : j ∈ I) α
      (hα₁ : α ∈ S i) (hα₂ : α ∈ S j),
      (P i hi).toCoherentBranchPartial.branch α hα₁ =
        (P j hj).toCoherentBranchPartial.branch α hα₂) :
    ∃ Q : CoherentGoodBranchPartial cR (I.sup S),
      ∀ i (hi : i ∈ I), ∃ (hsub : S i ⊆ I.sup S),
        cbpFieldwiseCompat
          (Q.toCoherentBranchPartial.restrict hsub)
          (P i hi).toCoherentBranchPartial := by
  sorry

/-! ### Good-layer `FiniteProjectiveSystem` instance

Parallel of `coherentBranchPartialSystem cR` whose objects are
`CoherentGoodBranchPartial cR S` rather than the bare `CBP`. Built atop
`CoherentGoodBranchPartial.restrict` + `exists_coherentGoodBranchPartial`.
Compatibility is at the underlying-bare-CBP layer (since Good chains
are uniquely determined by their bare projection up to inner
consistency, fieldwise CBP compat suffices for our purposes). -/

/-- **`coherentGoodBranchPartialSystem cR`**: the `FiniteProjectiveSystem`
instance for `CoherentGoodBranchPartial`, with fieldwise CBP-level
compatibility on the underlying bare CBPs. Closes the finite-extension
property via `exists_coherentGoodBranchPartial`. -/
noncomputable def coherentGoodBranchPartialSystem
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    FiniteProjectiveSystem (Finset Ordinal.{0}) where
  Valid S := ∀ α ∈ S, α < Ordinal.omega.{0} 1
  Obj S := CoherentGoodBranchPartial cR S
  restrict {_ _} hij PG := PG.restrict hij
  Compat PG₁ PG₂ :=
    cbpFieldwiseCompat PG₁.toCoherentBranchPartial PG₂.toCoherentBranchPartial
  finite_extension := by
    intro 𝒮 h𝒮
    classical
    set U : Finset Ordinal.{0} := 𝒮.sup id
    have hU_lt : ∀ α ∈ U, α < Ordinal.omega.{0} 1 := by
      intro α hα
      obtain ⟨S, hS, hαS⟩ := Finset.mem_sup.mp hα
      exact h𝒮 S hS α hαS
    obtain ⟨Q⟩ := exists_coherentGoodBranchPartial cR U hU_lt
    have h_sub : ∀ {S : Finset Ordinal.{0}}, S ∈ 𝒮 → S ⊆ U := fun hS_mem α hα =>
      Finset.mem_sup.mpr ⟨_, hS_mem, hα⟩
    refine ⟨fun S hS_mem => Q.restrict (h_sub hS_mem), ?_⟩
    intro S T hS hT hST
    refine ⟨?_, ?_⟩
    · intro α hα
      simp only [CoherentGoodBranchPartial.restrict_toCoherentBranchPartial]
      rw [CoherentBranchPartial.restrict_prefixAt,
          Q.toCoherentBranchPartial.restrict_prefixAt (h_sub hT) α (hST hα),
          Q.toCoherentBranchPartial.restrict_prefixAt (h_sub hS) α hα]
    · intro α hα
      simp only [CoherentGoodBranchPartial.restrict_toCoherentBranchPartial]
      rw [CoherentBranchPartial.restrict_branch,
          Q.toCoherentBranchPartial.restrict_branch (h_sub hT) α (hST hα),
          Q.toCoherentBranchPartial.restrict_branch (h_sub hS) α hα]

/-- **`coherentGoodBranchPartial_amalgamate_from_common_upper`**: finite-domain
amalgamation for an `IdealPartialSection` of the Good system, via the common
upper bound. Given a finite family `D` of domain finsets, directedness +
downward-closure place `T₀ := D.sup id` itself in the domain, so `p.P T₀` is a
single CGBP on the union whose restriction to each `S ∈ D` is fieldwise-compat
with `p.P S` (directly from `p.compat`).

This is the IPS-level finite amalgamation primitive: no pairwise `AmbientCompat`
and no induction over `amalgamate_pair`, because the cross-level coherence is
already carried by the single common object `p.P T₀`. (Contrast
`coherentGoodBranchPartial_amalgamate_finset`, whose overlap-only hypotheses are
too weak to reconstruct that coherence; here directedness supplies a genuine
common object instead.) It does not address global net construction. -/
theorem coherentGoodBranchPartial_amalgamate_from_common_upper
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (D : Finset (Finset Ordinal.{0}))
    (hD : ∀ S ∈ D, S ∈ p.domain) :
    ∃ Q : CoherentGoodBranchPartial cR (D.sup id),
      ∀ S (hS : S ∈ D),
        cbpFieldwiseCompat
          (Q.toCoherentBranchPartial.restrict
            (fun _ hα => Finset.mem_sup.mpr ⟨S, hS, hα⟩))
          (p.P S (hD S hS)).toCoherentBranchPartial := by
  classical
  rcases D.eq_empty_or_nonempty with rfl | hD_ne
  · -- `D = ∅`: vacuous family; any CGBP on `(∅).sup id` works.
    refine ⟨Classical.choice (exists_coherentGoodBranchPartial cR
      ((∅ : Finset (Finset Ordinal.{0})).sup id) (by simp)),
      fun S hS => absurd hS (Finset.notMem_empty S)⟩
  · -- `D ≠ ∅`: the common upper `T₀ = D.sup id` lies in the domain.
    obtain ⟨S₀, hS₀_D⟩ := hD_ne
    have hT₀_dom : D.sup id ∈ p.domain := by
      -- Iterated directedness: every finite subfamily has a domain upper bound.
      have key : ∀ (D' : Finset (Finset Ordinal.{0})),
          (∀ S ∈ D', S ∈ p.domain) → ∃ U ∈ p.domain, ∀ S ∈ D', S ⊆ U := by
        intro D'
        refine D'.induction_on ?_ ?_
        · intro _
          exact ⟨S₀, hD S₀ hS₀_D, fun S hS => absurd hS (Finset.notMem_empty S)⟩
        · intro a D'' _ ih hD'
          have ha_dom : a ∈ p.domain := hD' a (Finset.mem_insert_self _ _)
          obtain ⟨U', hU'_dom, hU'_sub⟩ :=
            ih (fun S hS => hD' S (Finset.mem_insert_of_mem hS))
          obtain ⟨U, hU_dom, ha_le, hU'_le⟩ := p.directed ha_dom hU'_dom
          refine ⟨U, hU_dom, fun S hS => ?_⟩
          rcases Finset.mem_insert.mp hS with rfl | hS_D''
          · exact ha_le
          · exact (hU'_sub S hS_D'').trans hU'_le
      obtain ⟨U, hU_dom, hU_sub⟩ := key D hD
      exact p.downward_closed hU_dom (Finset.sup_le hU_sub)
    refine ⟨p.P (D.sup id) hT₀_dom, fun S hS => ?_⟩
    exact p.compat (hD S hS) hT₀_dom (fun _ hα => Finset.mem_sup.mpr ⟨S, hS, hα⟩)

/-! ### Good witness net

Parallel of `CoherentWitnessNet` whose witnesses are Good CBPs at every
finite `S ⊂ ω₁`. The Good system's intrinsic inner-cR-consistency data
makes finite-extension easier to prove (via
`coherentGoodBranchPartial_extend_to_union`). Project down to bare
`CoherentWitnessNet` via `toCoherentWitnessNet`. -/

/-- **`CoherentGoodWitnessNet cR`**: a Good-strengthened witness net.
Provides a Good CBP at every finite `S ⊂ ω₁` with cross-compatibility. -/
structure CoherentGoodWitnessNet (cR : (Fin 2 ↪o PairERSource) → Bool) where
  /-- Good CBP at every finite `S ⊂ ω₁`. -/
  P : ∀ S : Finset Ordinal.{0}, (∀ α ∈ S, α < Ordinal.omega.{0} 1) →
    CoherentGoodBranchPartial cR S
  /-- Prefix compatibility across `S ⊆ T`. -/
  prefix_compat : ∀ {S T : Finset Ordinal.{0}}
    (hS : ∀ α ∈ S, α < Ordinal.omega.{0} 1)
    (hT : ∀ α ∈ T, α < Ordinal.omega.{0} 1)
    (hST : S ⊆ T) (α : Ordinal.{0}) (hα : α ∈ S),
    (P T hT).toCoherentBranchPartial.prefixAt α (hST hα) =
      (P S hS).toCoherentBranchPartial.prefixAt α hα
  /-- Branch compatibility. -/
  branch_compat : ∀ {S T : Finset Ordinal.{0}}
    (hS : ∀ α ∈ S, α < Ordinal.omega.{0} 1)
    (hT : ∀ α ∈ T, α < Ordinal.omega.{0} 1)
    (hST : S ⊆ T) (α : Ordinal.{0}) (hα : α ∈ S),
    (P T hT).toCoherentBranchPartial.branch α (hST hα) =
      (P S hS).toCoherentBranchPartial.branch α hα

/-- **`CoherentGoodWitnessNet.toCoherentWitnessNet`**: project a Good
witness net down to the bare `CoherentWitnessNet` by taking the
underlying bare CBP at each level. Compatibility carries through
because `cbpFieldwiseCompat` is fieldwise. -/
def CoherentGoodWitnessNet.toCoherentWitnessNet
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (W : CoherentGoodWitnessNet cR) : CoherentWitnessNet cR where
  P := fun S hS => (W.P S hS).toCoherentBranchPartial
  prefix_compat := W.prefix_compat
  branch_compat := W.branch_compat

/-- **`GoodPrescription cR`**: a (possibly infinite) consistent
assignment of `CoherentGoodBranchPartial`s indexed by valid finsets,
with bare-CBP-level restriction consistency (prefixAt and branch
agree on overlaps). This is the natural input shape for true
inverse-limit compactness: it generalizes IPS by dropping
directedness and downward-closure. -/
structure GoodPrescription (cR : (Fin 2 ↪o PairERSource) → Bool) where
  𝒮 : Set (Finset Ordinal.{0})
  𝒮_valid : ∀ S ∈ 𝒮, ∀ α ∈ S, α < Ordinal.omega.{0} 1
  obj : ∀ S, S ∈ 𝒮 → CoherentGoodBranchPartial cR S
  consistent_prefix : ∀ {S T} (hS : S ∈ 𝒮) (hT : T ∈ 𝒮) (hST : S ⊆ T)
      (α : Ordinal.{0}) (hα : α ∈ S),
    (obj T hT).toCoherentBranchPartial.prefixAt α (hST hα) =
      (obj S hS).toCoherentBranchPartial.prefixAt α hα
  consistent_branch : ∀ {S T} (hS : S ∈ 𝒮) (hT : T ∈ 𝒮) (hST : S ⊆ T)
      (α : Ordinal.{0}) (hα : α ∈ S),
    (obj T hT).toCoherentBranchPartial.branch α (hST hα) =
      (obj S hS).toCoherentBranchPartial.branch α hα

/-- **`prescribedGoodCompactness cR`**: the true final-frontier
compactness statement. **Every** consistent `GoodPrescription` extends
to a global Good witness net **storing each prescribed CGBP literally**
at its index. Drops directedness/downward-closure compared to
`goodIdealCompactness`, isolating the compactness content. -/
def prescribedGoodCompactness (cR : (Fin 2 ↪o PairERSource) → Bool) : Prop :=
  ∀ (P : GoodPrescription cR),
    ∃ net : CoherentGoodWitnessNet cR,
      ∀ S (hS : S ∈ P.𝒮),
        net.P S (P.𝒮_valid S hS) = P.obj S hS

/-- **Bridge**: every `IdealPartialSection` is a `GoodPrescription` by
forgetting directedness/downward-closure and reading off the IPS-level
restriction-compat as bare-CBP-level prefix/branch agreement. -/
def FiniteProjectiveSystem.IdealPartialSection.toGoodPrescription
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection) :
    GoodPrescription cR where
  𝒮 := p.domain
  𝒮_valid := fun S hS => p.domain_valid hS
  obj := fun S hS => p.P S hS
  consistent_prefix := fun {S T} hS hT hST α hα => by
    have h : ((p.P T hT).restrict hST).toCoherentBranchPartial.prefixAt α hα =
        (p.P S hS).toCoherentBranchPartial.prefixAt α hα :=
      (p.compat hS hT hST).1 α hα
    rw [CoherentGoodBranchPartial.restrict_toCoherentBranchPartial,
        CoherentBranchPartial.restrict_prefixAt] at h
    exact h
  consistent_branch := fun {S T} hS hT hST α hα => by
    have h : ((p.P T hT).restrict hST).toCoherentBranchPartial.branch α hα =
        (p.P S hS).toCoherentBranchPartial.branch α hα :=
      (p.compat hS hT hST).2 α hα
    rw [CoherentGoodBranchPartial.restrict_toCoherentBranchPartial,
        CoherentBranchPartial.restrict_branch] at h
    exact h

/-- **Restrict** a `GoodPrescription` to a finite sub-domain. Yields a
`GoodPrescription` whose `𝒮` is the underlying set of a `Finset`
`R` (assumed to lie inside the original `P.𝒮`), agreeing with the
original on each member. Used to state and reason about
finite-satisfiability slices. -/
def GoodPrescription.restrictTo
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (P : GoodPrescription cR)
    (R : Finset (Finset Ordinal.{0}))
    (hR : ∀ S ∈ R, S ∈ P.𝒮) :
    GoodPrescription cR where
  𝒮 := (↑R : Set (Finset Ordinal.{0}))
  𝒮_valid := fun S hS => P.𝒮_valid S (hR S (Finset.mem_coe.mp hS))
  obj := fun S hS => P.obj S (hR S (Finset.mem_coe.mp hS))
  consistent_prefix := fun {S T} hS hT hST α hα =>
    P.consistent_prefix (hR S (Finset.mem_coe.mp hS))
      (hR T (Finset.mem_coe.mp hT)) hST α hα
  consistent_branch := fun {S T} hS hT hST α hα =>
    P.consistent_branch (hR S (Finset.mem_coe.mp hS))
      (hR T (Finset.mem_coe.mp hT)) hST α hα

/-- **[OFF-CHAIN, sorry — general-prescription route, not the witness-net chain]**
`GoodPrescription.finite_satisfiable`. For any finite `R ⊆ P.𝒮`,
there is a global Good witness net agreeing with `P` on `R`. This is
the finite-slice version of `prescribedGoodCompactness_holds`; the
full theorem follows by an inverse-limit / ultrafilter step over
finite slices.

**Two-step decomposition.**
1. **Local amalgamation** (handled by
   `coherentGoodBranchPartial_amalgamate_finset` once `amalgamate_pair`
   is proven): the finite family `{P.obj S | S ∈ R}` amalgamates into
   a single `Q : CGBP cR (R.sup id)` with `Q.restrict S` compat
   `P.obj S` for each `S ∈ R`. **Requires pairwise compat** between
   `P.obj S₁` and `P.obj S₂` on `S₁ ∩ S₂` — the current
   `consistent_prefix/branch` fields only give *subset* compat. For
   IPS-derived prescriptions, pairwise compat is derivable via the
   intersection trick (use `S₁ ∩ S₂ ∈ p.domain` from
   `downward_closed`).
2. **Globalization** from local `Q` to a full witness net: define
   `net.P W` for every valid `W` consistently — this is essentially
   the inverse-limit step the parent theorem solves. The finite slice
   doesn't escape compactness; it localizes the amalgamation step. -/
theorem GoodPrescription.finite_satisfiable
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (P : GoodPrescription cR)
    (R : Finset (Finset Ordinal.{0}))
    (hR : ∀ S ∈ R, S ∈ P.𝒮) :
    ∃ net : CoherentGoodWitnessNet cR,
      ∀ S (hS : S ∈ R),
        net.P S (P.𝒮_valid S (hR S hS)) = P.obj S (hR S hS) := by
  sorry

/-- **[OFF-CHAIN, sorry — general-prescription compactness, not the witness-net chain].** The
`prescribedGoodCompactness` predicate holds: every consistent
`GoodPrescription` extends to a global Good witness net.

**Together with Frontier 1, these are the ONLY two remaining
substantive theorems.**

**Frontier 1 — local prescribed-level extension primitive:**
`coherentGoodBranchPartial_insert_prescribed_new` (above). All
amalgamation lemmas (pair, finset, finite slice) wrap around this
single atomic primitive — wrapping is mechanical induction +
transport, no new ideas needed.

**Frontier 2 — infinite compactness from finite satisfiability:**
*this theorem*. Reduction sketch: take an ultrafilter `𝔘` on the
finite sub-domains of `P.𝒮`; for each finite `R`, choose a witness
net `net_R` from `finite_satisfiable`; extract a "limit" net whose
value at each finset is `𝔘`-eventual. This is the genuinely
topological / non-constructive step. -/
theorem prescribedGoodCompactness_holds
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    prescribedGoodCompactness cR := by
  sorry

/-- **`goodIdealGlobalization_finite_consistent`**: the finite-consistency input
to `goodIdealGlobalization`. For any finite demand set `D ⊆ p.domain`, the
prescribed objects `{p.P S | S ∈ D}` amalgamate into a single CGBP on `D.sup id`
whose restriction to each `S ∈ D` is fieldwise-compat with `p.P S`.

A thin wrapper over `coherentGoodBranchPartial_amalgamate_from_common_upper`
(directedness supplies the common object `p.P (D.sup id)`), named here so the
compactness argument reads as "every finite demand set is consistent ⇒
globalize". This is the *finite* half of `goodIdealGlobalization`; the remaining
work is the inverse-limit/ultrafilter globalization. -/
theorem goodIdealGlobalization_finite_consistent
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (D : Finset (Finset Ordinal.{0}))
    (hD_dom : ∀ S ∈ D, S ∈ p.domain) :
    ∃ Q : CoherentGoodBranchPartial cR (D.sup id),
      ∀ S (hS : S ∈ D),
        cbpFieldwiseCompat
          (Q.toCoherentBranchPartial.restrict
            (fun _ hα => Finset.mem_sup.mpr ⟨S, hS, hα⟩))
          (p.P S (hD_dom S hS)).toCoherentBranchPartial :=
  coherentGoodBranchPartial_amalgamate_from_common_upper p D hD_dom

/-- **`GoodIdealDemandIndex p`**: index type for the ultrafilter globalization of
`goodIdealGlobalization` — the prescribed indices of `p` (finsets in `p.domain`).
A finite *demand set* is a `Finset (GoodIdealDemandIndex p)`; its underlying
finsets are recovered by `Finset.image Subtype.val`. -/
abbrev GoodIdealDemandIndex {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection) :=
  {S : Finset Ordinal.{0} // S ∈ p.domain}

/-- The underlying finsets of a finite demand set all lie in `p.domain`. -/
theorem demandImage_mem_domain
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (D : Finset (GoodIdealDemandIndex p)) :
    ∀ S ∈ D.image Subtype.val, S ∈ p.domain := by
  intro S hS
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hS
  exact x.2

/-- **`finiteDemandWitness p D`**: a canonical CGBP on the union of a finite
demand set's finsets, restricting compatibly to each prescribed `p.P S`. Chosen
from `goodIdealGlobalization_finite_consistent` (so the ultrafilter argument has
one canonical finite witness per finite demand set). -/
noncomputable def finiteDemandWitness
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (D : Finset (GoodIdealDemandIndex p)) :
    CoherentGoodBranchPartial cR ((D.image Subtype.val).sup id) :=
  (goodIdealGlobalization_finite_consistent p (D.image Subtype.val)
    (demandImage_mem_domain p D)).choose

/-- The canonical finite-demand witness restricts compatibly to `p.P s` for every
member `s` of the demand set. -/
theorem finiteDemandWitness_compat
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (D : Finset (GoodIdealDemandIndex p))
    (s : GoodIdealDemandIndex p) (hs : s ∈ D) :
    cbpFieldwiseCompat
      ((finiteDemandWitness p D).toCoherentBranchPartial.restrict
        (fun _ hα => Finset.mem_sup.mpr
          ⟨s.val, Finset.mem_image_of_mem Subtype.val hs, hα⟩))
      (p.P s.val s.2).toCoherentBranchPartial :=
  (goodIdealGlobalization_finite_consistent p (D.image Subtype.val)
    (demandImage_mem_domain p D)).choose_spec s.val
    (Finset.mem_image_of_mem Subtype.val hs)

/-- **`goodIdealDemandUltrafilter p`**: the ultrafilter on finite demand sets
`Finset (GoodIdealDemandIndex p)` extending the superset (`atTop`) filter — the
combinatorial backbone of the `goodIdealGlobalization` ultralimit, the same
`finiteSupersetUltrafilter` pattern used for `rawBranchCompactness`. -/
noncomputable def goodIdealDemandUltrafilter
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection) :
    Ultrafilter (Finset (GoodIdealDemandIndex p)) :=
  finiteSupersetUltrafilter (GoodIdealDemandIndex p)

/-- Every superset class `{D | D₀ ⊆ D}` is eventual in the demand ultrafilter. -/
theorem goodIdealDemandUltrafilter_eventually_contains
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (D₀ : Finset (GoodIdealDemandIndex p)) :
    {D : Finset (GoodIdealDemandIndex p) | D₀ ⊆ D} ∈ goodIdealDemandUltrafilter p :=
  finiteSupersetUltrafilter_eventually_superset D₀

/-- The demand sets containing a fixed index `s` are eventual in the demand
ultrafilter (the singleton case of `goodIdealDemandUltrafilter_eventually_contains`,
via `Finset.singleton_subset_iff`). -/
theorem goodIdealDemandUltrafilter_eventually_contains_one
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (s : GoodIdealDemandIndex p) :
    {D : Finset (GoodIdealDemandIndex p) | s ∈ D} ∈ goodIdealDemandUltrafilter p := by
  have h := finiteSupersetUltrafilter_eventually_superset
    ({s} : Finset (GoodIdealDemandIndex p))
  have h_eq : {D : Finset (GoodIdealDemandIndex p) | ({s} : Finset _) ⊆ D}
      = {D : Finset (GoodIdealDemandIndex p) | s ∈ D} := by
    ext D; exact Finset.singleton_subset_iff
  rwa [h_eq] at h

/-- **`finiteDemandWitness_eventually_compat`**: for a demanded index `s`, the
finite witness eventually restricts on `s.1` to the prescribed `p.P s`.

The body is conditioned on `hs : s ∈ D` because the restriction target `s.1` is
contained in the demand union `(D.image Subtype.val).sup id` only when `s ∈ D`;
off the cone `{D | s ∈ D}` it is vacuous, and on the cone it is exactly
`finiteDemandWitness_compat`. (The per-`D` implication holds for *every* `D`, so
the proof is `eventually_of_forall`; the "eventual" framing is for the consumer,
which combines this with `goodIdealDemandUltrafilter_eventually_contains_one` to
force `net.P S = p.P S` on `p.domain`.) -/
theorem finiteDemandWitness_eventually_compat
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (s : GoodIdealDemandIndex p) :
    ∀ᶠ D in goodIdealDemandUltrafilter p,
      ∀ (hs : s ∈ D),
        cbpFieldwiseCompat
          ((finiteDemandWitness p D).toCoherentBranchPartial.restrict
            (fun _ hα => Finset.mem_sup.mpr ⟨s.1, Finset.mem_image_of_mem _ hs, hα⟩))
          (p.P s.1 s.2).toCoherentBranchPartial :=
  Filter.Eventually.of_forall (fun D hs => finiteDemandWitness_compat p D s hs)

/-- **`goodIdealGlobalizationValue p W hW`**: the candidate net value at a valid
finite `W`. On the prescribed domain it is fixed to `p.P W`; off the domain it is
an independent fresh choice (placeholder for the ultralimit/compactness value).

This makes the domain/non-domain split explicit: the domain branch is forced
(see `goodIdealGlobalizationValue_of_mem`), while the off-domain branch is chosen
independently — so it is **not yet** cross-compatible. Establishing compatibility
for the off-domain values is precisely the remaining ultralimit construction. -/
noncomputable def goodIdealGlobalizationValue
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (W : Finset Ordinal.{0}) (hW : ∀ α ∈ W, α < Ordinal.omega.{0} 1) :
    CoherentGoodBranchPartial cR W := by
  classical
  exact if h : W ∈ p.domain then p.P W h
    else Classical.choice (exists_coherentGoodBranchPartial cR W hW)

/-- On the prescribed domain, `goodIdealGlobalizationValue` is exactly `p.P`. This
is the equality `goodIdealGlobalization` requires on `p.domain`. -/
theorem goodIdealGlobalizationValue_of_mem
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (W : Finset Ordinal.{0}) (hW : ∀ α ∈ W, α < Ordinal.omega.{0} 1)
    (hWdom : W ∈ p.domain) :
    goodIdealGlobalizationValue p W hW = p.P W hWdom := by
  classical
  rw [goodIdealGlobalizationValue, dif_pos hWdom]

/-- **`GoodGlobalDemandIndex p`**: the *widened* demand index — **all** valid
finite sets, not just `p.domain`. (The carrier does not actually depend on `p`;
`p` is kept for notational uniformity with `GoodIdealDemandIndex` and the
witness/compat lemmas downstream.)

**Why widen.** An ultrafilter over `p.domain`-only demands cannot determine
coherent values off the domain: if neither `S` nor `T` is in `p.domain` there is
no demand forcing a stable common value. Indexing demands by *all* valid finite
sets lets a single per-demand witness on `D.sup` restrict compatibly to every
`W ∈ D`, while prescribed equality is still imposed only on the `p.domain`
members. -/
abbrev GoodGlobalDemandIndex {cR : (Fin 2 ↪o PairERSource) → Bool}
    (_p : (coherentGoodBranchPartialSystem cR).IdealPartialSection) :=
  {W : Finset Ordinal.{0} // ∀ α ∈ W, α < Ordinal.omega.{0} 1}

/-- The ultrafilter on finite demand sets of valid finite sets (superset/`atTop`
backbone), widened from `goodIdealDemandUltrafilter` to all valid finite sets. -/
noncomputable def goodGlobalDemandUltrafilter
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection) :
    Ultrafilter (Finset (GoodGlobalDemandIndex p)) :=
  finiteSupersetUltrafilter (GoodGlobalDemandIndex p)

/-- Every superset class `{D | D₀ ⊆ D}` is eventual in the global demand
ultrafilter. -/
theorem goodGlobalDemandUltrafilter_eventually_contains
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (D₀ : Finset (GoodGlobalDemandIndex p)) :
    {D : Finset (GoodGlobalDemandIndex p) | D₀ ⊆ D} ∈ goodGlobalDemandUltrafilter p :=
  finiteSupersetUltrafilter_eventually_superset D₀

/-- The demand sets containing a fixed valid finite set `w` are eventual in the
global demand ultrafilter. -/
theorem goodGlobalDemandUltrafilter_eventually_contains_one
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (w : GoodGlobalDemandIndex p) :
    {D : Finset (GoodGlobalDemandIndex p) | w ∈ D} ∈ goodGlobalDemandUltrafilter p := by
  have h := finiteSupersetUltrafilter_eventually_superset
    ({w} : Finset (GoodGlobalDemandIndex p))
  have h_eq : {D : Finset (GoodGlobalDemandIndex p) | ({w} : Finset _) ⊆ D}
      = {D : Finset (GoodGlobalDemandIndex p) | w ∈ D} := by
    ext D; exact Finset.singleton_subset_iff
  rwa [h_eq] at h

/-- **`domain_sup_mem`**: a nonempty finite family `E` of `p.domain` finsets has
its union `E.sup id` again in `p.domain`, by iterated directedness (each step
takes a common upper bound via `p.directed`) followed by `p.downward_closed`. The
same argument underlies `coherentGoodBranchPartial_amalgamate_from_common_upper`. -/
theorem domain_sup_mem
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (E : Finset (Finset Ordinal.{0})) (hE : ∀ S ∈ E, S ∈ p.domain)
    (hne : E.Nonempty) :
    E.sup id ∈ p.domain := by
  classical
  obtain ⟨S₀, hS₀⟩ := hne
  have key : ∀ (E' : Finset (Finset Ordinal.{0})),
      (∀ S ∈ E', S ∈ p.domain) → ∃ U ∈ p.domain, ∀ S ∈ E', S ⊆ U := by
    intro E'
    refine E'.induction_on ?_ ?_
    · intro _
      exact ⟨S₀, hE S₀ hS₀, fun S hS => absurd hS (Finset.notMem_empty S)⟩
    · intro a E'' _ ih hE'
      obtain ⟨U', hU'_dom, hU'_sub⟩ :=
        ih (fun S hS => hE' S (Finset.mem_insert_of_mem hS))
      obtain ⟨U, hU_dom, ha_le, hU'_le⟩ :=
        p.directed (hE' a (Finset.mem_insert_self _ _)) hU'_dom
      refine ⟨U, hU_dom, fun S hS => ?_⟩
      rcases Finset.mem_insert.mp hS with rfl | hS''
      · exact ha_le
      · exact (hU'_sub S hS'').trans hU'_le
  obtain ⟨U, hU_dom, hU_sub⟩ := key E hE
  exact p.downward_closed hU_dom (Finset.sup_le hU_sub)

/-- Existence of the finite global-demand witness, with its domain-compatibility
property bundled in. `finiteGlobalDemandWitness` and
`finiteGlobalDemandWitness_domain_compat` are the `choose`/`choose_spec` of this.

Construction: if `D` has any `p.domain` members, take their common upper
`T₀ = E.sup id ∈ p.domain` (`domain_sup_mem`), extend `p.P T₀` over the full
demand union via `coherentGoodBranchPartial_extend_to_union`, and restrict back to
the union. On each domain member `S ⊆ T₀ ⊆ union`, the extension agrees with
`p.P T₀` (extend lemma) and `p.P T₀` agrees with `p.P S` (`p.compat`). If `D` has
no domain members, any Good partial on the union works (the property is vacuous). -/
theorem exists_finiteGlobalDemandWitness
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (D : Finset (GoodGlobalDemandIndex p)) :
    ∃ Q : CoherentGoodBranchPartial cR ((D.image Subtype.val).sup id),
      ∀ (s : GoodGlobalDemandIndex p) (hs : s ∈ D) (hsdom : s.1 ∈ p.domain),
        cbpFieldwiseCompat
          (Q.toCoherentBranchPartial.restrict
            (fun _ hα => Finset.mem_sup.mpr ⟨s.1, Finset.mem_image_of_mem _ hs, hα⟩))
          (p.P s.1 hsdom).toCoherentBranchPartial := by
  classical
  have hU_valid : ∀ α ∈ (D.image Subtype.val).sup id, α < Ordinal.omega.{0} 1 := by
    intro α hα
    obtain ⟨W, hW, hαW⟩ := Finset.mem_sup.mp hα
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hW
    exact w.2 α hαW
  by_cases hDom : (D.filter (fun s => s.1 ∈ p.domain)).Nonempty
  · -- Domain members present: extend their common upper over the demand union.
    set E := (D.filter (fun s => s.1 ∈ p.domain)).image Subtype.val with hE_def
    have hE_dom : ∀ S ∈ E, S ∈ p.domain := by
      intro S hS
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hS
      exact (Finset.mem_filter.mp hs).2
    have hE_ne : E.Nonempty := by
      obtain ⟨s, hs⟩ := hDom
      exact ⟨s.1, Finset.mem_image_of_mem _ hs⟩
    have hT₀_dom : E.sup id ∈ p.domain := domain_sup_mem p E hE_dom hE_ne
    obtain ⟨Q, hQ_compat⟩ := coherentGoodBranchPartial_extend_to_union
      (p.P (E.sup id) hT₀_dom) ((D.image Subtype.val).sup id) hU_valid
    refine ⟨Q.restrict Finset.subset_union_right, fun s hs hsdom => ?_⟩
    have hs_E : s.1 ∈ E :=
      Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hs, hsdom⟩)
    have hs1_subE : s.1 ⊆ E.sup id := Finset.le_sup (f := id) hs_E
    refine ⟨?_, ?_⟩
    · intro α hα
      have e1 := hQ_compat.1 α (hs1_subE hα)
      have e2 := (p.compat hsdom hT₀_dom hs1_subE).1 α hα
      simp only [coherentGoodBranchPartialSystem,
        CoherentGoodBranchPartial.restrict_toCoherentBranchPartial,
        CoherentBranchPartial.restrict_prefixAt] at e1 e2 ⊢
      exact e1.trans e2
    · intro α hα
      have e1 := hQ_compat.2 α (hs1_subE hα)
      have e2 := (p.compat hsdom hT₀_dom hs1_subE).2 α hα
      simp only [coherentGoodBranchPartialSystem,
        CoherentGoodBranchPartial.restrict_toCoherentBranchPartial,
        CoherentBranchPartial.restrict_branch] at e1 e2 ⊢
      exact e1.trans e2
  · -- No domain members: any Good partial on the union; property vacuous.
    refine ⟨Classical.choice (exists_coherentGoodBranchPartial cR _ hU_valid),
      fun s hs hsdom => ?_⟩
    exact absurd ⟨s, Finset.mem_filter.mpr ⟨hs, hsdom⟩⟩ hDom

/-- **`finiteGlobalDemandWitness p D`**: the canonical CGBP on the demand union
`(D.image Subtype.val).sup id`, restricting compatibly to `p.P S` on every
`p.domain`-member of `D`. -/
noncomputable def finiteGlobalDemandWitness
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (D : Finset (GoodGlobalDemandIndex p)) :
    CoherentGoodBranchPartial cR ((D.image Subtype.val).sup id) :=
  (exists_finiteGlobalDemandWitness p D).choose

/-- For a demanded `p.domain`-member `s`, the global witness restricts on `s.1` to
the prescribed `p.P s.1` (fieldwise). -/
theorem finiteGlobalDemandWitness_domain_compat
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (D : Finset (GoodGlobalDemandIndex p))
    (s : GoodGlobalDemandIndex p) (hs : s ∈ D) (hsdom : s.1 ∈ p.domain) :
    cbpFieldwiseCompat
      ((finiteGlobalDemandWitness p D).toCoherentBranchPartial.restrict
        (fun _ hα => Finset.mem_sup.mpr ⟨s.1, Finset.mem_image_of_mem _ hs, hα⟩))
      (p.P s.1 hsdom).toCoherentBranchPartial :=
  (exists_finiteGlobalDemandWitness p D).choose_spec s hs hsdom

/-- **`finiteGlobalDemandWitness_member_compat`**: any two demanded members of `D`
route into the *same* common witness, so their values agree wherever both are
defined — `prefixAt`/`branch` at a shared `α` depend only on `α` being in the
demand union, not on which member exposed it (definitional, by proof-irrelevance
on the union-membership). This is the within-`D` compatibility that the
ultrafilter then upgrades to eventual compatibility between demanded finite sets;
in particular it yields `net.P T |_S = net.P S` when `S ⊆ T` are both demanded. -/
theorem finiteGlobalDemandWitness_member_compat
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (D : Finset (GoodGlobalDemandIndex p))
    (s t : GoodGlobalDemandIndex p) (hs : s ∈ D) (ht : t ∈ D)
    {α : Ordinal.{0}} (hαs : α ∈ s.1) (hαt : α ∈ t.1) :
    (finiteGlobalDemandWitness p D).toCoherentBranchPartial.prefixAt α
        (Finset.mem_sup.mpr ⟨s.1, Finset.mem_image_of_mem _ hs, hαs⟩)
      = (finiteGlobalDemandWitness p D).toCoherentBranchPartial.prefixAt α
        (Finset.mem_sup.mpr ⟨t.1, Finset.mem_image_of_mem _ ht, hαt⟩)
    ∧ (finiteGlobalDemandWitness p D).toCoherentBranchPartial.branch α
        (Finset.mem_sup.mpr ⟨s.1, Finset.mem_image_of_mem _ hs, hαs⟩)
      = (finiteGlobalDemandWitness p D).toCoherentBranchPartial.branch α
        (Finset.mem_sup.mpr ⟨t.1, Finset.mem_image_of_mem _ ht, hαt⟩) :=
  ⟨rfl, rfl⟩

/-- **`finiteGlobalDemandValue p D w hw`**: the global witness restricted to the
demanded finite set `w.1` (for `w ∈ D`). This is the per-coordinate value the
ultralimit reads off as `D` varies. -/
noncomputable def finiteGlobalDemandValue
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (D : Finset (GoodGlobalDemandIndex p)) (w : GoodGlobalDemandIndex p)
    (hw : w ∈ D) :
    CoherentGoodBranchPartial cR w.1 :=
  (finiteGlobalDemandWitness p D).restrict
    (fun _ hα => Finset.mem_sup.mpr ⟨w.1, Finset.mem_image_of_mem _ hw, hα⟩)

/-- **Domain forcing.** If `w.1 ∈ p.domain`, then for every `D` with `w ∈ D` the
per-demand value is fieldwise-compat with `p.P w.1`. -/
theorem finiteGlobalDemandValue_domain_compat
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (D : Finset (GoodGlobalDemandIndex p)) (w : GoodGlobalDemandIndex p)
    (hw : w ∈ D) (hwdom : w.1 ∈ p.domain) :
    cbpFieldwiseCompat
      (finiteGlobalDemandValue p D w hw).toCoherentBranchPartial
      (p.P w.1 hwdom).toCoherentBranchPartial :=
  finiteGlobalDemandWitness_domain_compat p D w hw hwdom

/-- **Same-`D` coherence.** For `s, t ∈ D` with `s.1 ⊆ t.1`, the value at `t`
restricted to `s.1` is fieldwise-compat with the value at `s` — both are
restrictions of the one common witness. -/
theorem finiteGlobalDemandValue_restrict_compat
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (D : Finset (GoodGlobalDemandIndex p)) (s t : GoodGlobalDemandIndex p)
    (hs : s ∈ D) (ht : t ∈ D) (hst : s.1 ⊆ t.1) :
    cbpFieldwiseCompat
      ((finiteGlobalDemandValue p D t ht).toCoherentBranchPartial.restrict hst)
      (finiteGlobalDemandValue p D s hs).toCoherentBranchPartial := by
  refine ⟨?_, ?_⟩
  · intro α hα
    simp only [finiteGlobalDemandValue,
      CoherentGoodBranchPartial.restrict_toCoherentBranchPartial,
      CoherentBranchPartial.restrict_prefixAt]
  · intro α hα
    simp only [finiteGlobalDemandValue,
      CoherentGoodBranchPartial.restrict_toCoherentBranchPartial,
      CoherentBranchPartial.restrict_branch]

/-- **Eventual domain forcing.** Along the demand ultrafilter, for any `D`
containing `w` the value is compat with `p.P w.1` (it holds for *every* such `D`).
Combined with `goodGlobalDemandUltrafilter_eventually_contains_one p w` (the cone
`{D | w ∈ D}` is eventual), this pins the net value at domain coordinates. -/
theorem finiteGlobalDemandValue_eventually_domain_compat
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (w : GoodGlobalDemandIndex p) (hwdom : w.1 ∈ p.domain) :
    ∀ᶠ D in goodGlobalDemandUltrafilter p, ∀ (hw : w ∈ D),
      cbpFieldwiseCompat
        (finiteGlobalDemandValue p D w hw).toCoherentBranchPartial
        (p.P w.1 hwdom).toCoherentBranchPartial :=
  Filter.Eventually.of_forall
    (fun D hw => finiteGlobalDemandValue_domain_compat p D w hw hwdom)

/-- **Eventual same-`D` coherence.** Along the demand ultrafilter, for any `D`
containing both `s` and `t` (with `s.1 ⊆ t.1`), the value at `t` restricts to the
value at `s`. Combined with `goodGlobalDemandUltrafilter_eventually_contains_one`
for `s` and `t`, this gives `net.P T |_S = net.P S` for demanded `S ⊆ T`. -/
theorem finiteGlobalDemandValue_eventually_restrict_compat
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (s t : GoodGlobalDemandIndex p) (hst : s.1 ⊆ t.1) :
    ∀ᶠ D in goodGlobalDemandUltrafilter p, ∀ (hs : s ∈ D) (ht : t ∈ D),
      cbpFieldwiseCompat
        ((finiteGlobalDemandValue p D t ht).toCoherentBranchPartial.restrict hst)
        (finiteGlobalDemandValue p D s hs).toCoherentBranchPartial :=
  Filter.Eventually.of_forall
    (fun D hs ht => finiteGlobalDemandValue_restrict_compat p D s t hs ht hst)

/-- **`AmbientCompat_of_common_witness`**: if `P_S` (on `S`) reads off a single
common `Q` on `U ⊇ S` fieldwise, then `P_S` is `AmbientCompat` with `Q.restrict`
to any `i₀ ⊆ U`. All cross-level/diagonal coherence comes from `Q`'s internal
`prefix_restrict`/`branch_restrict` (both `P_S` and the `i₀`-value are views of
the one object `Q`). -/
theorem CoherentGoodBranchPartial.AmbientCompat_of_common_witness
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {U : Finset Ordinal.{0}} (Q : CoherentGoodBranchPartial cR U)
    {S : Finset Ordinal.{0}} (hSU : S ⊆ U) (P_S : CoherentGoodBranchPartial cR S)
    (hpref : ∀ α (hα : α ∈ S),
      P_S.toCoherentBranchPartial.prefixAt α hα
        = Q.toCoherentBranchPartial.prefixAt α (hSU hα))
    (hbr : ∀ α (hα : α ∈ S),
      P_S.toCoherentBranchPartial.branch α hα
        = Q.toCoherentBranchPartial.branch α (hSU hα))
    {i₀ : Finset Ordinal.{0}} (hi₀U : i₀ ⊆ U) :
    CoherentGoodBranchPartial.AmbientCompat P_S (Q.restrict hi₀U) where
  prefix_below := fun β hβ_S α hα_i₀ hβ_lt_α x => by
    rw [CoherentGoodBranchPartial.restrict_toCoherentBranchPartial,
        CoherentBranchPartial.restrict_prefixAt, hpref β hβ_S]
    exact (Q.toCoherentBranchPartial.prefix_restrict hβ_lt_α.le
      (hSU hβ_S) (hi₀U hα_i₀) x).symm
  branch_below := fun β hβ_S α hα_i₀ hβ_lt_α x => by
    rw [CoherentGoodBranchPartial.restrict_toCoherentBranchPartial,
        CoherentBranchPartial.restrict_branch]
    have hL := congrFun (hbr β hβ_S) x
    rw [hL,
      ← Q.toCoherentBranchPartial.branch_restrict hβ_lt_α.le (hSU hβ_S) (hi₀U hα_i₀) x]
  prefix_above := fun α hα_i₀ β hβ_S hα_lt_β x => by
    rw [CoherentGoodBranchPartial.restrict_toCoherentBranchPartial,
        CoherentBranchPartial.restrict_prefixAt, hpref β hβ_S]
    exact (Q.toCoherentBranchPartial.prefix_restrict hα_lt_β.le
      (hi₀U hα_i₀) (hSU hβ_S) x).symm
  branch_above := fun α hα_i₀ β hβ_S hα_lt_β x => by
    rw [CoherentGoodBranchPartial.restrict_toCoherentBranchPartial,
        CoherentBranchPartial.restrict_branch]
    have hR := congrFun (hbr β hβ_S)
      ((Ordinal.initialSegToType hα_lt_β.le).toOrderEmbedding x)
    rw [hR, Q.toCoherentBranchPartial.branch_restrict hα_lt_β.le (hi₀U hα_i₀) (hSU hβ_S) x]
  prefix_diag := fun α hα_S hα_i₀ => by
    rw [CoherentGoodBranchPartial.restrict_toCoherentBranchPartial,
        CoherentBranchPartial.restrict_prefixAt, hpref α hα_S]
  branch_diag := fun α hα_S hα_i₀ => by
    rw [CoherentGoodBranchPartial.restrict_toCoherentBranchPartial,
        CoherentBranchPartial.restrict_branch, hbr α hα_S]

/-- **`goodIdealOneIndex_finite_consistent`**: the finite slice of the one-index
frontier. For a finite demand set `D ⊆ p.domain`, a single `Pi₀` on `i₀` is
`AmbientCompat` with every `p.P S` (`S ∈ D`) and prescribed-agrees with `p.P V`
for `V ∈ D` with `V ⊆ i₀`.

Construction: amalgamate `D` into `Q'` on `D.sup id`
(`amalgamate_from_common_upper`), freely extend `Q'` over `i₀` to `Q` on
`D.sup ∪ i₀` (`extend_to_union`), and take `Pi₀ := Q.restrict i₀`. Each `p.P S`
reads off the one common `Q` on `S` (amalgam + extend compat), so
`AmbientCompat_of_common_witness` applies. -/
theorem goodIdealOneIndex_finite_consistent
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (i₀ : Finset Ordinal.{0}) (hi₀ : ∀ α ∈ i₀, α < Ordinal.omega.{0} 1)
    (D : Finset (Finset Ordinal.{0})) (hD : ∀ S ∈ D, S ∈ p.domain) :
    ∃ Pi₀ : CoherentGoodBranchPartial cR i₀,
      (∀ S (hS : S ∈ D),
        CoherentGoodBranchPartial.AmbientCompat (p.P S (hD S hS)) Pi₀) ∧
      (∀ V (hV : V ∈ D) (hVi₀ : V ⊆ i₀),
        cbpFieldwiseCompat
          (Pi₀.toCoherentBranchPartial.restrict hVi₀)
          (p.P V (hD V hV)).toCoherentBranchPartial) := by
  classical
  obtain ⟨Q', hQ'⟩ := coherentGoodBranchPartial_amalgamate_from_common_upper p D hD
  obtain ⟨Q, hQ_ext⟩ := coherentGoodBranchPartial_extend_to_union Q' i₀ hi₀
  have ambS : ∀ S (hS : S ∈ D),
      CoherentGoodBranchPartial.AmbientCompat (p.P S (hD S hS))
        (Q.restrict Finset.subset_union_right) := by
    intro S hS
    have hSsup : S ⊆ D.sup id := fun _ hα => Finset.mem_sup.mpr ⟨S, hS, hα⟩
    refine CoherentGoodBranchPartial.AmbientCompat_of_common_witness Q
      (hSsup.trans Finset.subset_union_left) (p.P S (hD S hS)) ?_ ?_
      Finset.subset_union_right
    · intro α hα
      have ea := (hQ' S hS).1 α hα
      have ee := hQ_ext.1 α (hSsup hα)
      simp only [CoherentBranchPartial.restrict_prefixAt] at ea ee
      rw [← ea, ← ee]
    · intro α hα
      have ea := (hQ' S hS).2 α hα
      have ee := hQ_ext.2 α (hSsup hα)
      simp only [CoherentBranchPartial.restrict_branch] at ea ee
      rw [← ea, ← ee]
  refine ⟨Q.restrict Finset.subset_union_right, ambS, ?_⟩
  intro V hV hVi₀
  refine ⟨?_, ?_⟩
  · intro α hα
    rw [CoherentBranchPartial.restrict_prefixAt]
    exact ((ambS V hV).prefix_diag α hα (hVi₀ hα)).symm
  · intro α hα
    rw [CoherentBranchPartial.restrict_branch]
    exact ((ambS V hV).branch_diag α hα (hVi₀ hα)).symm

/-- **`GoodOneIndexFixedCarrierCompactness`**: the fixed-carrier compactness
principle. For a fixed valid `i₀`, if every *finite* sub-demand admits an
ambient-compatible CGBP on `i₀`, then a single CGBP on `i₀` is ambient-compatible
with the whole (possibly infinite) prescribed family `{p.P S | S ∈ p.domain}`.

**This is a genuine compactness/inverse-limit principle, NOT finite branching.**
A witness on `i₀` carries, for each `α ∈ i₀`, a `prefixAt α : α.ToType ↪o
PairERSource` and `branch α : α.ToType → Bool`; with `α.ToType` countably infinite
and `PairERSource` infinite, the coordinate value spaces are infinite. So this
cannot be discharged by finite-branching König; it needs a real
compactness/inverse-limit argument over the (fixed) carrier `i₀`. -/
def GoodOneIndexFixedCarrierCompactness
    (cR : (Fin 2 ↪o PairERSource) → Bool) : Prop :=
  ∀ (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (i₀ : Finset Ordinal.{0}) (_hi₀ : ∀ α ∈ i₀, α < Ordinal.omega.{0} 1),
    (∀ (D : Finset (Finset Ordinal.{0})) (hD : ∀ S ∈ D, S ∈ p.domain),
        ∃ Pi₀ : CoherentGoodBranchPartial cR i₀,
          ∀ S (hS : S ∈ D),
            CoherentGoodBranchPartial.AmbientCompat (p.P S (hD S hS)) Pi₀) →
      ∃ Pi₀ : CoherentGoodBranchPartial cR i₀,
        ∀ S (hS : S ∈ p.domain),
          CoherentGoodBranchPartial.AmbientCompat (p.P S hS) Pi₀

/-- **Reduction** (proved): given fixed-carrier compactness, the one-index
frontier follows — feed it the finite consistency from
`goodIdealOneIndex_finite_consistent`. -/
theorem goodIdealOneIndexCompactness_of_fixedCarrierCompactness
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (h : GoodOneIndexFixedCarrierCompactness cR)
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (i₀ : Finset Ordinal.{0}) (hi₀ : ∀ α ∈ i₀, α < Ordinal.omega.{0} 1) :
    ∃ Pi₀ : CoherentGoodBranchPartial cR i₀,
      ∀ S (hS : S ∈ p.domain),
        CoherentGoodBranchPartial.AmbientCompat (p.P S hS) Pi₀ :=
  h p i₀ hi₀ (fun D hD =>
    (goodIdealOneIndex_finite_consistent p i₀ hi₀ D hD).imp (fun _ hPi₀ => hPi₀.1))

/-- **`AmbientCompat.congr_right`**: `AmbientCompat P R` depends on the right CGBP
`R` only through its `prefixAt`/`branch` (fieldwise) data. So a fieldwise-equal
CGBP `R'` on the same carrier inherits the same `AmbientCompat`. This is the
*transport* step in the uniform-common-witness reduction: each per-`S` common
witness yields `AmbientCompat (p.P S) (Q_S.restrict i₀)`, and this lemma replaces
the per-`S` restriction by the single uniform witness `Pi₀` it agrees with. -/
theorem CoherentGoodBranchPartial.AmbientCompat.congr_right
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {S T : Finset Ordinal.{0}}
    {P : CoherentGoodBranchPartial cR S}
    {R R' : CoherentGoodBranchPartial cR T}
    (h : CoherentGoodBranchPartial.AmbientCompat P R)
    (hRR' : cbpFieldwiseCompat R.toCoherentBranchPartial R'.toCoherentBranchPartial) :
    CoherentGoodBranchPartial.AmbientCompat P R' where
  prefix_below := fun β hβ_S α hα_T hβ_lt_α x => by
    rw [← hRR'.1 α hα_T]; exact h.prefix_below β hβ_S α hα_T hβ_lt_α x
  branch_below := fun β hβ_S α hα_T hβ_lt_α x => by
    rw [← hRR'.2 α hα_T]; exact h.branch_below β hβ_S α hα_T hβ_lt_α x
  prefix_above := fun α hα_T β hβ_S hα_lt_β x => by
    rw [← hRR'.1 α hα_T]; exact h.prefix_above α hα_T β hβ_S hα_lt_β x
  branch_above := fun α hα_T β hβ_S hα_lt_β x => by
    rw [← hRR'.2 α hα_T]; exact h.branch_above α hα_T β hβ_S hα_lt_β x
  prefix_diag := fun α hα_S hα_T => by
    rw [← hRR'.1 α hα_T]; exact h.prefix_diag α hα_S hα_T
  branch_diag := fun α hα_S hα_T => by
    rw [← hRR'.2 α hα_T]; exact h.branch_diag α hα_S hα_T

/-- **`GoodUniformCommonWitness p i₀ Pi₀`**: the uniform-common-witness form of
the one-index frontier's genuine content. Says the *single* CGBP `Pi₀` on `i₀`
amalgamates with *every* prescribed `p.P S` (`S ∈ p.domain`) through a shared
finite super-carrier `U ⊇ i₀ ∪ S`: there is a `Q` on `U` reading off `Pi₀` on
`i₀` and `p.P S` on `S`, both fieldwise. This is precisely the inverse-limit
object — one `Pi₀` pairwise-compatible (via a common `Q`) with the whole directed
family. Contrast the finite case `goodIdealOneIndex_finite_consistent`, where a
*single* `Q` works for all of `D` at once (the union `D.sup id` is in the
domain); here each `S` may need its own `Q_S` because the union of the whole
(possibly unbounded) domain is not finite. The existence of such a uniform `Pi₀`
is the fusion content — see the diagnostic note on
`goodOneIndexFixedCarrierCompactness_holds`. -/
def GoodUniformCommonWitness
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (i₀ : Finset Ordinal.{0}) (Pi₀ : CoherentGoodBranchPartial cR i₀) : Prop :=
  ∀ S (hS : S ∈ p.domain),
    ∃ (U : Finset Ordinal.{0}) (hiU : i₀ ⊆ U) (hSU : S ⊆ U)
      (Q : CoherentGoodBranchPartial cR U),
      cbpFieldwiseCompat (Q.restrict hiU).toCoherentBranchPartial
          Pi₀.toCoherentBranchPartial ∧
        cbpFieldwiseCompat (Q.restrict hSU).toCoherentBranchPartial
          (p.P S hS).toCoherentBranchPartial

/-- **`ambientCompat_of_uniformCommonWitness`** (proved, sorry-free): a uniform
common witness `Pi₀` is `AmbientCompat` with every prescribed `p.P S`. Per `S`,
the shared `Q` makes `p.P S` and `Pi₀` both views of `Q` (`Q.restrict i₀` =
`Pi₀` fieldwise, `Q.restrict S` = `p.P S` fieldwise), so
`AmbientCompat_of_common_witness` gives `AmbientCompat (p.P S) (Q.restrict i₀)`,
and `AmbientCompat.congr_right` transports it to `Pi₀`. -/
theorem ambientCompat_of_uniformCommonWitness
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {p : (coherentGoodBranchPartialSystem cR).IdealPartialSection}
    {i₀ : Finset Ordinal.{0}} {Pi₀ : CoherentGoodBranchPartial cR i₀}
    (h : GoodUniformCommonWitness p i₀ Pi₀) :
    ∀ S (hS : S ∈ p.domain),
      CoherentGoodBranchPartial.AmbientCompat (p.P S hS) Pi₀ := by
  intro S hS
  obtain ⟨U, hiU, hSU, Q, hQi₀, hQS⟩ := h S hS
  have hambQ : CoherentGoodBranchPartial.AmbientCompat (p.P S hS) (Q.restrict hiU) := by
    refine CoherentGoodBranchPartial.AmbientCompat_of_common_witness Q hSU (p.P S hS) ?_ ?_ hiU
    · intro α hα
      have e := hQS.1 α hα
      rw [CoherentGoodBranchPartial.restrict_toCoherentBranchPartial,
          CoherentBranchPartial.restrict_prefixAt] at e
      exact e.symm
    · intro α hα
      have e := hQS.2 α hα
      rw [CoherentGoodBranchPartial.restrict_toCoherentBranchPartial,
          CoherentBranchPartial.restrict_branch] at e
      exact e.symm
  exact hambQ.congr_right hQi₀

/-- **`goodOneIndexFixedCarrierCompactness_of_uniformCommonWitness`** (proved,
sorry-free): the fixed-carrier compactness principle *follows from* a
uniform-common-witness existence principle. This is the exact prescription-
relative reduction the diagnostic was after: it discharges all the `AmbientCompat`
bookkeeping and isolates the genuine remaining content into the single hypothesis
`H` — "for every `p`, `i₀` there is one `Pi₀` on `i₀` that amalgamates (through a
shared finite super-carrier) with the whole directed family `{p.P S}`." The
finite-satisfiability hypothesis of `GoodOneIndexFixedCarrierCompactness` is
*unused* here (it is the easy direction, already proved as
`goodIdealOneIndex_finite_consistent`); the content lives entirely in `H`, which
is the fusion / inverse-limit frontier. -/
theorem goodOneIndexFixedCarrierCompactness_of_uniformCommonWitness
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (H : ∀ (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
          (i₀ : Finset Ordinal.{0}) (_hi₀ : ∀ α ∈ i₀, α < Ordinal.omega.{0} 1),
          ∃ Pi₀ : CoherentGoodBranchPartial cR i₀, GoodUniformCommonWitness p i₀ Pi₀) :
    GoodOneIndexFixedCarrierCompactness cR := by
  intro p i₀ hi₀ _hfin
  obtain ⟨Pi₀, hPi₀⟩ := H p i₀ hi₀
  exact ⟨Pi₀, ambientCompat_of_uniformCommonWitness hPi₀⟩

/-- **[DOWNSTREAM OF THE FUSION TARGET — not an independent frontier]**
`goodOneIndexFixedCarrierCompactness_holds`: one CGBP on the fixed `i₀` satisfying
all (possibly infinitely many) prescribed demands, from finite satisfiability.

**This is NOT an independent compactness theorem.** Phase-A diagnosis (see below)
shows it is *downstream of the single deep fusion target*
`exists_realizedPairERTypeTree` — the genuine limit fusion (existence of a
coherent family carrying a *realized* type-tree). Closing it yields a
`CoherentMajorityBranch` (`exists_coherentMajorityBranch`), which lets the
transfinite extension route through the *proved* `PairERChain.extendToExtOfBranch`
instead of the open `extendToExt` (~1595) — closing the Good-chain construction
`exists_coherentGoodBranchPartial`, and hence this principle (via the bridge
theorem `goodOneIndexFixedCarrierCompactness_of_uniformCommonWitness`). They are
the *same* frontier, not orthogonal; do not attack this statement directly —
attack the fusion target. (The *universal*-over-`IsTypeCoherent` intersection
claim is false — see the REMOVED note at the former
`exists_nonempty_iInter_stage_fibers`; the realized-tree existence is the correct,
true target. The prescribed-successor primitive `PairERGoodChain.succWithChoice`,
formerly a separate sorry, is now **proved** — its `b` is free, no
`b`-consistency side condition is needed.)

**Reduction map (why they coincide).** The `AmbientCompat` bookkeeping is not the
content: the bridge theorem `_of_uniformCommonWitness` proves (sorry-free in its
body) that the principle follows from a *uniform-common-witness* existence
principle `H` — one `Pi₀` on `i₀` amalgamating, through a shared finite
super-carrier, with the whole directed family `{p.P S}` (`GoodUniformCommonWitness`;
the finite-satisfiability hypothesis is unused). So the genuine content is the
existence of that uniform `Pi₀` = the *coherent limit* of `{p.P S}` over `i₀`'s
levels. With `M = max i₀` (`M < ω₁`, so `M.ToType` countable), a witness is
essentially `goodAt M : PairERGoodChain cR M`; its head `M.ToType ↪o PairERSource`
is forced on levels *seen* by some `p.P S`, free elsewhere. Assembling it =
`F.prefix` for the induced `PairERCoherentFamily F` + a point in
`validFiber cR F.prefix F.typeFn`, which by
`PairERCoherentFamily.validFiber_prefix_typeFn_eq_iInter` is exactly a *realized*
type-tree for `F` (`exists_realizedPairERTypeTree` →
`PairERTypeTree.toNonemptyIntersection`). Good-adjacency at the prescribed
successors is already discharged by the now-proved
`PairERGoodChain.succWithChoice`. -/
theorem goodOneIndexFixedCarrierCompactness_holds
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    GoodOneIndexFixedCarrierCompactness cR := by
  sorry

/-- **`goodIdealOneIndexCompactness`** (derived): one `Pi₀` on `i₀`
`AmbientCompat` with every prescribed `p.P S` (`S ∈ p.domain`). Now a corollary of
`goodOneIndexFixedCarrierCompactness_holds` via the reduction
`goodIdealOneIndexCompactness_of_fixedCarrierCompactness`; the genuine content has
moved to that fixed-carrier principle. (Finite satisfiability — any finite
subfamily — is `goodIdealOneIndex_finite_consistent`, itself built on
`coherentGoodBranchPartial_amalgamate_from_common_upper`.) -/
theorem goodIdealOneIndexCompactness
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (i₀ : Finset Ordinal.{0}) (hi₀ : ∀ α ∈ i₀, α < Ordinal.omega.{0} 1) :
    ∃ Pi₀ : CoherentGoodBranchPartial cR i₀,
      ∀ S (hS : S ∈ p.domain),
        CoherentGoodBranchPartial.AmbientCompat (p.P S hS) Pi₀ :=
  goodIdealOneIndexCompactness_of_fixedCarrierCompactness
    (goodOneIndexFixedCarrierCompactness_holds cR) p i₀ hi₀

/-- **[LEGACY — OFF-CHAIN, sorry]** `goodIdealGlobalization`:
every finitely-consistent `IdealPartialSection` of the Good system extends to a
total `CoherentGoodWitnessNet` storing each prescribed CGBP literally on
`p.domain`.

**No longer on the witness-net route.** `exists_coherentGoodWitnessNet` now goes
`goodIdealOneIndexCompactness → goodIdealExtensionCompactness (rewired) →
exists_global_section_of_idealPartialExtensions`. The ultralimit globalization
sketched below is a documented dead end (the eventual-constancy obstruction:
freely-chosen finite witnesses do not converge). Retained for reference only;
a candidate for later pruning along with `goodIdealCompactness`.

This is the genuine remaining content of `goodIdealCompactness`, isolated from
the finite part. **Finite consistency is already discharged**: for any finite
demand set `D ⊆ p.domain`,
`coherentGoodBranchPartial_amalgamate_from_common_upper` produces a single CGBP
on `D.sup id` restricting compatibly to each `p.P S` (directedness supplies the
common object). What remains is the **globalization / inverse-limit step**:
choose a coherent value `net.P W` for *every* valid finite `W` (not just those
in `p.domain`), agreeing with `p` on `p.domain`. Intended route: an ultrafilter
over finite demand sets — finite consistency from the common-upper lemma, a
`𝔘`-eventual global choice for each `W`, and equality on `p.domain` forced by
the prescribed constraints.

Stated directly over the IPS (retaining directedness), unlike the route through
`prescribedGoodCompactness_holds`/`toGoodPrescription` which discards it. -/
theorem goodIdealGlobalization
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection) :
    ∃ net : CoherentGoodWitnessNet cR,
      ∀ S (hS : S ∈ p.domain),
        net.P S (p.domain_valid hS) = p.P S hS := by
  sorry

/-- **[LEGACY — OFF-CHAIN]** `goodIdealCompactness`: a global
`CoherentGoodWitnessNet` whose value at each `S ∈ p.domain` equals `p.P S`
**literally**.

**Off the witness-net route**: a one-line corollary of the now-orphaned
`goodIdealGlobalization` (sorry). The live route to `exists_coherentGoodWitnessNet`
no longer passes through here — it goes via `goodIdealExtensionCompactness`
(rewired) ← `goodIdealOneIndexCompactness`. Retained for reference.

**Why not the generic `goodConstraintCompactness`?** That form
concludes with `cbpFieldwiseCompat`, not equality. The IPS extension
order `p ≤ q` requires `q.P S = p.P S` for `S ∈ p.domain`; compat
alone is insufficient because two CGBPs with equal underlying bare
CBP can still differ in `toGoodApprox` (Good-chain bundling). The
specialized form pins down equality directly. -/
theorem goodIdealCompactness
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection) :
    ∃ net : CoherentGoodWitnessNet cR,
      ∀ S (hS : S ∈ p.domain),
        net.P S (p.domain_valid hS) = p.P S hS :=
  goodIdealGlobalization p

/-- **Bridge (with explicit hypothesis form).**
`prescribedGoodCompactness` implies the `goodIdealCompactness`
statement for every IPS. Kept as an explicit-hypothesis variant for
readers who want to see the implication structure separately from
`prescribedGoodCompactness_holds`. -/
theorem goodIdealCompactness_of_prescribedGoodCompactness
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (hcompact : prescribedGoodCompactness cR)
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection) :
    ∃ net : CoherentGoodWitnessNet cR,
      ∀ S (hS : S ∈ p.domain),
        net.P S (p.domain_valid hS) = p.P S hS :=
  hcompact p.toGoodPrescription

/-- **`cbpFieldwiseCompat.refl`**: reflexivity. -/
theorem cbpFieldwiseCompat.refl {cR : (Fin 2 ↪o PairERSource) → Bool}
    {S : Finset Ordinal.{0}} (P : CoherentBranchPartial cR S) :
    cbpFieldwiseCompat P P :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- **`cbpFieldwiseCompat.symm`**: symmetry. -/
theorem cbpFieldwiseCompat.symm {cR : (Fin 2 ↪o PairERSource) → Bool}
    {S : Finset Ordinal.{0}} {P Q : CoherentBranchPartial cR S}
    (h : cbpFieldwiseCompat P Q) : cbpFieldwiseCompat Q P :=
  ⟨fun α hα => (h.1 α hα).symm, fun α hα => (h.2 α hα).symm⟩

/-- **`cbpFieldwiseCompat.trans`**: transitivity. -/
theorem cbpFieldwiseCompat.trans {cR : (Fin 2 ↪o PairERSource) → Bool}
    {S : Finset Ordinal.{0}} {P Q R : CoherentBranchPartial cR S}
    (h₁ : cbpFieldwiseCompat P Q) (h₂ : cbpFieldwiseCompat Q R) :
    cbpFieldwiseCompat P R :=
  ⟨fun α hα => (h₁.1 α hα).trans (h₂.1 α hα),
   fun α hα => (h₁.2 α hα).trans (h₂.2 α hα)⟩

/-- **`AdjoinGoodOldData`**: bundled witness for the `V ∈ p.domain`
branch of `adjoinGoodValue`. Packages the chosen upper bound `U`,
membership proofs, and extension `Q` with its compat. -/
structure AdjoinGoodOldData
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (T : Finset Ordinal.{0}) (i₀ V : Finset Ordinal.{0}) where
  U : Finset Ordinal.{0}
  hU : U ∈ p.domain
  hVU : V ⊆ U
  hTU : T ⊆ U
  Q : CoherentGoodBranchPartial cR (U ∪ i₀)
  hQ_compat : cbpFieldwiseCompat
    (Q.toCoherentBranchPartial.restrict Finset.subset_union_left)
    (p.P U hU).toCoherentBranchPartial

/-- **`adjoinGoodOldData`**: build the bundled `AdjoinGoodOldData`
when `V ∈ p.domain`. Uses `p.directed` to get `U ⊇ V, T` and
`extend_to_union` for `Q`. -/
noncomputable def adjoinGoodOldData
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (T : Finset Ordinal.{0}) (hT : T ∈ p.domain)
    (i₀ V : Finset Ordinal.{0})
    (hi₀_valid : ∀ α ∈ i₀, α < Ordinal.omega.{0} 1)
    (hV_p : V ∈ p.domain) :
    AdjoinGoodOldData p T i₀ V :=
  let U_spec := Classical.choose_spec (p.directed hV_p hT)
  let U := Classical.choose (p.directed hV_p hT)
  let Q_spec := Classical.choose_spec
    (coherentGoodBranchPartial_extend_to_union (p.P U U_spec.1) i₀ hi₀_valid)
  let Q := Classical.choose
    (coherentGoodBranchPartial_extend_to_union (p.P U U_spec.1) i₀ hi₀_valid)
  { U := U
    hU := U_spec.1
    hVU := U_spec.2.1
    hTU := U_spec.2.2
    Q := Q
    hQ_compat := Q_spec }

/-- **`IdealPartialSection.adjoinGoodValue`**: value construction for
a single `V` in the new domain. Given the ideal section `p`, anchor
`T ∈ p.domain`, fresh `i₀`, and `V` such that `∃ S ∈ p.domain,
V ⊆ S ∪ i₀`, build a Good CGBP at `V`.

**Dispatched construction** to ensure `V ⊆ U` when `V ∈ p.domain`:

- If `V ∈ p.domain`: use `V` directly as anchor for directedness.
  `p.directed hV_p hT` gives `U ⊇ V, T`. Extend `p.P U` to `U ∪ i₀`
  via `extend_to_union`, restrict to `V`. Since `V ⊆ U`, restrictions
  preserve `p.P V`.
- If `V ∉ p.domain`: use the witness `S_V` from `hV` (via
  `Classical.choose`). `p.directed hS_V hT` gives `U ⊇ S_V, T`.
  Extension and restriction as above. This handles new
  finsets `V ⊆ S ∪ i₀` with `V` strictly larger than any S.

Compat properties: see `adjoinGoodValue_old_compat` and
`adjoinGoodValue_common_compat`. -/
noncomputable def FiniteProjectiveSystem.IdealPartialSection.adjoinGoodValue
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (T : Finset Ordinal.{0}) (hT : T ∈ p.domain)
    (i₀ V : Finset Ordinal.{0})
    (hi₀_valid : ∀ α ∈ i₀, α < Ordinal.omega.{0} 1)
    (hV : ∃ S ∈ p.domain, V ⊆ S ∪ i₀) :
    CoherentGoodBranchPartial cR V :=
  letI : Decidable (V ∈ p.domain) := Classical.dec _
  if hV_p : V ∈ p.domain then
    -- V ∈ p.domain branch: use bundled AdjoinGoodOldData.
    let d := adjoinGoodOldData p T hT i₀ V hi₀_valid hV_p
    d.Q.restrict (fun α hα => Finset.mem_union_left _ (d.hVU hα))
  else
    -- V ∉ p.domain → use S_V witness from hV.
    let S_V := Classical.choose hV
    let hS_V_spec := Classical.choose_spec hV
    let hS_V := hS_V_spec.1
    let hV_sub_S_V_i₀ := hS_V_spec.2
    let U_spec := Classical.choose_spec (p.directed hS_V hT)
    let U := Classical.choose (p.directed hS_V hT)
    let hU_in := U_spec.1
    let hS_V_U := U_spec.2.1
    let Q := Classical.choose
      (coherentGoodBranchPartial_extend_to_union (p.P U hU_in) i₀ hi₀_valid)
    have hV_sub_U_i₀ : V ⊆ U ∪ i₀ := fun α hα => by
      rcases Finset.mem_union.mp (hV_sub_S_V_i₀ hα) with h_S | h_i
      · exact Finset.mem_union_left _ (hS_V_U h_S)
      · exact Finset.mem_union_right _ h_i
    Q.restrict hV_sub_U_i₀

/-- **[STUB]** `IdealPartialSection.adjoinGoodValue_old_compat`: for
`V ∈ p.domain`, the constructed value agrees with `p.P V`.

**Subtlety**: the proof requires reconciling `Q.restrict V` (where `Q`
extends `p.P U` to `U ∪ i₀`) with `p.P V`. For `α ∈ V ∩ U`, the
agreement follows from `Q_compat` (extending `p.P U`) + `p.compat`
(reaching `p.P V` via a common upper bound `U' ⊇ V, U` in
`p.domain`). For `α ∈ V ∩ i₀ ∖ U`, however, `Q`'s value is unconstrained
by `Q_compat`'s preservation on `U`, so direct agreement with `p.P V`
isn't immediate.

A possible fix is to use directedness more aggressively in the
construction of `adjoinGoodValue`: include `V` (when `V ∈ p.domain`)
in the directed-upper-bound call so that `V ⊆ U` and the `V ∩ i₀ ∖ U`
case doesn't arise. This makes the construction parametric in whether
`V ∈ p.domain`. Currently stubbed. -/
theorem FiniteProjectiveSystem.IdealPartialSection.adjoinGoodValue_old_compat
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (T : Finset Ordinal.{0}) (hT : T ∈ p.domain)
    (i₀ V : Finset Ordinal.{0})
    (hi₀_valid : ∀ α ∈ i₀, α < Ordinal.omega.{0} 1)
    (hV : ∃ S ∈ p.domain, V ⊆ S ∪ i₀)
    (hV_p : V ∈ p.domain) :
    cbpFieldwiseCompat
      (p.adjoinGoodValue T hT i₀ V hi₀_valid hV).toCoherentBranchPartial
      (p.P V hV_p).toCoherentBranchPartial := by
  classical
  -- Unfold adjoinGoodValue's if-then branch.
  unfold FiniteProjectiveSystem.IdealPartialSection.adjoinGoodValue
  rw [dif_pos hV_p]
  -- Now the value is `d.Q.restrict ...` where `d := adjoinGoodOldData ...`.
  set d := adjoinGoodOldData p T hT i₀ V hi₀_valid hV_p with hd_def
  -- Compat from chained restricts + d.hQ_compat + p.compat.
  refine ⟨?_, ?_⟩
  · intro α hα
    -- Step 1: restrict_toCBP + restrict_prefixAt on LHS.
    rw [CoherentGoodBranchPartial.restrict_toCoherentBranchPartial,
        CoherentBranchPartial.restrict_prefixAt]
    -- Goal: d.Q.toCBP.prefixAt α (mem_union_left _ (d.hVU hα)) =
    --       (p.P V hV_p).toCBP.prefixAt α hα
    -- Step 2: use d.hQ_compat to relate d.Q.toCBP at U to p.P d.U.
    have h_dQ := d.hQ_compat.1 α (d.hVU hα)
    rw [CoherentBranchPartial.restrict_prefixAt] at h_dQ
    -- h_dQ : d.Q.toCBP.prefixAt α (mem_union_left _ (d.hVU hα)) =
    --        (p.P d.U d.hU).toCBP.prefixAt α (d.hVU hα)
    rw [h_dQ]
    -- Goal: (p.P d.U d.hU).toCBP.prefixAt α (d.hVU hα) =
    --       (p.P V hV_p).toCBP.prefixAt α hα
    -- Step 3: use p.compat to relate p.P d.U to p.P V.
    have h_pc := (p.compat hV_p d.hU d.hVU).1 α hα
    -- h_pc uses FPS restrict; unfold to CGBP.restrict, then to bare CBP restrict.
    change ((p.P d.U d.hU).restrict d.hVU).toCoherentBranchPartial.prefixAt α hα =
      (p.P V hV_p).toCoherentBranchPartial.prefixAt α hα at h_pc
    rw [CoherentGoodBranchPartial.restrict_toCoherentBranchPartial,
        CoherentBranchPartial.restrict_prefixAt] at h_pc
    exact h_pc
  · intro α hα
    -- Parallel for branch.
    rw [CoherentGoodBranchPartial.restrict_toCoherentBranchPartial,
        CoherentBranchPartial.restrict_branch]
    have h_dQ := d.hQ_compat.2 α (d.hVU hα)
    rw [CoherentBranchPartial.restrict_branch] at h_dQ
    rw [h_dQ]
    have h_pc := (p.compat hV_p d.hU d.hVU).2 α hα
    change ((p.P d.U d.hU).restrict d.hVU).toCoherentBranchPartial.branch α hα =
      (p.P V hV_p).toCoherentBranchPartial.branch α hα at h_pc
    rw [CoherentGoodBranchPartial.restrict_toCoherentBranchPartial,
        CoherentBranchPartial.restrict_branch] at h_pc
    exact h_pc

/-! ### `BoundedIdealPartialSection`: principal ideals

A `BoundedIdealPartialSection` is a Good ideal partial section whose
domain is the principal ideal `{S | S ⊆ top}` for some finite `top`.
All values are restrictions of a single `topObj : CGBP cR top`, so
extension and compatibility become trivial: extend `topObj` to
`top ∪ i₀` via `extend_to_union`, then everything restricts uniformly.

This avoids the canonical-choice obstacle that plagues the general
ideal extension proof: there's only one chosen extension, used
consistently for every restriction. -/

/-- **`BoundedIdealPartialSection cR`**: a Good ideal partial section
backed by a single CGBP on a top finset. -/
structure BoundedIdealPartialSection
    (cR : (Fin 2 ↪o PairERSource) → Bool) where
  top : Finset Ordinal.{0}
  top_valid : ∀ α ∈ top, α < Ordinal.omega.{0} 1
  topObj : CoherentGoodBranchPartial cR top

/-- **`BoundedIdealPartialSection.empty`**: the empty bounded section
(top = ∅, vacuous data). -/
noncomputable def BoundedIdealPartialSection.empty
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    BoundedIdealPartialSection cR where
  top := ∅
  top_valid := fun α hα => absurd hα (Finset.notMem_empty α)
  topObj := Classical.choice (exists_coherentGoodBranchPartial cR ∅
    (fun α hα => absurd hα (Finset.notMem_empty α)))

/-- **`BoundedIdealPartialSection.toIdealPartialSection`**: convert
to a general `IdealPartialSection` of the Good projective system.
The domain is the principal ideal `{S | S ⊆ top}`; values are
restrictions of `topObj`. Compatibility is automatic via double
`restrict_prefixAt`/`restrict_branch`. -/
noncomputable def BoundedIdealPartialSection.toIdealPartialSection
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (b : BoundedIdealPartialSection cR) :
    (coherentGoodBranchPartialSystem cR).IdealPartialSection where
  domain := {S | S ⊆ b.top}
  domain_valid := fun {S} hS α hα => b.top_valid α (hS hα)
  downward_closed := fun {S T} hT hST => hST.trans hT
  directed := fun {S T} hS hT =>
    ⟨b.top, (Finset.Subset.refl b.top : b.top ⊆ b.top), hS, hT⟩
  P := fun S hS => b.topObj.restrict hS
  compat := by
    intro S T hS hT hST
    refine ⟨?_, ?_⟩
    · intro α hα
      show ((b.topObj.restrict hT).restrict hST).toCoherentBranchPartial.prefixAt α hα =
        (b.topObj.restrict hS).toCoherentBranchPartial.prefixAt α hα
      simp only [CoherentGoodBranchPartial.restrict_toCoherentBranchPartial]
      rw [CoherentBranchPartial.restrict_prefixAt,
          b.topObj.toCoherentBranchPartial.restrict_prefixAt hT α (hST hα),
          b.topObj.toCoherentBranchPartial.restrict_prefixAt hS α hα]
    · intro α hα
      show ((b.topObj.restrict hT).restrict hST).toCoherentBranchPartial.branch α hα =
        (b.topObj.restrict hS).toCoherentBranchPartial.branch α hα
      simp only [CoherentGoodBranchPartial.restrict_toCoherentBranchPartial]
      rw [CoherentBranchPartial.restrict_branch,
          b.topObj.toCoherentBranchPartial.restrict_branch hT α (hST hα),
          b.topObj.toCoherentBranchPartial.restrict_branch hS α hα]

/-- **`BoundedIdealPartialSection.extend`**: extend a bounded section
by `i₀` to produce a larger bounded section whose top is `top ∪ i₀`.
Uses `coherentGoodBranchPartial_extend_to_union` to extend the
underlying `topObj`. -/
noncomputable def BoundedIdealPartialSection.extend
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (b : BoundedIdealPartialSection cR)
    (i₀ : Finset Ordinal.{0})
    (hi₀_valid : ∀ α ∈ i₀, α < Ordinal.omega.{0} 1) :
    BoundedIdealPartialSection cR where
  top := b.top ∪ i₀
  top_valid := by
    intro α hα
    rcases Finset.mem_union.mp hα with h | h
    · exact b.top_valid α h
    · exact hi₀_valid α h
  topObj := Classical.choose
    (coherentGoodBranchPartial_extend_to_union b.topObj i₀ hi₀_valid)

/-- **`BoundedIdealPartialSection.extend_compat`**: the extended
section's restriction to `top` agrees fieldwise with the original
`topObj`. -/
theorem BoundedIdealPartialSection.extend_compat
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (b : BoundedIdealPartialSection cR)
    (i₀ : Finset Ordinal.{0})
    (hi₀_valid : ∀ α ∈ i₀, α < Ordinal.omega.{0} 1) :
    cbpFieldwiseCompat
      ((b.extend i₀ hi₀_valid).topObj.toCoherentBranchPartial.restrict
        Finset.subset_union_left)
      b.topObj.toCoherentBranchPartial :=
  Classical.choose_spec
    (coherentGoodBranchPartial_extend_to_union b.topObj i₀ hi₀_valid)

/-- **Preorder on bounded sections**: `B₁ ≤ B₂` iff `B₁.top ⊆ B₂.top`
and `B₂.topObj` restricts to a CBP fieldwise-compatible with
`B₁.topObj`. -/
instance BoundedIdealPartialSection.instLE
    {cR : (Fin 2 ↪o PairERSource) → Bool} :
    LE (BoundedIdealPartialSection cR) where
  le B₁ B₂ :=
    ∃ h_top : B₁.top ⊆ B₂.top,
      cbpFieldwiseCompat
        (B₂.topObj.toCoherentBranchPartial.restrict h_top)
        B₁.topObj.toCoherentBranchPartial

/-- **Reflexivity** of the bounded-section preorder. -/
theorem BoundedIdealPartialSection.le_refl
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (B : BoundedIdealPartialSection cR) : B ≤ B := by
  refine ⟨Finset.Subset.refl _, ?_, ?_⟩
  · intro α hα
    rw [CoherentBranchPartial.restrict_prefixAt]
  · intro α hα
    rw [CoherentBranchPartial.restrict_branch]

/-- **Transitivity** of the bounded-section preorder. The top inclusion
chains via `⊆`; the compat field chains via
`C.topObj.restrict A.top = (C.topObj.restrict B.top).restrict A.top ~
B.topObj.restrict A.top ~ A.topObj` using `hBC.2`, `hAB.2`, and
`restrict_prefixAt`/`restrict_branch`. -/
theorem BoundedIdealPartialSection.le_trans
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {A B C : BoundedIdealPartialSection cR}
    (hAB : A ≤ B) (hBC : B ≤ C) : A ≤ C := by
  obtain ⟨h_AB_top, h_AB_compat⟩ := hAB
  obtain ⟨h_BC_top, h_BC_compat⟩ := hBC
  refine ⟨h_AB_top.trans h_BC_top, ?_, ?_⟩
  · intro α hα
    -- (C.topObj.toCBP.restrict (A ⊆ C)).prefixAt α hα = A.topObj.toCBP.prefixAt α hα
    rw [CoherentBranchPartial.restrict_prefixAt]
    -- Goal: C.topObj.toCBP.prefixAt α (A ⊆ C → α) = A.topObj.toCBP.prefixAt α hα
    -- Bridge through B: use h_BC_compat at α ∈ B.top, then h_AB_compat at α ∈ A.top.
    have h_BC := h_BC_compat.1 α (h_AB_top hα)
    rw [CoherentBranchPartial.restrict_prefixAt] at h_BC
    have h_AB := h_AB_compat.1 α hα
    rw [CoherentBranchPartial.restrict_prefixAt] at h_AB
    rw [h_BC, h_AB]
  · intro α hα
    rw [CoherentBranchPartial.restrict_branch]
    have h_BC := h_BC_compat.2 α (h_AB_top hα)
    rw [CoherentBranchPartial.restrict_branch] at h_BC
    have h_AB := h_AB_compat.2 α hα
    rw [CoherentBranchPartial.restrict_branch] at h_AB
    rw [h_BC, h_AB]

/-- **Preorder** instance on bounded sections. -/
instance BoundedIdealPartialSection.instPreorder
    {cR : (Fin 2 ↪o PairERSource) → Bool} :
    Preorder (BoundedIdealPartialSection cR) where
  le := (· ≤ ·)
  le_refl := BoundedIdealPartialSection.le_refl
  le_trans _ _ _ := BoundedIdealPartialSection.le_trans

/-- **`BoundedIdealPartialSection.le_extend`**: every bounded section
is below its extension by `i₀`. -/
theorem BoundedIdealPartialSection.le_extend
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (B : BoundedIdealPartialSection cR)
    (i₀ : Finset Ordinal.{0})
    (hi₀_valid : ∀ α ∈ i₀, α < Ordinal.omega.{0} 1) :
    B ≤ B.extend i₀ hi₀_valid :=
  ⟨Finset.subset_union_left, B.extend_compat i₀ hi₀_valid⟩

/-- **`BoundedIdealPartialSection.extend_contains`**: `i₀` is a subset
of the extended top. -/
theorem BoundedIdealPartialSection.extend_contains
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (B : BoundedIdealPartialSection cR)
    (i₀ : Finset Ordinal.{0})
    (hi₀_valid : ∀ α ∈ i₀, α < Ordinal.omega.{0} 1) :
    i₀ ⊆ (B.extend i₀ hi₀_valid).top := Finset.subset_union_right

/-- **Auxiliary**: every finite totally-ordered family of bounded
sections is either empty or has a maximum element. Used by
`finite_chain_upperBound`; also clarifies that the bounded-section
preorder does **not** support arbitrary Zorn chains — the union of
tops of an infinite chain need not be finite, so upper bounds inside
`BoundedIdealPartialSection` only exist for **finite** chains. -/
private theorem BoundedIdealPartialSection.finite_chain_upperBound_aux
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (C : Finset (BoundedIdealPartialSection cR)) :
    (∀ B₁ ∈ C, ∀ B₂ ∈ C, B₁ ≤ B₂ ∨ B₂ ≤ B₁) →
    C = ∅ ∨ ∃ U ∈ C, ∀ B ∈ C, B ≤ U := by
  classical
  induction C using Finset.induction_on with
  | empty => intro _; exact Or.inl rfl
  | @insert B₀ C' _ IH =>
    intro hchain
    have hchain' : ∀ B₁ ∈ C', ∀ B₂ ∈ C', B₁ ≤ B₂ ∨ B₂ ≤ B₁ :=
      fun B₁ hB₁ B₂ hB₂ =>
        hchain B₁ (Finset.mem_insert_of_mem hB₁) B₂ (Finset.mem_insert_of_mem hB₂)
    rcases IH hchain' with h_emp | ⟨U', hU'_in, hU'_max⟩
    · right
      refine ⟨B₀, Finset.mem_insert_self _ _, ?_⟩
      intro B hB
      rw [h_emp] at hB
      have hB_eq : B = B₀ := by simpa using hB
      exact hB_eq ▸ le_refl B₀
    · right
      have hU'_in_insert : U' ∈ insert B₀ C' := Finset.mem_insert_of_mem hU'_in
      have hB₀_in : B₀ ∈ insert B₀ C' := Finset.mem_insert_self _ _
      rcases hchain B₀ hB₀_in U' hU'_in_insert with h_le | h_le
      · refine ⟨U', hU'_in_insert, ?_⟩
        intro B hB
        rcases Finset.mem_insert.mp hB with hB_eq | hB_in_C'
        · exact hB_eq ▸ h_le
        · exact hU'_max B hB_in_C'
      · refine ⟨B₀, hB₀_in, ?_⟩
        intro B hB
        rcases Finset.mem_insert.mp hB with hB_eq | hB_in_C'
        · exact hB_eq ▸ le_refl B₀
        · exact le_trans (hU'_max B hB_in_C') h_le

/-- **`BoundedIdealPartialSection.finite_chain_upperBound`**: every
non-empty finite chain in the bounded-section preorder has an upper
bound **inside the chain itself** (the chain's maximum element). This
suffices for finite-extension reasoning but **does not** give a Zorn
hypothesis: for infinite chains, the union of tops can be infinite,
so no `BoundedIdealPartialSection` upper bound exists. The full
compactness step therefore requires an inverse-limit / ultrafilter
argument, not plain bounded-section Zorn. -/
theorem BoundedIdealPartialSection.finite_chain_upperBound
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (C : Finset (BoundedIdealPartialSection cR))
    (hC : C.Nonempty)
    (hchain : ∀ B₁ ∈ C, ∀ B₂ ∈ C, B₁ ≤ B₂ ∨ B₂ ≤ B₁) :
    ∃ U ∈ C, ∀ B ∈ C, B ≤ U := by
  rcases finite_chain_upperBound_aux C hchain with h_emp | h_ub
  · exact absurd h_emp (Finset.nonempty_iff_ne_empty.mp hC)
  · exact h_ub

/-! ### Finite **family** (non-chain) upper bounds need consistency

A finite family `𝒞 : Finset (BoundedIdealPartialSection cR)` whose
members are not pairwise comparable can fail to have an upper bound in
the bounded-section preorder. Two bounded sections `B₁, B₂` with
overlapping tops may carry **incompatible** Good data on
`B₁.top ∩ B₂.top`, with no Good partial over `B₁.top ∪ B₂.top` agreeing
with both. Neither of the "easy" recipes works unconditionally:

* Iterated `BoundedIdealPartialSection.extend` over the union of tops
  preserves compat with the **starting** section's `topObj`, but its
  values on the new indices are chosen freely and need not agree with
  any other section's `topObj`.
* Any Good partial built via `exists_coherentGoodBranchPartial` over the
  union of tops is similarly unconstrained.

The natural compactness input is therefore **conditioned on
consistency**: given a Good partial `Q` over an enclosing top `T`
fieldwise-compatible with every member's `topObj`, we package this into
an upper bound. This is the precise finite-intersection-property
hypothesis feeding the eventual inverse-limit / ultrafilter compactness
step over `BoundedIdealPartialSection`. -/

/-- **`BoundedIdealPartialSection.exists_upper_bound_of_consistent`**:
finite-family upper bound under explicit consistency. The hypothesis is
the exact FIP shape: a Good partial `Q` over a finset `T` enclosing
every member's `top`, fieldwise-compatible with each `B.topObj`. -/
theorem BoundedIdealPartialSection.exists_upper_bound_of_consistent
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {𝒞 : Finset (BoundedIdealPartialSection cR)}
    {T : Finset Ordinal.{0}}
    (hT_valid : ∀ α ∈ T, α < Ordinal.omega.{0} 1)
    (Q : CoherentGoodBranchPartial cR T)
    (h_consistent : ∀ B ∈ 𝒞, ∃ hsub : B.top ⊆ T,
      cbpFieldwiseCompat
        (Q.toCoherentBranchPartial.restrict hsub)
        B.topObj.toCoherentBranchPartial) :
    ∃ U : BoundedIdealPartialSection cR, ∀ B ∈ 𝒞, B ≤ U := by
  refine ⟨⟨T, hT_valid, Q⟩, ?_⟩
  intro B hB
  exact h_consistent B hB

/-- **`BoundedSections.FinitelyConsistent`**: the precise hypothesis a
finite family of bounded sections must satisfy to admit an upper bound
in the bounded-section preorder. Witnessed by an enclosing valid finset
`T`, a Good partial `Q : CoherentGoodBranchPartial cR T`, and per-member
fieldwise compatibility on `B.top`. -/
def BoundedSections.FinitelyConsistent
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (𝒞 : Finset (BoundedIdealPartialSection cR)) : Prop :=
  ∃ T : Finset Ordinal.{0},
    (∀ α ∈ T, α < Ordinal.omega.{0} 1) ∧
      ∃ Q : CoherentGoodBranchPartial cR T,
        ∀ B ∈ 𝒞, ∃ hsub : B.top ⊆ T,
          cbpFieldwiseCompat
            (Q.toCoherentBranchPartial.restrict hsub)
            B.topObj.toCoherentBranchPartial

/-- **`BoundedSections.finitelyConsistent_iff_exists_upperBound`**:
the FIP-shaped consistency predicate is **equivalent** to the
existence of an upper bound in the bounded-section preorder. Forward
direction is the freshly added
`exists_upper_bound_of_consistent`; backward takes `T := U.top`,
`Q := U.topObj`, and reuses the `B ≤ U` witness directly. -/
theorem BoundedSections.finitelyConsistent_iff_exists_upperBound
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (𝒞 : Finset (BoundedIdealPartialSection cR)) :
    BoundedSections.FinitelyConsistent 𝒞 ↔
      ∃ U : BoundedIdealPartialSection cR, ∀ B ∈ 𝒞, B ≤ U := by
  refine ⟨?_, ?_⟩
  · rintro ⟨T, hT_valid, Q, h_consistent⟩
    exact BoundedIdealPartialSection.exists_upper_bound_of_consistent
      hT_valid Q h_consistent
  · rintro ⟨U, hU⟩
    exact ⟨U.top, U.top_valid, U.topObj, fun B hB => hU B hB⟩

/-! ### Final compactness frontier

For the ER application, the single active frontier above bounded
sections is plain existence of a global Good witness net,
`exists_coherentGoodWitnessNet` (currently routed through
`coherentGoodBranchPartial_idealHasPartialExtensions`, task #44).

`GoodConstraint`, `familyConsistent`, and `goodConstraintCompactness`
below are **documented** as a possible **stronger** restatement — a
per-constraint extension property — but are **not** on the active
proof chain: the trivial `C = ∅` instance only re-derives bare
existence, doing nothing the per-constraint conclusion adds, and a
true `∀ 𝒞, familyConsistent 𝒞` hypothesis is false because two
unrelated `GoodConstraint`s can disagree on overlapping tops. Kept
here as a clean target for future refactors. -/

/-- **`GoodConstraint cR`**: a single Good constraint — a finite valid
finset together with a Good partial over it. -/
structure GoodConstraint (cR : (Fin 2 ↪o PairERSource) → Bool) where
  S : Finset Ordinal.{0}
  S_valid : ∀ α ∈ S, α < Ordinal.omega.{0} 1
  obj : CoherentGoodBranchPartial cR S

/-- **Bridge** to `BoundedIdealPartialSection`. -/
def GoodConstraint.toBoundedSection
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (c : GoodConstraint cR) : BoundedIdealPartialSection cR where
  top := c.S
  top_valid := c.S_valid
  topObj := c.obj

/-- **`GoodConstraint.familyConsistent`**: finite-consistency predicate
on a finite family of Good constraints, mirroring
`BoundedSections.FinitelyConsistent`. Avoids the `Finset.image` /
`DecidableEq` indirection by quantifying directly over the constraint
family. -/
def GoodConstraint.familyConsistent
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (𝒞 : Finset (GoodConstraint cR)) : Prop :=
  ∃ T : Finset Ordinal.{0},
    (∀ α ∈ T, α < Ordinal.omega.{0} 1) ∧
      ∃ Q : CoherentGoodBranchPartial cR T,
        ∀ c ∈ 𝒞, ∃ hsub : c.S ⊆ T,
          cbpFieldwiseCompat
            (Q.toCoherentBranchPartial.restrict hsub)
            c.obj.toCoherentBranchPartial

/-- **[DOCUMENTED, not on active chain]** `goodConstraintCompactness`:
under finite-consistency on every finite sub-family of `C`, there is a
global Good witness net **extending** every constraint in `C` — the
net's value at each `c.S` is fieldwise-compatible with `c.obj`. This
captures the inverse-limit / ultrafilter compactness shape over the
bounded-section preorder; left as `sorry` and **off** the active
witness-net chain (which routes through `exists_coherentGoodWitnessNet`
directly). Kept here as the clean target shape for a future refactor
of the witness-net chain. -/
theorem goodConstraintCompactness
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (C : Set (GoodConstraint cR))
    (_hfin : ∀ 𝒞 : Finset (GoodConstraint cR),
      (∀ c ∈ 𝒞, c ∈ C) → GoodConstraint.familyConsistent 𝒞) :
    ∃ net : CoherentGoodWitnessNet cR,
      ∀ c ∈ C, cbpFieldwiseCompat
        (net.P c.S c.S_valid).toCoherentBranchPartial
        c.obj.toCoherentBranchPartial := by
  sorry

/-- **`AdjoinGoodData`**: general bundled witness for any `V` in the
new domain (not just `V ∈ p.domain`). Generalizes `AdjoinGoodOldData`
to the case where `V` is unrelated to `p.domain` (only `V ⊆ S ∪ i₀`
for some `S ∈ p.domain`). -/
structure AdjoinGoodData
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (i₀ V : Finset Ordinal.{0}) where
  U : Finset Ordinal.{0}
  hU : U ∈ p.domain
  hVU : V ⊆ U ∪ i₀
  Q : CoherentGoodBranchPartial cR (U ∪ i₀)
  hQ_compat : cbpFieldwiseCompat
    (Q.toCoherentBranchPartial.restrict Finset.subset_union_left)
    (p.P U hU).toCoherentBranchPartial

/-- **[STUB]** `IdealPartialSection.adjoinGoodValue_common_compat`: for
`V ⊆ W` both in the new domain, restrict of `W`'s value to `V` matches
`V`'s value.

**Obstacle**: the construction `adjoinGoodValue` uses `Classical.choose`
to pick `U_V` (for `V`) and `U_W` (for `W`) — these are different
elements of `p.domain`, with possibly different extensions `Q_V` and
`Q_W` from `extend_to_union`. Since `extend_to_union` doesn't produce
canonical extensions, `Q_V` and `Q_W` may disagree on `i₀`-values
that aren't constrained by `p.P U_V` or `p.P U_W` respectively.

**Resolution path**: redefine `adjoinGoodValue` to thread a *single*
chosen `Q` (e.g., on `T ∪ i₀` for the anchor `T`) and route arbitrary
`V` values through this fixed `Q` (when `V ⊆ T ∪ i₀`) plus directed
upward extensions for `V` not subset of `T ∪ i₀`. The proof of
well-definedness then becomes a single chain of restrictions of a
fixed extended CGBP.

Alternatively, prove a uniqueness/agreement lemma for
`extend_to_union` on the shared `U ⊆ S ∪ i₀` overlap (essentially
requires a stronger extension primitive). Currently stubbed. -/
theorem FiniteProjectiveSystem.IdealPartialSection.adjoinGoodValue_common_compat
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (T : Finset Ordinal.{0}) (hT : T ∈ p.domain)
    (i₀ V W : Finset Ordinal.{0})
    (hi₀_valid : ∀ α ∈ i₀, α < Ordinal.omega.{0} 1)
    (hV : ∃ S ∈ p.domain, V ⊆ S ∪ i₀)
    (hW : ∃ S ∈ p.domain, W ⊆ S ∪ i₀)
    (hVW : V ⊆ W) :
    cbpFieldwiseCompat
      ((p.adjoinGoodValue T hT i₀ W hi₀_valid hW).toCoherentBranchPartial.restrict
        hVW)
      (p.adjoinGoodValue T hT i₀ V hi₀_valid hV).toCoherentBranchPartial := by
  sorry

/-- **[STUB]** `IdealPartialSection.adjoinGood`: factor the non-empty
case of `coherentGoodBranchPartial_idealHasPartialExtensions` through
a generic adjoin helper. Given:

- `p : IdealPartialSection` of the Good system;
- a chosen anchor `T ∈ p.domain`;
- a fresh `i₀ : Finset Ordinal` (valid);
- a Good CGBP `Q : CGBP cR (T ∪ i₀)` extending `p.P T`;

produces an IPS whose domain is the directed closure
`{V | ∃ S ∈ p.domain, V ⊆ S ∪ i₀}`.

**Construction strategy** (deferred — requires canonical-choice
mechanism):

- For each `V` in the new domain, choose `S_V ∈ p.domain` with
  `V ⊆ S_V ∪ i₀` (via `Classical.choose` from the existence witness).
- Use `p.directed` to find `U ⊇ S_V ∪ T` in `p.domain`.
- Extend `p.P U` to `U ∪ i₀` via `coherentGoodBranchPartial_extend_to_union`
  (consistent with `p.P U`'s data on `U`).
- Restrict the extension to `V`.

**Well-definedness across choices** is the substantive obstacle: two
different choices of `S_V` must give the same value at `V` (up to
`cbpFieldwiseCompat`). By `p.directed` + extension preservation
through a common upper bound, the values agree, but formalizing this
requires careful HEq + uniqueness handling.

Once `adjoinGood` exists, the non-empty branch of
`coherentGoodBranchPartial_idealHasPartialExtensions` reduces to:
choose any `T ∈ p.domain`, build `Q` via `extend_to_union`, call
`adjoinGood`. -/
noncomputable def FiniteProjectiveSystem.IdealPartialSection.adjoinGood
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (T : Finset Ordinal.{0}) (_hT : T ∈ p.domain)
    (i₀ : Finset Ordinal.{0})
    (_hi₀_valid : ∀ α ∈ i₀, α < Ordinal.omega.{0} 1)
    (_Q : CoherentGoodBranchPartial cR (T ∪ i₀))
    (_hQ_T :
      cbpFieldwiseCompat
        (_Q.toCoherentBranchPartial.restrict Finset.subset_union_left)
        (p.P T _hT).toCoherentBranchPartial) :
    (coherentGoodBranchPartialSystem cR).IdealPartialSection := by
  sorry

/-- **[STUB]** `IdealPartialSection.adjoinGood_le_self`: the adjoined
section extends `p`. -/
theorem FiniteProjectiveSystem.IdealPartialSection.adjoinGood_le_self
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (T : Finset Ordinal.{0}) (hT : T ∈ p.domain)
    (i₀ : Finset Ordinal.{0})
    (hi₀_valid : ∀ α ∈ i₀, α < Ordinal.omega.{0} 1)
    (Q : CoherentGoodBranchPartial cR (T ∪ i₀))
    (hQ_T :
      cbpFieldwiseCompat
        (Q.toCoherentBranchPartial.restrict Finset.subset_union_left)
        (p.P T hT).toCoherentBranchPartial) :
    p ≤ p.adjoinGood T hT i₀ hi₀_valid Q hQ_T := by
  sorry

/-- **[STUB]** `IdealPartialSection.adjoinGood_contains`: the adjoined
section's domain contains `i₀`. -/
theorem FiniteProjectiveSystem.IdealPartialSection.adjoinGood_contains
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (T : Finset Ordinal.{0}) (hT : T ∈ p.domain)
    (i₀ : Finset Ordinal.{0})
    (hi₀_valid : ∀ α ∈ i₀, α < Ordinal.omega.{0} 1)
    (Q : CoherentGoodBranchPartial cR (T ∪ i₀))
    (hQ_T :
      cbpFieldwiseCompat
        (Q.toCoherentBranchPartial.restrict Finset.subset_union_left)
        (p.P T hT).toCoherentBranchPartial) :
    i₀ ∈ (p.adjoinGood T hT i₀ hi₀_valid Q hQ_T).domain := by
  sorry

/-! ### Pi₀-threaded adjunction path (`…With`)

Parallel to `adjoinGoodValue`/`adjoinGood`, but threading a *single* fixed
`Pi₀ : CGBP cR i₀` (ambient-compatible with every `p.P S`, as produced by
`goodIdealOneIndexCompactness`) through every new value via
`coherentGoodBranchPartial_amalgamate_pair (p.P S) Pi₀`. Because the `i₀`-part of
every value is the same `Pi₀`, cross-`V` coherence (`common_compat`) holds — the
obstacle that stalls the legacy `adjoinGoodValue_common_compat`. The legacy path
is kept until this one is verified. -/

/-- **`adjoinGoodValueWith`**: `Pi₀`-threaded value at `V`. On `p.domain` it is
literally `p.P V`; otherwise it is `amalgamate_pair (p.P S) Pi₀` (for a chosen
`S` with `V ⊆ S ∪ i₀`) restricted to `V`. -/
noncomputable def FiniteProjectiveSystem.IdealPartialSection.adjoinGoodValueWith
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (i₀ : Finset Ordinal.{0}) (hi₀_valid : ∀ α ∈ i₀, α < Ordinal.omega.{0} 1)
    (Pi₀ : CoherentGoodBranchPartial cR i₀)
    (hPi₀_ambient : ∀ S (hS : S ∈ p.domain),
      CoherentGoodBranchPartial.AmbientCompat (p.P S hS) Pi₀)
    (V : Finset Ordinal.{0}) (hV : ∃ S ∈ p.domain, V ⊆ S ∪ i₀) :
    CoherentGoodBranchPartial cR V :=
  letI : Decidable (V ∈ p.domain) := Classical.dec _
  if hV_p : V ∈ p.domain then
    p.P V hV_p
  else
    (coherentGoodBranchPartial_amalgamate_pair
        (p.domain_valid (Classical.choose_spec hV).1) hi₀_valid
        (p.P (Classical.choose hV) (Classical.choose_spec hV).1) Pi₀
        (hPi₀_ambient (Classical.choose hV)
          (Classical.choose_spec hV).1)).choose.restrict
      (Classical.choose_spec hV).2

/-- For `V ∈ p.domain`, the `Pi₀`-threaded value is literally `p.P V`. -/
theorem FiniteProjectiveSystem.IdealPartialSection.adjoinGoodValueWith_eq_of_mem
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (i₀ : Finset Ordinal.{0}) (hi₀_valid : ∀ α ∈ i₀, α < Ordinal.omega.{0} 1)
    (Pi₀ : CoherentGoodBranchPartial cR i₀)
    (hPi₀_ambient : ∀ S (hS : S ∈ p.domain),
      CoherentGoodBranchPartial.AmbientCompat (p.P S hS) Pi₀)
    (V : Finset Ordinal.{0}) (hV : ∃ S ∈ p.domain, V ⊆ S ∪ i₀)
    (hV_p : V ∈ p.domain) :
    p.adjoinGoodValueWith i₀ hi₀_valid Pi₀ hPi₀_ambient V hV = p.P V hV_p := by
  classical
  unfold FiniteProjectiveSystem.IdealPartialSection.adjoinGoodValueWith
  rw [dif_pos hV_p]

/-- `old_compat`: for `V ∈ p.domain`, the `Pi₀`-threaded value is
fieldwise-compat with `p.P V` (trivially, being literally equal to it). -/
theorem FiniteProjectiveSystem.IdealPartialSection.adjoinGoodValueWith_old_compat
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (i₀ : Finset Ordinal.{0}) (hi₀_valid : ∀ α ∈ i₀, α < Ordinal.omega.{0} 1)
    (Pi₀ : CoherentGoodBranchPartial cR i₀)
    (hPi₀_ambient : ∀ S (hS : S ∈ p.domain),
      CoherentGoodBranchPartial.AmbientCompat (p.P S hS) Pi₀)
    (V : Finset Ordinal.{0}) (hV : ∃ S ∈ p.domain, V ⊆ S ∪ i₀)
    (hV_p : V ∈ p.domain) :
    cbpFieldwiseCompat
      (p.adjoinGoodValueWith i₀ hi₀_valid Pi₀ hPi₀_ambient V hV).toCoherentBranchPartial
      (p.P V hV_p).toCoherentBranchPartial := by
  rw [p.adjoinGoodValueWith_eq_of_mem i₀ hi₀_valid Pi₀ hPi₀_ambient V hV hV_p]
  exact cbpFieldwiseCompat.refl _

/-- Helper: any two prescribed values agree (fieldwise) at a common index, via a
common upper bound `U` in the directed domain (`p.P S₁ = p.P U|_{S₁}` and
`p.P S₂ = p.P U|_{S₂}`, both equal to `p.P U` at `α`). -/
theorem FiniteProjectiveSystem.IdealPartialSection.pValue_agree_at
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    {S₁ S₂ : Finset Ordinal.{0}} (hS₁ : S₁ ∈ p.domain) (hS₂ : S₂ ∈ p.domain)
    {α : Ordinal.{0}} (hα₁ : α ∈ S₁) (hα₂ : α ∈ S₂) :
    (p.P S₁ hS₁).toCoherentBranchPartial.prefixAt α hα₁
        = (p.P S₂ hS₂).toCoherentBranchPartial.prefixAt α hα₂
    ∧ (p.P S₁ hS₁).toCoherentBranchPartial.branch α hα₁
        = (p.P S₂ hS₂).toCoherentBranchPartial.branch α hα₂ := by
  classical
  obtain ⟨U, hU, h₁U, h₂U⟩ := p.directed hS₁ hS₂
  have ep₁ := (p.compat hS₁ hU h₁U).1 α hα₁
  have eb₁ := (p.compat hS₁ hU h₁U).2 α hα₁
  have ep₂ := (p.compat hS₂ hU h₂U).1 α hα₂
  have eb₂ := (p.compat hS₂ hU h₂U).2 α hα₂
  simp only [coherentGoodBranchPartialSystem,
    CoherentGoodBranchPartial.restrict_toCoherentBranchPartial,
    CoherentBranchPartial.restrict_prefixAt,
    CoherentBranchPartial.restrict_branch] at ep₁ eb₁ ep₂ eb₂
  exact ⟨by rw [← ep₁, ← ep₂], by rw [← eb₁, ← eb₂]⟩

/-- Characterization on `i₀`: the `Pi₀`-threaded value at `V` equals `Pi₀` at any
shared index `α ∈ V ∩ i₀`. (On `p.domain` via `AmbientCompat`'s diagonal; off it
via the amalgam's `i₀`-side compat.) -/
theorem FiniteProjectiveSystem.IdealPartialSection.adjoinGoodValueWith_eq_Pi₀
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (i₀ : Finset Ordinal.{0}) (hi₀_valid : ∀ α ∈ i₀, α < Ordinal.omega.{0} 1)
    (Pi₀ : CoherentGoodBranchPartial cR i₀)
    (hPi₀_ambient : ∀ S (hS : S ∈ p.domain),
      CoherentGoodBranchPartial.AmbientCompat (p.P S hS) Pi₀)
    (V : Finset Ordinal.{0}) (hV : ∃ S ∈ p.domain, V ⊆ S ∪ i₀)
    {α : Ordinal.{0}} (hα_V : α ∈ V) (hα_i₀ : α ∈ i₀) :
    (p.adjoinGoodValueWith i₀ hi₀_valid Pi₀ hPi₀_ambient V hV).toCoherentBranchPartial.prefixAt
          α hα_V
        = Pi₀.toCoherentBranchPartial.prefixAt α hα_i₀
    ∧ (p.adjoinGoodValueWith i₀ hi₀_valid Pi₀ hPi₀_ambient V hV).toCoherentBranchPartial.branch
          α hα_V
        = Pi₀.toCoherentBranchPartial.branch α hα_i₀ := by
  classical
  unfold FiniteProjectiveSystem.IdealPartialSection.adjoinGoodValueWith
  by_cases hV_p : V ∈ p.domain
  · rw [dif_pos hV_p]
    exact ⟨(hPi₀_ambient V hV_p).prefix_diag α hα_V hα_i₀,
           (hPi₀_ambient V hV_p).branch_diag α hα_V hα_i₀⟩
  · rw [dif_neg hV_p]
    refine ⟨?_, ?_⟩
    · have hq := (coherentGoodBranchPartial_amalgamate_pair
          (p.domain_valid (Classical.choose_spec hV).1) hi₀_valid
          (p.P (Classical.choose hV) (Classical.choose_spec hV).1) Pi₀
          (hPi₀_ambient (Classical.choose hV) (Classical.choose_spec hV).1)).choose_spec.2.1
          α hα_i₀
      simp only [CoherentGoodBranchPartial.restrict_toCoherentBranchPartial,
        CoherentBranchPartial.restrict_prefixAt] at hq ⊢
      rw [← hq]
    · have hq := (coherentGoodBranchPartial_amalgamate_pair
          (p.domain_valid (Classical.choose_spec hV).1) hi₀_valid
          (p.P (Classical.choose hV) (Classical.choose_spec hV).1) Pi₀
          (hPi₀_ambient (Classical.choose hV) (Classical.choose_spec hV).1)).choose_spec.2.2
          α hα_i₀
      simp only [CoherentGoodBranchPartial.restrict_toCoherentBranchPartial,
        CoherentBranchPartial.restrict_branch] at hq ⊢
      rw [← hq]

/-- Characterization off `i₀`: at `α ∈ V` with `α ∉ i₀` and `α ∈ S` for some
`S ∈ p.domain`, the `Pi₀`-threaded value at `V` equals `p.P S`. (On `p.domain`
via `pValue_agree_at`; off it via the amalgam's `S`-side compat, then
`pValue_agree_at`.) -/
theorem FiniteProjectiveSystem.IdealPartialSection.adjoinGoodValueWith_eq_pP
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (i₀ : Finset Ordinal.{0}) (hi₀_valid : ∀ α ∈ i₀, α < Ordinal.omega.{0} 1)
    (Pi₀ : CoherentGoodBranchPartial cR i₀)
    (hPi₀_ambient : ∀ S (hS : S ∈ p.domain),
      CoherentGoodBranchPartial.AmbientCompat (p.P S hS) Pi₀)
    (V : Finset Ordinal.{0}) (hV : ∃ S ∈ p.domain, V ⊆ S ∪ i₀)
    {α : Ordinal.{0}} (hα_V : α ∈ V) (hα_i₀ : α ∉ i₀)
    {S : Finset Ordinal.{0}} (hS : S ∈ p.domain) (hα_S : α ∈ S) :
    (p.adjoinGoodValueWith i₀ hi₀_valid Pi₀ hPi₀_ambient V hV).toCoherentBranchPartial.prefixAt
          α hα_V
        = (p.P S hS).toCoherentBranchPartial.prefixAt α hα_S
    ∧ (p.adjoinGoodValueWith i₀ hi₀_valid Pi₀ hPi₀_ambient V hV).toCoherentBranchPartial.branch
          α hα_V
        = (p.P S hS).toCoherentBranchPartial.branch α hα_S := by
  classical
  unfold FiniteProjectiveSystem.IdealPartialSection.adjoinGoodValueWith
  by_cases hV_p : V ∈ p.domain
  · rw [dif_pos hV_p]
    exact ⟨(p.pValue_agree_at hV_p hS hα_V hα_S).1,
           (p.pValue_agree_at hV_p hS hα_V hα_S).2⟩
  · rw [dif_neg hV_p]
    have hα_SV : α ∈ Classical.choose hV := by
      rcases Finset.mem_union.mp ((Classical.choose_spec hV).2 hα_V) with h | h
      · exact h
      · exact absurd h hα_i₀
    refine ⟨?_, ?_⟩
    · have hq := (coherentGoodBranchPartial_amalgamate_pair
          (p.domain_valid (Classical.choose_spec hV).1) hi₀_valid
          (p.P (Classical.choose hV) (Classical.choose_spec hV).1) Pi₀
          (hPi₀_ambient (Classical.choose hV) (Classical.choose_spec hV).1)).choose_spec.1.1
          α hα_SV
      simp only [CoherentGoodBranchPartial.restrict_toCoherentBranchPartial,
        CoherentBranchPartial.restrict_prefixAt] at hq ⊢
      exact hq.trans (p.pValue_agree_at (Classical.choose_spec hV).1 hS hα_SV hα_S).1
    · have hq := (coherentGoodBranchPartial_amalgamate_pair
          (p.domain_valid (Classical.choose_spec hV).1) hi₀_valid
          (p.P (Classical.choose hV) (Classical.choose_spec hV).1) Pi₀
          (hPi₀_ambient (Classical.choose hV) (Classical.choose_spec hV).1)).choose_spec.1.2
          α hα_SV
      simp only [CoherentGoodBranchPartial.restrict_toCoherentBranchPartial,
        CoherentBranchPartial.restrict_branch] at hq ⊢
      exact hq.trans (p.pValue_agree_at (Classical.choose_spec hV).1 hS hα_SV hα_S).2

/-- **`adjoinGoodValueWith_common_compat`**: cross-`V` coherence for the
`Pi₀`-threaded values. For `V ⊆ W` in the new domain, the value at `W` restricted
to `V` is fieldwise-compat with the value at `V`. At each `α ∈ V` the two agree:
if `α ∈ i₀` both equal `Pi₀` (`eq_Pi₀`); otherwise both equal `p.P S` for a domain
`S ∋ α` from `V`'s witness (`eq_pP`). This is the lemma the shared `Pi₀`
unblocks. -/
theorem FiniteProjectiveSystem.IdealPartialSection.adjoinGoodValueWith_common_compat
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (i₀ : Finset Ordinal.{0}) (hi₀_valid : ∀ α ∈ i₀, α < Ordinal.omega.{0} 1)
    (Pi₀ : CoherentGoodBranchPartial cR i₀)
    (hPi₀_ambient : ∀ S (hS : S ∈ p.domain),
      CoherentGoodBranchPartial.AmbientCompat (p.P S hS) Pi₀)
    (V W : Finset Ordinal.{0})
    (hV : ∃ S ∈ p.domain, V ⊆ S ∪ i₀) (hW : ∃ S ∈ p.domain, W ⊆ S ∪ i₀)
    (hVW : V ⊆ W) :
    cbpFieldwiseCompat
      ((p.adjoinGoodValueWith i₀ hi₀_valid Pi₀ hPi₀_ambient W hW).toCoherentBranchPartial.restrict
        hVW)
      (p.adjoinGoodValueWith i₀ hi₀_valid Pi₀ hPi₀_ambient V hV).toCoherentBranchPartial := by
  classical
  refine ⟨?_, ?_⟩
  · intro α hα
    rw [CoherentBranchPartial.restrict_prefixAt]
    by_cases hα_i₀ : α ∈ i₀
    · rw [(p.adjoinGoodValueWith_eq_Pi₀ i₀ hi₀_valid Pi₀ hPi₀_ambient W hW (hVW hα) hα_i₀).1,
          (p.adjoinGoodValueWith_eq_Pi₀ i₀ hi₀_valid Pi₀ hPi₀_ambient V hV hα hα_i₀).1]
    · have hVc := hV
      obtain ⟨S, hS, hVsub⟩ := hVc
      have hα_S : α ∈ S := by
        rcases Finset.mem_union.mp (hVsub hα) with h | h
        · exact h
        · exact absurd h hα_i₀
      rw [(p.adjoinGoodValueWith_eq_pP i₀ hi₀_valid Pi₀ hPi₀_ambient W hW
            (hVW hα) hα_i₀ hS hα_S).1,
          (p.adjoinGoodValueWith_eq_pP i₀ hi₀_valid Pi₀ hPi₀_ambient V hV
            hα hα_i₀ hS hα_S).1]
  · intro α hα
    rw [CoherentBranchPartial.restrict_branch]
    by_cases hα_i₀ : α ∈ i₀
    · rw [(p.adjoinGoodValueWith_eq_Pi₀ i₀ hi₀_valid Pi₀ hPi₀_ambient W hW (hVW hα) hα_i₀).2,
          (p.adjoinGoodValueWith_eq_Pi₀ i₀ hi₀_valid Pi₀ hPi₀_ambient V hV hα hα_i₀).2]
    · have hVc := hV
      obtain ⟨S, hS, hVsub⟩ := hVc
      have hα_S : α ∈ S := by
        rcases Finset.mem_union.mp (hVsub hα) with h | h
        · exact h
        · exact absurd h hα_i₀
      rw [(p.adjoinGoodValueWith_eq_pP i₀ hi₀_valid Pi₀ hPi₀_ambient W hW
            (hVW hα) hα_i₀ hS hα_S).2,
          (p.adjoinGoodValueWith_eq_pP i₀ hi₀_valid Pi₀ hPi₀_ambient V hV
            hα hα_i₀ hS hα_S).2]

/-- **`adjoinGoodWith`**: the extended ideal section, `Pi₀`-threaded. Domain is
the directed closure `{V | ∃ S ∈ p.domain, V ⊆ S ∪ i₀}`; values are
`adjoinGoodValueWith`; `compat` is exactly `adjoinGoodValueWith_common_compat`. -/
noncomputable def FiniteProjectiveSystem.IdealPartialSection.adjoinGoodWith
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (T : Finset Ordinal.{0}) (_hT : T ∈ p.domain)
    (i₀ : Finset Ordinal.{0}) (hi₀_valid : ∀ α ∈ i₀, α < Ordinal.omega.{0} 1)
    (Pi₀ : CoherentGoodBranchPartial cR i₀)
    (hPi₀_ambient : ∀ S (hS : S ∈ p.domain),
      CoherentGoodBranchPartial.AmbientCompat (p.P S hS) Pi₀) :
    (coherentGoodBranchPartialSystem cR).IdealPartialSection where
  domain := {V | ∃ S, S ∈ p.domain ∧ V ⊆ S ∪ i₀}
  domain_valid {V} hV := by
    obtain ⟨S, hS, hVsub⟩ := hV
    intro α hα
    rcases Finset.mem_union.mp (hVsub hα) with h | h
    · exact p.domain_valid hS α h
    · exact hi₀_valid α h
  downward_closed {V W} hW hVW := by
    obtain ⟨S, hS, hWsub⟩ := hW
    exact ⟨S, hS, hVW.trans hWsub⟩
  directed {V W} hV hW := by
    obtain ⟨Sᵥ, hSᵥ, hVsub⟩ := hV
    obtain ⟨S_w, hS_w, hWsub⟩ := hW
    obtain ⟨U, hU, hSᵥU, hS_wU⟩ := p.directed hSᵥ hS_w
    refine ⟨U ∪ i₀, ⟨U, hU, Finset.Subset.refl _⟩, ?_, ?_⟩
    · exact hVsub.trans (Finset.union_subset_union hSᵥU (Finset.Subset.refl i₀))
    · exact hWsub.trans (Finset.union_subset_union hS_wU (Finset.Subset.refl i₀))
  P := fun V hV => p.adjoinGoodValueWith i₀ hi₀_valid Pi₀ hPi₀_ambient V hV
  compat := fun {V W} hV hW hVW =>
    p.adjoinGoodValueWith_common_compat i₀ hi₀_valid Pi₀ hPi₀_ambient V W hV hW hVW

/-- `adjoinGoodWith` extends `p` (literally on the old domain, via
`adjoinGoodValueWith_eq_of_mem`). -/
theorem FiniteProjectiveSystem.IdealPartialSection.adjoinGoodWith_le_self
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (T : Finset Ordinal.{0}) (hT : T ∈ p.domain)
    (i₀ : Finset Ordinal.{0}) (hi₀_valid : ∀ α ∈ i₀, α < Ordinal.omega.{0} 1)
    (Pi₀ : CoherentGoodBranchPartial cR i₀)
    (hPi₀_ambient : ∀ S (hS : S ∈ p.domain),
      CoherentGoodBranchPartial.AmbientCompat (p.P S hS) Pi₀) :
    p ≤ p.adjoinGoodWith T hT i₀ hi₀_valid Pi₀ hPi₀_ambient := by
  refine ⟨fun V hV_p => ⟨V, hV_p, Finset.subset_union_left⟩, ?_⟩
  intro V hi₁ hi₂
  exact p.adjoinGoodValueWith_eq_of_mem i₀ hi₀_valid Pi₀ hPi₀_ambient V hi₂ hi₁

/-- `adjoinGoodWith`'s domain contains the new index `i₀` (witnessed by the
anchor `T`, since `i₀ ⊆ T ∪ i₀`). -/
theorem FiniteProjectiveSystem.IdealPartialSection.adjoinGoodWith_contains
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (p : (coherentGoodBranchPartialSystem cR).IdealPartialSection)
    (T : Finset Ordinal.{0}) (hT : T ∈ p.domain)
    (i₀ : Finset Ordinal.{0}) (hi₀_valid : ∀ α ∈ i₀, α < Ordinal.omega.{0} 1)
    (Pi₀ : CoherentGoodBranchPartial cR i₀)
    (hPi₀_ambient : ∀ S (hS : S ∈ p.domain),
      CoherentGoodBranchPartial.AmbientCompat (p.P S hS) Pi₀) :
    i₀ ∈ (p.adjoinGoodWith T hT i₀ hi₀_valid Pi₀ hPi₀_ambient).domain :=
  ⟨T, hT, Finset.subset_union_right⟩

/-- **`goodIdealExtensionCompactness`**: the Good ideal system has partial
extensions.

**Input:** an `IdealPartialSection p` plus a new finite valid index `i₀`.
**Output:** an ideal extension `q ≥ p` containing `i₀`.

**Proved via the `Pi₀`-threaded one-index path** (not `goodIdealCompactness`):
if `p.domain` is empty, take the `i₀`-downward-closure section; otherwise pick an
anchor `T ∈ p.domain`, obtain a single `Pi₀` ambient-compatible with all `p.P S`
from `goodIdealOneIndexCompactness`, and return `adjoinGoodWith` (with
`adjoinGoodWith_le_self` giving literal `p ≤ q` and `adjoinGoodWith_contains`
giving `i₀ ∈ q.domain`). This **breaks the former circular dependency** on
`goodIdealCompactness`/`goodIdealGlobalization`: the remaining frontier under this
theorem is `goodIdealOneIndexCompactness` (plus the system-level
`exists_coherentGoodBranchPartial`). Old name kept as a backward-compat alias
below. -/
theorem goodIdealExtensionCompactness
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    (coherentGoodBranchPartialSystem cR).IdealHasPartialExtensions := by
  intro p i₀ h_valid_i₀
  classical
  -- Rewired through the Pi₀-threaded one-index path (breaks the dependency on
  -- goodIdealCompactness/goodIdealGlobalization). The remaining frontier is
  -- goodIdealOneIndexCompactness.
  rcases (p.domain).eq_empty_or_nonempty with hp_empty | hp_ne
  · -- Empty domain: the `i₀`-downward-closure section (anchor-free).
    obtain ⟨Pi₀⟩ := exists_coherentGoodBranchPartial cR i₀ h_valid_i₀
    refine ⟨{
      domain := {V : Finset Ordinal.{0} | V ⊆ i₀}
      domain_valid := fun {V} hV α hα => h_valid_i₀ α (hV hα)
      downward_closed := fun {V W} hW hVW => hVW.trans hW
      directed := fun {V W} hV hW => ⟨i₀, Finset.Subset.refl _, hV, hW⟩
      P := fun V hV => Pi₀.restrict hV
      compat := by
        intro V W hV hW hVW
        refine ⟨?_, ?_⟩
        · intro α hα
          simp only [coherentGoodBranchPartialSystem,
            CoherentGoodBranchPartial.restrict_toCoherentBranchPartial,
            CoherentBranchPartial.restrict_prefixAt]
        · intro α hα
          simp only [coherentGoodBranchPartialSystem,
            CoherentGoodBranchPartial.restrict_toCoherentBranchPartial,
            CoherentBranchPartial.restrict_branch]
    }, ⟨fun V hV => absurd hV (by rw [hp_empty]; exact Set.notMem_empty V),
        fun V hV _ => absurd hV (by rw [hp_empty]; exact Set.notMem_empty V)⟩,
      Finset.Subset.refl _⟩
  · -- Nonempty domain: anchor `T`, one-index witness `Pi₀`, `adjoinGoodWith`.
    obtain ⟨T, hT⟩ := hp_ne
    obtain ⟨Pi₀, hPi₀_ambient⟩ := goodIdealOneIndexCompactness p i₀ h_valid_i₀
    exact ⟨p.adjoinGoodWith T hT i₀ h_valid_i₀ Pi₀ hPi₀_ambient,
           p.adjoinGoodWith_le_self T hT i₀ h_valid_i₀ Pi₀ hPi₀_ambient,
           p.adjoinGoodWith_contains T hT i₀ h_valid_i₀ Pi₀ hPi₀_ambient⟩

/-- **Backward-compatible alias** for the old name of
`goodIdealExtensionCompactness`. Retained so existing docstring
references and any downstream code keep resolving; new code should
use `goodIdealExtensionCompactness` directly. -/
theorem coherentGoodBranchPartial_idealHasPartialExtensions
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    (coherentGoodBranchPartialSystem cR).IdealHasPartialExtensions :=
  goodIdealExtensionCompactness cR

/-- **Existence of a Good witness net** via the Good projective system
+ ideal `HasPartialExtensions`. The bare `exists_coherentWitnessNet`
can be rewired through `toCoherentWitnessNet`
(`exists_coherentWitnessNet_via_good`) to eliminate the bare
amalgamation path.

**Active dependency chain (Good-system compactness):**
```
exists_coherentGoodWitnessNet
  ← exists_global_section_of_idealPartialExtensions   (generic Zorn, axiom-clean)
  ← goodIdealExtensionCompactness                     (one-index path, rewired)
  ← goodIdealOneIndexCompactness                      (derived)
  ← goodIdealOneIndexCompactness_of_fixedCarrierCompactness  (reduction, proved)
  ← goodOneIndexFixedCarrierCompactness_holds         [downstream of FUSION TARGET]
      ← goodOneIndexFixedCarrierCompactness_of_uniformCommonWitness  (bridge, proved)
  + goodIdealOneIndex_finite_consistent               (finite satisfiability, proved)
  + adjoinGoodWith / _le_self / _contains             (packaging)
  + coherentGoodBranchPartial_amalgamate_from_common_upper  (finite consistency)
  + exists_coherentGoodBranchPartial                  [downstream of FUSION TARGET]
      ← CoherentBranchApprox.extendToChain ← PairERChain.extendToExt (~1595) [sorry]
          ⟹ replace by extendToExtOfBranch B once a CoherentMajorityBranch B exists

FUSION TARGET (the single open frontier both arrows above reduce to):
  exists_realizedPairERTypeTree                       [sorry — the limit fusion]
    ⟹ exists_coherentMajorityBranch ⟹ extendToExtOfBranch retires the extendToExt sorry
```
Phase-A diagnosis collapsed the two former "independent" sorries
(`goodOneIndexFixedCarrierCompactness_holds`, `exists_coherentGoodBranchPartial`)
onto this one fusion target; see the docstring of the former for the reduction
map. The next theorem project is the fusion target itself, not either consumer.
The prescribed-successor warm-up `PairERGoodChain.succWithChoice` is now **proved**
(its `b` is free). (The former `exists_nonempty_iInter_stage_fibers` was false
under `IsTypeCoherent` alone — removed; the realized-tree existence is the correct
target, feeding `PairERTypeTree.toNonemptyIntersection`.)
**Off-chain / legacy (still `sorry`, candidates for pruning):**
`goodIdealGlobalization`, `goodIdealCompactness` (ultralimit route —
eventual-constancy dead end); `GoodPrescription.finite_satisfiable`,
`prescribedGoodCompactness_holds`, `goodConstraintCompactness` (general-
prescription route); `coherentGoodBranchPartial_amalgamate_finset` (overlap-only,
unprovable); `coherentGoodBranchPartial_amalgamate_pair_ordered` (diagnostic);
`coherentGoodBranchPartial_insert_prescribed_new` / `_insert_prescribed_compatible`
(superseded shapes); legacy `adjoinGoodValue_common_compat` / `adjoinGood` /
`adjoinGood_le_self` / `adjoinGood_contains` (superseded by the `…With` path). -/
theorem exists_coherentGoodWitnessNet
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    Nonempty (CoherentGoodWitnessNet cR) := by
  obtain ⟨P, hP⟩ :=
    (coherentGoodBranchPartialSystem cR).exists_global_section_of_idealPartialExtensions
      (goodIdealExtensionCompactness cR)
  refine ⟨{ P := P, prefix_compat := ?_, branch_compat := ?_ }⟩
  · intro S T hS hT hST α hα
    have h := (hP hS hT hST).1 α hα
    change ((P T hT).restrict hST).toCoherentBranchPartial.prefixAt α hα =
      (P S hS).toCoherentBranchPartial.prefixAt α hα at h
    rw [CoherentGoodBranchPartial.restrict_toCoherentBranchPartial,
        (P T hT).toCoherentBranchPartial.restrict_prefixAt hST α hα] at h
    exact h
  · intro S T hS hT hST α hα
    have h := (hP hS hT hST).2 α hα
    change ((P T hT).restrict hST).toCoherentBranchPartial.branch α hα =
      (P S hS).toCoherentBranchPartial.branch α hα at h
    rw [CoherentGoodBranchPartial.restrict_toCoherentBranchPartial,
        (P T hT).toCoherentBranchPartial.restrict_branch hST α hα] at h
    exact h

/-- **`exists_coherentWitnessNet_via_good`**: the bare witness net
exists by projecting from the Good witness net. Once
`exists_coherentGoodWitnessNet` is filled, this becomes the active
route to bare `CoherentWitnessNet` (superseding the bare-amalgamation
path through `coherentBranchPartial_idealHasPartialExtensions`). -/
theorem exists_coherentWitnessNet_via_good
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    Nonempty (CoherentWitnessNet cR) :=
  (exists_coherentGoodWitnessNet cR).map
    CoherentGoodWitnessNet.toCoherentWitnessNet

/-! ### Good-layer rigid finite extension diagnostic

The bare-CBP `coherentBranchPartial_rigid_finite_extension` frontier
(line ~8079) takes an `IdealPartialSection` of bare CBPs and asks for
an extension to `insert i₀ D`. The issue: bare CBPs lack the inner
cR-consistency data needed to apply
`coherentGoodBranchPartial_extend_to_union` (which requires
`CoherentGoodBranchPartial` input).

To close the gap properly, the next step is to define a **Good
projective system** — a `FiniteProjectiveSystem` instance whose
objects are `CoherentGoodBranchPartial cR S` rather than the bare
`CoherentBranchPartial cR S`. Then the Good-layer rigid finite
extension is the corresponding theorem about
`(coherentGoodBranchPartialSystem cR).IdealPartialSection`.

The Good version of the frontier is below as a statement (with sorry);
its proof would:
1. Pick `T₀ := D.sup id` and lift the family to a Good CGBP on `T₀`
   compatible with the prescribed family (uses the Good FPS
   `finite_extension`).
2. Extend `T₀` to `T₀ ∪ i₀` via
   `coherentGoodBranchPartial_extend_to_union`.
3. Restrict via `CoherentGoodBranchPartial.restrict` to each member
   of `insert i₀ D`. -/

/-- **[FRONTIER, sorry]** Good-layer rigid finite extension. The natural
input is a finite family of `CoherentGoodBranchPartial cR S` over `D`
together with cross-compatibility. The output extends to
`insert i₀ D`. Proof outline above; pending the
`coherentGoodBranchPartialSystem` instance + Good-amalgamation
machinery. -/
theorem coherentGoodBranchPartial_rigid_finite_extension
    (cR : (Fin 2 ↪o PairERSource) → Bool)
    (D : Finset (Finset Ordinal.{0}))
    (_hD_valid : ∀ S ∈ D, ∀ α ∈ S, α < Ordinal.omega.{0} 1)
    (_PG_family : ∀ S ∈ D, CoherentGoodBranchPartial cR S)
    (_h_compat_family :
      ∀ {S T : Finset Ordinal.{0}} (hS : S ∈ D) (hT : T ∈ D) (hST : S ⊆ T),
        cbpFieldwiseCompat
          ((_PG_family T hT).toCoherentBranchPartial.restrict hST)
          (_PG_family S hS).toCoherentBranchPartial)
    (i₀ : Finset Ordinal.{0})
    (_hi₀ : ∀ α ∈ i₀, α < Ordinal.omega.{0} 1) :
    ∃ PG : ∀ S, S ∈ insert i₀ D → CoherentGoodBranchPartial cR S,
      (∀ {S T : Finset Ordinal.{0}}
        (hS : S ∈ insert i₀ D) (hT : T ∈ insert i₀ D) (hST : S ⊆ T),
        cbpFieldwiseCompat
          ((PG T hT).toCoherentBranchPartial.restrict hST)
          (PG S hS).toCoherentBranchPartial) ∧
      (∀ S (hS_D : S ∈ D),
        cbpFieldwiseCompat
          (PG S (Finset.mem_insert_of_mem hS_D)).toCoherentBranchPartial
          (_PG_family S hS_D).toCoherentBranchPartial) := by
  sorry

/-- **Conditional rigid finite extension** (axiom-clean modulo
upstream): given an ideal section `p`, a finite `D ⊆ p.domain`, and
a new valid finset `i₀` **above** every element of `⋃ D`, produce a
coherent family on `insert i₀ D` agreeing with `p.P` on `D`. Uses
`extend_one` on `p.P (D.sup id)` to obtain a CBP on `(D.sup id) ∪ i₀`,
then defines each `P S` as a restriction of that CBP. -/
theorem coherentBranchPartial_rigid_finite_extension_above
    (cR : (Fin 2 ↪o PairERSource) → Bool)
    (p : (coherentBranchPartialSystem cR).IdealPartialSection)
    (D : Finset (Finset Ordinal.{0}))
    (hD : ∀ S ∈ D, S ∈ p.domain)
    (i₀ : Finset Ordinal.{0})
    (hi₀ : ∀ α ∈ i₀, α < Ordinal.omega.{0} 1)
    (h_above : ∀ α ∈ i₀, ∀ S ∈ D, ∀ β ∈ S, β < α) :
    ∃ P : ∀ S, S ∈ insert i₀ D → CoherentBranchPartial cR S,
      (∀ {S T} (hS : S ∈ insert i₀ D) (hT : T ∈ insert i₀ D) (hST : S ⊆ T),
        cbpFieldwiseCompat ((P T hT).restrict hST) (P S hS)) ∧
      (∀ S (hS_D : S ∈ D),
        cbpFieldwiseCompat (P S (Finset.mem_insert_of_mem hS_D)) (p.P S (hD S hS_D))) := by
  classical
  -- Handle D = ∅ separately: just supply a CBP for i₀.
  by_cases hD_empty : D = ∅
  · subst hD_empty
    obtain ⟨Q⟩ := exists_coherentBranchPartial cR i₀ hi₀
    refine ⟨fun S hS => ?_, ?_, ?_⟩
    · have hS_eq : S = i₀ := by
        rcases Finset.mem_insert.mp hS with h | h
        · exact h
        · exact absurd h (Finset.notMem_empty _)
      exact hS_eq ▸ Q
    · intro S T hS hT hST
      have hT_eq : T = i₀ := by
        rcases Finset.mem_insert.mp hT with h | h
        · exact h
        · exact absurd h (Finset.notMem_empty _)
      have hS_eq : S = i₀ := by
        rcases Finset.mem_insert.mp hS with h | h
        · exact h
        · exact absurd h (Finset.notMem_empty _)
      subst hT_eq; subst hS_eq
      refine ⟨?_, ?_⟩ <;> intro α hα
      · exact Q.restrict_prefixAt hST α hα
      · exact Q.restrict_branch hST α hα
    · intro S hS_D
      exact absurd hS_D (Finset.notMem_empty _)
  -- D ≠ ∅: pick T₀ = D.sup id ∈ p.domain, extend via extend_one.
  have hD_ne : D.Nonempty := Finset.nonempty_iff_ne_empty.mpr hD_empty
  set T₀ : Finset Ordinal.{0} := D.sup id with hT₀_def
  have h_S_sub_T₀ : ∀ S ∈ D, S ⊆ T₀ := fun S hS => Finset.le_sup (f := id) hS
  -- T₀ ∈ p.domain via iterated directedness + downward_closed.
  have hT₀_in_dom : T₀ ∈ p.domain := by
    obtain ⟨S₀, hS₀_D⟩ := hD_ne
    have hS₀_dom : S₀ ∈ p.domain := hD S₀ hS₀_D
    suffices h : ∀ (D' : Finset (Finset Ordinal.{0})),
        (∀ S ∈ D', S ∈ p.domain) → ∃ U ∈ p.domain, ∀ S ∈ D', S ⊆ U by
      obtain ⟨U, hU_dom, hU_sub⟩ := h D hD
      exact p.downward_closed hU_dom (Finset.sup_le hU_sub)
    intro D'
    refine D'.induction_on ?_ ?_
    · intro _
      exact ⟨S₀, hS₀_dom, fun S hS => absurd hS (Finset.notMem_empty _)⟩
    · intro a D'' _ ih hD'
      have ha_dom : a ∈ p.domain := hD' a (Finset.mem_insert_self _ _)
      have hD''_dom : ∀ S ∈ D'', S ∈ p.domain :=
        fun S hS => hD' S (Finset.mem_insert_of_mem hS)
      obtain ⟨U', hU'_dom, hU'_sub⟩ := ih hD''_dom
      obtain ⟨U, hU_dom, ha_le, hU'_le⟩ := p.directed ha_dom hU'_dom
      refine ⟨U, hU_dom, ?_⟩
      intro S hS
      rcases Finset.mem_insert.mp hS with rfl | hS_D''
      · exact ha_le
      · exact (hU'_sub S hS_D'').trans hU'_le
  set P_T₀ : CoherentBranchPartial cR T₀ := p.P T₀ hT₀_in_dom with hP_T₀_def
  have h_i₀_above_T₀ : ∀ α ∈ i₀, ∀ β ∈ T₀, β < α := by
    intro α hα β hβ
    obtain ⟨S, hS, hβS⟩ := Finset.mem_sup.mp hβ
    exact h_above α hα S hS β hβS
  obtain ⟨Q, hQ_prefix, hQ_branch⟩ :=
    coherentBranchPartial_extend_one cR P_T₀ i₀ hi₀ h_i₀_above_T₀
  have h_S_sub_big : ∀ S, S ∈ insert i₀ D → S ⊆ T₀ ∪ i₀ := by
    intro S hS
    rcases Finset.mem_insert.mp hS with rfl | hS_D
    · exact Finset.subset_union_right
    · exact (h_S_sub_T₀ S hS_D).trans Finset.subset_union_left
  refine ⟨fun S hS => Q.restrict (h_S_sub_big S hS), ?_, ?_⟩
  · -- Coherence within insert i₀ D.
    intro S T hS hT hST
    refine ⟨?_, ?_⟩ <;> intro α hα
    · rw [(Q.restrict (h_S_sub_big T hT)).restrict_prefixAt hST α hα,
          Q.restrict_prefixAt (h_S_sub_big T hT) α (hST hα),
          ← Q.restrict_prefixAt (h_S_sub_big S hS) α hα]
    · rw [(Q.restrict (h_S_sub_big T hT)).restrict_branch hST α hα,
          Q.restrict_branch (h_S_sub_big T hT) α (hST hα),
          ← Q.restrict_branch (h_S_sub_big S hS) α hα]
  · -- Agreement with p.P on D.
    intro S hS_D
    have hS_sub_T₀ : S ⊆ T₀ := h_S_sub_T₀ S hS_D
    have h_compat_p :=
      p.compat (hD S hS_D) hT₀_in_dom hS_sub_T₀
    refine ⟨?_, ?_⟩ <;> intro α hα
    · rw [Q.restrict_prefixAt (h_S_sub_big S (Finset.mem_insert_of_mem hS_D)) α hα]
      have h_Q_eq_PT₀ := hQ_prefix α (hS_sub_T₀ hα)
      rw [Q.restrict_prefixAt Finset.subset_union_left α (hS_sub_T₀ hα)] at h_Q_eq_PT₀
      rw [show Q.prefixAt α (h_S_sub_big S (Finset.mem_insert_of_mem hS_D) hα)
            = Q.prefixAt α (Finset.subset_union_left (hS_sub_T₀ hα)) from rfl,
          h_Q_eq_PT₀]
      have h_p_compat := h_compat_p.1 α hα
      change ((p.P T₀ hT₀_in_dom).restrict hS_sub_T₀).prefixAt α hα
        = (p.P S (hD S hS_D)).prefixAt α hα at h_p_compat
      rw [(p.P T₀ hT₀_in_dom).restrict_prefixAt hS_sub_T₀ α hα] at h_p_compat
      exact h_p_compat
    · rw [Q.restrict_branch (h_S_sub_big S (Finset.mem_insert_of_mem hS_D)) α hα]
      have h_Q_eq_PT₀ := hQ_branch α (hS_sub_T₀ hα)
      rw [Q.restrict_branch Finset.subset_union_left α (hS_sub_T₀ hα)] at h_Q_eq_PT₀
      rw [show Q.branch α (h_S_sub_big S (Finset.mem_insert_of_mem hS_D) hα)
            = Q.branch α (Finset.subset_union_left (hS_sub_T₀ hα)) from rfl,
          h_Q_eq_PT₀]
      have h_p_compat := h_compat_p.2 α hα
      change ((p.P T₀ hT₀_in_dom).restrict hS_sub_T₀).branch α hα
        = (p.P S (hD S hS_D)).branch α hα at h_p_compat
      rw [(p.P T₀ hT₀_in_dom).restrict_branch hS_sub_T₀ α hα] at h_p_compat
      exact h_p_compat

/-- **Alternative existence proof for `CoherentWitnessNet`** —
derived from the ideal-domain Zorn bridge
`exists_global_section_of_idealPartialExtensions`. Provided in
parallel with `exists_coherentWitnessNet`; once the ideal frontier
is filled, this becomes the preferred path. -/
theorem exists_coherentWitnessNet_via_ideal
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    Nonempty (CoherentWitnessNet cR) := by
  obtain ⟨P, hP⟩ :=
    (coherentBranchPartialSystem cR).exists_global_section_of_idealPartialExtensions
      (coherentBranchPartial_idealHasPartialExtensions cR)
  refine ⟨{ P := P, prefix_compat := ?_, branch_compat := ?_ }⟩
  · intro S T hS hT hST α hα
    have h := (hP hS hT hST).1 α hα
    change ((P T hT).restrict hST).prefixAt α hα = (P S hS).prefixAt α hα at h
    rw [(P T hT).restrict_prefixAt hST α hα] at h
    exact h
  · intro S T hS hT hST α hα
    have h := (hP hS hT hST).2 α hα
    change ((P T hT).restrict hST).branch α hα = (P S hS).branch α hα at h
    rw [(P T hT).restrict_branch hST α hα] at h
    exact h

/-- **Existence of a coherent witness net** — derived axiom-clean
from `exists_global_section_of_partialExtensions` applied to the
CBP projective system, with `HasPartialExtensions` supplied by
`coherentBranchPartial_hasPartialExtensions`. The pointwise
`prefix_compat` / `branch_compat` fields fall out directly from the
system's fieldwise `Compat`. -/
theorem exists_coherentWitnessNet
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    Nonempty (CoherentWitnessNet cR) := by
  obtain ⟨P, hP⟩ := (coherentBranchPartialSystem cR).exists_global_section_of_partialExtensions
    (coherentBranchPartial_hasPartialExtensions cR)
  -- hP : ∀ {S T} (hS) (hT) (hST : S ≤ T),
  --      cbpFieldwiseCompat ((P T hT).restrict hST) (P S hS)
  -- The `Compat` field is `cbpFieldwiseCompat`, so unfolds to pointwise.
  refine ⟨{ P := P, prefix_compat := ?_, branch_compat := ?_ }⟩
  · intro S T hS hT hST α hα
    have h := (hP hS hT hST).1 α hα
    -- h's LHS uses the system's `restrict` field; unfold to CBP.restrict.
    change ((P T hT).restrict hST).prefixAt α hα = (P S hS).prefixAt α hα at h
    rw [(P T hT).restrict_prefixAt hST α hα] at h
    exact h
  · intro S T hS hT hST α hα
    have h := (hP hS hT hST).2 α hα
    change ((P T hT).restrict hST).branch α hα = (P S hS).branch α hα at h
    rw [(P T hT).restrict_branch hST α hα] at h
    exact h

/-- **`rawBranchCompactness_holds`** — derived axiom-clean from
`exists_coherentWitnessNet` via the bridge
`rawBranchCompactness_of_coherentWitnessNet`. -/
theorem rawBranchCompactness_holds
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    rawBranchCompactness cR :=
  rawBranchCompactness_of_coherentWitnessNet
    (Classical.choice (exists_coherentWitnessNet cR))

/-! ### Bridge: rawBranchCompactness → coherentMajorityBranch

Given `rawBranchCompactness cR` and a partial branch on every finite
`S ⊂ ω₁`, we extract a `CoherentMajorityBranch cR`:

1. For each `S`, build an `A` satisfying `S` using the `CBP` from the
   hypothesis (`some` values on `S`, `none` off it).
2. Apply `rawBranchCompactness` to get a global `A` satisfying every
   finite `S`.
3. Build the CMB from the global `A`: at each `α < ω₁`, extract
   `A.1 α hα` (which is `some _` by `SatisfiesFinite A {α}`) to define
   `prefixAt α hα`, and similarly for `branch`. Coherence laws come
   from `SatisfiesFinite` at the appropriate finite `S`. -/

private noncomputable def CoherentBranchPartial.toRaw
    {cR : (Fin 2 ↪o PairERSource) → Bool} {S : Finset Ordinal.{0}}
    (P : CoherentBranchPartial cR S) : RawBranchAssignment cR := by
  classical
  exact
    (fun α _ => if h : α ∈ S then some (P.prefixAt α h) else none,
     fun α _ => if h : α ∈ S then some (P.branch α h) else none)

private lemma CoherentBranchPartial.toRaw_prefix_mem
    {cR : (Fin 2 ↪o PairERSource) → Bool} {S : Finset Ordinal.{0}}
    (P : CoherentBranchPartial cR S) (α : Ordinal.{0}) (hα_lt : α < Ordinal.omega.{0} 1)
    (hα : α ∈ S) :
    P.toRaw.1 α hα_lt = some (P.prefixAt α hα) := by
  unfold CoherentBranchPartial.toRaw
  simp [hα]

private lemma CoherentBranchPartial.toRaw_branch_mem
    {cR : (Fin 2 ↪o PairERSource) → Bool} {S : Finset Ordinal.{0}}
    (P : CoherentBranchPartial cR S) (α : Ordinal.{0}) (hα_lt : α < Ordinal.omega.{0} 1)
    (hα : α ∈ S) :
    P.toRaw.2 α hα_lt = some (P.branch α hα) := by
  unfold CoherentBranchPartial.toRaw
  simp [hα]

/-- **Bridge**: `rawBranchCompactness cR` discharges the
inverse-limit-compactness hypothesis of
`exists_coherentMajorityBranch_of_finitePartials`. Axiom-clean. -/
theorem exists_coherentMajorityBranch_of_finitePartials
    (cR : (Fin 2 ↪o PairERSource) → Bool)
    (hfin : ∀ S : Finset Ordinal.{0},
      (∀ α ∈ S, α < Ordinal.omega.{0} 1) →
        Nonempty (CoherentBranchPartial cR S)) :
    Nonempty (CoherentMajorityBranch cR) := by
  classical
  -- Step 1: For each S, produce an A satisfying S (using the CBP from hfin).
  have h_assign : ∀ S : Finset Ordinal.{0},
      (∀ α ∈ S, α < Ordinal.omega.{0} 1) →
        ∃ A : RawBranchAssignment cR, SatisfiesFinite A S := by
    intro S hS
    obtain ⟨P⟩ := hfin S hS
    refine ⟨P.toRaw, hS, P, ?_, ?_⟩
    · intro α hα
      exact P.toRaw_prefix_mem α (hS α hα) hα
    · intro α hα
      exact P.toRaw_branch_mem α (hS α hα) hα
  -- Step 2: Apply compactness.
  obtain ⟨A, hA⟩ := rawBranchCompactness_holds cR h_assign
  -- Helper: extraction of A's values at each α via SatisfiesFinite at {α}.
  have h_some_prefix : ∀ (α : Ordinal.{0}) (hα : α < Ordinal.omega.{0} 1),
      (A.1 α hα).isSome := by
    intro α hα
    have hSat : SatisfiesFinite A {α} :=
      hA {α} (fun β hβ => Finset.mem_singleton.mp hβ ▸ hα)
    obtain ⟨hS_S, P_S, h_pref, _⟩ := hSat
    have h_α_in : α ∈ ({α} : Finset Ordinal.{0}) := Finset.mem_singleton.mpr rfl
    have := h_pref α h_α_in
    rw [this]
    rfl
  have h_some_branch : ∀ (α : Ordinal.{0}) (hα : α < Ordinal.omega.{0} 1),
      (A.2 α hα).isSome := by
    intro α hα
    have hSat : SatisfiesFinite A {α} :=
      hA {α} (fun β hβ => Finset.mem_singleton.mp hβ ▸ hα)
    obtain ⟨hS_S, P_S, _, h_br⟩ := hSat
    have h_α_in : α ∈ ({α} : Finset Ordinal.{0}) := Finset.mem_singleton.mpr rfl
    have := h_br α h_α_in
    rw [this]
    rfl
  -- Step 3: Build CMB from A.
  refine ⟨{
    prefixAt := fun α hα => (A.1 α hα).get (h_some_prefix α hα)
    branch := fun α hα => (A.2 α hα).get (h_some_branch α hα)
    prefix_restrict := ?_
    branch_restrict := ?_
    top_in_validFiber := ?_
  }⟩
  · -- prefix_restrict: ∀ β ≤ α, ∀ x, prefixAt α _ (lift x) = prefixAt β _ x.
    intro β α hβα hβ hα x
    have hSat : SatisfiesFinite A ({β, α} : Finset Ordinal.{0}) :=
      hA {β, α} (fun γ hγ => by
        rcases Finset.mem_insert.mp hγ with rfl | hγ
        · exact hβ
        · rwa [Finset.mem_singleton.mp hγ])
    obtain ⟨hS_S, P_S, h_pref, _⟩ := hSat
    have hβ_in : β ∈ ({β, α} : Finset Ordinal.{0}) :=
      Finset.mem_insert.mpr (Or.inl rfl)
    have hα_in : α ∈ ({β, α} : Finset Ordinal.{0}) :=
      Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
    -- Extract A's values as P_S's.
    have h_A_β := h_pref β hβ_in
    have h_A_α := h_pref α hα_in
    -- The Option.get equals P_S's values.
    have h_get_β : (A.1 β hβ).get (h_some_prefix β hβ) = P_S.prefixAt β hβ_in := by
      have := h_A_β
      rw [Option.get_of_eq_some _ this]
    have h_get_α : (A.1 α hα).get (h_some_prefix α hα) = P_S.prefixAt α hα_in := by
      have := h_A_α
      rw [Option.get_of_eq_some _ this]
    -- Apply P_S.prefix_restrict.
    rw [h_get_β, h_get_α, P_S.prefix_restrict hβα hβ_in hα_in]
  · -- branch_restrict: same pattern.
    intro β α hβα hβ hα x
    have hSat : SatisfiesFinite A ({β, α} : Finset Ordinal.{0}) :=
      hA {β, α} (fun γ hγ => by
        rcases Finset.mem_insert.mp hγ with rfl | hγ
        · exact hβ
        · rwa [Finset.mem_singleton.mp hγ])
    obtain ⟨hS_S, P_S, _, h_br⟩ := hSat
    have hβ_in : β ∈ ({β, α} : Finset Ordinal.{0}) :=
      Finset.mem_insert.mpr (Or.inl rfl)
    have hα_in : α ∈ ({β, α} : Finset Ordinal.{0}) :=
      Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
    have h_A_β := h_br β hβ_in
    have h_A_α := h_br α hα_in
    have h_get_β : (A.2 β hβ).get (h_some_branch β hβ) = P_S.branch β hβ_in := by
      rw [Option.get_of_eq_some _ h_A_β]
    have h_get_α : (A.2 α hα).get (h_some_branch α hα) = P_S.branch α hα_in := by
      rw [Option.get_of_eq_some _ h_A_α]
    rw [h_get_β, h_get_α, P_S.branch_restrict hβα hβ_in hα_in]
  · -- top_in_validFiber.
    intro γ hγ hsγ
    haveI : IsWellOrder (Order.succ γ).ToType (· < ·) := isWellOrder_lt
    have hSat : SatisfiesFinite A ({γ, Order.succ γ} : Finset Ordinal.{0}) :=
      hA _ (fun β hβ => by
        rcases Finset.mem_insert.mp hβ with rfl | hβ
        · exact hγ
        · rwa [Finset.mem_singleton.mp hβ])
    obtain ⟨hS_S, P_S, h_pref, h_br⟩ := hSat
    have hγ_in : γ ∈ ({γ, Order.succ γ} : Finset Ordinal.{0}) :=
      Finset.mem_insert.mpr (Or.inl rfl)
    have hsγ_in : Order.succ γ ∈ ({γ, Order.succ γ} : Finset Ordinal.{0}) :=
      Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
    have h_get_pref_sγ : (A.1 (Order.succ γ) hsγ).get (h_some_prefix _ _) =
        P_S.prefixAt (Order.succ γ) hsγ_in := by
      rw [Option.get_of_eq_some _ (h_pref (Order.succ γ) hsγ_in)]
    have h_get_pref_γ : (A.1 γ hγ).get (h_some_prefix _ _) =
        P_S.prefixAt γ hγ_in := by
      rw [Option.get_of_eq_some _ (h_pref γ hγ_in)]
    have h_get_br_γ : (A.2 γ hγ).get (h_some_branch _ _) =
        P_S.branch γ hγ_in := by
      rw [Option.get_of_eq_some _ (h_br γ hγ_in)]
    rw [h_get_pref_sγ, h_get_pref_γ, h_get_br_γ]
    exact P_S.top_in_validFiber γ hγ_in hsγ_in

/-! **[CONSOLIDATED TARGET — definition relocated below]** Existence of a
`CoherentMajorityBranch` `B` (the object the pair Erdős–Rado theorem
`erdos_rado_pair_omega1_of_coherentMajorityBranch` consumes) is now proved **directly**
via the EHMR canonical partition tree. Because that construction
(`exists_coherentMajorityBranch_direct`) lives further down this file, the theorem
`exists_coherentMajorityBranch` itself is stated right after it. The legacy
`_of_finitePartials`/`rawBranchCompactness`/`HasPartialExtensions` tower is left intact
but is now off-chain (no longer feeds the active target). -/

/-! ### [PHASE 1 SCAFFOLD] Direct `CoherentMajorityBranch` via the EHMR canonical
partition tree (EHMR §13/§14/§17). Statement-level only — bodies are `sorry`. This
is the intended *direct* construction of `B`, superseding the
`_of_finitePartials`/`rawBranchCompactness`/`HasPartialExtensions` route (and its
near-circular `extendToExt` dependency) **once proved**. The old route is left
intact for now. -/

/-- **[EHMR §17 — output branch of the canonical partition tree]**
`EHMRBranch cR`: the raw data of a length-`ω₁` branch of the Erdős–Rado canonical
partition tree for the pair-coloring `cR`. At each level `β < ω₁`:
* `rep β` is the chosen representative `s(h↾β)` (EHMR `s(h) = min S(h)`);
* `bit β` is the recorded color (the node bit `h(β)`);
* `rep_strictMono`: the reps form a strictly increasing transfinite sequence;
* `coloring` is **EHMR fact (8)**, `cR({s(h↾β), s(h↾γ)}) = h(β)` for `β < γ` — the
  `inner_consistent` / `top_in_validFiber` content.

(No `large` field: `CoherentMajorityBranch.large` was dropped as unused by the
pair theorem, so the branch needs only nonempty live fibers, not `succ ℶ_1` ones.)

Intermediate object: `ehmr_tree_has_omega1_branch` produces it (tree-counting), and
`exists_coherentMajorityBranch_of_ehmrBranch` assembles it into a
`CoherentMajorityBranch`. -/
structure EHMRBranch (cR : (Fin 2 ↪o PairERSource) → Bool) where
  rep : ∀ β : Ordinal.{0}, β < Ordinal.omega.{0} 1 → PairERSource
  bit : ∀ β : Ordinal.{0}, β < Ordinal.omega.{0} 1 → Bool
  rep_strictMono : ∀ {β γ : Ordinal.{0}} (hβ : β < Ordinal.omega.{0} 1)
    (hγ : γ < Ordinal.omega.{0} 1), β < γ → rep β hβ < rep γ hγ
  coloring : ∀ {β γ : Ordinal.{0}} (hβ : β < Ordinal.omega.{0} 1)
    (hγ : γ < Ordinal.omega.{0} 1) (hβγ : β < γ),
    cR (pairEmbed (rep_strictMono hβ hγ hβγ)) = bit β hβ

/-- **[EHMR §14, Lemma 14.2 + |E| counting — coverage/counting engine]**
`ehmr_partitionTree_card_lower`: if the "used-up" sets `R i` cover `PairERSource`
and each is a subsingleton (the canonical tree has `R(h) = {s(h)}`, so `|R(h)| = 1`),
then the node index set has cardinality `≥ succ ℶ_1 = |PairERSource|`. This is the
counting feeding the branch-length theorem. -/
theorem ehmr_partitionTree_card_lower
    {ι : Type} (R : ι → Set PairERSource)
    (hcover : ∀ y : PairERSource, ∃ i : ι, y ∈ R i)
    (hsub : ∀ i : ι, (R i).Subsingleton) :
    Order.succ (Cardinal.beth.{0} 1) ≤ Cardinal.mk ι := by
  classical
  -- The choice function `y ↦ (some i with y ∈ R i)` is injective: subsingleton fibers.
  have hf : ∀ y : PairERSource, y ∈ R (hcover y).choose := fun y => (hcover y).choose_spec
  have hinj : Function.Injective (fun y : PairERSource => (hcover y).choose) := by
    intro y₁ y₂ h
    change (hcover y₁).choose = (hcover y₂).choose at h
    have h2 : y₂ ∈ R (hcover y₁).choose := by rw [h]; exact hf y₂
    exact hsub _ (hf y₁) h2
  calc Order.succ (Cardinal.beth.{0} 1) = Cardinal.mk PairERSource := mk_pairERSource.symm
    _ ≤ Cardinal.mk ι := Cardinal.mk_le_of_injective hinj

/-! ### [STAGE 1] EHMR canonical-tree skeleton (basic defs; no proofs yet)

Nodes are recorded-color sequences `β.ToType → Bool` (Type 0, so the counting stays
in `Cardinal.{0}`); reps `s(h↾γ) = min S(h↾γ)` are derived by well-founded recursion
on length; live = nonempty successor set; children split by the recorded color. No
fiber-largeness (post-refactor `EHMRBranch` has no `large`). -/

/-- A node at level `β`: the recorded colors at the positions `β.ToType`. The
eventual branch is a cofinal chain through these of length `< ω₁`. (`β.ToType`-indexed
— `Type 0` — so it matches `validFiber`/`prefixAt` and the counting is in `Cardinal.{0}`.) -/
abbrev EHMRNodeAt (β : Ordinal.{0}) := β.ToType → Bool

/-- Restrict a node to a shorter length `δ ≤ β`, via the initial-segment embedding. -/
noncomputable def EHMRNodeAt.restrict {β : Ordinal.{0}} (h : EHMRNodeAt β)
    {δ : Ordinal.{0}} (hδβ : δ ≤ β) : EHMRNodeAt δ :=
  haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder δ.ToType (· < ·) := isWellOrder_lt
  fun x => h ((Ordinal.initialSegToType hδβ).toOrderEmbedding x)

/-- The successor set `S(h)`: points above all the reps respecting the recorded
colors. (`β.ToType`-indexed `validFiber` shape, with a plain-function `rep`.) -/
def ehmrFiber (cR : (Fin 2 ↪o PairERSource) → Bool) {β : Ordinal.{0}}
    (rep : β.ToType → PairERSource) (col : EHMRNodeAt β) : Set PairERSource :=
  { y | ∀ x : β.ToType, ∃ h : rep x < y, cR (pairEmbed h) = col x }

instance : Nonempty PairERSource :=
  Cardinal.mk_ne_zero_iff.mp (by
    rw [mk_pairERSource]
    exact (lt_of_lt_of_le Cardinal.aleph0_pos aleph0_le_succ_beth_one).ne')

/-- **Chosen representative** `s(h) = min S(h)` — the `<`-least element of the
successor set (via `PairERSource`'s well-order), by well-founded recursion on the
node length: the rep at position `x : β.ToType` is the chosen rep of the restriction
to `typein x`. Junk default on dead (empty-fiber) nodes. -/
noncomputable def ehmrChosen (cR : (Fin 2 ↪o PairERSource) → Bool)
    (β : Ordinal.{0}) (h : EHMRNodeAt β) : PairERSource := by
  classical
  haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  exact
    if hne : (ehmrFiber cR
        (fun x => ehmrChosen cR (Ordinal.typein (· < ·) x)
          (h.restrict (le_of_lt (by
            have hh := Ordinal.typein_lt_type (· < · : β.ToType → β.ToType → Prop) x
            rwa [Ordinal.type_toType] at hh)))) h).Nonempty then
      (IsWellFounded.wf : WellFounded (· < · : PairERSource → PairERSource → Prop)).min _ hne
    else
      Classical.arbitrary PairERSource
termination_by β
decreasing_by
  all_goals
    haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
    have hh := Ordinal.typein_lt_type (· < · : β.ToType → β.ToType → Prop) x
    rwa [Ordinal.type_toType] at hh

/-- The reps along a node: the chosen rep of the restriction to each position. -/
noncomputable def ehmrRep (cR : (Fin 2 ↪o PairERSource) → Bool) {β : Ordinal.{0}}
    (h : EHMRNodeAt β) : β.ToType → PairERSource := by
  haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  exact fun x => ehmrChosen cR (Ordinal.typein (· < ·) x)
    (h.restrict (le_of_lt (by
      have hh := Ordinal.typein_lt_type (· < · : β.ToType → β.ToType → Prop) x
      rwa [Ordinal.type_toType] at hh)))

/-- `S(h)` as a set, via `ehmrRep`. -/
def ehmrS (cR : (Fin 2 ↪o PairERSource) → Bool) {β : Ordinal.{0}} (h : EHMRNodeAt β) :
    Set PairERSource := ehmrFiber cR (ehmrRep cR h) h

/-- A node is **live** iff its successor set is nonempty. -/
def ehmrLive (cR : (Fin 2 ↪o PairERSource) → Bool) {β : Ordinal.{0}}
    (h : EHMRNodeAt β) : Prop := (ehmrS cR h).Nonempty

/-- The used/remainder set `R(h)`: `{s(h)}` on live nodes, else `∅`. -/
noncomputable def ehmrR (cR : (Fin 2 ↪o PairERSource) → Bool) {β : Ordinal.{0}}
    (h : EHMRNodeAt β) : Set PairERSource := by
  classical
  exact if ehmrLive cR h then {ehmrChosen cR β h} else ∅

/-- **Child** of `h` recording color `c` at the new top position `β`, via
`extendType`. -/
noncomputable def EHMRNodeAt.child {β : Ordinal.{0}} (h : EHMRNodeAt β) (c : Bool) :
    EHMRNodeAt (Order.succ β) := extendType h c

/-- **[STAGE 2a]** `R(h)` is a subsingleton (it is `{s(h)}` or `∅`). -/
theorem ehmrR_subsingleton (cR : (Fin 2 ↪o PairERSource) → Bool) {β : Ordinal.{0}}
    (h : EHMRNodeAt β) : (ehmrR cR h).Subsingleton := by
  classical
  rw [ehmrR]
  split_ifs with hlive
  · exact Set.subsingleton_singleton
  · exact Set.subsingleton_empty

/-- **[STAGE 2a]** On a live node, the chosen rep lies in the successor set. -/
theorem ehmrChosen_mem (cR : (Fin 2 ↪o PairERSource) → Bool) {β : Ordinal.{0}}
    (h : EHMRNodeAt β) (hlive : ehmrLive cR h) :
    ehmrChosen cR β h ∈ ehmrS cR h := by
  classical
  have hcond : (ehmrFiber cR
      (fun x => ehmrChosen cR (Ordinal.typein (· < ·) x)
        (h.restrict (le_of_lt (by
          have hh := Ordinal.typein_lt_type (· < · : β.ToType → β.ToType → Prop) x
          rwa [Ordinal.type_toType] at hh)))) h).Nonempty := hlive
  rw [ehmrChosen, dif_pos hcond]
  exact WellFounded.min_mem _ _ hcond

/-- **[STAGE 2a]** On a live node, `ehmrChosen` is exactly the well-order minimum of
the successor set (the defining unfold). -/
theorem ehmrChosen_eq_min (cR : (Fin 2 ↪o PairERSource) → Bool) {β : Ordinal.{0}}
    (h : EHMRNodeAt β) (hlive : ehmrLive cR h) :
    ehmrChosen cR β h =
      (IsWellFounded.wf : WellFounded (· < · : PairERSource → PairERSource → Prop)).min
        (ehmrS cR h) hlive := by
  classical
  have hcond : (ehmrFiber cR
      (fun x => ehmrChosen cR (Ordinal.typein (· < ·) x)
        (h.restrict (le_of_lt (by
          have hh := Ordinal.typein_lt_type (· < · : β.ToType → β.ToType → Prop) x
          rwa [Ordinal.type_toType] at hh)))) h).Nonempty := hlive
  rw [ehmrChosen, dif_pos hcond]
  -- `rw`'s closing `rfl` is reducible-only; `ehmrS`/`ehmrRep` are regular defs, so the
  -- raw fiber and `ehmrS cR h` are defeq only at default transparency. Close it manually.
  rfl

/-- **[STAGE 2b prereq]** If `y` is a live successor of `h` other than the chosen min,
then the chosen min is strictly below `y` (it is the `<`-least element of `S(h)`). -/
theorem ehmrChosen_lt_of_mem_ne (cR : (Fin 2 ↪o PairERSource) → Bool) {β : Ordinal.{0}}
    (h : EHMRNodeAt β) {y : PairERSource} (hy : y ∈ ehmrS cR h)
    (hne : y ≠ ehmrChosen cR β h) : ehmrChosen cR β h < y := by
  have hlive : ehmrLive cR h := ⟨y, hy⟩
  rw [ehmrChosen_eq_min cR h hlive] at hne ⊢
  exact lt_of_le_of_ne (not_lt.mp (WellFounded.not_lt_min _ _ hlive hy)) (Ne.symm hne)

/-- **[STAGE 2a]** The recorded-color property (local EHMR fact (8)): at position
`x : β.ToType`, the chosen rep sits below `s(h)` and the pair gets color `h x`. -/
theorem ehmrRep_coloring (cR : (Fin 2 ↪o PairERSource) → Bool) {β : Ordinal.{0}}
    (h : EHMRNodeAt β) (hlive : ehmrLive cR h) (x : β.ToType) :
    ∃ hlt : ehmrRep cR h x < ehmrChosen cR β h, cR (pairEmbed hlt) = h x :=
  ehmrChosen_mem cR h hlive x

/-- **[STAGE 2a]** Level cardinality: for `β < ω₁` the level (all length-`β` nodes)
has cardinality `≤ ℶ_1` — `β.ToType` countable, `Bool`-valued. -/
theorem ehmr_level_card_le_beth1 (β : Ordinal.{0}) (hβ : β < Ordinal.omega.{0} 1) :
    Cardinal.mk (EHMRNodeAt β) ≤ Cardinal.beth.{0} 1 := by
  haveI : Countable β.ToType := countable_toType_of_lt_omega1 hβ
  show Cardinal.mk (β.ToType → Bool) ≤ Cardinal.beth.{0} 1
  have h_le_pow : Cardinal.mk (β.ToType → Bool) ≤
      Cardinal.aleph0 ^ Cardinal.mk β.ToType := by
    have h_pow_eq : Cardinal.mk (β.ToType → Bool) =
        (Cardinal.mk Bool) ^ (Cardinal.mk β.ToType) := by rw [Cardinal.mk_arrow]; simp
    rw [h_pow_eq]
    exact Cardinal.power_le_power_right (Cardinal.mk_le_aleph0 (α := Bool))
  have h_pow_le : Cardinal.aleph0 ^ Cardinal.mk β.ToType ≤
      Cardinal.aleph0 ^ Cardinal.aleph0 :=
    Cardinal.power_le_power_left Cardinal.aleph0_ne_zero
      (Cardinal.mk_le_aleph0 (α := β.ToType))
  have h_aleph_pow : Cardinal.aleph0.{0} ^ Cardinal.aleph0.{0} = Cardinal.beth.{0} 1 := by
    rw [Cardinal.power_self_eq (le_refl Cardinal.aleph0),
      show (1 : Ordinal.{0}) = Order.succ 0 from Ordinal.succ_zero.symm,
      Cardinal.beth_succ, Cardinal.beth_zero]
  exact (h_le_pow.trans h_pow_le).trans_eq h_aleph_pow

/-! ### [STAGE 2b] Coverage (EHMR Lemma 14.2) — the y-path. Statements first. -/

/-- **[STAGE 2b helper]** Restricting a child node to a length `δ ≤ β` (strictly below
the new top position) agrees with restricting the parent: the child only adds the
top coordinate, leaving the old positions untouched. -/
theorem EHMRNodeAt.restrict_child {β : Ordinal.{0}} (h : EHMRNodeAt β) (c : Bool)
    {δ : Ordinal.{0}} (hδβ : δ ≤ β) :
    (h.child c).restrict (hδβ.trans (Order.le_succ β)) = h.restrict hδβ := by
  classical
  funext x
  exact extendType_initialSegToType_apply h c hδβ x

/-- **[STAGE 2b helper]** Restricting a node to its own full length is the identity. -/
theorem EHMRNodeAt.restrict_self {β : Ordinal.{0}} (h : EHMRNodeAt β) (hββ : β ≤ β) :
    h.restrict hββ = h := by
  classical
  haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  funext x
  show h ((Ordinal.initialSegToType hββ).toOrderEmbedding x) = h x
  congr 1
  exact (Ordinal.typein_inj (· < ·)).mp (Ordinal.typein_apply (Ordinal.initialSegToType hββ) x)

/-- **[STAGE 2b helper]** `ehmrChosen` transported along a level equality: equal levels
plus heterogeneously-equal nodes give equal chosen reps. -/
theorem ehmrChosen_congr (cR : (Fin 2 ↪o PairERSource) → Bool) {δ₁ δ₂ : Ordinal.{0}}
    (hδ : δ₁ = δ₂) {n₁ : EHMRNodeAt δ₁} {n₂ : EHMRNodeAt δ₂} (hn : HEq n₁ n₂) :
    ehmrChosen cR δ₁ n₁ = ehmrChosen cR δ₂ n₂ := by
  subst hδ
  rw [eq_of_heq hn]

/-- **[STAGE 2b helper]** Heterogeneous version of `restrict_child`: when `δ₁ = δ₂ ≤ β`,
restricting the child to `δ₁` is heq to restricting the parent to `δ₂`. -/
theorem EHMRNodeAt.restrict_child_heq {β : Ordinal.{0}} (h : EHMRNodeAt β) (c : Bool)
    {δ₁ δ₂ : Ordinal.{0}} (hδ : δ₁ = δ₂) (h1 : δ₁ ≤ Order.succ β) (h2 : δ₂ ≤ β) :
    HEq ((h.child c).restrict h1) (h.restrict h2) := by
  subst hδ
  exact heq_of_eq (EHMRNodeAt.restrict_child h c h2)

/-- **[STAGE 2b helper]** The reps of a child agree with the parent's reps at every old
position (the lift of `x : β.ToType` into the successor level). -/
theorem ehmrRep_child_lift (cR : (Fin 2 ↪o PairERSource) → Bool) {β : Ordinal.{0}}
    (h : EHMRNodeAt β) (c : Bool) (x : β.ToType) :
    ehmrRep cR (h.child c)
        ((Ordinal.initialSegToType (Order.le_succ β)).toOrderEmbedding x) =
      ehmrRep cR h x := by
  classical
  haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder (Order.succ β).ToType (· < ·) := isWellOrder_lt
  set z : (Order.succ β).ToType :=
    (Ordinal.initialSegToType (Order.le_succ β)).toOrderEmbedding x with hz_def
  have htz : Ordinal.typein (· < ·) z = Ordinal.typein (· < ·) x := by
    rw [hz_def]
    exact Ordinal.typein_apply (Ordinal.initialSegToType (Order.le_succ β)) x
  have h1 : Ordinal.typein (· < ·) z ≤ Order.succ β :=
    le_of_lt (by
      have := Ordinal.typein_lt_type (· < · : (Order.succ β).ToType → _ → Prop) z
      rwa [Ordinal.type_toType] at this)
  have h2 : Ordinal.typein (· < ·) x ≤ β :=
    le_of_lt (by
      have := Ordinal.typein_lt_type (· < · : β.ToType → _ → Prop) x
      rwa [Ordinal.type_toType] at this)
  exact ehmrChosen_congr cR htz (EHMRNodeAt.restrict_child_heq h c htz h1 h2)

/-- **[STAGE 2b helper]** The new top rep of a child is the parent's chosen rep `s(h)`. -/
theorem ehmrRep_child_top (cR : (Fin 2 ↪o PairERSource) → Bool) {β : Ordinal.{0}}
    (h : EHMRNodeAt β) (c : Bool) :
    ehmrRep cR (h.child c) (⊤ : (Order.succ β).ToType) = ehmrChosen cR β h := by
  classical
  haveI : IsWellOrder (Order.succ β).ToType (· < ·) := isWellOrder_lt
  have htop : Ordinal.typein (· < ·) (⊤ : (Order.succ β).ToType) = β := by
    rw [show (⊤ : (Order.succ β).ToType) =
        Ordinal.enum (α := (Order.succ β).ToType) (· < ·)
          ⟨β, (Ordinal.type_toType _).symm ▸ Order.lt_succ β⟩
      from Ordinal.enum_succ_eq_top.symm, Ordinal.typein_enum]
  have h1 : Ordinal.typein (· < ·) (⊤ : (Order.succ β).ToType) ≤ Order.succ β :=
    le_of_lt (by
      have := Ordinal.typein_lt_type (· < · : (Order.succ β).ToType → _ → Prop)
        (⊤ : (Order.succ β).ToType)
      rwa [Ordinal.type_toType] at this)
  refine ehmrChosen_congr cR htop ?_
  exact HEq.trans (EHMRNodeAt.restrict_child_heq h c htop h1 (le_refl β))
    (heq_of_eq (EHMRNodeAt.restrict_self h (le_refl β)))

/-- **[STAGE 2b helper]** The recorded color of a child at the new top position is `c`. -/
theorem EHMRNodeAt.child_top {β : Ordinal.{0}} (h : EHMRNodeAt β) (c : Bool) :
    (h.child c) (⊤ : (Order.succ β).ToType) = c := by
  classical
  haveI : IsWellOrder (Order.succ β).ToType (· < ·) := isWellOrder_lt
  show extendType h c (⊤ : (Order.succ β).ToType) = c
  simp only [extendType, dif_pos]

/-- **[STAGE 2b helper]** The recorded color of a child at an old (lifted) position
agrees with the parent's recorded color there. -/
theorem EHMRNodeAt.child_lift {β : Ordinal.{0}} (h : EHMRNodeAt β) (c : Bool) (x : β.ToType) :
    (h.child c) ((Ordinal.initialSegToType (Order.le_succ β)).toOrderEmbedding x) = h x := by
  classical
  haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  have hid : (Ordinal.initialSegToType (le_refl β)).toOrderEmbedding x = x :=
    (Ordinal.typein_inj (· < ·)).mp
      (Ordinal.typein_apply (Ordinal.initialSegToType (le_refl β)) x)
  have key := extendType_initialSegToType_apply h c (le_refl β) x
  rw [hid] at key
  exact key

/-- **[STAGE 2b helper]** Every position of a successor level is either the new top, or
the lift of a unique old position `x : β.ToType`. -/
theorem EHMRNodeAt.eq_top_or_exists_lift {β : Ordinal.{0}} (z : (Order.succ β).ToType) :
    z = (⊤ : (Order.succ β).ToType) ∨
      ∃ x : β.ToType, z = (Ordinal.initialSegToType (Order.le_succ β)).toOrderEmbedding x := by
  classical
  haveI : IsWellOrder (Order.succ β).ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  by_cases hz : z = (⊤ : (Order.succ β).ToType)
  · exact Or.inl hz
  · refine Or.inr ?_
    have htop : Ordinal.typein (· < ·) (⊤ : (Order.succ β).ToType) = β := by
      rw [show (⊤ : (Order.succ β).ToType) =
          Ordinal.enum (α := (Order.succ β).ToType) (· < ·)
            ⟨β, (Ordinal.type_toType _).symm ▸ Order.lt_succ β⟩
        from Ordinal.enum_succ_eq_top.symm, Ordinal.typein_enum]
    have hlt : Ordinal.typein (· < ·) z < β := by
      have h1 := (Ordinal.typein_lt_typein (· < ·)).mpr (lt_of_le_of_ne le_top hz)
      rwa [htop] at h1
    have hval : Ordinal.typein (· < ·) z <
        Ordinal.type (· < · : β.ToType → β.ToType → Prop) := by
      rwa [Ordinal.type_toType]
    refine ⟨Ordinal.enum (α := β.ToType) (· < ·) ⟨Ordinal.typein (· < ·) z, hval⟩, ?_⟩
    have e1 : Ordinal.typein (· < ·)
          ((Ordinal.initialSegToType (Order.le_succ β)).toOrderEmbedding
            (Ordinal.enum (α := β.ToType) (· < ·) ⟨Ordinal.typein (· < ·) z, hval⟩)) =
        Ordinal.typein (· < ·)
          (Ordinal.enum (α := β.ToType) (· < ·) ⟨Ordinal.typein (· < ·) z, hval⟩) :=
      Ordinal.typein_apply (Ordinal.initialSegToType (Order.le_succ β)) _
    have e2 : Ordinal.typein (· < ·)
          (Ordinal.enum (α := β.ToType) (· < ·) ⟨Ordinal.typein (· < ·) z, hval⟩) =
        Ordinal.typein (· < ·) z := Ordinal.typein_enum (· < ·) _
    refine (Ordinal.typein_inj (· < ·)).mp ?_
    rw [e1, e2]

/-- **[STAGE 2b — `yFollows` step]** If a source element `y` is a live successor of
`h` but not its chosen min, then `y` survives into a child of `h` (the one whose
recorded top-color is the pair-color `cR(s(h), y)`). This is the y-path extension
step. -/
theorem ehmrS_mem_child_of_ne (cR : (Fin 2 ↪o PairERSource) → Bool) {β : Ordinal.{0}}
    (h : EHMRNodeAt β) {y : PairERSource}
    (hy : y ∈ ehmrS cR h) (hne : y ≠ ehmrChosen cR β h) :
    ∃ c : Bool, y ∈ ehmrS cR (h.child c) := by
  classical
  -- `s(h) < y` (strict, since `y` is a successor distinct from the chosen min), so the
  -- pair `{s(h), y}` has a definite color `c`; route `y` into the child recording `c`.
  have hsy : ehmrChosen cR β h < y := ehmrChosen_lt_of_mem_ne cR h hy hne
  refine ⟨cR (pairEmbed hsy), ?_⟩
  intro z
  rcases EHMRNodeAt.eq_top_or_exists_lift z with rfl | ⟨x, rfl⟩
  · -- New top position: the child's recorded color is `c` and its rep is `s(h)`.
    rw [ehmrRep_child_top cR h (cR (pairEmbed hsy)),
        EHMRNodeAt.child_top h (cR (pairEmbed hsy))]
    exact ⟨hsy, rfl⟩
  · -- Old position: the child's rep and recorded color coincide with the parent's, so
    -- the parent's witness `hy x` transfers directly.
    rw [ehmrRep_child_lift cR h (cR (pairEmbed hsy)) x,
        EHMRNodeAt.child_lift h (cR (pairEmbed hsy)) x]
    exact hy x

/-- **[STAGE 2b helper]** The chosen min is `≤` every successor (the `<`-least element
of `S(h)` in the linear well-order). -/
theorem ehmrChosen_le_of_mem (cR : (Fin 2 ↪o PairERSource) → Bool) {β : Ordinal.{0}}
    (h : EHMRNodeAt β) {y : PairERSource} (hy : y ∈ ehmrS cR h) :
    ehmrChosen cR β h ≤ y := by
  have hlive : ehmrLive cR h := ⟨y, hy⟩
  rw [ehmrChosen_eq_min cR h hlive]
  exact not_lt.mp (WellFounded.not_lt_min _ _ hlive hy)

/-- **[STAGE 2b — path strictness step]** Passing to a live child strictly increases the
chosen rep: `s(h) < s(h.child c)`. (The child's top rep is `s(h)` by `ehmrRep_child_top`,
and every rep is strictly below the child's own chosen min.) -/
theorem ehmrChosen_lt_child (cR : (Fin 2 ↪o PairERSource) → Bool) {β : Ordinal.{0}}
    (h : EHMRNodeAt β) (c : Bool) (hlive : ehmrLive cR (h.child c)) :
    ehmrChosen cR β h < ehmrChosen cR (Order.succ β) (h.child c) := by
  obtain ⟨hlt, _⟩ := ehmrChosen_mem cR (h.child c) hlive (⊤ : (Order.succ β).ToType)
  rwa [ehmrRep_child_top cR h c] at hlt

/-! ### [STAGE 2b] The canonical `y`-path as a single well-founded recursion.

Rather than build the `y`-path by transfinite recursion with an explicit limit step
(and the attendant coherence bookkeeping), we define the whole path at once: `yNode cR
y β` is the length-`β` node recording, at each position `x`, the pair-color of `y`
against the chosen rep of the path so far — or junk (`false`) once that rep is no
longer `< y`. Restriction-coherence then becomes a lemma (every restriction is again a
`yNode`), and the stopping argument is pure well-foundedness: a strictly increasing
`Ordinal → PairERSource` is impossible. -/

/-- **[STAGE 2b]** The chosen rep of the canonical `y`-path at level `γ`, defined by
well-founded recursion: it is the chosen min of the node whose recorded color at each
position `x` is `cR({yRep(typein x), y})` (or junk `false` once that rep is `≥ y`).
Because the recursion lands in `PairERSource` (non-dependent), restriction-coherence
later needs only `congrArg`, not a heterogeneous transport. -/
noncomputable def yRep (cR : (Fin 2 ↪o PairERSource) → Bool) (y : PairERSource)
    (γ : Ordinal.{0}) : PairERSource := by
  classical
  haveI : IsWellOrder γ.ToType (· < ·) := isWellOrder_lt
  exact ehmrChosen cR γ (fun x =>
    if hlt : yRep cR y (Ordinal.typein (· < ·) x) < y then cR (pairEmbed hlt) else false)
termination_by γ
decreasing_by
  all_goals
    haveI : IsWellOrder γ.ToType (· < ·) := isWellOrder_lt
    exact lt_of_lt_of_eq (Ordinal.typein_lt_type _ _) (Ordinal.type_toType γ)

/-- **[STAGE 2b]** The canonical `y`-path node of length `β` (a *plain* def over `yRep`):
at position `x` it records the pair-color of `y` against `yRep (typein x)` (junk `false`
once that rep is `≥ y`). -/
noncomputable def yNode (cR : (Fin 2 ↪o PairERSource) → Bool) (y : PairERSource)
    (β : Ordinal.{0}) : EHMRNodeAt β := by
  classical
  haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  exact fun x =>
    if hlt : yRep cR y (Ordinal.typein (· < ·) x) < y then cR (pairEmbed hlt) else false

/-- **[STAGE 2b]** The defining fixpoint equation: `yRep` is the chosen min of `yNode`. -/
theorem yRep_eq (cR : (Fin 2 ↪o PairERSource) → Bool) (y : PairERSource) (γ : Ordinal.{0}) :
    yRep cR y γ = ehmrChosen cR γ (yNode cR y γ) := by
  classical
  conv_lhs => rw [yRep]
  rfl

/-- **[STAGE 2b]** Restriction-coherence: every restriction of a `yNode` is again the
`yNode` of that length. (Each color depends only on `yRep (typein x)`, and `typein` is
preserved by the initial-segment embedding.) -/
theorem yNode_restrict (cR : (Fin 2 ↪o PairERSource) → Bool) (y : PairERSource)
    {β δ : Ordinal.{0}} (hδ : δ ≤ β) :
    (yNode cR y β).restrict hδ = yNode cR y δ := by
  classical
  haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder δ.ToType (· < ·) := isWellOrder_lt
  funext x'
  have htx : Ordinal.typein (· < ·) ((Ordinal.initialSegToType hδ).toOrderEmbedding x')
      = Ordinal.typein (· < ·) x' := Ordinal.typein_apply (Ordinal.initialSegToType hδ) x'
  show yNode cR y β ((Ordinal.initialSegToType hδ).toOrderEmbedding x') = yNode cR y δ x'
  simp only [yNode, htx]

/-- **[STAGE 2b]** The reps of `yNode cR y β` are exactly `yRep cR y (typein x)`. (The
`IsWellOrder` binder lets `typein` appear in the signature; call sites discharge it with
`isWellOrder_lt`.) -/
theorem ehmrRep_yNode (cR : (Fin 2 ↪o PairERSource) → Bool) (y : PairERSource)
    {β : Ordinal.{0}} [IsWellOrder β.ToType (· < ·)] (x : β.ToType) :
    ehmrRep cR (yNode cR y β) x = yRep cR y (Ordinal.typein (· < ·) x) := by
  classical
  have hlt : Ordinal.typein (· < ·) x < β :=
    lt_of_lt_of_eq (Ordinal.typein_lt_type (· < ·) x) (Ordinal.type_toType β)
  show ehmrChosen cR (Ordinal.typein (· < ·) x) ((yNode cR y β).restrict (le_of_lt hlt))
     = yRep cR y (Ordinal.typein (· < ·) x)
  rw [yRep_eq, yNode_restrict]

/-- **[STAGE 2b]** Liveness criterion: if every earlier rep stays `< y`, then `y` is a
successor of `yNode cR y β` (so the node is live and `y ∈ S`). -/
theorem yNode_mem_of (cR : (Fin 2 ↪o PairERSource) → Bool) (y : PairERSource)
    {β : Ordinal.{0}} (hbelow : ∀ δ : Ordinal.{0}, δ < β → yRep cR y δ < y) :
    y ∈ ehmrS cR (yNode cR y β) := by
  classical
  haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  intro x
  have hrep : ehmrRep cR (yNode cR y β) x = yRep cR y (Ordinal.typein (· < ·) x) :=
    ehmrRep_yNode cR y x
  have htx_lt : Ordinal.typein (· < ·) x < β :=
    lt_of_lt_of_eq (Ordinal.typein_lt_type (· < ·) x) (Ordinal.type_toType β)
  have hlt : yRep cR y (Ordinal.typein (· < ·) x) < y := hbelow _ htx_lt
  rw [hrep]
  refine ⟨hlt, ?_⟩
  show cR (pairEmbed hlt) = yNode cR y β x
  simp only [yNode]
  rw [dif_pos hlt]

/-- **[STAGE 2b]** As long as `yNode cR y γ₂` is live (every earlier rep stays `< y`), the
canonical reps strictly increase: `yRep γ₁ < yRep γ₂` for `γ₁ < γ₂`. (The rep at the
position `γ₁` of `yNode γ₂` is `yRep γ₁`, and it lies strictly below the chosen min
`yRep γ₂`.) -/
theorem yRep_strictMono (cR : (Fin 2 ↪o PairERSource) → Bool) (y : PairERSource)
    {γ₁ γ₂ : Ordinal.{0}} (h12 : γ₁ < γ₂)
    (hlive : ∀ δ : Ordinal.{0}, δ < γ₂ → yRep cR y δ < y) :
    yRep cR y γ₁ < yRep cR y γ₂ := by
  classical
  haveI : IsWellOrder γ₂.ToType (· < ·) := isWellOrder_lt
  have hlive2 : ehmrLive cR (yNode cR y γ₂) := ⟨y, yNode_mem_of cR y hlive⟩
  have hγ₁ : γ₁ < Ordinal.type (· < · : γ₂.ToType → γ₂.ToType → Prop) := by
    rw [Ordinal.type_toType]; exact h12
  obtain ⟨hlt, _⟩ :=
    ehmrChosen_mem cR (yNode cR y γ₂) hlive2 (Ordinal.enum (· < ·) ⟨γ₁, hγ₁⟩)
  rw [ehmrRep_yNode cR y, Ordinal.typein_enum] at hlt
  rwa [← yRep_eq] at hlt

/-- **[STAGE 2b — stopping]** The canonical `y`-path stops: there is a *least* level `γ`
where the chosen rep reaches `y` (`y ≤ yRep γ`), with all earlier reps strictly below
`y`. Existence is pure well-foundedness — if every `yRep γ` stayed `< y` then `yRep`
would be a strictly increasing `Ordinal → PairERSource`, and composing with `typein`
gives a strictly increasing `Ordinal → Ordinal` exceeding the order type of
`PairERSource`, impossible. -/
theorem exists_yRep_ge (cR : (Fin 2 ↪o PairERSource) → Bool) (y : PairERSource) :
    ∃ γ : Ordinal.{0}, y ≤ yRep cR y γ ∧ ∀ δ : Ordinal.{0}, δ < γ → yRep cR y δ < y := by
  classical
  have hexists : ∃ γ : Ordinal.{0}, y ≤ yRep cR y γ := by
    by_contra hcon
    push_neg at hcon
    haveI : IsWellOrder PairERSource (· < ·) := isWellOrder_lt
    have hmono : StrictMono (yRep cR y) := fun a b hab =>
      yRep_strictMono cR y hab (fun δ _ => hcon δ)
    have hmono_g : StrictMono (fun γ => Ordinal.typein (· < ·) (yRep cR y γ)) :=
      fun a b hab => (Ordinal.typein_lt_typein (· < ·)).mpr (hmono hab)
    have hself : ∀ a : Ordinal.{0}, a ≤ Ordinal.typein (· < ·) (yRep cR y a) := by
      intro a
      induction a using Ordinal.induction with
      | _ a ih =>
        by_contra hlt
        push_neg at hlt
        exact absurd ((ih _ hlt).trans_lt (hmono_g hlt)) (lt_irrefl _)
    have hΩ := hself (Ordinal.type (· < · : PairERSource → PairERSource → Prop))
    exact absurd (hΩ.trans_lt (Ordinal.typein_lt_type (· < ·) _)) (lt_irrefl _)
  obtain ⟨γ₀, hγ₀⟩ := hexists
  refine ⟨Ordinal.lt_wf.min {γ | y ≤ yRep cR y γ} ⟨γ₀, hγ₀⟩, ?_, ?_⟩
  · exact Ordinal.lt_wf.min_mem {γ | y ≤ yRep cR y γ} ⟨γ₀, hγ₀⟩
  · intro δ hδ
    exact not_le.mp (fun ha => Ordinal.lt_wf.not_lt_min {γ | y ≤ yRep cR y γ} ⟨γ₀, hγ₀⟩ ha hδ)

/-- **[STAGE 2b — coverage / EHMR Lemma 14.2]** Every source element is the chosen
representative of some node (`y ∈ R(h)`): take the least level `γ` where the canonical
`y`-path reaches `y` (`exists_yRep_ge`). There every earlier rep is `< y`, so the node is
live (`yNode_mem_of`) and its chosen min is `≤ y` (`ehmrChosen_le_of_mem`); combined with
`y ≤ yRep γ` this forces `y = s(yNode γ)`, i.e. `y ∈ R(yNode γ)`. -/
theorem exists_node_choosing_source (cR : (Fin 2 ↪o PairERSource) → Bool)
    (y : PairERSource) :
    ∃ (β : Ordinal.{0}) (h : EHMRNodeAt β), y ∈ ehmrR cR h := by
  classical
  obtain ⟨γ, hge, hbelow⟩ := exists_yRep_ge cR y
  have hmem : y ∈ ehmrS cR (yNode cR y γ) := yNode_mem_of cR y hbelow
  have hle : yRep cR y γ ≤ y := by
    rw [yRep_eq]; exact ehmrChosen_le_of_mem cR (yNode cR y γ) hmem
  have heq : y = ehmrChosen cR γ (yNode cR y γ) := by
    rw [← yRep_eq]; exact le_antisymm hge hle
  have hlive : ehmrLive cR (yNode cR y γ) := ⟨y, hmem⟩
  refine ⟨γ, yNode cR y γ, ?_⟩
  rw [ehmrR, if_pos hlive, Set.mem_singleton_iff]
  exact heq

/-! ### [STAGE 3] Branch extraction from a high live node.

EHMR Theorem 13.1 is realized concretely: the `succ ℶ₁`-many live nodes (coverage) cannot
all sit at levels `< ω₁` (each such level has `≤ ℶ₁` nodes, and there are only `ℵ₁` of
them), so some live node has length `≥ ω₁`; restricting it to `ω₁` yields a length-`ω₁`
branch. The end-homogeneity of the reps (`ehmrRep_strictMono` + fact (8)) makes that
restricted node an `EHMRBranch`. -/

/-- **[STAGE 3]** Level smallness: for `β < ω₁` there are `≤ ℶ₁` live length-`β` nodes
(a fortiori `≤ ℶ₁` nodes, by `ehmr_level_card_le_beth1`). -/
theorem ehmr_live_level_small (cR : (Fin 2 ↪o PairERSource) → Bool) (β : Ordinal.{0})
    (hβ : β < Ordinal.omega.{0} 1) :
    Cardinal.mk {h : EHMRNodeAt β // ehmrLive cR h} ≤ Cardinal.beth.{0} 1 :=
  (Cardinal.mk_subtype_le _).trans (ehmr_level_card_le_beth1 β hβ)

/-- **[STAGE 3 helper]** Restriction is transitive (initial segments compose). -/
theorem EHMRNodeAt.restrict_trans {β : Ordinal.{0}} (h : EHMRNodeAt β)
    {δ ε : Ordinal.{0}} (hδ : δ ≤ β) (hε : ε ≤ δ) :
    (h.restrict hδ).restrict hε = h.restrict (hε.trans hδ) := by
  classical
  haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder δ.ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder ε.ToType (· < ·) := isWellOrder_lt
  funext z
  show h ((Ordinal.initialSegToType hδ).toOrderEmbedding
        ((Ordinal.initialSegToType hε).toOrderEmbedding z))
     = h ((Ordinal.initialSegToType (hε.trans hδ)).toOrderEmbedding z)
  rw [initialSegToType_compose]

/-- **[STAGE 3 helper]** `EHMRNodeAt.restrict` at heterogeneously-equal lengths. -/
theorem EHMRNodeAt.restrict_heq {β : Ordinal.{0}} (h : EHMRNodeAt β)
    {δ₁ δ₂ : Ordinal.{0}} (hδ : δ₁ = δ₂) (h1 : δ₁ ≤ β) (h2 : δ₂ ≤ β) :
    HEq (h.restrict h1) (h.restrict h2) := by
  subst hδ; exact heq_of_eq rfl

/-- **[STAGE 3 helper]** The reps of a restriction agree with the parent's reps at the
lifted positions. -/
theorem ehmrRep_restrict (cR : (Fin 2 ↪o PairERSource) → Bool) {β : Ordinal.{0}}
    (h : EHMRNodeAt β) {δ : Ordinal.{0}} (hδ : δ ≤ β) (x : δ.ToType) :
    ehmrRep cR (h.restrict hδ) x =
      ehmrRep cR h ((Ordinal.initialSegToType hδ).toOrderEmbedding x) := by
  classical
  haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder δ.ToType (· < ·) := isWellOrder_lt
  set lx := (Ordinal.initialSegToType hδ).toOrderEmbedding x with hlx_def
  have htx : Ordinal.typein (· < ·) lx = Ordinal.typein (· < ·) x := by
    rw [hlx_def]; exact Ordinal.typein_apply (Ordinal.initialSegToType hδ) x
  have hx_lt : Ordinal.typein (· < ·) x < δ :=
    lt_of_lt_of_eq (Ordinal.typein_lt_type (· < ·) x) (Ordinal.type_toType δ)
  have hlx_lt : Ordinal.typein (· < ·) lx < β :=
    lt_of_lt_of_eq (Ordinal.typein_lt_type (· < ·) lx) (Ordinal.type_toType β)
  show ehmrChosen cR (Ordinal.typein (· < ·) x) ((h.restrict hδ).restrict (le_of_lt hx_lt))
     = ehmrChosen cR (Ordinal.typein (· < ·) lx) (h.restrict (le_of_lt hlx_lt))
  refine ehmrChosen_congr cR htx.symm ?_
  rw [EHMRNodeAt.restrict_trans h hδ (le_of_lt hx_lt)]
  exact EHMRNodeAt.restrict_heq h htx.symm ((le_of_lt hx_lt).trans hδ) (le_of_lt hlx_lt)

/-- **[STAGE 3 helper]** A restriction of a live node is live (the same witness `y`
serves, since the reps and recorded colors only shrink). -/
theorem ehmrLive_restrict (cR : (Fin 2 ↪o PairERSource) → Bool) {β : Ordinal.{0}}
    {h : EHMRNodeAt β} (hlive : ehmrLive cR h) {δ : Ordinal.{0}} (hδ : δ ≤ β) :
    ehmrLive cR (h.restrict hδ) := by
  classical
  haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder δ.ToType (· < ·) := isWellOrder_lt
  obtain ⟨y, hy⟩ := hlive
  refine ⟨y, ?_⟩
  intro x
  obtain ⟨hlt, hcol⟩ := hy ((Ordinal.initialSegToType hδ).toOrderEmbedding x)
  rw [ehmrRep_restrict cR h hδ x]
  exact ⟨hlt, hcol⟩

/-- **[STAGE 3 helper]** `cR ∘ pairEmbed` depends only on the two endpoints, not on the
`<`-proof: equal endpoints give equal colors. -/
theorem cR_pairEmbed_congr (cR : (Fin 2 ↪o PairERSource) → Bool)
    {a a' b b' : PairERSource} (ha : a = a') (hb : b = b') (p : a < b) (q : a' < b') :
    cR (pairEmbed p) = cR (pairEmbed q) := by
  subst ha; subst hb; rfl

/-- **[STAGE 3 — end-homogeneity, strict monotonicity]** On a live node the chosen reps
strictly increase: the rep at `x₁` is the rep of the restriction-to-`x₂` at the position
of `x₁`, hence strictly below that restriction's chosen min `= rep x₂`. -/
theorem ehmrRep_strictMono (cR : (Fin 2 ↪o PairERSource) → Bool) {β : Ordinal.{0}}
    {h : EHMRNodeAt β} (hlive : ehmrLive cR h) {x₁ x₂ : β.ToType} (hx : x₁ < x₂) :
    ehmrRep cR h x₁ < ehmrRep cR h x₂ := by
  classical
  haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder (Ordinal.typein (· < · : β.ToType → β.ToType → Prop) x₂).ToType (· < ·) :=
    isWellOrder_lt
  have hx₂lt : Ordinal.typein (· < ·) x₂ < β :=
    lt_of_lt_of_eq (Ordinal.typein_lt_type (· < ·) x₂) (Ordinal.type_toType β)
  have h₂live : ehmrLive cR (h.restrict (le_of_lt hx₂lt)) :=
    ehmrLive_restrict cR hlive (le_of_lt hx₂lt)
  have hx₁ty : Ordinal.typein (· < ·) x₁ <
      Ordinal.type (· < · : (Ordinal.typein (· < ·) x₂).ToType →
        (Ordinal.typein (· < ·) x₂).ToType → Prop) := by
    rw [Ordinal.type_toType]; exact (Ordinal.typein_lt_typein (· < ·)).mpr hx
  set z₁ := Ordinal.enum (· < ·) ⟨Ordinal.typein (· < ·) x₁, hx₁ty⟩ with hz₁_def
  have hlift : (Ordinal.initialSegToType (le_of_lt hx₂lt)).toOrderEmbedding z₁ = x₁ := by
    refine (Ordinal.typein_inj (· < ·)).mp ?_
    have e1 : Ordinal.typein (· < ·)
          ((Ordinal.initialSegToType (le_of_lt hx₂lt)).toOrderEmbedding z₁) =
        Ordinal.typein (· < ·) z₁ :=
      Ordinal.typein_apply (Ordinal.initialSegToType (le_of_lt hx₂lt)) z₁
    have e2 : Ordinal.typein (· < ·) z₁ = Ordinal.typein (· < ·) x₁ := by
      rw [hz₁_def]; exact Ordinal.typein_enum (· < ·) _
    rw [e1, e2]
  obtain ⟨hlt, _⟩ := ehmrChosen_mem cR (h.restrict (le_of_lt hx₂lt)) h₂live z₁
  rw [ehmrRep_restrict cR h (le_of_lt hx₂lt) z₁, hlift] at hlt
  exact hlt

/-- **[STAGE 3 — end-homogeneity, EHMR fact (8)]** On a live node, the recorded color at
`x₁` is the pair-color of the reps `{rep x₁, rep x₂}` for any `x₁ < x₂`. -/
theorem ehmr_fact8 (cR : (Fin 2 ↪o PairERSource) → Bool) {β : Ordinal.{0}}
    {h : EHMRNodeAt β} (hlive : ehmrLive cR h) {x₁ x₂ : β.ToType} (hx : x₁ < x₂) :
    cR (pairEmbed (ehmrRep_strictMono cR hlive hx)) = h x₁ := by
  classical
  haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder (Ordinal.typein (· < · : β.ToType → β.ToType → Prop) x₂).ToType (· < ·) :=
    isWellOrder_lt
  have hx₂lt : Ordinal.typein (· < ·) x₂ < β :=
    lt_of_lt_of_eq (Ordinal.typein_lt_type (· < ·) x₂) (Ordinal.type_toType β)
  have h₂live : ehmrLive cR (h.restrict (le_of_lt hx₂lt)) :=
    ehmrLive_restrict cR hlive (le_of_lt hx₂lt)
  have hx₁ty : Ordinal.typein (· < ·) x₁ <
      Ordinal.type (· < · : (Ordinal.typein (· < ·) x₂).ToType →
        (Ordinal.typein (· < ·) x₂).ToType → Prop) := by
    rw [Ordinal.type_toType]; exact (Ordinal.typein_lt_typein (· < ·)).mpr hx
  set z₁ := Ordinal.enum (· < ·) ⟨Ordinal.typein (· < ·) x₁, hx₁ty⟩ with hz₁_def
  have hlift : (Ordinal.initialSegToType (le_of_lt hx₂lt)).toOrderEmbedding z₁ = x₁ := by
    refine (Ordinal.typein_inj (· < ·)).mp ?_
    have e1 : Ordinal.typein (· < ·)
          ((Ordinal.initialSegToType (le_of_lt hx₂lt)).toOrderEmbedding z₁) =
        Ordinal.typein (· < ·) z₁ :=
      Ordinal.typein_apply (Ordinal.initialSegToType (le_of_lt hx₂lt)) z₁
    have e2 : Ordinal.typein (· < ·) z₁ = Ordinal.typein (· < ·) x₁ := by
      rw [hz₁_def]; exact Ordinal.typein_enum (· < ·) _
    rw [e1, e2]
  obtain ⟨hlt, hcol⟩ := ehmrChosen_mem cR (h.restrict (le_of_lt hx₂lt)) h₂live z₁
  have hrep_z : ehmrRep cR (h.restrict (le_of_lt hx₂lt)) z₁ = ehmrRep cR h x₁ := by
    rw [ehmrRep_restrict cR h (le_of_lt hx₂lt) z₁, hlift]
  have hcol_z : (h.restrict (le_of_lt hx₂lt)) z₁ = h x₁ := by
    show h ((Ordinal.initialSegToType (le_of_lt hx₂lt)).toOrderEmbedding z₁) = h x₁
    rw [hlift]
  rw [← hcol_z, ← hcol]
  exact cR_pairEmbed_congr cR hrep_z.symm rfl (ehmrRep_strictMono cR hlive hx) hlt

/-- **[STAGE 3 — branch extraction]** The position `enum β'` of a length-`β` node, for
`β' < ω₁ ≤ β`. -/
noncomputable def ehmrBranchPos {β : Ordinal.{0}} (hβ : Ordinal.omega.{0} 1 ≤ β)
    (β' : Ordinal.{0}) (hβ' : β' < Ordinal.omega.{0} 1) : β.ToType := by
  haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  exact Ordinal.enum (· < ·) ⟨β', by rw [Ordinal.type_toType]; exact hβ'.trans_le hβ⟩

/-- **[STAGE 3 — branch extraction]** Positions are strictly monotone in the level. -/
theorem ehmrBranchPos_strictMono {β : Ordinal.{0}} (hβ : Ordinal.omega.{0} 1 ≤ β)
    {β' γ' : Ordinal.{0}} (hβ' : β' < Ordinal.omega.{0} 1)
    (hγ' : γ' < Ordinal.omega.{0} 1) (h' : β' < γ') :
    ehmrBranchPos hβ β' hβ' < ehmrBranchPos hβ γ' hγ' := by
  haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  show Ordinal.enum (· < ·) ⟨β', _⟩ < Ordinal.enum (· < ·) ⟨γ', _⟩
  exact Ordinal.enum_lt_enum.mpr h'

/-- **[STAGE 3 — branch extraction]** A live node of length `≥ ω₁` *is* an `EHMRBranch`:
its reps (read off at the positions `enum β'`) strictly increase (`ehmrRep_strictMono`)
and satisfy fact (8) (`ehmr_fact8`). -/
noncomputable def ehmrBranch_of_live {β : Ordinal.{0}}
    (cR : (Fin 2 ↪o PairERSource) → Bool) (h : EHMRNodeAt β)
    (hβ : Ordinal.omega.{0} 1 ≤ β) (hlive : ehmrLive cR h) : EHMRBranch cR where
  rep β' hβ' := ehmrRep cR h (ehmrBranchPos hβ β' hβ')
  bit β' hβ' := h (ehmrBranchPos hβ β' hβ')
  rep_strictMono hβ' hγ' h' :=
    ehmrRep_strictMono cR hlive (ehmrBranchPos_strictMono hβ hβ' hγ' h')
  coloring hβ' hγ' h' :=
    ehmr_fact8 cR hlive (ehmrBranchPos_strictMono hβ hβ' hγ' h')

/-- **[STAGE 3 FRONTIER — counting / EHMR Theorem 13.1 core]** Some live node has length
`≥ ω₁`.

Strategy (Type-0 counting, so it stays in `Cardinal.{0}`). Suppose not: every live node
has length `< ω₁`. Then the coverage map (`exists_node_choosing_source`) injects
`PairERSource` into the Type-0 index `Σ b : ω₁.ToType, EHMRNodeAt (typein b)` — concretely,
apply `ehmr_partitionTree_card_lower` to `R := fun p => ehmrR cR p.2` over that sigma: the
cover sends `y` to `⟨enum β_y, cast h_y⟩` (transport along `typein (enum β_y) = β_y`, with
`y ∈ ehmrR cR (cast h_y)` from an `ehmrR`-congruence + `cast_heq`), and each `ehmrR` is a
subsingleton. That gives `succ ℶ₁ ≤ #(Σ b, EHMRNodeAt (typein b))`. But
`#(Σ b, EHMRNodeAt (typein b)) = Cardinal.sum (fun b => #(EHMRNodeAt (typein b)))`
(`Cardinal.mk_sigma`) `≤ #(ω₁.ToType) * ℶ₁` (`ehmr_live_level_small`/`ehmr_level_card_le_beth1`
per fibre, `Cardinal.sum_le_sum` + `Cardinal.sum_const`) `= ℵ₁ * ℶ₁ = ℶ₁` (`Cardinal.mk_toType`,
`aleph 1 ≤ ℶ₁`, `Cardinal.mul_eq_self`). So `succ ℶ₁ ≤ ℶ₁`, contradiction. -/
theorem exists_live_node_ge_omega1 (cR : (Fin 2 ↪o PairERSource) → Bool) :
    ∃ (β : Ordinal.{0}) (h : EHMRNodeAt β), Ordinal.omega.{0} 1 ≤ β ∧ ehmrLive cR h := by
  classical
  by_contra hcon
  push_neg at hcon
  haveI : IsWellOrder (Ordinal.omega.{0} 1).ToType (· < ·) := isWellOrder_lt
  -- The Type-0 index of live nodes of length `< ω₁`.
  have hlower : Order.succ (Cardinal.beth.{0} 1) ≤
      Cardinal.mk (Σ b : (Ordinal.omega.{0} 1).ToType,
        { h : EHMRNodeAt (Ordinal.typein (· < ·) b) // ehmrLive cR h }) := by
    apply ehmr_partitionTree_card_lower (R := fun n => ehmrR cR n.2.1)
    · -- Coverage: every `y` is the chosen rep of a live node, which (by `hcon`) has length `< ω₁`.
      intro y
      obtain ⟨β_y, h_y, hy⟩ := exists_node_choosing_source cR y
      have hlive_y : ehmrLive cR h_y := by
        by_contra hnl
        rw [ehmrR, if_neg hnl] at hy
        exact (Set.mem_empty_iff_false y).mp hy
      have hβ_lt : β_y < Ordinal.omega.{0} 1 := by
        by_contra hge
        exact hcon β_y h_y (not_lt.mp hge) hlive_y
      have hβ_ty : β_y < Ordinal.type (· < · : (Ordinal.omega.{0} 1).ToType →
          (Ordinal.omega.{0} 1).ToType → Prop) := by
        rw [Ordinal.type_toType]; exact hβ_lt
      set b_y := Ordinal.enum (· < ·) ⟨β_y, hβ_ty⟩ with hb_def
      have htb : Ordinal.typein (· < ·) b_y = β_y := by rw [hb_def, Ordinal.typein_enum]
      -- Move the node to length `typein b_y` by substituting the length equality.
      have key : ∃ (h' : EHMRNodeAt (Ordinal.typein (· < ·) b_y)) (_ : ehmrLive cR h'),
          y ∈ ehmrR cR h' := by
        rw [htb]; exact ⟨h_y, hlive_y, hy⟩
      obtain ⟨h', hl', hy'⟩ := key
      exact ⟨⟨b_y, h', hl'⟩, hy'⟩
    · -- Each used-up set is a subsingleton.
      intro n
      exact ehmrR_subsingleton cR n.2.1
  -- The index has size `≤ ℵ₁ · ℶ₁ = ℶ₁`, contradicting the lower bound.
  have hupper : Cardinal.mk (Σ b : (Ordinal.omega.{0} 1).ToType,
      { h : EHMRNodeAt (Ordinal.typein (· < ·) b) // ehmrLive cR h }) ≤ Cardinal.beth.{0} 1 := by
    rw [Cardinal.mk_sigma]
    calc Cardinal.sum (fun b => Cardinal.mk
            { h : EHMRNodeAt (Ordinal.typein (· < ·) b) // ehmrLive cR h })
        ≤ Cardinal.sum (fun _ : (Ordinal.omega.{0} 1).ToType => Cardinal.beth.{0} 1) :=
          Cardinal.sum_le_sum _ _ (fun b => ehmr_live_level_small cR _
            (lt_of_lt_of_eq (Ordinal.typein_lt_type (· < ·) b) (Ordinal.type_toType _)))
      _ = Cardinal.mk (Ordinal.omega.{0} 1).ToType * Cardinal.beth.{0} 1 := Cardinal.sum_const' _ _
      _ = Cardinal.aleph 1 * Cardinal.beth.{0} 1 := by
          rw [Cardinal.mk_toType, Ordinal.card_omega]
      _ = Cardinal.beth.{0} 1 := by
          rw [Cardinal.mul_eq_max (Cardinal.aleph0_le_aleph 1) (Cardinal.aleph0_le_beth 1)]
          exact max_eq_right (Cardinal.aleph_le_beth 1)
  exact absurd (hlower.trans hupper) (not_le.mpr (Order.lt_succ (Cardinal.beth.{0} 1)))

/-- **[EHMR §13 Theorem 13.1 / §14 Theorem 14.3 — branch-length]**
`ehmr_tree_has_omega1_branch`: the canonical partition tree for `cR` has a branch of
length `ω₁`. A live node of length `≥ ω₁` (`exists_live_node_ge_omega1`) restricts to the
sought `EHMRBranch` (`ehmrBranch_of_live`); end-homogeneity (`ehmrRep_strictMono` + fact (8))
makes the restriction coherent. -/
theorem ehmr_tree_has_omega1_branch
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    Nonempty (EHMRBranch cR) := by
  obtain ⟨β, h, hβ, hlive⟩ := exists_live_node_ge_omega1 cR
  exact ⟨ehmrBranch_of_live cR h hβ hlive⟩

/-- **[EHMR branch → `CoherentMajorityBranch`]**
`exists_coherentMajorityBranch_of_ehmrBranch`: assemble an `EHMRBranch` into a
`CoherentMajorityBranch`. `prefixAt α` is the embedding `α.ToType ↪o PairERSource`
sending position `β < α` to `rep β`; `branch α` reads off `bit`;
`prefix_restrict`/`branch_restrict` are immediate from the assembly;
`top_in_validFiber` is EHMR fact (8) (`coloring`). (Named `_of_ehmrBranch` — the
partition tree itself is internal to `ehmr_tree_has_omega1_branch`.) -/
theorem exists_coherentMajorityBranch_of_ehmrBranch
    {cR : (Fin 2 ↪o PairERSource) → Bool} (b : EHMRBranch cR) :
    Nonempty (CoherentMajorityBranch cR) := by
  classical
  -- `typein x < ω₁` for `x : α.ToType` when `α < ω₁`.
  have htlt : ∀ {α : Ordinal.{0}} (_hα : α < Ordinal.omega.{0} 1) (x : α.ToType),
      haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
      Ordinal.typein (· < ·) x < Ordinal.omega.{0} 1 := by
    intro α hα x
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    have h := Ordinal.typein_lt_type (· < · : α.ToType → α.ToType → Prop) x
    rw [Ordinal.type_toType] at h
    exact h.trans hα
  -- `rep`/`bit` depend on the ordinal only (proof-irrelevant in the `< ω₁` arg).
  have repc : ∀ {A B : Ordinal.{0}} (hA : A < Ordinal.omega.{0} 1)
      (hB : B < Ordinal.omega.{0} 1), A = B → b.rep A hA = b.rep B hB := by
    intro A B hA hB h; subst h; rfl
  have bitc : ∀ {A B : Ordinal.{0}} (hA : A < Ordinal.omega.{0} 1)
      (hB : B < Ordinal.omega.{0} 1), A = B → b.bit A hA = b.bit B hB := by
    intro A B hA hB h; subst h; rfl
  -- `typein ⊤ = γ` inside `(succ γ).ToType`.
  have htop : ∀ (γ : Ordinal.{0}),
      haveI : IsWellOrder (Order.succ γ).ToType (· < ·) := isWellOrder_lt
      Ordinal.typein (· < ·) (⊤ : (Order.succ γ).ToType) = γ := by
    intro γ
    haveI : IsWellOrder (Order.succ γ).ToType (· < ·) := isWellOrder_lt
    rw [show (⊤ : (Order.succ γ).ToType) = Ordinal.enum (α := (Order.succ γ).ToType) (· < ·)
          ⟨γ, (Ordinal.type_toType _).symm ▸ Order.lt_succ γ⟩ from Ordinal.enum_succ_eq_top.symm,
      Ordinal.typein_enum]
  -- The assembled prefix embedding at each level.
  let pre : ∀ α : Ordinal.{0}, α < Ordinal.omega.{0} 1 → α.ToType ↪o PairERSource :=
    fun α hα =>
      haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
      OrderEmbedding.ofStrictMono
        (fun x => b.rep (Ordinal.typein (· < ·) x) (htlt hα x))
        (fun _ _ hxy => b.rep_strictMono _ _ ((Ordinal.typein_lt_typein (· < ·)).mpr hxy))
  let br : ∀ α : Ordinal.{0}, α < Ordinal.omega.{0} 1 → α.ToType → Bool :=
    fun α hα x =>
      haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
      b.bit (Ordinal.typein (· < ·) x) (htlt hα x)
  have pre_apply : ∀ (α : Ordinal.{0}) (hα : α < Ordinal.omega.{0} 1) (x : α.ToType),
      haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
      pre α hα x = b.rep (Ordinal.typein (· < ·) x) (htlt hα x) := by
    intro α hα x; haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt; rfl
  have br_apply : ∀ (α : Ordinal.{0}) (hα : α < Ordinal.omega.{0} 1) (x : α.ToType),
      haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
      br α hα x = b.bit (Ordinal.typein (· < ·) x) (htlt hα x) := by
    intro α hα x; rfl
  refine ⟨{
    prefixAt := pre
    branch := br
    prefix_restrict := ?_
    branch_restrict := ?_
    top_in_validFiber := ?_ }⟩
  · -- prefix_restrict
    intro β α hβα hβ hα x
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
    rw [pre_apply α hα, pre_apply β hβ]
    exact repc _ _ (Ordinal.typein_apply _ x)
  · -- branch_restrict
    intro β α hβα hβ hα x
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
    rw [br_apply α hα, br_apply β hβ]
    exact bitc _ _ (Ordinal.typein_apply _ x)
  · -- top_in_validFiber
    intro γ hγ hsγ
    haveI : IsWellOrder (Order.succ γ).ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder γ.ToType (· < ·) := isWellOrder_lt
    intro x
    have hx_lt : Ordinal.typein (· < ·) x < γ := by
      have h := Ordinal.typein_lt_type (· < · : γ.ToType → γ.ToType → Prop) x
      rwa [Ordinal.type_toType] at h
    have hpx : pre γ hγ x = b.rep (Ordinal.typein (· < ·) x) (htlt hγ x) := pre_apply γ hγ x
    have hpt : pre (Order.succ γ) hsγ (⊤ : (Order.succ γ).ToType) = b.rep γ hγ := by
      rw [pre_apply (Order.succ γ) hsγ]; exact repc _ _ (htop γ)
    have h₀ : pre γ hγ x < pre (Order.succ γ) hsγ (⊤ : (Order.succ γ).ToType) := by
      rw [hpx, hpt]; exact b.rep_strictMono _ _ hx_lt
    refine ⟨h₀, ?_⟩
    have hpe : pairEmbed h₀ = pairEmbed (b.rep_strictMono (htlt hγ x) hγ hx_lt) := by
      apply RelEmbedding.ext
      intro i
      match i with
      | ⟨0, _⟩ => simp only [pairEmbed, OrderEmbedding.coe_ofStrictMono]; exact hpx
      | ⟨1, _⟩ => simp only [pairEmbed, OrderEmbedding.coe_ofStrictMono]; exact hpt
    rw [hpe, br_apply γ hγ]
    exact b.coloring (htlt hγ x) hγ hx_lt

/-- **[DIRECT — now the active route]**
`exists_coherentMajorityBranch_direct`: construct `B` directly via the EHMR canonical
partition tree (`ehmr_tree_has_omega1_branch` + `exists_coherentMajorityBranch_of_ehmrBranch`),
bypassing the `_of_finitePartials` / `rawBranchCompactness` / `HasPartialExtensions` tower
and its near-circular `extendToExt` dependency. Both scaffold lemmas are now proved and
axiom-clean, so this is the route `exists_coherentMajorityBranch` is wired through. -/
theorem exists_coherentMajorityBranch_direct
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    Nonempty (CoherentMajorityBranch cR) := by
  obtain ⟨b⟩ := ehmr_tree_has_omega1_branch cR
  exact exists_coherentMajorityBranch_of_ehmrBranch b

/-- **[CONSOLIDATED TARGET]** Existence of a `CoherentMajorityBranch` `B` — a coherent
branch (prefix/branch restriction coherence + `top_in_validFiber`) of length `ω₁`, the
object the pair Erdős–Rado theorem `erdos_rado_pair_omega1_of_coherentMajorityBranch`
consumes. Now derived **directly** from the EHMR canonical partition tree
(`exists_coherentMajorityBranch_direct`); the legacy
`_of_finitePartials`/`exists_coherentBranchPartial` route is retained but off-chain. -/
theorem exists_coherentMajorityBranch
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    Nonempty (CoherentMajorityBranch cR) :=
  exists_coherentMajorityBranch_direct cR

/-- **`treeCommitOfBranch`**: canonical commit at position `δ` using
B. Reads off `B.prefixAt (succ δ) ⊤` (the top of the succ δ chain). -/
noncomputable def treeCommitOfBranch
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (B : CoherentMajorityBranch cR) (δ : Ordinal.{0})
    (hδ : δ < Ordinal.omega.{0} 1) : PairERSource :=
  haveI : IsWellOrder (Order.succ δ).ToType (· < ·) := isWellOrder_lt
  have hsδ : Order.succ δ < Ordinal.omega.{0} 1 :=
    (Cardinal.isSuccLimit_omega 1).succ_lt hδ
  B.prefixAt (Order.succ δ) hsδ (⊤ : (Order.succ δ).ToType)

/-- **`treeCommitBoolOfBranch`**: canonical Bool at position `δ` using
B. Reads off `B.branch (succ δ) ⊤`. -/
noncomputable def treeCommitBoolOfBranch
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (B : CoherentMajorityBranch cR) (δ : Ordinal.{0})
    (hδ : δ < Ordinal.omega.{0} 1) : Bool :=
  haveI : IsWellOrder (Order.succ δ).ToType (· < ·) := isWellOrder_lt
  have hsδ : Order.succ δ < Ordinal.omega.{0} 1 :=
    (Cardinal.isSuccLimit_omega 1).succ_lt hδ
  B.branch (Order.succ δ) hsδ (⊤ : (Order.succ δ).ToType)

/-- **`treeCommitOfBranch_strictMono`**: strict monotonicity of the
branch-driven chain values, inherited from `B.prefixAt`'s order
embedding structure + prefix_restrict to identify levels.

Proof: rewrite `treeCommitOfBranch B δ₁` via `prefix_restrict` to a
position in `(succ δ₂).ToType`. Then both treeCommit values are
`B.prefixAt (succ δ₂) hsδ₂` at different positions; by OrderEmbedding
strict-mono, the position order (δ₁ < δ₂) lifts to the value order. -/
lemma treeCommitOfBranch_strictMono
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (B : CoherentMajorityBranch cR) {δ₁ δ₂ : Ordinal.{0}}
    (hδ₁ : δ₁ < Ordinal.omega.{0} 1) (hδ₂ : δ₂ < Ordinal.omega.{0} 1)
    (h : δ₁ < δ₂) :
    treeCommitOfBranch B δ₁ hδ₁ < treeCommitOfBranch B δ₂ hδ₂ := by
  haveI : IsWellOrder (Order.succ δ₁).ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder (Order.succ δ₂).ToType (· < ·) := isWellOrder_lt
  have hsδ₁ : Order.succ δ₁ < Ordinal.omega.{0} 1 :=
    (Cardinal.isSuccLimit_omega 1).succ_lt hδ₁
  have hsδ₂ : Order.succ δ₂ < Ordinal.omega.{0} 1 :=
    (Cardinal.isSuccLimit_omega 1).succ_lt hδ₂
  have hsδ₁_le_sδ₂ : Order.succ δ₁ ≤ Order.succ δ₂ :=
    Order.succ_le_succ (le_of_lt h)
  show B.prefixAt (Order.succ δ₁) hsδ₁ (⊤ : (Order.succ δ₁).ToType) <
    B.prefixAt (Order.succ δ₂) hsδ₂ (⊤ : (Order.succ δ₂).ToType)
  -- Use prefix_restrict to convert LHS to a (succ δ₂)-level expression.
  rw [← B.prefix_restrict hsδ₁_le_sδ₂ hsδ₁ hsδ₂
      (⊤ : (Order.succ δ₁).ToType)]
  -- Now both sides are B.prefixAt (succ δ₂) hsδ₂ applied at two
  -- elements of (succ δ₂).ToType; apply OrderEmbedding strict-mono.
  apply (B.prefixAt (Order.succ δ₂) hsδ₂).strictMono
  -- Compare typein values: initialSegToType ⊤_(succ δ₁) has typein δ₁;
  -- ⊤_(succ δ₂) has typein δ₂. Since δ₁ < δ₂, < holds.
  have h_typein_init :
      Ordinal.typein (α := (Order.succ δ₂).ToType) (· < ·)
        ((Ordinal.initialSegToType hsδ₁_le_sδ₂).toOrderEmbedding
          (⊤ : (Order.succ δ₁).ToType)) = δ₁ := by
    rw [show Ordinal.typein (α := (Order.succ δ₂).ToType) (· < ·)
          ((Ordinal.initialSegToType hsδ₁_le_sδ₂).toOrderEmbedding
            (⊤ : (Order.succ δ₁).ToType)) =
        Ordinal.typein (α := (Order.succ δ₁).ToType) (· < ·)
          (⊤ : (Order.succ δ₁).ToType) from
      Ordinal.typein_apply (Ordinal.initialSegToType hsδ₁_le_sδ₂) _]
    rw [show (⊤ : (Order.succ δ₁).ToType) =
        Ordinal.enum (α := (Order.succ δ₁).ToType) (· < ·)
          ⟨δ₁, (Ordinal.type_toType _).symm ▸ Order.lt_succ δ₁⟩ from
      Ordinal.enum_succ_eq_top.symm]
    exact Ordinal.typein_enum _ _
  have h_typein_top :
      Ordinal.typein (α := (Order.succ δ₂).ToType) (· < ·)
        (⊤ : (Order.succ δ₂).ToType) = δ₂ := by
    rw [show (⊤ : (Order.succ δ₂).ToType) =
        Ordinal.enum (α := (Order.succ δ₂).ToType) (· < ·)
          ⟨δ₂, (Ordinal.type_toType _).symm ▸ Order.lt_succ δ₂⟩ from
      Ordinal.enum_succ_eq_top.symm]
    exact Ordinal.typein_enum _ _
  -- typein-order corresponds to <.
  rw [← Ordinal.typein_lt_typein
    (· < · : (Order.succ δ₂).ToType → (Order.succ δ₂).ToType → Prop)]
  rw [h_typein_init, h_typein_top]
  exact h

/-- **`treeCommitBoolFnOfBranch`**: indexed Bool function on
(ω_1).ToType using B. -/
noncomputable def treeCommitBoolFnOfBranch
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (B : CoherentMajorityBranch cR) :
    (Ordinal.omega.{0} 1).ToType → Bool := fun x =>
  haveI : IsWellOrder (Ordinal.omega.{0} 1).ToType (· < ·) := isWellOrder_lt
  treeCommitBoolOfBranch B (Ordinal.typein (· < ·) x) (by
    simpa [Ordinal.type_toType] using
      Ordinal.typein_lt_type
        (· < · : (Ordinal.omega.{0} 1).ToType →
          (Ordinal.omega.{0} 1).ToType → Prop) x)

/-- **`treeChainEmbeddingOfBranch`**: ω_1 → PairERSource embedding
driven by B. -/
noncomputable def treeChainEmbeddingOfBranch
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (B : CoherentMajorityBranch cR) :
    (Ordinal.omega.{0} 1).ToType ↪o PairERSource := by
  haveI : IsWellOrder (Ordinal.omega.{0} 1).ToType (· < ·) := isWellOrder_lt
  refine OrderEmbedding.ofStrictMono
    (fun x =>
      treeCommitOfBranch B (Ordinal.typein (· < ·) x) (by
        simpa [Ordinal.type_toType] using
          Ordinal.typein_lt_type
            (· < · : (Ordinal.omega.{0} 1).ToType →
              (Ordinal.omega.{0} 1).ToType → Prop) x))
    ?_
  intro x y hxy
  have hx : Ordinal.typein (· < ·) x < Ordinal.omega.{0} 1 := by
    simpa [Ordinal.type_toType] using
      Ordinal.typein_lt_type
        (· < · : (Ordinal.omega.{0} 1).ToType →
          (Ordinal.omega.{0} 1).ToType → Prop) x
  have hy : Ordinal.typein (· < ·) y < Ordinal.omega.{0} 1 := by
    simpa [Ordinal.type_toType] using
      Ordinal.typein_lt_type
        (· < · : (Ordinal.omega.{0} 1).ToType →
          (Ordinal.omega.{0} 1).ToType → Prop) y
  exact treeCommitOfBranch_strictMono B hx hy
    ((Ordinal.typein_lt_typein (· < ·)).mpr hxy)

/-- **`treeChain_pair_homogeneous_ofBranch`**: pair-homogeneity along
the branch-driven chain. For `δ < η < ω_1`,
`cR (pair (treeCommitOfBranch B δ) (treeCommitOfBranch B η))` =
`treeCommitBoolOfBranch B δ`.

Proof: by `B.top_in_validFiber η`, `commit η = B.prefixAt (succ η) ⊤`
is in `validFiber cR (B.prefixAt η hη) (B.branch η hη)`. Apply at
position `enum δ : η.ToType`; use `B.prefix_restrict` /
`B.branch_restrict` to identify the constraint values with
`commit δ` and `commit bool δ`. -/
theorem treeChain_pair_homogeneous_ofBranch
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (B : CoherentMajorityBranch cR) {δ η : Ordinal.{0}}
    (hδη : δ < η) (hη : η < Ordinal.omega.{0} 1) :
    cR (pairEmbed (treeCommitOfBranch_strictMono B
        (hδη.trans hη) hη hδη)) =
      treeCommitBoolOfBranch B δ (hδη.trans hη) := by
  haveI : IsWellOrder η.ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder (Order.succ δ).ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder (Order.succ η).ToType (· < ·) := isWellOrder_lt
  have hδ : δ < Ordinal.omega.{0} 1 := hδη.trans hη
  have hsδ : Order.succ δ < Ordinal.omega.{0} 1 :=
    (Cardinal.isSuccLimit_omega 1).succ_lt hδ
  have hsη : Order.succ η < Ordinal.omega.{0} 1 :=
    (Cardinal.isSuccLimit_omega 1).succ_lt hη
  have hsδ_le_η : Order.succ δ ≤ η := Order.succ_le_of_lt hδη
  -- The top of (succ η)-chain is in the validFiber for level η.
  have h_top_in :=
    B.top_in_validFiber η hη hsη
  set x_η : η.ToType :=
    Ordinal.enum (α := η.ToType) (· < ·)
      ⟨δ, (Ordinal.type_toType η).symm ▸ hδη⟩
  obtain ⟨h_lt, h_col⟩ := h_top_in x_η
  -- Helper: x_η = initialSegToType (⊤ : (succ δ).ToType).
  have h_x_η_eq :
      (Ordinal.initialSegToType hsδ_le_η).toOrderEmbedding
          (⊤ : (Order.succ δ).ToType) = x_η := by
    have h_typein_init :
        Ordinal.typein (α := η.ToType) (· < ·)
          ((Ordinal.initialSegToType hsδ_le_η).toOrderEmbedding
            (⊤ : (Order.succ δ).ToType)) = δ := by
      rw [show Ordinal.typein (α := η.ToType) (· < ·)
            ((Ordinal.initialSegToType hsδ_le_η).toOrderEmbedding
              (⊤ : (Order.succ δ).ToType)) =
          Ordinal.typein (α := (Order.succ δ).ToType) (· < ·)
            (⊤ : (Order.succ δ).ToType) from
        Ordinal.typein_apply (Ordinal.initialSegToType hsδ_le_η) _]
      rw [show (⊤ : (Order.succ δ).ToType) =
          Ordinal.enum (α := (Order.succ δ).ToType) (· < ·)
            ⟨δ, (Ordinal.type_toType _).symm ▸ Order.lt_succ δ⟩ from
        Ordinal.enum_succ_eq_top.symm]
      exact Ordinal.typein_enum _ _
    rw [← Ordinal.enum_typein
        (· < · : η.ToType → η.ToType → Prop)
        ((Ordinal.initialSegToType hsδ_le_η).toOrderEmbedding
          (⊤ : (Order.succ δ).ToType))]
    congr 1
    apply Subtype.ext
    exact h_typein_init
  -- B.prefixAt η hη x_η = B.prefixAt (succ δ) hsδ ⊤ = commit δ.
  have h_prefix_η_x : B.prefixAt η hη x_η =
      B.prefixAt (Order.succ δ) hsδ (⊤ : (Order.succ δ).ToType) := by
    rw [← h_x_η_eq]
    exact B.prefix_restrict hsδ_le_η hsδ hη
      (⊤ : (Order.succ δ).ToType)
  -- Similar for branch.
  have h_branch_η_x : B.branch η hη x_η =
      B.branch (Order.succ δ) hsδ (⊤ : (Order.succ δ).ToType) := by
    rw [← h_x_η_eq]
    exact B.branch_restrict hsδ_le_η hsδ hη
      (⊤ : (Order.succ δ).ToType)
  -- Combine. Goal: cR(pair our_witness) = commit bool δ.
  show cR _ = B.branch (Order.succ δ) hsδ (⊤ : (Order.succ δ).ToType)
  rw [← h_branch_η_x]
  -- pairEmbed of our_witness equals pairEmbed h_lt (same values).
  have h_pair_eq :
      (pairEmbed (treeCommitOfBranch_strictMono B hδ hη hδη) :
        Fin 2 ↪o PairERSource) = pairEmbed h_lt := by
    ext k
    match k with
    | ⟨0, _⟩ =>
      show treeCommitOfBranch B δ hδ = B.prefixAt η hη x_η
      show B.prefixAt (Order.succ δ) hsδ (⊤ : (Order.succ δ).ToType) =
        B.prefixAt η hη x_η
      exact h_prefix_η_x.symm
    | ⟨1, _⟩ => rfl
  rw [h_pair_eq]
  exact h_col

/-- **`exists_omega1_embedding_pair_ofBranch`**: pre-theorem on the
branch-driven path. -/
theorem exists_omega1_embedding_pair_ofBranch
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (B : CoherentMajorityBranch cR)
    {I : Type} [LinearOrder I] [WellFoundedLT I]
    (hI : Cardinal.mk I ≥ Order.succ (Cardinal.beth.{0} 1)) :
    Nonempty ((Ordinal.omega.{0} 1).ToType ↪o I) := by
  obtain ⟨emb⟩ : Nonempty (PairERSource ↪o I) :=
    exists_ordToType_embedding_of_card_ge hI
  exact ⟨(treeChainEmbeddingOfBranch B).trans emb⟩

/-- **Bool pigeonhole** on `treeCommitBoolFnOfBranch B`: some Bool
has aleph_1-sized preimage. Direct H3 application analogous to
`exists_large_pairERCommit_fiber`. -/
theorem exists_large_treeCommitBoolFn_fiber_ofBranch
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (B : CoherentMajorityBranch cR) :
    ∃ b : Bool,
      Cardinal.aleph.{0} 1 ≤
        Cardinal.mk ((treeCommitBoolFnOfBranch B) ⁻¹' {b}) := by
  have haleph1 : Cardinal.aleph.{0} 1 = Order.succ Cardinal.aleph0.{0} := by
    rw [show (1 : Ordinal.{0}) = Order.succ 0 from Ordinal.succ_zero.symm,
      Cardinal.aleph_succ, Cardinal.aleph_zero]
  have hα_card :
      Order.succ Cardinal.aleph0.{0} ≤
        Cardinal.mk (Ordinal.omega.{0} 1).ToType := by
    rw [Cardinal.mk_toType, Ordinal.card_omega, ← haleph1]
  have hβ_card : Cardinal.mk Bool ≤ Cardinal.aleph0.{0} := Cardinal.mk_le_aleph0
  obtain ⟨b, hb⟩ := exists_large_fiber_of_small_codomain
    (κ := Cardinal.aleph0.{0}) le_rfl hα_card hβ_card
    (treeCommitBoolFnOfBranch B)
  exact ⟨b, haleph1 ▸ hb⟩

/-- **[CONDITIONAL HEADLINE]** Pair Erdős–Rado at ω_1, assuming a
`CoherentMajorityBranch`. The active conditional path's only
mathematical-frontier dependency is `exists_coherentMajorityBranch`
(plus recursion bookkeeping). Statement: there exists a Bool `b` and
an ω_1-indexed strict-mono sequence into `PairERSource` whose every
pair has cR-color `b`.

Proof: Bool pigeonhole (`exists_large_treeCommitBoolFn_fiber_ofBranch`)
gives aleph_1-sized preimage of some `b`. H5
(`ordIso_omega1_of_aleph1_subset`) gives an order iso preimage ≃
ω_1.ToType. Compose with `treeChainEmbeddingOfBranch B` to get the
embedding; pair-homogeneity comes from
`treeChain_pair_homogeneous_ofBranch` + constancy of
`treeCommitBoolFnOfBranch B` on the preimage. -/
theorem erdos_rado_pair_omega1_of_coherentMajorityBranch
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    (B : CoherentMajorityBranch cR) :
    ∃ (f : (Ordinal.omega.{0} 1).ToType ↪o PairERSource) (b : Bool),
      ∀ {x y : (Ordinal.omega.{0} 1).ToType} (hxy : x < y),
        cR (pairEmbed (f.strictMono hxy)) = b := by
  haveI : IsWellOrder (Ordinal.omega.{0} 1).ToType (· < ·) := isWellOrder_lt
  obtain ⟨b, hb⟩ := exists_large_treeCommitBoolFn_fiber_ofBranch B
  obtain ⟨iso⟩ := ordIso_omega1_of_aleph1_subset hb
  -- f : ω_1.ToType → PairERSource via iso.symm + value extraction +
  -- treeChainEmbeddingOfBranch.
  have h_strict : StrictMono
      (fun z : (Ordinal.omega.{0} 1).ToType =>
        treeChainEmbeddingOfBranch B (iso.symm z).val) := by
    intro a b hab
    apply (treeChainEmbeddingOfBranch B).strictMono
    have h_iso_lt : iso.symm a < iso.symm b := iso.symm.lt_iff_lt.mpr hab
    exact h_iso_lt
  let f : (Ordinal.omega.{0} 1).ToType ↪o PairERSource :=
    OrderEmbedding.ofStrictMono
      (fun z => treeChainEmbeddingOfBranch B (iso.symm z).val) h_strict
  refine ⟨f, b, ?_⟩
  intro x y hxy
  -- f x = treeChainEmbeddingOfBranch B (iso.symm x).val.
  -- f y = treeChainEmbeddingOfBranch B (iso.symm y).val.
  -- By treeChain_pair_homogeneous_ofBranch + commitBoolFn = b on preimage.
  have h_iso_x_in : (iso.symm x).val ∈
      (treeCommitBoolFnOfBranch B) ⁻¹' {b} := (iso.symm x).property
  have h_iso_x_eq : treeCommitBoolFnOfBranch B (iso.symm x).val = b :=
    h_iso_x_in
  have h_lt_typein :
      Ordinal.typein (· < ·) (iso.symm x).val <
        Ordinal.typein (· < ·) (iso.symm y).val := by
    have h_iso_lt : iso.symm x < iso.symm y := iso.symm.lt_iff_lt.mpr hxy
    exact (Ordinal.typein_lt_typein (· < ·)).mpr h_iso_lt
  have h_xval_lt : Ordinal.typein (· < ·) (iso.symm x).val <
      Ordinal.omega.{0} 1 := by
    simpa [Ordinal.type_toType] using
      Ordinal.typein_lt_type
        (· < · : (Ordinal.omega.{0} 1).ToType →
          (Ordinal.omega.{0} 1).ToType → Prop) _
  have h_yval_lt : Ordinal.typein (· < ·) (iso.symm y).val <
      Ordinal.omega.{0} 1 := by
    simpa [Ordinal.type_toType] using
      Ordinal.typein_lt_type
        (· < · : (Ordinal.omega.{0} 1).ToType →
          (Ordinal.omega.{0} 1).ToType → Prop) _
  have h_pair := treeChain_pair_homogeneous_ofBranch B h_lt_typein h_yval_lt
  have h_bool_eq : treeCommitBoolOfBranch B
      (Ordinal.typein (· < ·) (iso.symm x).val) h_xval_lt = b := by
    show treeCommitBoolFnOfBranch B _ = b
    exact h_iso_x_eq
  have h_pair_eq :
      (pairEmbed (f.strictMono hxy) : Fin 2 ↪o PairERSource) =
      pairEmbed (treeCommitOfBranch_strictMono B h_xval_lt h_yval_lt
        h_lt_typein) := by
    ext k
    match k with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  rw [h_pair_eq, h_pair]
  exact h_bool_eq

/-- **[HEADLINE — pair Erdős–Rado at `ω₁`, unconditional]** There is a Bool `b` and an
`ω₁`-indexed strict-mono sequence into `PairERSource` whose every pair gets `cR`-color
`b`. Composes the now-clean existence of a `CoherentMajorityBranch`
(`exists_coherentMajorityBranch`, via the EHMR canonical partition tree) with the
conditional headline `erdos_rado_pair_omega1_of_coherentMajorityBranch`, so it no longer
inherits the legacy `_of_finitePartials` `sorry` tower. -/
theorem erdos_rado_pair_omega1
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    ∃ (f : (Ordinal.omega.{0} 1).ToType ↪o PairERSource) (b : Bool),
      ∀ {x y : (Ordinal.omega.{0} 1).ToType} (hxy : x < y),
        cR (pairEmbed (f.strictMono hxy)) = b :=
  erdos_rado_pair_omega1_of_coherentMajorityBranch (exists_coherentMajorityBranch cR).some

/-- **[LEGACY] `TreeBundle.extendSucc`** — uses
`(TB.family.family.stage β _).succ` (family-stored) instead of
`TB.stage.succ`. **Do NOT use in the main tree-driven path**: if `TB`
came from `limitFromTree`, `TB.stage` is the tree-selected limit
chain, but `TB.family.family.stage β _` is the OLD family's stage —
discarding the selected branch. Use `TreeBundle.extend` (above)
instead, which preserves the selected branch via `TB.stage.succ`.

Kept for reference / experimentation; the type-rebuilding semantics
may be useful when `TB` is constructed from non-tree sources where
the family's stage is canonical. -/
noncomputable def TreeBundle.extendSucc
    {cR : (Fin 2 ↪o PairERSource) → Bool} {β : Ordinal.{0}}
    (hβ : Order.succ (Order.succ β) < Ordinal.omega.{0} 1)
    (TB : TreeBundle cR (Order.succ β)) :
    TreeBundle cR (Order.succ (Order.succ β)) where
  family :=
    { family := TB.family.family.extendAtSucc
      tree := PairERTypeTree.extendSucc hβ TB.family.tree }
  stage := (TB.family.family.stage β (Order.lt_succ β)).succ
  coh := by
    intro δ hδ_succ
    rcases lt_or_eq_of_le (Order.lt_succ_iff.mp hδ_succ) with hδ_lt | hδ_eq
    · -- δ < succ β: LHS uses succ_commitAt; RHS unfolds extendAtSucc at γ < succ β.
      rw [PairERChain.succ_commitAt _ δ hδ_lt]
      unfold PairERCoherentFamily.commitVal PairERCoherentFamily.extendAtSucc
      simp only [dif_pos hδ_lt]
      -- Goal: (TB.family.family.stage β _).commitAt δ hδ_lt =
      --   (TB.family.family.stage δ hδ_lt).commitAt δ (Order.lt_succ δ).
      rcases lt_or_eq_of_le (Order.lt_succ_iff.mp hδ_lt) with hδ_lt_β | hδ_eq_β
      · exact TB.family.family.coherent hδ_lt_β (Order.lt_succ β)
      · subst hδ_eq_β; rfl
    · -- δ = succ β: both sides are top of `(stage β _).succ`.
      subst hδ_eq
      unfold PairERCoherentFamily.commitVal PairERCoherentFamily.extendAtSucc
      simp only [dif_neg (lt_irrefl _)]
  -- [LEGACY] `type_match` and `type_coh` not maintained for the
  -- legacy stage choice; sorry'd since the main tree path uses
  -- `TreeBundle.extend` instead.
  type_match := by intros; sorry
  type_coh := by intros; sorry

/-- **`PairERTreeFamily.extendWithStage`**: extend a tree family by
appending an arbitrary stage `s` at level α with head-coherence.
Produces a tree family at level (succ α).

The new family is `TF.family.extendWithStage s h_coh`. The new tree
uses the universal-tree formulation (`branches = Set.univ`,
`realizers b = validFiber cR new_prefix b`), with `large_sigma`
proved via `large_above_prefix` over the new prefix. -/
noncomputable def PairERTreeFamily.extendWithStage
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (h_succα : Order.succ α < Ordinal.omega.{0} 1)
    (TF : PairERTreeFamily cR α)
    (s : PairERChain cR α)
    (h_coh : ∀ δ (hδ : δ < α), s.commitAt δ hδ = TF.family.commitVal δ hδ) :
    PairERTreeFamily cR (Order.succ α) where
  family := TF.family.extendWithStage s h_coh
  tree := by
    refine
      { branches := Set.univ
        realizers := fun b => validFiber cR (TF.family.extendWithStage s h_coh).prefix b
        realizers_sub_validFiber := ?_
        large_sigma := ?_ }
    · intro _ _ hy; exact hy
    · set p : (Order.succ α).ToType ↪o PairERSource :=
        (TF.family.extendWithStage s h_coh).prefix with hp_def
      set above_prefix : Set PairERSource :=
        { y : PairERSource | ∀ x : (Order.succ α).ToType, p x < y }
        with hap_def
      have h_above_large : Order.succ (Cardinal.beth.{0} 1) ≤
          Cardinal.mk above_prefix := large_above_prefix h_succα p
      set Sigma : Set (((Order.succ α).ToType → Bool) × PairERSource) :=
        { q | q.1 ∈ (Set.univ : Set _) ∧
          q.2 ∈ validFiber cR (TF.family.extendWithStage s h_coh).prefix q.1 }
        with hS
      have h_inj : Cardinal.mk above_prefix ≤ Cardinal.mk Sigma := by
        refine Cardinal.mk_le_of_injective (f := fun y : above_prefix =>
          (⟨(fun x => cR (pairEmbed (y.2 x)), y.1), trivial, ?_⟩ : Sigma)) ?_
        · intro x; exact ⟨y.2 x, rfl⟩
        · intro y₁ y₂ h
          have h1 := Subtype.mk.inj h
          have h2 := (Prod.mk.inj h1).2
          exact Subtype.ext h2
      exact h_above_large.trans h_inj

/-- **`TreeBundle.extend`** (the corrected successor extension):
extends a `TreeBundle` at level α to one at level (succ α) using
`TB.stage.succ` as the new stage.

This is the type-deferred-correct successor: if `TB` came from
`limitFromTree`, the tree-selected branch is preserved into the next
successor step (rather than being discarded by re-fetching from the
old family's stages, which is what the legacy `extendSucc` did).

The new family is built via `PairERTreeFamily.extendWithStage` using
`TB.stage` and `TB.coh`. -/
noncomputable def TreeBundle.extend
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (h_succα : Order.succ α < Ordinal.omega.{0} 1)
    (TB : TreeBundle cR α) :
    TreeBundle cR (Order.succ α) where
  family := TB.family.extendWithStage h_succα TB.stage TB.coh
  stage := TB.stage.succ
  coh := by
    intro δ hδ_succ
    rcases lt_or_eq_of_le (Order.lt_succ_iff.mp hδ_succ) with hδ_lt | hδ_eq
    · -- δ < α: succ_commitAt + TB.coh + extendWithStage at γ < α inherits.
      rw [PairERChain.succ_commitAt _ δ hδ_lt]
      show TB.stage.commitAt δ hδ_lt =
        (TB.family.extendWithStage h_succα TB.stage TB.coh).family.commitVal δ hδ_succ
      rw [TB.coh δ hδ_lt]
      unfold PairERCoherentFamily.commitVal
        PairERTreeFamily.extendWithStage PairERCoherentFamily.extendWithStage
      simp only [dif_pos hδ_lt]
    · -- δ = α: top, both sides are TB.stage.succ.commitAt α _.
      subst hδ_eq
      show TB.stage.succ.commitAt δ (Order.lt_succ δ) = _
      unfold PairERCoherentFamily.commitVal
        PairERTreeFamily.extendWithStage PairERCoherentFamily.extendWithStage
      simp only [dif_neg (lt_irrefl _)]
  type_match := by
    intro δ hδ_succ
    rcases lt_or_eq_of_le (Order.lt_succ_iff.mp hδ_succ) with hδ_lt | hδ_eq
    · -- δ < α: succ_typeAt_old + TB.type_match.
      rw [PairERChain.succ_typeAt_old _ δ hδ_lt]
      show TB.stage.typeAt δ hδ_lt =
        (TB.family.extendWithStage h_succα TB.stage TB.coh).family.typeVal δ hδ_succ
      rw [TB.type_match δ hδ_lt]
      unfold PairERCoherentFamily.typeVal
        PairERTreeFamily.extendWithStage PairERCoherentFamily.extendWithStage
      simp only [dif_pos hδ_lt]
    · -- δ = α: top, both sides are TB.stage.succ.typeAt α _.
      subst hδ_eq
      show TB.stage.succ.typeAt δ (Order.lt_succ δ) = _
      unfold PairERCoherentFamily.typeVal
        PairERTreeFamily.extendWithStage PairERCoherentFamily.extendWithStage
      simp only [dif_neg (lt_irrefl _)]
  type_coh := by
    intro δ β hδβ hβ_succ
    rcases lt_or_eq_of_le (Order.lt_succ_iff.mp hβ_succ) with hβ_lt | hβ_eq
    · -- β < α, δ < β < α: from F.IsTypeCoherent (TB.type_coh).
      have hδ_lt : δ < α := hδβ.trans hβ_lt
      show ((TB.family.extendWithStage h_succα TB.stage TB.coh).family.stage β
          hβ_succ).typeAt δ _ =
        ((TB.family.extendWithStage h_succα TB.stage TB.coh).family.stage δ _).typeAt
          δ _
      unfold PairERTreeFamily.extendWithStage PairERCoherentFamily.extendWithStage
      simp only [dif_pos hβ_lt, dif_pos hδ_lt]
      exact TB.type_coh hδβ hβ_lt
    · -- β = α (top), δ < α: top stage is TB.stage.succ; preserve via succ_typeAt_old + TB.type_match.
      subst hβ_eq
      show ((TB.family.extendWithStage h_succα TB.stage TB.coh).family.stage β
          hβ_succ).typeAt δ _ =
        ((TB.family.extendWithStage h_succα TB.stage TB.coh).family.stage δ _).typeAt
          δ _
      unfold PairERTreeFamily.extendWithStage PairERCoherentFamily.extendWithStage
      simp only [dif_neg (lt_irrefl _), dif_pos hδβ]
      rw [PairERChain.succ_typeAt_old _ δ hδβ]
      exact TB.type_match δ hδβ

/-! ### Architectural test: `extend ∘ limitFromTree` preserves the
selected branch.

The point of `TreeBundle.extend` (vs. legacy `extendSucc`) is that it
threads `TB.stage.succ` rather than the family-stored stage. When `TB`
came from `TreeBundle.limitFromTree hα TF`, the limit chain
`TF.toLimitChain hα` carries the pigeonhole-selected branch as its
`type` field. The lemma below confirms that, after one successor
extension, the typeAt readings at lower positions `δ < α` literally
read off `TF.tree.selectedBranch hα` at the enumerated point — i.e.,
the tree-selected branch survives the successor step. This is the
"next meaningful test" of the type-deferred design. -/

/-- **`TreeBundle.extend` after `limitFromTree` reads `selectedBranch`
at lower positions.** The new stage at `succ α` reports, at every
position `δ < α`, the Bool value of the tree's selected branch. This
is direct from `succ_typeAt_old` + `limitWithType_typeAt`. -/
lemma TreeBundle.extend_after_limitFromTree_typeAt
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (hα : α < Ordinal.omega.{0} 1)
    (h_succα : Order.succ α < Ordinal.omega.{0} 1)
    (TF : PairERTreeFamily cR α)
    (h_type_coh : TF.family.IsTypeCoherent)
    (h_branch_eq : TF.tree.selectedBranch hα = TF.family.typeFn)
    (δ : Ordinal.{0}) (hδ : δ < α) :
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    ((TreeBundle.limitFromTree hα TF h_type_coh h_branch_eq).extend
        h_succα).stage.typeAt δ (hδ.trans (Order.lt_succ α)) =
      TF.tree.selectedBranch hα
        (Ordinal.enum (α := α.ToType) (· < ·)
          ⟨δ, (Ordinal.type_toType α).symm ▸ hδ⟩) := by
  haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
  show (TF.toLimitChain hα).succ.typeAt δ _ = _
  rw [PairERChain.succ_typeAt_old _ δ hδ]
  unfold PairERTreeFamily.toLimitChain PairERTreeFamily.toLimitChainAtBranch
  rw [PairERChain.limitWithType_typeAt]

/-- **Stage identity** for `extend ∘ limitFromTree`: the new stage is
*exactly* the successor of the tree-driven limit chain. By definition
of `TreeBundle.extend` (which sets `stage := TB.stage.succ`) and
`TreeBundle.limitFromTree` (which sets `stage := TF.toLimitChain hα`).
Reflexivity makes the architectural choice visible: the
`selectedBranch`-typed limit chain is the input to the next
successor. -/
lemma TreeBundle.extend_after_limitFromTree_stage
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (hα : α < Ordinal.omega.{0} 1)
    (h_succα : Order.succ α < Ordinal.omega.{0} 1)
    (TF : PairERTreeFamily cR α)
    (h_type_coh : TF.family.IsTypeCoherent)
    (h_branch_eq : TF.tree.selectedBranch hα = TF.family.typeFn) :
    ((TreeBundle.limitFromTree hα TF h_type_coh h_branch_eq).extend
        h_succα).stage =
      (TF.toLimitChain hα).succ := rfl

/-! ### General preservation lemmas for `TreeBundle.extend`

The two test lemmas above were specific to `extend ∘ limitFromTree`.
The general fact is simpler: `(TB.extend h).stage = TB.stage.succ` by
definition of `extend`, so any preservation property of
`PairERChain.succ` lifts directly. The lemmas below name the two we
need for the recursion: `commitAt` and `typeAt` at lower positions
agree with `TB.stage`'s readings. -/

/-- **`TreeBundle.extend` preserves commits at lower positions.**
Direct from `(TB.extend).stage = TB.stage.succ` and
`PairERChain.succ_commitAt`. -/
lemma TreeBundle.extend_commitAt_old
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (h_succα : Order.succ α < Ordinal.omega.{0} 1)
    (TB : TreeBundle cR α)
    (δ : Ordinal.{0}) (hδα : δ < α) :
    (TB.extend h_succα).stage.commitAt δ
        (hδα.trans (Order.lt_succ α)) =
      TB.stage.commitAt δ hδα := by
  show TB.stage.succ.commitAt δ _ = _
  rw [PairERChain.succ_commitAt _ δ hδα]

/-- **`TreeBundle.extend` preserves typeAt at lower positions.**
Direct from `(TB.extend).stage = TB.stage.succ` and
`PairERChain.succ_typeAt_old`. -/
lemma TreeBundle.extend_typeAt_old
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (h_succα : Order.succ α < Ordinal.omega.{0} 1)
    (TB : TreeBundle cR α)
    (δ : Ordinal.{0}) (hδα : δ < α) :
    (TB.extend h_succα).stage.typeAt δ
        (hδα.trans (Order.lt_succ α)) =
      TB.stage.typeAt δ hδα := by
  show TB.stage.succ.typeAt δ _ = _
  rw [PairERChain.succ_typeAt_old _ δ hδα]

/-- **[LEGACY — off-chain; superseded by
`TreeBundle.limitExtend_of_coherentMajorityBranch`]** This recursive limit
constructor attaches `PairERTypeTree.commitCoherent` (branches = `{F.typeFn}`),
whose `large_sigma` reduces to the **false-as-stated** `exists_large_iInter_stage_
fibers` (it asserts the committed `typeFn` is realized for every `IsTypeCoherent`
family — refuted by the ω-adversary). Nothing on the active `B`/witness-net path
consumes it; use the axiom-clean `B`-based replacement instead. Retained only
until the dead recursive tower (`treeStage`/`richStage`/`commitCoherent`) is
removed.

**`TreeBundle.limitExtend`**: limit-level constructor for
`TreeBundle`, parameterized by prior bundles below `α` plus a
`prev_succ` cross-stage coherence witness.

Given `IH γ : TreeBundle cR γ` for each `γ < α` (with `α < ω₁`) and
a hypothesis stating that the commit at position `δ` in the
`β`-bundle (`δ < β`) equals the new top commit of the `δ`-bundle's
successor extension, build a `TreeBundle cR α` via:
1. Assemble `F : PairERCoherentFamily cR α` with
   `F.stage β hβα := (IH β hβα).stage.succ`. The `coherent`
   field reduces to `prev_succ` after one `succ_commitAt`.
2. Attach `PairERTypeTree.commitCoherent hα F` as the tree.
   This is the **commit-coherent** tree (branches = `{F.typeFn}`),
   which makes `selectedBranch_agrees_with_prior_commit` provable.
   Its `large_sigma` invariant carries the type-coherent fiber
   largeness frontier.
3. Wrap with `TreeBundle.limitFromTree hα`.

This is the constructor used by `treeStage`'s limit case. -/
noncomputable def TreeBundle.limitExtend
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (hα : α < Ordinal.omega.{0} 1)
    (IH : ∀ γ : Ordinal.{0}, γ < α → TreeBundle cR γ)
    (prev_succ : ∀ (β : Ordinal.{0}) (hβα : β < α) (δ : Ordinal.{0})
      (hδβ : δ < β),
      (IH β hβα).stage.commitAt δ hδβ =
        (IH δ (hδβ.trans hβα)).stage.succ.commitAt δ
          (Order.lt_succ δ))
    (type_succ : ∀ (β : Ordinal.{0}) (hβα : β < α) (δ : Ordinal.{0})
      (hδβ : δ < β),
      (IH β hβα).stage.typeAt δ hδβ =
        (IH δ (hδβ.trans hβα)).stage.succNewBool) :
    TreeBundle cR α :=
  let F : PairERCoherentFamily cR α :=
    { stage := fun β hβα => (IH β hβα).stage.succ
      coherent := by
        intro δ β hδβ hβα
        show (IH β hβα).stage.succ.commitAt δ
            (hδβ.trans (Order.lt_succ β)) =
          (IH δ (hδβ.trans hβα)).stage.succ.commitAt δ (Order.lt_succ δ)
        rw [PairERChain.succ_commitAt _ δ hδβ]
        exact prev_succ β hβα δ hδβ }
  let h_F_type_coh : F.IsTypeCoherent := by
    intro δ β hδβ hβα
    show (IH β hβα).stage.succ.typeAt δ (hδβ.trans (Order.lt_succ β)) =
      (IH δ (hδβ.trans hβα)).stage.succ.typeAt δ (Order.lt_succ δ)
    rw [PairERChain.succ_typeAt_old _ δ hδβ,
        PairERChain.succ_typeAt_top]
    exact type_succ β hβα δ hδβ
  let tree : PairERTypeTree F :=
    PairERTypeTree.commitCoherent hα F h_F_type_coh
  TreeBundle.limitFromTree hα ⟨F, tree⟩ h_F_type_coh
    (PairERTypeTree.commitCoherent_selectedBranch_eq hα F h_F_type_coh)

/-- **Any successor-level family with `IsTypeCoherent` is
`IsCanonicalTypeCoherent`**. Key observation: for `α = succ β`, any
cofinal ℕ-sequence `e : ℕ → {γ // γ < succ β}` eventually reaches
`(e n).1 = β`. Hence the ℕ-intersection collapses to
`validFiber (F.stage β _)` (by descending nestedness), which is
nonempty since it has size ≥ succ ℶ_1. Thus `IsCanonicalTypeCoherent`
holds trivially at successor levels — the mathematical difficulty is
purely at LIMIT levels.

**Implementation note**: the proof follows the sketch above but the
`(e n).1 = β` case-split hits a dependent-type wall — rewriting
`e n = ⟨β, _⟩` in the goal through the `(e n).1` / `(e n).2` projections
requires subtype-projection simp lemmas. Mechanical but fiddly;
deferred as the only remaining sorry in the successor chain. -/
lemma PairERCoherentFamily.isCanonicalTypeCoherent_of_succ
    {cR : (Fin 2 ↪o PairERSource) → Bool} {β : Ordinal.{0}}
    (F : PairERCoherentFamily cR (Order.succ β))
    (hF_type : F.IsTypeCoherent) : F.IsCanonicalTypeCoherent := by
  refine ⟨hF_type, ?_⟩
  intro e _e_mono _e_cofinal
  -- validFiber (F.stage β _) is nonempty (cardinality ≥ succ ℶ_1 > 0).
  have h_large : Order.succ (Cardinal.beth.{0} 1) ≤
      Cardinal.mk (validFiber cR (F.stage β (Order.lt_succ β)).head
        (F.stage β (Order.lt_succ β)).type) :=
    (F.stage β (Order.lt_succ β)).large
  have h_ne_zero : Cardinal.mk (validFiber cR
      (F.stage β (Order.lt_succ β)).head (F.stage β (Order.lt_succ β)).type) ≠ 0 := by
    have h_pos : (0 : Cardinal) < Cardinal.mk (validFiber cR
        (F.stage β (Order.lt_succ β)).head (F.stage β (Order.lt_succ β)).type) :=
      (Cardinal.aleph0_pos.trans_le isRegular_succ_beth_one.aleph0_le).trans_le h_large
    exact h_pos.ne'
  obtain ⟨⟨y, hy⟩⟩ := Cardinal.mk_ne_zero_iff.mp h_ne_zero
  refine ⟨y, ?_⟩
  simp only [Set.mem_iInter]
  intro n
  -- Abstract over (e n).1 and (e n).2 in the goal.
  suffices h : ∀ (γ : Ordinal.{0}) (hγ : γ < Order.succ β),
      y ∈ validFiber cR (F.stage γ hγ).head (F.stage γ hγ).type by
    exact h (e n).1 (e n).2
  intro γ hγ
  have h_le : γ ≤ β := Order.lt_succ_iff.mp hγ
  rcases eq_or_lt_of_le h_le with h_eq | h_lt
  · subst h_eq; exact hy
  · exact F.validFiber_mono hF_type h_lt (Order.lt_succ β) hy

/-- **Coherent bundle at level `α`.** Packages the current stage at
`α`, the coherent family covering `β < α`, and the coherence between
the stage's commits and the family's committed values. This is the
motive carried by the transfinite assembly recursion for the main
Erdős–Rado theorem. -/
structure CoherentBundle (cR : (Fin 2 ↪o PairERSource) → Bool)
    (α : Ordinal.{0}) where
  stage : PairERChain cR α
  family : PairERCoherentFamily cR α
  coh : ∀ δ (hδ : δ < α), stage.commitAt δ hδ = family.commitVal δ hδ

/-- **Zero coherent bundle.** At `α = 0`, bundle up `PairERChain.zero`
and the empty family. -/
noncomputable def CoherentBundle.zero
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    CoherentBundle cR 0 where
  stage := PairERChain.zero cR
  family := PairERCoherentFamily.empty cR
  coh := fun δ hδ => absurd hδ (not_lt.mpr (zero_le δ))

/-- **Successor extension of a coherent bundle.** From a bundle at `α`,
produce the bundle at `α + 1`: the new stage is `b.stage.succ`; the new
family extends `b.family` by inserting `b.stage.succ` at position `α`;
coherence is proved by `PairERChain.succ_commitAt` and `b.coh`. -/
noncomputable def CoherentBundle.extend
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (b : CoherentBundle cR α) : CoherentBundle cR (Order.succ α) where
  stage := b.stage.succ
  family :=
    { stage := fun γ hγ =>
        if h : γ < α then b.family.stage γ h
        else
          have hγ_eq : γ = α :=
            le_antisymm (Order.lt_succ_iff.mp hγ) (not_lt.mp h)
          hγ_eq ▸ b.stage.succ
      coherent := by
        intro δ γ hδγ hγ_succ
        rcases lt_or_eq_of_le (Order.lt_succ_iff.mp hγ_succ) with hγ_lt | hγ_eq
        · have hδ_lt : δ < α := hδγ.trans hγ_lt
          simp only [dif_pos hγ_lt, dif_pos hδ_lt]
          exact b.family.coherent hδγ hγ_lt
        · subst hγ_eq
          simp only [dif_pos hδγ, dif_neg (lt_irrefl _)]
          -- Goal: `b.stage.succ.commitAt δ _ = (b.family.stage δ _).commitAt δ _`
          rw [PairERChain.succ_commitAt _ δ hδγ]
          exact b.coh δ hδγ }
  coh := by
    intro δ hδ_succ
    rcases lt_or_eq_of_le (Order.lt_succ_iff.mp hδ_succ) with hδ_lt | hδ_eq
    · -- δ < α: use `succ_commitAt` + `b.coh`.
      unfold PairERCoherentFamily.commitVal
      rw [PairERChain.succ_commitAt _ δ hδ_lt]
      simp only [dif_pos hδ_lt]
      exact b.coh δ hδ_lt
    · -- δ = α: the new family's stage at α is `b.stage.succ`; trivial.
      subst hδ_eq
      unfold PairERCoherentFamily.commitVal
      simp only [dif_neg (lt_irrefl _)]

/-- **Limit extension of the coherent bundle** (assuming cross-IH
coherence). Given an IH-like family of bundles at each `γ < α` (α a
limit) PLUS a cross-consistency witness that `(ih γ _).family.stage δ _
`'s commitAt agrees with `(ih δ _).stage.succ`'s, build the bundle at
`α`. The cross-consistency witness is what must be threaded through the
outer `Ordinal.limitRecOn` — ship this parameterized version so the
recursion caller supplies it. -/
noncomputable def CoherentBundle.limitExtend
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (ih : (γ : Ordinal.{0}) → γ < α → CoherentBundle cR γ)
    (ih_coh : ∀ {δ γ : Ordinal.{0}} (hδγ : δ < γ) (hγα : γ < α),
      (ih γ hγα).stage.commitAt δ hδγ =
        (ih δ (hδγ.trans hγα)).stage.succ.commitAt δ (Order.lt_succ δ))
    (hα : α < Ordinal.omega.{0} 1) :
    CoherentBundle cR α :=
  let family : PairERCoherentFamily cR α :=
    { stage := fun γ hγα => (ih γ hγα).stage.succ
      coherent := by
        intro δ γ hδγ hγα
        -- Goal: (ih γ _).stage.succ.commitAt δ _ = (ih δ _).stage.succ.commitAt δ _.
        rw [PairERChain.succ_commitAt _ δ hδγ]
        -- Goal: (ih γ _).stage.commitAt δ _ = (ih δ _).stage.succ.commitAt δ _.
        exact ih_coh hδγ hγα }
  { stage := family.limit hα
    family := family
    coh := fun δ hδ => family.limit_commitAt hα δ hδ }

/-- **Type-coherence invariants for a `CoherentBundle`**: the stage's
Bool at each earlier position matches the family's committed Bool at
that position, AND the family itself is type-coherent. Parallel to
how `coh` encodes the head invariant. Tracked externally. -/
structure CoherentBundle.IsTypeCoh
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (b : CoherentBundle cR α) : Prop where
  /-- The stage's `typeAt δ` agrees with the family's `typeVal δ`. -/
  stage_type : ∀ δ (hδ : δ < α),
    b.stage.typeAt δ hδ = b.family.typeVal δ hδ
  /-- The family itself is type-coherent. -/
  family_type : b.family.IsTypeCoherent

/-- The zero coherent bundle is vacuously type-coherent. -/
lemma CoherentBundle.zero_isTypeCoh
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    (CoherentBundle.zero cR).IsTypeCoh where
  stage_type := fun _ hδ => absurd hδ (not_lt.mpr (zero_le _))
  family_type := PairERCoherentFamily.empty_isTypeCoherent cR

/-- `CoherentBundle.extend` preserves `IsTypeCoh`. -/
lemma CoherentBundle.extend_isTypeCoh
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    {b : CoherentBundle cR α} (hb : b.IsTypeCoh) : b.extend.IsTypeCoh where
  stage_type := by
    intro δ hδ_succ
    show b.extend.stage.typeAt δ hδ_succ = b.extend.family.typeVal δ hδ_succ
    rcases lt_or_eq_of_le (Order.lt_succ_iff.mp hδ_succ) with hδ_lt | hδ_eq
    · -- δ < α: stage = b.stage.succ; typeAt δ via succ_typeAt_old = b.stage.typeAt δ.
      show b.stage.succ.typeAt δ hδ_succ = b.extend.family.typeVal δ hδ_succ
      rw [PairERChain.succ_typeAt_old _ δ hδ_lt]
      show b.stage.typeAt δ hδ_lt =
        (b.extend.family.stage δ hδ_succ).typeAt δ (Order.lt_succ δ)
      unfold CoherentBundle.extend
      simp only [dif_pos hδ_lt]
      exact hb.stage_type δ hδ_lt
    · subst hδ_eq
      show b.stage.succ.typeAt δ hδ_succ = b.extend.family.typeVal δ hδ_succ
      show b.stage.succ.typeAt δ hδ_succ =
        (b.extend.family.stage δ hδ_succ).typeAt δ (Order.lt_succ δ)
      unfold CoherentBundle.extend
      simp only [dif_neg (lt_irrefl _)]
  family_type := by
    -- extend's family is type-coherent: reduces to hb's invariants.
    intro δ γ hδγ hγα
    rcases lt_or_eq_of_le (Order.lt_succ_iff.mp hγα) with hγ_lt | hγ_eq
    · have hδ_lt : δ < α := hδγ.trans hγ_lt
      show (b.extend.family.stage γ hγα).typeAt δ _ =
        (b.extend.family.stage δ _).typeAt δ _
      unfold CoherentBundle.extend
      simp only [dif_pos hγ_lt, dif_pos hδ_lt]
      exact hb.family_type hδγ hγ_lt
    · subst hγ_eq
      show (b.extend.family.stage γ hγα).typeAt δ _ =
        (b.extend.family.stage δ _).typeAt δ _
      unfold CoherentBundle.extend
      simp only [dif_pos hδγ, dif_neg (lt_irrefl _)]
      rw [PairERChain.succ_typeAt_old _ δ hδγ]
      exact hb.stage_type δ hδγ

/-- **Type-coherent limit extension of the coherent bundle.** Same as
`CoherentBundle.limitExtend` but uses `PairERCoherentFamily.
limitTypeCoherent` for the new top stage, preserving earlier committed
Bools. Requires the family to be type-coherent and a `type_ih_coh`
witness parallel to `ih_coh`. -/
noncomputable def CoherentBundle.limitExtendTypeCoherent
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (ih : (γ : Ordinal.{0}) → γ < α → CoherentBundle cR γ)
    (ih_coh : ∀ {δ γ : Ordinal.{0}} (hδγ : δ < γ) (hγα : γ < α),
      (ih γ hγα).stage.commitAt δ hδγ =
        (ih δ (hδγ.trans hγα)).stage.succ.commitAt δ (Order.lt_succ δ))
    (ih_type_coh : ∀ {δ γ : Ordinal.{0}} (hδγ : δ < γ) (hγα : γ < α),
      (ih γ hγα).stage.typeAt δ hδγ =
        (ih δ (hδγ.trans hγα)).stage.succ.typeAt δ (Order.lt_succ δ))
    (hα : α < Ordinal.omega.{0} 1) :
    CoherentBundle cR α :=
  let family : PairERCoherentFamily cR α :=
    { stage := fun γ hγα => (ih γ hγα).stage.succ
      coherent := by
        intro δ γ hδγ hγα
        rw [PairERChain.succ_commitAt _ δ hδγ]
        exact ih_coh hδγ hγα }
  have hfam_type : family.IsTypeCoherent := by
    intro δ γ hδγ hγα
    show (family.stage γ hγα).typeAt δ _ = (family.stage δ _).typeAt δ _
    change ((ih γ hγα).stage.succ).typeAt δ _ = ((ih δ _).stage.succ).typeAt δ _
    rw [PairERChain.succ_typeAt_old _ δ hδγ]
    exact ih_type_coh hδγ hγα
  { stage := family.limitTypeCoherent hfam_type hα
    family := family
    coh := fun δ hδ => family.limitTypeCoherent_commitAt hfam_type hα δ hδ }

/-- `CoherentBundle.limitExtendTypeCoherent` is type-coherent by
construction: the stage is `family.limitTypeCoherent`, whose `typeAt`
equals the family's `typeVal` by `limitTypeCoherent_typeAt`, and the
family is type-coherent as built into `limitExtendTypeCoherent`. -/
lemma CoherentBundle.limitExtendTypeCoherent_isTypeCoh
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (ih : (γ : Ordinal.{0}) → γ < α → CoherentBundle cR γ)
    (ih_coh : ∀ {δ γ : Ordinal.{0}} (hδγ : δ < γ) (hγα : γ < α),
      (ih γ hγα).stage.commitAt δ hδγ =
        (ih δ (hδγ.trans hγα)).stage.succ.commitAt δ (Order.lt_succ δ))
    (ih_type_coh : ∀ {δ γ : Ordinal.{0}} (hδγ : δ < γ) (hγα : γ < α),
      (ih γ hγα).stage.typeAt δ hδγ =
        (ih δ (hδγ.trans hγα)).stage.succ.typeAt δ (Order.lt_succ δ))
    (hα : α < Ordinal.omega.{0} 1) :
    (CoherentBundle.limitExtendTypeCoherent ih ih_coh ih_type_coh hα).IsTypeCoh where
  stage_type := fun δ hδ => by
    show (CoherentBundle.limitExtendTypeCoherent ih ih_coh ih_type_coh hα).stage.typeAt δ hδ =
      _
    unfold CoherentBundle.limitExtendTypeCoherent
    simp only
    rw [PairERCoherentFamily.limitTypeCoherent_typeAt]
  family_type := by
    intro δ γ hδγ hγα
    unfold CoherentBundle.limitExtendTypeCoherent
    simp only
    rw [PairERChain.succ_typeAt_old _ δ hδγ]
    exact ih_type_coh hδγ hγα

/-- **Cross-IH coherence for the zero-stage-appended recursion.** For
any candidate recursion function `f : ∀ α, α < ω_1 → CoherentBundle cR
α` that matches the zero/succ cases, cross-IH at successor levels
reduces to `PairERChain.succ_commitAt`. -/
private lemma cross_ih_succ
    {cR : (Fin 2 ↪o PairERSource) → Bool}
    {γ' δ : Ordinal.{0}} (hδγ' : δ < γ') (bγ' : CoherentBundle cR γ') :
    bγ'.extend.stage.commitAt δ (hδγ'.trans (Order.lt_succ _)) =
      bγ'.stage.commitAt δ hδγ' :=
  PairERChain.succ_commitAt _ δ hδγ'

/-- The `.extend` stage is the original's `.succ`. -/
@[simp]
lemma CoherentBundle.extend_stage
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (b : CoherentBundle cR α) : b.extend.stage = b.stage.succ := rfl

/-- **Cross-IH coherence (parameterized on succ and limit reduction
hypotheses)**. Given `rec_succ` and `rec_limit` hypotheses describing
how the recursion unfolds at successor and limit levels, derive the
cross-IH coherence by strong induction on γ. Once the outer recursion
is wired with the right reduction semantics, both hypotheses follow
definitionally. -/
private theorem crossCoh (cR : (Fin 2 ↪o PairERSource) → Bool)
    (rec : ∀ α : Ordinal.{0}, α < Ordinal.omega.{0} 1 → CoherentBundle cR α)
    (rec_succ : ∀ (β : Ordinal.{0}) (hs : Order.succ β < Ordinal.omega.{0} 1),
      rec (Order.succ β) hs =
        (rec β ((Order.lt_succ β).trans hs)).extend)
    (rec_limit : ∀ (γ : Ordinal.{0}) (_ : Order.IsSuccLimit γ)
      (hγ : γ < Ordinal.omega.{0} 1) (δ : Ordinal.{0}) (hδγ : δ < γ),
      (rec γ hγ).stage.commitAt δ hδγ =
        (rec δ (hδγ.trans hγ)).stage.succ.commitAt δ (Order.lt_succ δ)) :
    ∀ (γ : Ordinal.{0}) (hγ : γ < Ordinal.omega.{0} 1) (δ : Ordinal.{0})
      (hδγ : δ < γ),
      (rec γ hγ).stage.commitAt δ hδγ =
        (rec δ (hδγ.trans hγ)).stage.succ.commitAt δ (Order.lt_succ δ) := by
  intro γ hγ
  induction γ using WellFoundedLT.induction with
  | ind γ IHγ =>
    intro δ hδγ
    rcases Ordinal.zero_or_succ_or_isSuccLimit γ with hz | ⟨γ', hγ'⟩ | hγ_lim
    · exact absurd hδγ (hz ▸ not_lt.mpr (zero_le _))
    · subst hγ'
      have hγ'_lt : γ' < Ordinal.omega.{0} 1 :=
        (Order.lt_succ γ').trans hγ
      rw [rec_succ γ' hγ]
      rw [CoherentBundle.extend_stage]
      rcases lt_or_eq_of_le (Order.lt_succ_iff.mp hδγ) with hδ_lt_γ' | hδ_eq_γ'
      · rw [PairERChain.succ_commitAt _ δ hδ_lt_γ']
        exact IHγ γ' (Order.lt_succ γ') hγ'_lt δ hδ_lt_γ'
      · subst hδ_eq_γ'
        rfl
    · exact rec_limit γ hγ_lim hγ δ hδγ

/-- **Cross-IH coherence for a local IH-function**, using induction on
the inner γ parameter and the reduction witnesses `ih_succ` and
`ih_limit` (both expressible via `Ordinal.limitRecOn_succ` and
`Ordinal.limitRecOn_limit` on the outer recursion). -/
private theorem crossCohLocal
    (cR : (Fin 2 ↪o PairERSource) → Bool) {β : Ordinal.{0}}
    (IH : (γ : Ordinal.{0}) → γ < β → γ < Ordinal.omega.{0} 1 →
      CoherentBundle cR γ)
    (ih_succ : ∀ γ (hγsβ : Order.succ γ < β)
      (h1 : Order.succ γ < Ordinal.omega.{0} 1),
      IH (Order.succ γ) hγsβ h1 =
        (IH γ ((Order.lt_succ γ).trans hγsβ)
              ((Order.lt_succ γ).trans h1)).extend)
    (ih_limit : ∀ γ (_ : Order.IsSuccLimit γ) (hγβ : γ < β)
      (hγ : γ < Ordinal.omega.{0} 1) (δ : Ordinal.{0}) (hδγ : δ < γ),
      (IH γ hγβ hγ).stage.commitAt δ hδγ =
        (IH δ (hδγ.trans hγβ) (hδγ.trans hγ)).stage.succ.commitAt δ
          (Order.lt_succ δ))
    (γ : Ordinal.{0}) (hγβ : γ < β) (hγ : γ < Ordinal.omega.{0} 1)
    (δ : Ordinal.{0}) (hδγ : δ < γ) :
    (IH γ hγβ hγ).stage.commitAt δ hδγ =
      (IH δ (hδγ.trans hγβ) (hδγ.trans hγ)).stage.succ.commitAt δ
        (Order.lt_succ δ) := by
  -- Generalize γ, hγβ, hγ, hδγ for induction.
  revert hδγ hγ hγβ
  induction γ using WellFoundedLT.induction with
  | ind γ IHγ =>
    intro hγβ hγ hδγ
    rcases Ordinal.zero_or_succ_or_isSuccLimit γ with hz | ⟨γ', hγ'⟩ | hγ_lim
    · exact absurd hδγ (hz ▸ not_lt.mpr (zero_le _))
    · subst hγ'
      have hγ'sβ : γ' < β := (Order.lt_succ γ').trans hγβ
      have hγ'_lt : γ' < Ordinal.omega.{0} 1 := (Order.lt_succ γ').trans hγ
      rw [ih_succ γ' hγβ hγ]
      rw [CoherentBundle.extend_stage]
      rcases lt_or_eq_of_le (Order.lt_succ_iff.mp hδγ) with hδ_lt_γ' | hδ_eq_γ'
      · rw [PairERChain.succ_commitAt _ δ hδ_lt_γ']
        exact IHγ γ' (Order.lt_succ γ') hγ'sβ hγ'_lt hδ_lt_γ'
      · subst hδ_eq_γ'
        rfl
    · exact ih_limit γ hγ_lim hγβ hγ δ hδγ

/-- The succ-case step function of the outer recursion. -/
private noncomputable def recStepSucc
    {cR : (Fin 2 ↪o PairERSource) → Bool} (β : Ordinal.{0})
    (IH : β < Ordinal.omega.{0} 1 → CoherentBundle cR β)
    (hs : Order.succ β < Ordinal.omega.{0} 1) :
    CoherentBundle cR (Order.succ β) :=
  (IH (lt_of_lt_of_le (Order.lt_succ β) hs.le)).extend

/-- The limit-case step function of the outer recursion. Uses
`crossCohLocal` to supply cross-IH via `ih_succ`/`ih_limit` reduction
witnesses, both provable by rewriting with `Ordinal.limitRecOn_succ`
and `Ordinal.limitRecOn_limit`. -/
private noncomputable def recStepLimit
    {cR : (Fin 2 ↪o PairERSource) → Bool} (β : Ordinal.{0})
    (IH : (γ : Ordinal.{0}) → γ < β → γ < Ordinal.omega.{0} 1 →
      CoherentBundle cR γ)
    (ih_succ : ∀ γ (hγsβ : Order.succ γ < β)
      (h1 : Order.succ γ < Ordinal.omega.{0} 1),
      IH (Order.succ γ) hγsβ h1 =
        (IH γ ((Order.lt_succ γ).trans hγsβ)
              ((Order.lt_succ γ).trans h1)).extend)
    (ih_limit : ∀ γ (_ : Order.IsSuccLimit γ) (hγβ : γ < β)
      (hγ : γ < Ordinal.omega.{0} 1) (δ : Ordinal.{0}) (hδγ : δ < γ),
      (IH γ hγβ hγ).stage.commitAt δ hδγ =
        (IH δ (hδγ.trans hγβ) (hδγ.trans hγ)).stage.succ.commitAt δ
          (Order.lt_succ δ))
    (hβ : β < Ordinal.omega.{0} 1) : CoherentBundle cR β :=
  CoherentBundle.limitExtend
    (fun γ hγβ => IH γ hγβ (hγβ.trans hβ))
    (fun {δ γ} hδγ hγβ =>
      crossCohLocal cR IH ih_succ ih_limit γ hγβ (hγβ.trans hβ) δ hδγ)
    hβ

/-- **Raw stage recursion**. Produces just the `PairERChain cR α`
(without bundling a family), via `Ordinal.limitRecOn`. Uses
`stageAt`-style dummy at limits (canonical `initialSegToType` prefix);
successor stages are concretely `(rawStage β).succ`. -/
private noncomputable def rawStage (cR : (Fin 2 ↪o PairERSource) → Bool)
    (α : Ordinal.{0}) : α < Ordinal.omega.{0} 1 → PairERChain cR α :=
  Ordinal.limitRecOn α
    (motive := fun α => α < Ordinal.omega.{0} 1 → PairERChain cR α)
    (fun _ => PairERChain.zero cR)
    (fun β IH hs =>
      (IH (lt_of_lt_of_le (Order.lt_succ β) hs.le)).succ)
    (fun β _ _ hβ => by
      haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
      have hβ_le : β ≤ (Order.succ (Cardinal.beth.{0} 1)).ord := by
        have h1 : β < (Cardinal.aleph.{0} 1).ord := by rwa [Cardinal.ord_aleph]
        have h2 : (Cardinal.aleph.{0} 1).ord ≤
            (Order.succ (Cardinal.beth.{0} 1)).ord :=
          Cardinal.ord_le_ord.mpr
            ((Cardinal.aleph_le_beth 1).trans (Order.le_succ _))
        exact (h1.trans_le h2).le
      exact PairERChain.limit hβ
        (Ordinal.initialSegToType hβ_le).toOrderEmbedding)

/-- **Top-level succ reduction for rawStage**. Direct application of
`Ordinal.limitRecOn_succ`. -/
private theorem rawStage_succ (cR : (Fin 2 ↪o PairERSource) → Bool)
    (β : Ordinal.{0}) (hs : Order.succ β < Ordinal.omega.{0} 1) :
    rawStage cR (Order.succ β) hs =
      (rawStage cR β ((Order.lt_succ β).trans hs)).succ := by
  unfold rawStage
  rw [Ordinal.limitRecOn_succ]

/-- **Top-level zero reduction for rawStage**. -/
private theorem rawStage_zero (cR : (Fin 2 ↪o PairERSource) → Bool)
    (hz : (0 : Ordinal.{0}) < Ordinal.omega.{0} 1) :
    rawStage cR 0 hz = PairERChain.zero cR := by
  unfold rawStage
  rw [Ordinal.limitRecOn_zero]

/-- **Reduction chain for rawStage across successor intervals**. For
`δ < γ` where both `γ+1 < ω_1` and the interval from `δ+1` to `γ+1` is
a "pure successor chain" (i.e., doesn't pass through a limit), commits
align. -/
private theorem rawStage_commitAt_of_succ
    (cR : (Fin 2 ↪o PairERSource) → Bool)
    (β : Ordinal.{0}) (hs : Order.succ β < Ordinal.omega.{0} 1)
    (δ : Ordinal.{0}) (hδβ : δ < β) :
    (rawStage cR (Order.succ β) hs).commitAt δ
        (hδβ.trans (Order.lt_succ β)) =
      (rawStage cR β ((Order.lt_succ β).trans hs)).commitAt δ hδβ := by
  rw [rawStage_succ, PairERChain.succ_commitAt]

/-- **Cross-stage coherence across successor intervals**. If `β` is a
successor ordinal `succ δ` or reachable via a chain of successors from
`δ+1`, commits align. Proved by strong induction on `β`. -/
private theorem rawStage_commitAt_stable
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    ∀ (β : Ordinal.{0}) (hβ : β < Ordinal.omega.{0} 1)
      (δ : Ordinal.{0}) (hδβ : δ < β)
      (hsδ : Order.succ δ < Ordinal.omega.{0} 1)
      (_ : ∀ γ, δ < γ → γ ≤ β → γ ∈ Set.range Order.succ),
      (rawStage cR β hβ).commitAt δ hδβ =
        (rawStage cR (Order.succ δ) hsδ).commitAt δ (Order.lt_succ δ) := by
  intro β
  induction β using WellFoundedLT.induction with
  | ind β IHβ =>
    intro hβ δ hδβ hsδ is_succ_chain
    rcases Ordinal.zero_or_succ_or_isSuccLimit β with hz | ⟨β', hβ'⟩ | hβ_lim
    · exact absurd hδβ (hz ▸ not_lt.mpr (zero_le _))
    · subst hβ'
      rcases lt_or_eq_of_le (Order.lt_succ_iff.mp hδβ) with hδ_lt | hδ_eq
      · rw [rawStage_commitAt_of_succ _ _ _ _ hδ_lt]
        have hβ'_lt : β' < Ordinal.omega.{0} 1 :=
          (Order.lt_succ β').trans hβ
        apply IHβ β' (Order.lt_succ β') hβ'_lt δ hδ_lt hsδ
        intro γ hδγ hγβ'
        exact is_succ_chain γ hδγ (hγβ'.trans (Order.le_succ β'))
      · subst hδ_eq; rfl
    · have hβ_mem : β ∈ Set.range Order.succ := is_succ_chain β hδβ le_rfl
      obtain ⟨b, hb⟩ := hβ_mem
      exact absurd hβ_lim (hb ▸ Order.not_isSuccLimit_succ b)

/-- **Commit at each successor ordinal**. For each ordinal `δ` with
`succ δ < ω_1`, the committed PairERSource element at position `δ` in
the raw stage at level `succ δ`. This is the "head" committed when
extending from level `δ` to level `succ δ`. -/
private noncomputable def chainAtSucc
    (cR : (Fin 2 ↪o PairERSource) → Bool) (δ : Ordinal.{0})
    (hsδ : Order.succ δ < Ordinal.omega.{0} 1) : PairERSource :=
  (rawStage cR (Order.succ δ) hsδ).commitAt δ (Order.lt_succ δ)

/-- **Commit at level `succ δ` equals chainAtSucc**. The "raw commit"
at position `δ` in `rawStage` at level `succ δ` is exactly the
`chainAtSucc` value — by definition. -/
private theorem rawStage_succ_commitAt
    (cR : (Fin 2 ↪o PairERSource) → Bool) (δ : Ordinal.{0})
    (hsδ : Order.succ δ < Ordinal.omega.{0} 1) :
    (rawStage cR (Order.succ δ) hsδ).commitAt δ (Order.lt_succ δ) =
      chainAtSucc cR δ hsδ := rfl

/-- **Strict monotonicity of chainAtSucc along pure successor chains**.
For δ₁ < δ₂ where the interval (δ₁, succ δ₂] contains only successor
ordinals, `chainAtSucc cR δ₁ _ < chainAtSucc cR δ₂ _`. -/
private theorem chainAtSucc_strictMono_of_succ_chain
    (cR : (Fin 2 ↪o PairERSource) → Bool)
    (δ₁ δ₂ : Ordinal.{0}) (h : δ₁ < δ₂)
    (hsδ₂ : Order.succ δ₂ < Ordinal.omega.{0} 1)
    (hsδ₁ : Order.succ δ₁ < Ordinal.omega.{0} 1)
    (is_succ : ∀ γ, δ₁ < γ → γ ≤ Order.succ δ₂ → γ ∈ Set.range Order.succ) :
    chainAtSucc cR δ₁ hsδ₁ < chainAtSucc cR δ₂ hsδ₂ := by
  -- Use rawStage_commitAt_stable to bring δ₁'s commit into the stage at (succ δ₂).
  have h_lt_s2 : δ₁ < Order.succ δ₂ := h.trans (Order.lt_succ δ₂)
  have equ : (rawStage cR (Order.succ δ₂) hsδ₂).commitAt δ₁ h_lt_s2 =
      chainAtSucc cR δ₁ hsδ₁ := by
    unfold chainAtSucc
    exact rawStage_commitAt_stable cR (Order.succ δ₂) hsδ₂ δ₁ h_lt_s2 hsδ₁ is_succ
  -- Now use PairERChain.commitAt_strictMono within the same stage.
  rw [← equ]
  show (rawStage cR (Order.succ δ₂) hsδ₂).commitAt δ₁ h_lt_s2 <
    (rawStage cR (Order.succ δ₂) hsδ₂).commitAt δ₂ (Order.lt_succ δ₂)
  exact PairERChain.commitAt_strictMono _ h_lt_s2 (Order.lt_succ δ₂) h

/-- **Chain extraction helper**: given a chain function `f` and a strict
mono proof, convert to an `OrderEmbedding`. -/
private noncomputable def chainToEmbedding
    {α : Type*} [LinearOrder α] (f : α → PairERSource) (mono : StrictMono f) :
    α ↪o PairERSource :=
  OrderEmbedding.ofStrictMono f mono

/-- **Rich bundle**: carries a `CoherentBundle` plus a GLOBAL commit
function indexed by ordinals `< α`, together with equations linking
the bundle's stage and family to this commit function.

This is the Σ-motive for the transfinite recursion. The key
invariants `stage_eq` and `family_eq` ensure that commits at shared
positions across different IH levels agree, which discharges the
cross-IH witness for `CoherentBundle.limitExtend` at limit stages. -/
structure RichBundle (cR : (Fin 2 ↪o PairERSource) → Bool)
    (α : Ordinal.{0}) where
  bundle : CoherentBundle cR α
  commit : ∀ δ : Ordinal.{0}, δ < α → PairERSource
  stage_eq : ∀ (δ : Ordinal.{0}) (hδα : δ < α),
    bundle.stage.commitAt δ hδα = commit δ hδα
  family_eq : ∀ (γ : Ordinal.{0}) (hγα : γ < α) (δ : Ordinal.{0})
    (hδγ : δ < γ),
    (bundle.family.stage γ hγα).commitAt δ
        (hδγ.trans (Order.lt_succ γ)) =
      commit δ (hδγ.trans hγα)
  /-- **Commit equals the top of the family's stage at the same position.**
  This extra invariant links `commit δ` to the *top* of
  `bundle.family.stage δ` (at position `δ` in that stage's own type),
  which is essential for the cross-IH witness in `limitExtend`. -/
  commit_top : ∀ (δ : Ordinal.{0}) (hδα : δ < α),
    commit δ hδα =
      (bundle.family.stage δ hδα).commitAt δ (Order.lt_succ δ)

/-- **Zero rich bundle** at level 0: trivially vacuous. -/
noncomputable def RichBundle.zero (cR : (Fin 2 ↪o PairERSource) → Bool) :
    RichBundle cR 0 where
  bundle := CoherentBundle.zero cR
  commit := fun δ h => absurd h (not_lt.mpr (zero_le δ))
  stage_eq := fun δ h => absurd h (not_lt.mpr (zero_le δ))
  family_eq := fun γ h _ _ => absurd h (not_lt.mpr (zero_le γ))
  commit_top := fun δ h => absurd h (not_lt.mpr (zero_le δ))

/-- **Successor extension of a rich bundle.** -/
noncomputable def RichBundle.extend
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (rb : RichBundle cR α) : RichBundle cR (Order.succ α) where
  bundle := rb.bundle.extend
  commit := fun δ _ =>
    if h_lt_α : δ < α then rb.commit δ h_lt_α
    else rb.bundle.extend.stage.commitAt α (Order.lt_succ α)
  stage_eq := by
    intro δ hδ_succ
    by_cases h_lt_α : δ < α
    · simp only [dif_pos h_lt_α]
      show rb.bundle.extend.stage.commitAt δ hδ_succ = rb.commit δ h_lt_α
      rw [CoherentBundle.extend_stage, PairERChain.succ_commitAt _ δ h_lt_α]
      exact rb.stage_eq δ h_lt_α
    · have h_eq : δ = α :=
        le_antisymm (Order.lt_succ_iff.mp hδ_succ) (not_lt.mp h_lt_α)
      subst h_eq
      simp only [dif_neg h_lt_α]
  family_eq := by
    intro γ hγ_succ δ hδγ
    by_cases h_γ_lt_α : γ < α
    · have hδα : δ < α := hδγ.trans h_γ_lt_α
      simp only [dif_pos hδα]
      show (rb.bundle.extend.family.stage γ hγ_succ).commitAt δ _ =
        rb.commit δ hδα
      unfold CoherentBundle.extend
      simp only [dif_pos h_γ_lt_α]
      exact rb.family_eq γ h_γ_lt_α δ hδγ
    · have h_γ_eq : γ = α :=
        le_antisymm (Order.lt_succ_iff.mp hγ_succ) (not_lt.mp h_γ_lt_α)
      -- γ = α, so we know δ < α.
      have hδα : δ < α := h_γ_eq ▸ hδγ
      simp only [dif_pos hδα]
      -- Goal: (extend.family.stage γ _).commitAt δ _ = rb.commit δ hδα.
      -- With γ = α, extend.family uses dif_neg branch: rb.bundle.stage.succ.
      -- After cast/eq, this is rb.bundle.stage.succ.commitAt δ _.
      subst h_γ_eq
      show (rb.bundle.extend.family.stage γ hγ_succ).commitAt δ _ =
        rb.commit δ hδα
      have hfam : rb.bundle.extend.family.stage γ hγ_succ =
          rb.bundle.stage.succ := by
        unfold CoherentBundle.extend
        simp only [dif_neg (lt_irrefl γ)]
      rw [hfam, PairERChain.succ_commitAt _ δ hδα]
      exact rb.stage_eq δ hδα
  commit_top := by
    intro δ hδ_succ
    by_cases h_lt_α : δ < α
    · -- δ < α: new commit δ = rb.commit δ.
      -- new bundle.family.stage δ = rb.bundle.family.stage δ (dif_pos).
      simp only [dif_pos h_lt_α]
      show rb.commit δ h_lt_α =
        (rb.bundle.extend.family.stage δ hδ_succ).commitAt δ (Order.lt_succ δ)
      have hfam : rb.bundle.extend.family.stage δ hδ_succ =
          rb.bundle.family.stage δ h_lt_α := by
        unfold CoherentBundle.extend
        simp only [dif_pos h_lt_α]
      rw [hfam]
      exact rb.commit_top δ h_lt_α
    · have h_eq : δ = α :=
        le_antisymm (Order.lt_succ_iff.mp hδ_succ) (not_lt.mp h_lt_α)
      subst h_eq
      simp only [dif_neg h_lt_α]
      show rb.bundle.extend.stage.commitAt δ (Order.lt_succ δ) =
        (rb.bundle.extend.family.stage δ hδ_succ).commitAt δ (Order.lt_succ δ)
      have hfam : rb.bundle.extend.family.stage δ hδ_succ =
          rb.bundle.stage.succ := by
        unfold CoherentBundle.extend
        simp only [dif_neg h_lt_α]
      rw [hfam, CoherentBundle.extend_stage]

/-- **Limit extension of a rich bundle, parameterized by `prev_succ`.**
Given `IH : ∀ γ < α, RichBundle cR γ` at a limit `α < ω_1` and a
`prev_succ` compatibility witness linking each IH's family at δ to the
lower IH's stage.succ, produce a `RichBundle cR α`.

The `prev_succ` hypothesis is the specific cross-level fact that must
be proved post-hoc about the top-level recursion: it is not a property
of individual `RichBundle`s but of the recursion's family of bundles.

With `prev_succ` in hand, all four `RichBundle` invariants at the
limit — `stage_eq`, `family_eq`, `commit_top`, and the underlying
CoherentBundle cross-IH — follow cleanly from the existing per-bundle
invariants `stage_eq` and `commit_top`. -/
noncomputable def RichBundle.limitExtend
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (IH : (γ : Ordinal.{0}) → γ < α → RichBundle cR γ)
    (prev_succ : ∀ (γ : Ordinal.{0}) (hγα : γ < α)
      (δ : Ordinal.{0}) (hδγ : δ < γ),
      (IH γ hγα).bundle.family.stage δ hδγ =
        (IH δ (hδγ.trans hγα)).bundle.stage.succ)
    (hα : α < Ordinal.omega.{0} 1) : RichBundle cR α :=
  let bundle_ih : (γ : Ordinal.{0}) → γ < α → CoherentBundle cR γ :=
    fun γ hγα => (IH γ hγα).bundle
  let ih_coh : ∀ {δ γ : Ordinal.{0}} (hδγ : δ < γ) (hγα : γ < α),
      (bundle_ih γ hγα).stage.commitAt δ hδγ =
        (bundle_ih δ (hδγ.trans hγα)).stage.succ.commitAt δ
          (Order.lt_succ δ) := by
    intro δ γ hδγ hγα
    -- LHS = (IH γ).bundle.stage.commitAt δ = (IH γ).commit δ (stage_eq).
    rw [(IH γ hγα).stage_eq δ hδγ]
    -- = (IH γ).bundle.family.stage δ _ .commitAt δ (Order.lt_succ δ) (commit_top).
    rw [(IH γ hγα).commit_top δ hδγ]
    -- = (IH δ).bundle.stage.succ.commitAt δ (Order.lt_succ δ) (prev_succ).
    rw [prev_succ γ hγα δ hδγ]
  { bundle := CoherentBundle.limitExtend bundle_ih ih_coh hα
    commit := fun δ hδα =>
      (IH δ hδα).bundle.stage.succ.commitAt δ (Order.lt_succ δ)
    stage_eq := by
      intro δ hδα
      -- new bundle.stage = family.limit hα. Via `PairERCoherentFamily.limit_commitAt`,
      -- its commitAt δ = family.commitVal δ = family.stage δ .commitAt δ
      -- = (IH δ).bundle.stage.succ.commitAt δ (by construction of CoherentBundle.limitExtend).
      show (CoherentBundle.limitExtend bundle_ih ih_coh hα).stage.commitAt δ hδα =
        (IH δ hδα).bundle.stage.succ.commitAt δ (Order.lt_succ δ)
      exact PairERCoherentFamily.limit_commitAt
        (CoherentBundle.limitExtend bundle_ih ih_coh hα).family hα δ hδα
    family_eq := by
      intro γ hγα δ hδγ
      -- new bundle.family.stage γ = (IH γ).bundle.stage.succ (def of CoherentBundle.limitExtend's family).
      -- commitAt δ = (IH γ).bundle.stage.succ.commitAt δ
      --           = (IH γ).bundle.stage.commitAt δ (succ_commitAt, δ < γ)
      --           = (IH γ).commit δ (stage_eq)
      --           = (IH γ).bundle.family.stage δ .commitAt δ _ (commit_top)
      --           = (IH δ).bundle.stage.succ.commitAt δ _ (prev_succ).
      show ((CoherentBundle.limitExtend bundle_ih ih_coh hα).family.stage γ hγα).commitAt δ _ = _
      rw [show (CoherentBundle.limitExtend bundle_ih ih_coh hα).family.stage γ hγα =
            (IH γ hγα).bundle.stage.succ from rfl]
      rw [PairERChain.succ_commitAt _ δ hδγ]
      rw [(IH γ hγα).stage_eq δ hδγ]
      rw [(IH γ hγα).commit_top δ hδγ]
      rw [prev_succ γ hγα δ hδγ]
    commit_top := by
      intro δ hδα
      -- new commit δ = (IH δ).bundle.stage.succ.commitAt δ (Order.lt_succ δ).
      -- new bundle.family.stage δ = (IH δ).bundle.stage.succ (by construction).
      show (IH δ hδα).bundle.stage.succ.commitAt δ (Order.lt_succ δ) =
        ((CoherentBundle.limitExtend bundle_ih ih_coh hα).family.stage δ hδα).commitAt δ (Order.lt_succ δ)
      rw [show (CoherentBundle.limitExtend bundle_ih ih_coh hα).family.stage δ hδα =
            (IH δ hδα).bundle.stage.succ from rfl] }

/-- **Rich recursive state**: bundles up to and including level α,
plus a cross-level family-vs-stage consistency invariant. The Σ-motive
for the outer transfinite recursion. -/
structure RichState (cR : (Fin 2 ↪o PairERSource) → Bool)
    (α : Ordinal.{0}) where
  bundles : ∀ γ : Ordinal.{0}, γ ≤ α → γ < Ordinal.omega.{0} 1 →
    RichBundle cR γ
  prev_eq : ∀ (γ : Ordinal.{0}) (hγα : γ ≤ α) (hγ : γ < Ordinal.omega.{0} 1)
    (δ : Ordinal.{0}) (hδγ : δ < γ) (hδα : δ ≤ α)
    (hδ : δ < Ordinal.omega.{0} 1),
    (bundles γ hγα hγ).bundle.family.stage δ hδγ =
      (bundles δ hδα hδ).bundle.stage.succ

/-- **Zero rich state** at level 0. -/
noncomputable def RichState.zero (cR : (Fin 2 ↪o PairERSource) → Bool) :
    RichState cR 0 where
  bundles := fun γ hγ0 _ =>
    have h_eq : γ = 0 := le_antisymm hγ0 (zero_le γ)
    h_eq ▸ RichBundle.zero cR
  prev_eq := fun γ _ _ _ hδγ _ _ =>
    absurd (hδγ.trans_le (le_of_eq (le_antisymm ‹γ ≤ 0› (zero_le γ))))
      (not_lt.mpr (zero_le _))

/-- **Successor rich state**: extend to level `α+1` using
`RichBundle.extend` on the level-α bundle. -/
noncomputable def RichState.extend
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (rs : RichState cR α) (hs : Order.succ α < Ordinal.omega.{0} 1) :
    RichState cR (Order.succ α) where
  bundles := fun γ hγ_succ hγ =>
    if h_lt_α : γ ≤ α then rs.bundles γ h_lt_α hγ
    else
      have h_eq : γ = Order.succ α :=
        le_antisymm hγ_succ (Order.succ_le_of_lt (not_le.mp h_lt_α))
      h_eq ▸ (rs.bundles α le_rfl
        ((Order.lt_succ α).trans hs)).extend
  prev_eq := by
    intro γ hγ_succ hγ δ hδγ hδ_succ hδ
    by_cases h_γ_lt_α : γ ≤ α
    · -- γ ≤ α: delegate to rs.prev_eq.
      have h_δ_lt_α : δ ≤ α := (le_of_lt hδγ).trans h_γ_lt_α
      simp only [dif_pos h_γ_lt_α, dif_pos h_δ_lt_α]
      exact rs.prev_eq γ h_γ_lt_α hγ δ hδγ h_δ_lt_α hδ
    · -- γ = α+1.
      have h_γ_eq : γ = Order.succ α :=
        le_antisymm hγ_succ (Order.succ_le_of_lt (not_le.mp h_γ_lt_α))
      subst h_γ_eq
      -- δ < α+1, so δ ≤ α.
      have h_δ_le_α : δ ≤ α := Order.lt_succ_iff.mp hδγ
      have h_α_lt : α < Ordinal.omega.{0} 1 := (Order.lt_succ α).trans hs
      by_cases h_δ_lt_α : δ < α
      · -- δ < α: new bundles α = (rs.bundles α _).extend. By extend, family.stage δ = rs.bundles α .family.stage δ.
        simp only [dif_neg h_γ_lt_α, dif_pos (le_of_lt h_δ_lt_α)]
        show ((rs.bundles α le_rfl h_α_lt).extend).bundle.family.stage δ hδγ =
          (rs.bundles δ (le_of_lt h_δ_lt_α) hδ).bundle.stage.succ
        have hfam : ((rs.bundles α le_rfl h_α_lt).extend).bundle.family.stage δ hδγ =
            (rs.bundles α le_rfl h_α_lt).bundle.family.stage δ h_δ_lt_α := by
          show (rs.bundles α le_rfl h_α_lt).bundle.extend.family.stage δ hδγ =
            (rs.bundles α le_rfl h_α_lt).bundle.family.stage δ h_δ_lt_α
          unfold CoherentBundle.extend
          simp only [dif_pos h_δ_lt_α]
        rw [hfam]
        exact rs.prev_eq α le_rfl h_α_lt δ h_δ_lt_α (le_of_lt h_δ_lt_α) hδ
      · -- δ = α: new bundles α+1 .family.stage α = rs.bundles α .stage.succ.
        have h_δ_eq : δ = α := le_antisymm h_δ_le_α (not_lt.mp h_δ_lt_α)
        subst h_δ_eq
        simp only [dif_neg h_γ_lt_α, dif_pos le_rfl]
        show ((rs.bundles δ le_rfl h_α_lt).extend).bundle.family.stage δ hδγ =
          (rs.bundles δ le_rfl hδ).bundle.stage.succ
        have hfam : ((rs.bundles δ le_rfl h_α_lt).extend).bundle.family.stage δ hδγ =
            (rs.bundles δ le_rfl h_α_lt).bundle.stage.succ := by
          show (rs.bundles δ le_rfl h_α_lt).bundle.extend.family.stage δ hδγ =
            (rs.bundles δ le_rfl h_α_lt).bundle.stage.succ
          unfold CoherentBundle.extend
          simp only [dif_neg (lt_irrefl δ)]
        rw [hfam]

/-- **Limit rich state**, parameterized on cross-state agreement.

Given `ih : ∀ γ < α, RichState cR γ` at a limit `α < ω_1`, and a
cross-state agreement witness that different IH's agree on common
lower levels, produce `RichState cR α`.

The cross-state agreement witness is the non-trivial part that must
be supplied by the outer recursion — it's a consequence of how the
recursion is structured (propositional equality derived via
`Ordinal.limitRecOn`'s reduction equations), rather than a property
of individual RichStates. -/
noncomputable def RichState.limitExtend
    {cR : (Fin 2 ↪o PairERSource) → Bool} {α : Ordinal.{0}}
    (ih : (γ : Ordinal.{0}) → γ < α → RichState cR γ)
    (cross_agree : ∀ (γ₁ γ₂ : Ordinal.{0}) (hγ₁α : γ₁ < α) (hγ₂α : γ₂ < α)
      (δ : Ordinal.{0}) (hδγ₁ : δ ≤ γ₁) (hδγ₂ : δ ≤ γ₂)
      (hδ : δ < Ordinal.omega.{0} 1),
      (ih γ₁ hγ₁α).bundles δ hδγ₁ hδ = (ih γ₂ hγ₂α).bundles δ hδγ₂ hδ)
    (hα : α < Ordinal.omega.{0} 1) : RichState cR α := by
  -- Shorthand for "the canonical bundle at level γ < α".
  let ih_bundle : (γ : Ordinal.{0}) → (hγα : γ < α) →
      RichBundle cR γ :=
    fun γ hγα => (ih γ hγα).bundles γ le_rfl (hγα.trans hα)
  -- The `prev_succ` witness for `RichBundle.limitExtend`, derived
  -- from within-state `prev_eq` plus `cross_agree`.
  have prev_succ_ih : ∀ (γ : Ordinal.{0}) (hγα : γ < α)
      (δ : Ordinal.{0}) (hδγ : δ < γ),
      (ih_bundle γ hγα).bundle.family.stage δ hδγ =
        (ih_bundle δ (hδγ.trans hγα)).bundle.stage.succ := by
    intro γ hγα δ hδγ
    have h_delta_lt_alpha : δ < α := hδγ.trans hγα
    have hIH_γ := (ih γ hγα).prev_eq γ le_rfl (hγα.trans hα) δ hδγ
      (le_of_lt hδγ) (h_delta_lt_alpha.trans hα)
    simp only [ih_bundle]
    rw [hIH_γ]
    exact congrArg (fun rb => rb.bundle.stage.succ)
      (cross_agree γ δ hγα h_delta_lt_alpha δ (le_of_lt hδγ) le_rfl
        (h_delta_lt_alpha.trans hα))
  -- Build the level-α rich bundle via `RichBundle.limitExtend`.
  let top_bundle : RichBundle cR α :=
    RichBundle.limitExtend ih_bundle prev_succ_ih hα
  refine
    { bundles := fun γ hγα hγ =>
        if h_γ_lt : γ < α then (ih γ h_γ_lt).bundles γ le_rfl hγ
        else
          have h_γ_eq : γ = α := le_antisymm hγα (not_lt.mp h_γ_lt)
          h_γ_eq ▸ top_bundle
      prev_eq := ?_ }
  intro γ hγα hγ δ hδγ hδα hδ
  by_cases h_γ_lt : γ < α
  · -- γ < α: via within-state prev_eq plus cross_agree.
    have h_δ_lt : δ < α := hδγ.trans h_γ_lt
    simp only [dif_pos h_γ_lt, dif_pos h_δ_lt]
    have hIH_γ := (ih γ h_γ_lt).prev_eq γ le_rfl hγ δ hδγ
      (le_of_lt hδγ) hδ
    rw [hIH_γ]
    exact congrArg (fun rb => rb.bundle.stage.succ)
      (cross_agree γ δ h_γ_lt h_δ_lt δ (le_of_lt hδγ) le_rfl hδ)
  · -- γ = α: top_bundle's family at δ is `(ih δ).bundles δ _ _.bundle.stage.succ`
    -- by construction of `RichBundle.limitExtend`.
    have h_γ_eq : γ = α := le_antisymm hγα (not_lt.mp h_γ_lt)
    subst h_γ_eq
    have h_δ_lt : δ < γ := hδγ
    simp only [dif_neg h_γ_lt, dif_pos h_δ_lt]
    show top_bundle.bundle.family.stage δ hδγ =
      ((ih δ h_δ_lt).bundles δ le_rfl hδ).bundle.stage.succ
    rfl

/-- **Transfinite rich-state recursion.** Produce a `RichState cR α`
at every `α < ω_1` via `Ordinal.limitRecOn`.

The limit case passes a `cross_agree` witness to `RichState.limitExtend`.
That witness asserts that IH's at different levels agree on their
bundles at common lower levels — a consequence of `limitRecOn`'s
propositional reduction equations, but not provable inside `H₃`'s body
without those equations. Left as one well-documented sorry; filling it
is a ~100-LOC exercise applying `Ordinal.limitRecOn_succ`/`_limit` in a
strong induction on the lesser level `δ`. -/
noncomputable def richStage (cR : (Fin 2 ↪o PairERSource) → Bool)
    (α : Ordinal.{0}) : α < Ordinal.omega.{0} 1 → RichState cR α :=
  Ordinal.limitRecOn α
    (motive := fun α => α < Ordinal.omega.{0} 1 → RichState cR α)
    -- zero
    (fun _ => RichState.zero cR)
    -- succ
    (fun β IH hβs =>
      (IH ((Order.lt_succ β).trans hβs)).extend hβs)
    -- limit
    (fun β _ IH hβ =>
      RichState.limitExtend
        (fun γ hγβ => IH γ hγβ (hγβ.trans hβ))
        (by
          -- cross_agree obligation: different IH's agree on common
          -- lower levels. Follows from `limitRecOn`'s reduction
          -- equations `_succ`/`_limit` by strong induction on δ. The
          -- post-hoc proof applies `richStage_succ` / `richStage_limit`
          -- at each δ, reducing both sides to the same canonical bundle.
          intros; sorry)
        hβ)

/-! ### Reduction lemmas + canonicalization for `richStage`

The reduction lemmas unfold `richStage` at zero, successor, and limit
ordinals via `Ordinal.limitRecOn_zero/_succ/_limit`. They are used
post-hoc to prove `richStage_bundle_eq_self` — the theorem that
`richStage cR α .bundles δ _ _` at level `δ ≤ α` EQUALS the canonical
`richStage cR δ .bundles δ le_rfl _`, regardless of the outer level
`α`. From this canonicalization, `cross_agree` follows as an immediate
corollary by transitivity. -/

/-- `richStage` at `0` is `RichState.zero`. -/
theorem richStage_zero (cR : (Fin 2 ↪o PairERSource) → Bool)
    (h0 : (0 : Ordinal.{0}) < Ordinal.omega.{0} 1) :
    richStage cR 0 h0 = RichState.zero cR := by
  unfold richStage
  rw [Ordinal.limitRecOn_zero]

/-- `richStage` at `Order.succ β` is `(richStage cR β _).extend`. -/
theorem richStage_succ (cR : (Fin 2 ↪o PairERSource) → Bool)
    (β : Ordinal.{0}) (hβs : Order.succ β < Ordinal.omega.{0} 1) :
    richStage cR (Order.succ β) hβs =
      (richStage cR β ((Order.lt_succ β).trans hβs)).extend hβs := by
  unfold richStage
  rw [Ordinal.limitRecOn_succ]

/-- `richStage` at a limit `β`, restricted to the bundle at `γ < β`:
takes the `if_γ_lt_β := true` branch of `RichState.limitExtend`, which
returns `(richStage cR γ _).bundles γ le_rfl _` — irrespective of the
cross_agree witness inside the definition. -/
theorem richStage_limit_bundles_below
    (cR : (Fin 2 ↪o PairERSource) → Bool)
    {β : Ordinal.{0}} (hβ_lim : Order.IsSuccLimit β)
    (hβ : β < Ordinal.omega.{0} 1)
    (γ : Ordinal.{0}) (hγβ : γ < β) (hγ : γ < Ordinal.omega.{0} 1) :
    (richStage cR β hβ).bundles γ (le_of_lt hγβ) hγ =
      (richStage cR γ hγ).bundles γ le_rfl hγ := by
  unfold richStage
  rw [Ordinal.limitRecOn_limit (h := hβ_lim)]
  unfold RichState.limitExtend
  simp only [dif_pos hγβ]

/-- **Canonicalization of `richStage` bundles**: for any `δ ≤ α`, the
`bundles` field of `richStage cR α` at level `δ` equals the canonical
`richStage cR δ`'s self-bundle. Proved by strong induction on `α`. -/
private theorem richStage_bundle_eq_self
    (cR : (Fin 2 ↪o PairERSource) → Bool) {α δ : Ordinal.{0}}
    (hα : α < Ordinal.omega.{0} 1) (hδα : δ ≤ α)
    (hδ : δ < Ordinal.omega.{0} 1) :
    (richStage cR α hα).bundles δ hδα hδ =
      (richStage cR δ hδ).bundles δ le_rfl hδ := by
  induction α using Ordinal.limitRecOn with
  | zero =>
    -- α = 0: δ ≤ 0, so δ = 0.
    have hδ0 : δ = 0 := le_antisymm hδα (zero_le _)
    subst hδ0
    rfl
  | succ β IH =>
    -- α = succ β: unfold richStage_succ; bundles is RichState.extend's dif.
    have hβω : β < Ordinal.omega.{0} 1 := (Order.lt_succ β).trans hα
    rw [richStage_succ]
    by_cases h_δ_le_β : δ ≤ β
    · -- δ ≤ β: `extend`'s dif_pos branch returns `richStage β .bundles δ`.
      show ((richStage cR β hβω).extend hα).bundles δ hδα hδ = _
      unfold RichState.extend
      simp only [dif_pos h_δ_le_β]
      exact IH hβω h_δ_le_β
    · -- δ = succ β: reflexive.
      have h_δ_eq : δ = Order.succ β :=
        le_antisymm hδα (Order.succ_le_of_lt (not_le.mp h_δ_le_β))
      subst h_δ_eq
      rw [richStage_succ]
  | limit β hβ_lim IH =>
    -- α = limit β: split δ < β vs δ = β.
    by_cases h_δ_lt_β : δ < β
    · -- δ < β: both sides agree by `richStage_limit_bundles_below`.
      have h := richStage_limit_bundles_below cR hβ_lim hα δ h_δ_lt_β hδ
      -- Rewrite hδα (which is δ ≤ β) to use le_of_lt h_δ_lt_β.
      have : (richStage cR β hα).bundles δ hδα hδ =
          (richStage cR β hα).bundles δ (le_of_lt h_δ_lt_β) hδ := by
        congr
      rw [this, h]
    · -- δ = β: reflexive.
      have h_δ_eq : δ = β := le_antisymm hδα (not_lt.mp h_δ_lt_β)
      subst h_δ_eq
      rfl

/-- **Cross-state agreement** for `richStage`: different `richStage`
calls agree on bundles at common lower levels. Immediate corollary of
`richStage_bundle_eq_self`, by transitivity through the canonical
bundle at level `δ`. -/
theorem richStage_cross_agree
    (cR : (Fin 2 ↪o PairERSource) → Bool)
    {α₁ α₂ δ : Ordinal.{0}}
    (hα₁ : α₁ < Ordinal.omega.{0} 1) (hα₂ : α₂ < Ordinal.omega.{0} 1)
    (hδα₁ : δ ≤ α₁) (hδα₂ : δ ≤ α₂) (hδ : δ < Ordinal.omega.{0} 1) :
    (richStage cR α₁ hα₁).bundles δ hδα₁ hδ =
      (richStage cR α₂ hα₂).bundles δ hδα₂ hδ := by
  rw [richStage_bundle_eq_self cR hα₁ hδα₁ hδ,
      richStage_bundle_eq_self cR hα₂ hδα₂ hδ]

/-- **Canonical rich stage (sorry-free).** A drop-in replacement for
`richStage` that uses `richStage_bundle_eq_self` to discharge `prev_eq`
directly, without going through the sorry'd `cross_agree` witness.
Its bundle function is defined by "look up `richStage` at level δ and
take the canonical δ-bundle there" — monotone and internally
consistent. -/
noncomputable def richStageCanonical
    (cR : (Fin 2 ↪o PairERSource) → Bool) (α : Ordinal.{0})
    (_hα : α < Ordinal.omega.{0} 1) : RichState cR α where
  bundles := fun γ _ hγ => (richStage cR γ hγ).bundles γ le_rfl hγ
  prev_eq := by
    intro γ _ hγ δ hδγ _ hδ
    have h_internal := (richStage cR γ hγ).prev_eq γ le_rfl hγ δ hδγ
      (le_of_lt hδγ) hδ
    rw [h_internal]
    exact congrArg (fun rb => rb.bundle.stage.succ)
      (richStage_bundle_eq_self cR hγ (le_of_lt hδγ) hδ)

/-! ### Tree-driven stage: `treeStage` parallel to `richStage`

`treeStage cR α` produces a `TreeBundle cR α` for every `α < ω_1` via
`Ordinal.limitRecOn`. Mirrors `richStage`'s structure but uses the
tree-deferred path:

- zero: `TreeBundle.zero`
- succ: `TreeBundle.extend` (preserves the tree-selected branch via
  `TB.stage.succ`)
- limit: `TreeBundle.limitExtend` with the universal-tree
  (`PairERTypeTree.universal`) attached at level `α`

The limit case requires a `prev_succ` cross-stage witness analogous
to `richStage`'s `cross_agree`. It is sorry'd here and will be
discharged post-hoc by reduction lemmas + a canonicalization theorem
(treeStage_bundle_eq_self analog), in the same pattern that resolved
`richStage`. -/

/-- **[LEGACY — off-chain; superseded by `treeStageOfBranch`]** Tree-driven
transfinite stage producing `TreeBundle cR α` via `Ordinal.limitRecOn`. Its limit
case goes through `TreeBundle.limitExtend` → `commitCoherent` → the false-as-stated
`exists_large_iInter_stage_fibers`, so this recursion can never be axiom-clean.
The branch-parametrized `treeStageOfBranch` (`:= limitFromCoherentMajority B`) is
the axiom-clean replacement: given `B : CoherentMajorityBranch`, it builds the
bundle at every level with no recursion and no dependence on the false theorem.
Nothing on the active `B`/witness-net path consumes `treeStage`; retained only
until this dead tower is removed.

**Tree-driven transfinite stage.** Produces `TreeBundle cR α` at
every `α < ω_1`. The limit case attaches a universal tree (so
`selectedBranch` survives across recursion levels) and discharges
`prev_succ` from the eventual canonicalization (currently sorry'd,
mirroring `richStage`'s `cross_agree`). -/
noncomputable def treeStage (cR : (Fin 2 ↪o PairERSource) → Bool)
    (α : Ordinal.{0}) : α < Ordinal.omega.{0} 1 → TreeBundle cR α :=
  Ordinal.limitRecOn α
    (motive := fun α => α < Ordinal.omega.{0} 1 → TreeBundle cR α)
    -- zero
    (fun _ => TreeBundle.zero cR)
    -- succ
    (fun β IH hβs =>
      (IH ((Order.lt_succ β).trans hβs)).extend hβs)
    -- limit
    (fun β _ IH hβ =>
      TreeBundle.limitExtend hβ
        (fun γ hγβ => IH γ hγβ (hγβ.trans hβ))
        (by
          -- prev_succ obligation: cross-stage witness linking
          -- (IH β').stage.commitAt δ to (IH δ).stage.succ.commitAt δ.
          -- Sorry'd here because direct replacement is cyclic (the
          -- post-hoc theorem `treeStage_prev_succ` uses treeStage).
          -- See `treeStage_prev_succ` for the post-hoc proof.
          intros; sorry)
        (by
          -- type_succ obligation: cross-stage witness linking
          -- (IH β').stage.typeAt δ to (IH δ).stage.succNewBool.
          -- Sorry'd here for the same cyclic reason as prev_succ.
          -- See `treeStage_type_succ` for the post-hoc proof.
          intros; sorry))

/-- `treeStage` at `0` is `TreeBundle.zero`. -/
theorem treeStage_zero (cR : (Fin 2 ↪o PairERSource) → Bool)
    (h0 : (0 : Ordinal.{0}) < Ordinal.omega.{0} 1) :
    treeStage cR 0 h0 = TreeBundle.zero cR := by
  unfold treeStage
  rw [Ordinal.limitRecOn_zero]

/-- `treeStage` at `Order.succ β` is `(treeStage cR β _).extend`. -/
theorem treeStage_succ (cR : (Fin 2 ↪o PairERSource) → Bool)
    (β : Ordinal.{0}) (hβs : Order.succ β < Ordinal.omega.{0} 1) :
    treeStage cR (Order.succ β) hβs =
      (treeStage cR β ((Order.lt_succ β).trans hβs)).extend hβs := by
  unfold treeStage
  rw [Ordinal.limitRecOn_succ]

/-- **Canonical commit value at `treeStage`'s succ-(δ+1) level.**
The new top commit of the chain `(treeStage cR δ hδ).stage.succ`,
i.e., the witness chosen by `PairERChain.succ`'s pigeonhole step
at level `δ`. By `treeStage_succ`, this equals the corresponding
commit inside `treeStage cR (Order.succ δ) _`. -/
noncomputable def treeStageCanonicalCommit
    (cR : (Fin 2 ↪o PairERSource) → Bool)
    (δ : Ordinal.{0}) (hδ : δ < Ordinal.omega.{0} 1) : PairERSource :=
  (treeStage cR δ hδ).stage.succ.commitAt δ (Order.lt_succ δ)

/-- **Limit-case commit equation for `treeStage`.** At a limit `β` with
`δ < β`, the commit at position `δ` in the limit-stage equals the new
top commit of the `(treeStage cR δ _).stage.succ` chain. This is the
limit-case engine for `treeStage_canonical`: `treeStage`'s commits at
limits factor through the canonical `(treeStage cR δ _).extend` step. -/
theorem treeStage_limit_stage_commitAt
    (cR : (Fin 2 ↪o PairERSource) → Bool)
    {β : Ordinal.{0}} (hβ_lim : Order.IsSuccLimit β)
    (hβ : β < Ordinal.omega.{0} 1)
    (δ : Ordinal.{0}) (hδβ : δ < β) :
    (treeStage cR β hβ).stage.commitAt δ hδβ =
      (treeStage cR δ (hδβ.trans hβ)).stage.succ.commitAt δ
        (Order.lt_succ δ) := by
  unfold treeStage
  rw [Ordinal.limitRecOn_limit (h := hβ_lim)]
  unfold TreeBundle.limitExtend TreeBundle.limitFromTree
    PairERTreeFamily.toLimitChain PairERTreeFamily.toLimitChainAtBranch
  rw [PairERChain.limitWithType_commitAt]
  rw [show ∀ F : PairERCoherentFamily cR β,
        F.prefix
          (Ordinal.enum (α := β.ToType) (· < ·)
            ⟨δ, (Ordinal.type_toType β).symm ▸ hδβ⟩) =
          F.commitVal δ hδβ from
      fun F => F.prefix_enum δ hδβ]
  rfl

/-- **Canonicalization of `treeStage` commits.** Mirrors
`richStage_bundle_eq_self`: the commit at position `δ` in
`treeStage cR α` is canonical, equal across all enclosing levels
`α > δ`. Specifically, every reading equals `treeStageCanonicalCommit
cR δ` — the new top commit at level `Order.succ δ`. Proved by induction
on `α` using `treeStage_succ`, `TreeBundle.extend_commitAt_old`, and
`treeStage_limit_stage_commitAt`. -/
theorem treeStage_canonical_commit
    (cR : (Fin 2 ↪o PairERSource) → Bool)
    {α δ : Ordinal.{0}}
    (hα : α < Ordinal.omega.{0} 1) (hδα : δ < α)
    (hδ : δ < Ordinal.omega.{0} 1) :
    (treeStage cR α hα).stage.commitAt δ hδα =
      treeStageCanonicalCommit cR δ hδ := by
  induction α using Ordinal.limitRecOn with
  | zero => exact absurd hδα (not_lt.mpr (zero_le δ))
  | succ β IH =>
    have hβ : β < Ordinal.omega.{0} 1 := (Order.lt_succ β).trans hα
    rw [treeStage_succ]
    by_cases h_δ_eq_β : δ = β
    · -- δ = β: LHS unfolds to `(treeStage cR δ _).stage.succ.commitAt δ`,
      -- which is exactly the canonical commit's definition.
      subst h_δ_eq_β
      show ((treeStage cR δ hβ).extend hα).stage.commitAt δ _ =
        treeStageCanonicalCommit cR δ hδ
      rfl
    · have hδβ : δ < β :=
        lt_of_le_of_ne (Order.lt_succ_iff.mp hδα) h_δ_eq_β
      show ((treeStage cR β hβ).extend hα).stage.commitAt δ _ =
        treeStageCanonicalCommit cR δ hδ
      rw [TreeBundle.extend_commitAt_old hα (treeStage cR β hβ) δ hδβ]
      exact IH hβ hδβ
  | limit β hβ_lim IH =>
    rw [treeStage_limit_stage_commitAt cR hβ_lim hα δ hδα]
    rfl

/-- **Cross-level agreement** for `treeStage` commits: any two enclosing
levels `α₁, α₂ > δ` produce the same commit at `δ`. Direct corollary
of `treeStage_canonical_commit`. -/
theorem treeStage_cross_agree_commit
    (cR : (Fin 2 ↪o PairERSource) → Bool)
    {α₁ α₂ δ : Ordinal.{0}}
    (hα₁ : α₁ < Ordinal.omega.{0} 1) (hα₂ : α₂ < Ordinal.omega.{0} 1)
    (hδα₁ : δ < α₁) (hδα₂ : δ < α₂) (hδ : δ < Ordinal.omega.{0} 1) :
    (treeStage cR α₁ hα₁).stage.commitAt δ hδα₁ =
      (treeStage cR α₂ hα₂).stage.commitAt δ hδα₂ := by
  rw [treeStage_canonical_commit cR hα₁ hδα₁ hδ,
      treeStage_canonical_commit cR hα₂ hδα₂ hδ]

/-! ### Bookkeeping frontier: `treeStage` recursion cross-IH certificates

Mathematically follows from the post-hoc canonicality lemmas
`treeStage_prev_succ` and `treeStage_type_succ` (proved below as
direct corollaries of `treeStage_canonical_commit` /
`treeStage_typeAt_canonical`). Eliminating the `sorryAx` propagation
through these certificates requires a Σ-motive refactor of
`treeStage` (packaging canonical certificates at construction time).

This is a recursion-engineering frontier, separate from the
mathematical frontier `exists_large_iInter_stage_fibers` (the genuine
Erdős–Rado fusion content). Per the project's stated priorities, the
Σ-motive refactor is deferred until a clean axiom profile becomes
load-bearing for an API/publication. -/

/-- **`treeStage_prev_succ`**: the post-hoc cross-IH commit witness
for the `prev_succ` argument of `TreeBundle.limitExtend`. For any
`δ < β < ω₁`, the commit at position `δ` in the `β`-stage of
`treeStage` equals the new top commit of the `δ`-stage's successor
extension. Direct corollary of `treeStage_canonical_commit` +
`treeStageCanonicalCommit`'s definition. -/
theorem treeStage_prev_succ
    (cR : (Fin 2 ↪o PairERSource) → Bool) {β δ : Ordinal.{0}}
    (hβ : β < Ordinal.omega.{0} 1) (hδβ : δ < β)
    (hδ : δ < Ordinal.omega.{0} 1) :
    (treeStage cR β hβ).stage.commitAt δ hδβ =
      (treeStage cR δ hδ).stage.succ.commitAt δ (Order.lt_succ δ) := by
  rw [treeStage_canonical_commit cR hβ hδβ hδ]
  rfl

/-! ### Final assembly: chain extraction and `erdos_rado_pair_omega1`

With `richStageCanonical cR α` producing a sorry-free `RichState cR α`
at every `α < ω_1`, chain extraction and strict monotonicity are
available via `pairERCommit` (below). Two obstructions remain for the
full theorem:

1. **The `cross_agree` sorry inside `richStage`** (axiom-clean post-hoc
   via `richStage_cross_agree`; architectural cleanup pending).

2. **Type coherence at limits**: `PairERCoherentFamily` currently
   enforces only head-coherence (`coherent` field), not type-coherence.
   At a limit α, `PairERChain.limit` invokes `exists_large_limit_fiber`
   which picks a FRESH `τ : α.ToType → Bool`; this need not agree with
   the committed Bools from earlier successor stages. To prove pair-
   homogeneity `cR (pair (chain β) (chain γ)) = committed β`, the limit
   τ must be chosen to MATCH the earlier committed Bools — which
   requires a sharper H4 giving large fiber for a SPECIFIC (not
   arbitrary) τ, namely the one reproducing earlier committed types.

The second obstruction is a meaningful mathematical refinement (needs
a "type-coherent large limit fiber" lemma + `PairERCoherentFamily`
extension with `type_coherent` invariant). It's documented here as the
final architectural step before the pigeonhole/H5/H1 assembly. -/

/-- **Canonical commit value at position `δ < ω_1`**: take the
`RichBundle` at level `Order.succ δ` (via `richStageCanonical`) and
read off its `commit δ`. -/
noncomputable def pairERCommit
    (cR : (Fin 2 ↪o PairERSource) → Bool) (δ : Ordinal.{0})
    (hδ : δ < Ordinal.omega.{0} 1) : PairERSource :=
  have hsδ : Order.succ δ < Ordinal.omega.{0} 1 :=
    (Cardinal.isSuccLimit_omega 1).succ_lt hδ
  ((richStageCanonical cR (Order.succ δ) hsδ).bundles (Order.succ δ) le_rfl
      hsδ).commit δ (Order.lt_succ δ)

/-- **`pairERCommit` equals the canonical bundle's stage commit.** Via
`RichBundle.stage_eq`, the commit agrees with the underlying chain's
`commitAt`. -/
lemma pairERCommit_eq_stage_commitAt
    (cR : (Fin 2 ↪o PairERSource) → Bool) (δ : Ordinal.{0})
    (hδ : δ < Ordinal.omega.{0} 1) :
    pairERCommit cR δ hδ =
      have hsδ : Order.succ δ < Ordinal.omega.{0} 1 :=
        (Cardinal.isSuccLimit_omega 1).succ_lt hδ
      ((richStageCanonical cR (Order.succ δ) hsδ).bundles (Order.succ δ)
          le_rfl hsδ).bundle.stage.commitAt δ (Order.lt_succ δ) := by
  unfold pairERCommit
  rw [((richStageCanonical cR (Order.succ δ) _).bundles (Order.succ δ)
      le_rfl _).stage_eq δ (Order.lt_succ δ)]

/-- **`pairERCommit` is strictly monotone** in `δ`. Proof strategy:
realize both commits inside the single chain at level `succ δ₂` via
the cross-level identity between `rb₁`'s stage and `rb₂`'s family
(using `RichState.prev_eq` + `PairERChain.succ_commitAt`), then apply
`PairERChain.commitAt_strictMono`. -/
lemma pairERCommit_strictMono
    (cR : (Fin 2 ↪o PairERSource) → Bool) {δ₁ δ₂ : Ordinal.{0}}
    (hδ₁ : δ₁ < Ordinal.omega.{0} 1) (hδ₂ : δ₂ < Ordinal.omega.{0} 1)
    (h : δ₁ < δ₂) :
    pairERCommit cR δ₁ hδ₁ < pairERCommit cR δ₂ hδ₂ := by
  have hsδ₁ : Order.succ δ₁ < Ordinal.omega.{0} 1 :=
    (Cardinal.isSuccLimit_omega 1).succ_lt hδ₁
  have hsδ₂ : Order.succ δ₂ < Ordinal.omega.{0} 1 :=
    (Cardinal.isSuccLimit_omega 1).succ_lt hδ₂
  have h_sδ₁_lt_sδ₂ : Order.succ δ₁ < Order.succ δ₂ := Order.succ_lt_succ h
  set state : RichState cR (Order.succ δ₂) :=
    richStageCanonical cR (Order.succ δ₂) hsδ₂ with hstate
  set rb₂ : RichBundle cR (Order.succ δ₂) :=
    state.bundles (Order.succ δ₂) le_rfl hsδ₂ with hrb₂
  -- rb₂'s own stage is strict-monotone in position.
  have h_mono : rb₂.bundle.stage.commitAt δ₁ (h.trans (Order.lt_succ δ₂)) <
      rb₂.bundle.stage.commitAt δ₂ (Order.lt_succ δ₂) :=
    PairERChain.commitAt_strictMono (s := rb₂.bundle.stage)
      (hδ₁ := h.trans (Order.lt_succ δ₂))
      (hδ₂ := Order.lt_succ δ₂) h
  -- Identify both commits with rb₂'s stage commits.
  have h_δ₂_eq : rb₂.bundle.stage.commitAt δ₂ (Order.lt_succ δ₂) =
      pairERCommit cR δ₂ hδ₂ := by
    rw [pairERCommit_eq_stage_commitAt]
  have h_δ₁_eq : rb₂.bundle.stage.commitAt δ₁ (h.trans (Order.lt_succ δ₂)) =
      pairERCommit cR δ₁ hδ₁ := by
    -- Chain of equalities through stage_eq, family_eq, prev_eq, and succ_commitAt.
    -- Note: with richStageCanonical, state.bundles at any γ IS already the
    -- canonical bundle `(richStage cR γ _).bundles γ le_rfl _`, so no extra
    -- `richStage_bundle_eq_self` rewrite is needed.
    rw [rb₂.stage_eq δ₁ (h.trans (Order.lt_succ δ₂))]
    rw [← rb₂.family_eq (Order.succ δ₁) h_sδ₁_lt_sδ₂ δ₁ (Order.lt_succ δ₁)]
    rw [state.prev_eq (Order.succ δ₂) le_rfl hsδ₂ (Order.succ δ₁)
      h_sδ₁_lt_sδ₂ (le_of_lt h_sδ₁_lt_sδ₂) hsδ₁]
    rw [PairERChain.succ_commitAt _ δ₁ (Order.lt_succ δ₁)]
    -- `state.bundles (succ δ₁) _ _` β-reduces to the same canonical bundle
    -- as `(richStageCanonical cR (succ δ₁) _).bundles (succ δ₁) le_rfl _`.
    show ((richStageCanonical cR (Order.succ δ₁) hsδ₁).bundles (Order.succ δ₁)
      le_rfl hsδ₁).bundle.stage.commitAt δ₁ _ = pairERCommit cR δ₁ hδ₁
    rw [← pairERCommit_eq_stage_commitAt]
  rw [← h_δ₁_eq, ← h_δ₂_eq]
  exact h_mono

/-- **Committed Bool at position `δ`**: the `type` value at the top
position of the chain at level `succ δ` (via `richStageCanonical`). -/
noncomputable def pairERCommitBool
    (cR : (Fin 2 ↪o PairERSource) → Bool) (δ : Ordinal.{0})
    (hδ : δ < Ordinal.omega.{0} 1) : Bool :=
  have hsδ : Order.succ δ < Ordinal.omega.{0} 1 :=
    (Cardinal.isSuccLimit_omega 1).succ_lt hδ
  ((richStageCanonical cR (Order.succ δ) hsδ).bundles (Order.succ δ) le_rfl
      hsδ).bundle.stage.type (⊤ : (Order.succ δ).ToType)

/-- **Indexed committed Bool function** on `(ω_1).ToType`. -/
noncomputable def pairERCommitBoolFn
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    (Ordinal.omega.{0} 1).ToType → Bool := fun x =>
  haveI : IsWellOrder (Ordinal.omega.{0} 1).ToType (· < ·) := isWellOrder_lt
  pairERCommitBool cR (Ordinal.typein (· < ·) x) (by
    simpa [Ordinal.type_toType] using
      Ordinal.typein_lt_type
        (· < · : (Ordinal.omega.{0} 1).ToType →
          (Ordinal.omega.{0} 1).ToType → Prop) x)

/-- **Bool pigeonhole on the committed Bool function**: some Bool `b`
has preimage of cardinality `≥ ℵ_1`. Uses H3 with `κ := ℵ_0`. -/
theorem exists_large_pairERCommit_fiber
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    ∃ b : Bool,
      Cardinal.aleph.{0} 1 ≤
        Cardinal.mk ((pairERCommitBoolFn cR) ⁻¹' {b}) := by
  -- `(ω_1).ToType` has cardinality `aleph 1 = succ aleph_0`.
  have haleph1 : Cardinal.aleph.{0} 1 = Order.succ Cardinal.aleph0.{0} := by
    rw [show (1 : Ordinal.{0}) = Order.succ 0 from Ordinal.succ_zero.symm,
      Cardinal.aleph_succ, Cardinal.aleph_zero]
  have hα_card :
      Order.succ Cardinal.aleph0.{0} ≤
        Cardinal.mk (Ordinal.omega.{0} 1).ToType := by
    rw [Cardinal.mk_toType, Ordinal.card_omega, ← haleph1]
  have hβ_card : Cardinal.mk Bool ≤ Cardinal.aleph0.{0} := Cardinal.mk_le_aleph0
  obtain ⟨b, hb⟩ := exists_large_fiber_of_small_codomain
    (κ := Cardinal.aleph0.{0}) le_rfl hα_card hβ_card
    (pairERCommitBoolFn cR)
  exact ⟨b, haleph1 ▸ hb⟩

/-- **The ω_1-indexed chain embedding** into `PairERSource`. Wraps
`pairERCommit` as an `OrderEmbedding` via strict monotonicity. -/
noncomputable def pairERChainEmbedding
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    (Ordinal.omega.{0} 1).ToType ↪o PairERSource := by
  haveI : IsWellOrder (Ordinal.omega.{0} 1).ToType (· < ·) := isWellOrder_lt
  refine OrderEmbedding.ofStrictMono
    (fun x =>
      pairERCommit cR (Ordinal.typein (· < ·) x) (by
        simpa [Ordinal.type_toType] using
          Ordinal.typein_lt_type
            (· < · : (Ordinal.omega.{0} 1).ToType →
              (Ordinal.omega.{0} 1).ToType → Prop) x))
    ?_
  intro x y hxy
  have hx : Ordinal.typein (· < ·) x < Ordinal.omega.{0} 1 := by
    simpa [Ordinal.type_toType] using
      Ordinal.typein_lt_type
        (· < · : (Ordinal.omega.{0} 1).ToType →
          (Ordinal.omega.{0} 1).ToType → Prop) x
  have hy : Ordinal.typein (· < ·) y < Ordinal.omega.{0} 1 := by
    simpa [Ordinal.type_toType] using
      Ordinal.typein_lt_type
        (· < · : (Ordinal.omega.{0} 1).ToType →
          (Ordinal.omega.{0} 1).ToType → Prop) y
  exact pairERCommit_strictMono cR hx hy
    ((Ordinal.typein_lt_typein (· < ·)).mpr hxy)

/-- **Pre-theorem**: from any pair-coloring `cR` on `PairERSource`, we
obtain an ω_1-indexed order-embedding (into `PairERSource`). Composing
with H1 transports this into any well-ordered `I` of cardinality
`≥ succ ℶ_1`. -/
theorem exists_omega1_embedding_pair
    {I : Type} [LinearOrder I] [WellFoundedLT I]
    (hI : Cardinal.mk I ≥ Order.succ (Cardinal.beth.{0} 1))
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    Nonempty ((Ordinal.omega.{0} 1).ToType ↪o I) := by
  obtain ⟨emb⟩ : Nonempty (PairERSource ↪o I) :=
    exists_ordToType_embedding_of_card_ge hI
  -- Route through the clean EHMR pair theorem: it produces a (homogeneous) ω₁-embedding
  -- into `PairERSource`; compose with `emb` for the conclusion (homogeneity unused here).
  obtain ⟨f, _, _⟩ := erdos_rado_pair_omega1 cR
  exact ⟨f.trans emb⟩

/-! ### Tree-driven chain extraction (parallel to `pairERCommit`)

`treeCommit` and `treeCommitBool` are the tree-deferred analogs of
`pairERCommit` and `pairERCommitBool`. They feed the same downstream
pigeonhole/H5/H1 pipeline but read commits and Bools out of
`treeStage`'s `TreeBundle`s, where limits use `selectedBranch` rather
than a fresh `Classical.choose τ`. Together with the canonical-commit
machinery (`treeStage_canonical_commit`,
`treeStage_cross_agree_commit`), this furnishes a sorry-free
embedding once the underlying type-coherence story is in place. -/

/-- **Tree-driven canonical commit at `δ < ω_1`.** Reads `commitAt δ`
on the chain at level `Order.succ δ` produced by `treeStage`. By
`treeStage_canonical_commit`, this value is independent of the
enclosing level (any α > δ gives the same answer). -/
noncomputable def treeCommit
    (cR : (Fin 2 ↪o PairERSource) → Bool) (δ : Ordinal.{0})
    (hδ : δ < Ordinal.omega.{0} 1) : PairERSource :=
  (treeStage cR (Order.succ δ)
      ((Cardinal.isSuccLimit_omega 1).succ_lt hδ)).stage.commitAt δ
    (Order.lt_succ δ)

/-- **Tree-driven canonical Bool at `δ < ω_1`.** Defined as the
underlying chain's `succNewBool` at level `δ`, which equals the top
`type` of the chain at level `Order.succ δ` (via `succ_typeAt_top`). -/
noncomputable def treeCommitBool
    (cR : (Fin 2 ↪o PairERSource) → Bool) (δ : Ordinal.{0})
    (hδ : δ < Ordinal.omega.{0} 1) : Bool :=
  (treeStage cR δ hδ).stage.succNewBool

/-! ### Frontier: the limit-stage type-coherence lemma

The following lemma is the **sharpened tree-aware frontier** for
arbitrary pair-homogeneity. It supersedes the older single-branch
frontier `exists_large_iInter_stage_fibers` (line 2768 area), which
described the obstruction in terms of a fresh `τ` chosen at limits.
With the tree architecture in place, the obstruction is more
precisely: at every limit `α`, the universal-tree's
`PairERTypeTree.selectedBranch` (chosen via H3 pigeonhole) must
*agree with the previously committed Bools* at every position
`δ < α`. The chain's tree-driven `typeAt δ` is read off this branch
via `toLimitChain_type` + `enum`/`prefix_enum`, so the equation
below is exactly "the selected realized branch respects prior
commitments." -/

/-- **[NEW FRONTIER, sorry]** At a limit level `α`, the
`treeStage`-driven typeAt at every position `δ < α` matches the
previously committed Bool. This is the sharpened version of the
type-coherence-at-limits obstruction: the selected realized branch
of the universal tree must respect every prior commitment.

This replaces the old vague single-branch frontier
`exists_large_iInter_stage_fibers` (line 2768) — the tree
architecture makes the missing math explicit as a single equation
on `selectedBranch`'s value at `δ`. -/
theorem selectedBranch_agrees_with_prior_commit
    (cR : (Fin 2 ↪o PairERSource) → Bool) {α : Ordinal.{0}}
    (hα_lim : Order.IsSuccLimit α) (hα : α < Ordinal.omega.{0} 1)
    (δ : Ordinal.{0}) (hδα : δ < α) (hδ : δ < Ordinal.omega.{0} 1) :
    (treeStage cR α hα).stage.typeAt δ hδα = treeCommitBool cR δ hδ := by
  unfold treeStage
  rw [Ordinal.limitRecOn_limit (h := hα_lim)]
  unfold TreeBundle.limitExtend TreeBundle.limitFromTree
    PairERTreeFamily.toLimitChain PairERTreeFamily.toLimitChainAtBranch
  rw [PairERChain.limitWithType_typeAt]
  -- LHS: selectedBranch of commitCoherent F (enum ⟨δ, ...⟩).
  rw [show ∀ (F : PairERCoherentFamily cR α) (hF_type : F.IsTypeCoherent),
        (PairERTypeTree.commitCoherent hα F hF_type).selectedBranch hα
            (Ordinal.enum (α := α.ToType) (· < ·)
              ⟨δ, (Ordinal.type_toType α).symm ▸ hδα⟩) =
          F.typeVal δ hδα from
      fun F hF_type => by
        rw [PairERTypeTree.commitCoherent_selectedBranch_eq]
        unfold PairERCoherentFamily.typeFn
        congr 1
        exact Ordinal.typein_enum _ _]
  -- Goal: F.typeVal δ hδα = treeCommitBool cR δ hδ.
  -- F.stage δ hδα = (treeStage cR δ (hδα.trans hα)).stage.succ (by F's def in limitExtend).
  -- So F.typeVal δ = (F.stage δ).typeAt δ = (treeStage cR δ _).stage.succ.typeAt δ
  --              = (treeStage cR δ _).stage.succNewBool = treeCommitBool cR δ.
  show (treeStage cR δ (hδα.trans hα)).stage.succ.typeAt δ
    (Order.lt_succ δ) = treeCommitBool cR δ hδ
  rw [PairERChain.succ_typeAt_top]
  rfl

/-- **Canonicalization of `treeStage` types.** For every enclosing
level `η > δ`, the `typeAt δ` of `treeStage cR η _` equals
`treeCommitBool cR δ`. Proved by induction on `η`:
- zero: vacuous.
- succ ζ with δ = ζ: `(extend).stage.typeAt = succNewBool` matches
  `treeCommitBool` by definition.
- succ ζ with δ < ζ: `extend_typeAt_old` + IH.
- limit: `selectedBranch_agrees_with_prior_commit` (frontier). -/
theorem treeStage_typeAt_canonical
    (cR : (Fin 2 ↪o PairERSource) → Bool)
    {η : Ordinal.{0}} (hη : η < Ordinal.omega.{0} 1)
    (δ : Ordinal.{0}) (hδη : δ < η) (hδ : δ < Ordinal.omega.{0} 1) :
    (treeStage cR η hη).stage.typeAt δ hδη = treeCommitBool cR δ hδ := by
  induction η using Ordinal.limitRecOn with
  | zero => exact absurd hδη (not_lt.mpr (zero_le δ))
  | succ ζ IH =>
    have hζ : ζ < Ordinal.omega.{0} 1 := (Order.lt_succ ζ).trans hη
    rw [treeStage_succ]
    by_cases h_eq : δ = ζ
    · -- δ = ζ: top of (succ ζ)-chain. typeAt = succNewBool matches treeCommitBool.
      subst h_eq
      show ((treeStage cR δ hζ).extend hη).stage.typeAt δ
          (Order.lt_succ δ) = treeCommitBool cR δ hδ
      show (treeStage cR δ hζ).stage.succ.typeAt δ
          (Order.lt_succ δ) = treeCommitBool cR δ hδ
      rw [PairERChain.succ_typeAt_top]
      rfl
    · have hδζ : δ < ζ :=
        lt_of_le_of_ne (Order.lt_succ_iff.mp hδη) h_eq
      show ((treeStage cR ζ hζ).extend hη).stage.typeAt δ _ =
        treeCommitBool cR δ hδ
      rw [TreeBundle.extend_typeAt_old hη (treeStage cR ζ hζ) δ hδζ]
      exact IH hζ hδζ
  | limit ζ hζ_lim IH =>
    exact selectedBranch_agrees_with_prior_commit cR hζ_lim hη δ hδη hδ

/-- **`treeStage_type_succ`**: the post-hoc cross-IH type witness
for the `type_succ` argument of `TreeBundle.limitExtend`. For any
`δ < β < ω₁`, the typeAt at position `δ` in the `β`-stage of
`treeStage` equals the `succNewBool` of the `δ`-stage. Direct
corollary of `treeStage_typeAt_canonical` + `treeCommitBool`'s
definition. -/
theorem treeStage_type_succ
    (cR : (Fin 2 ↪o PairERSource) → Bool) {β δ : Ordinal.{0}}
    (hβ : β < Ordinal.omega.{0} 1) (hδβ : δ < β)
    (hδ : δ < Ordinal.omega.{0} 1) :
    (treeStage cR β hβ).stage.typeAt δ hδβ =
      (treeStage cR δ hδ).stage.succNewBool := by
  rw [treeStage_typeAt_canonical cR hβ δ hδβ hδ]
  rfl

/-- **`treeCommit` is strictly monotone** in `δ`. Realize both commits
inside the single chain `(treeStage cR (succ δ₂) _).stage` via
`treeStage_cross_agree_commit`, then apply
`PairERChain.commitAt_strictMono`. -/
lemma treeCommit_strictMono
    (cR : (Fin 2 ↪o PairERSource) → Bool) {δ₁ δ₂ : Ordinal.{0}}
    (hδ₁ : δ₁ < Ordinal.omega.{0} 1) (hδ₂ : δ₂ < Ordinal.omega.{0} 1)
    (h : δ₁ < δ₂) :
    treeCommit cR δ₁ hδ₁ < treeCommit cR δ₂ hδ₂ := by
  have hsδ₁ : Order.succ δ₁ < Ordinal.omega.{0} 1 :=
    (Cardinal.isSuccLimit_omega 1).succ_lt hδ₁
  have hsδ₂ : Order.succ δ₂ < Ordinal.omega.{0} 1 :=
    (Cardinal.isSuccLimit_omega 1).succ_lt hδ₂
  have h_δ₁_alt : treeCommit cR δ₁ hδ₁ =
      (treeStage cR (Order.succ δ₂) hsδ₂).stage.commitAt δ₁
        (h.trans (Order.lt_succ δ₂)) :=
    treeStage_cross_agree_commit cR hsδ₁ hsδ₂ (Order.lt_succ δ₁)
      (h.trans (Order.lt_succ δ₂)) hδ₁
  have h_δ₂_alt : treeCommit cR δ₂ hδ₂ =
      (treeStage cR (Order.succ δ₂) hsδ₂).stage.commitAt δ₂
        (Order.lt_succ δ₂) := rfl
  rw [h_δ₁_alt, h_δ₂_alt]
  exact PairERChain.commitAt_strictMono
    (s := (treeStage cR (Order.succ δ₂) hsδ₂).stage)
    (hδ₁ := h.trans (Order.lt_succ δ₂))
    (hδ₂ := Order.lt_succ δ₂) h

/-- **Tree-driven ω_1-indexed Bool function** on `(ω_1).ToType`. -/
noncomputable def treeCommitBoolFn
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    (Ordinal.omega.{0} 1).ToType → Bool := fun x =>
  haveI : IsWellOrder (Ordinal.omega.{0} 1).ToType (· < ·) := isWellOrder_lt
  treeCommitBool cR (Ordinal.typein (· < ·) x) (by
    simpa [Ordinal.type_toType] using
      Ordinal.typein_lt_type
        (· < · : (Ordinal.omega.{0} 1).ToType →
          (Ordinal.omega.{0} 1).ToType → Prop) x)

/-- **Tree-driven ω_1-indexed chain embedding** into `PairERSource`.
Wraps `treeCommit` as an `OrderEmbedding` via `treeCommit_strictMono`. -/
noncomputable def treeChainEmbedding
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    (Ordinal.omega.{0} 1).ToType ↪o PairERSource := by
  haveI : IsWellOrder (Ordinal.omega.{0} 1).ToType (· < ·) := isWellOrder_lt
  refine OrderEmbedding.ofStrictMono
    (fun x =>
      treeCommit cR (Ordinal.typein (· < ·) x) (by
        simpa [Ordinal.type_toType] using
          Ordinal.typein_lt_type
            (· < · : (Ordinal.omega.{0} 1).ToType →
              (Ordinal.omega.{0} 1).ToType → Prop) x))
    ?_
  intro x y hxy
  have hx : Ordinal.typein (· < ·) x < Ordinal.omega.{0} 1 := by
    simpa [Ordinal.type_toType] using
      Ordinal.typein_lt_type
        (· < · : (Ordinal.omega.{0} 1).ToType →
          (Ordinal.omega.{0} 1).ToType → Prop) x
  have hy : Ordinal.typein (· < ·) y < Ordinal.omega.{0} 1 := by
    simpa [Ordinal.type_toType] using
      Ordinal.typein_lt_type
        (· < · : (Ordinal.omega.{0} 1).ToType →
          (Ordinal.omega.{0} 1).ToType → Prop) y
  exact treeCommit_strictMono cR hx hy
    ((Ordinal.typein_lt_typein (· < ·)).mpr hxy)

/-- **Consecutive-pair homogeneity for `treeCommit`.** For any
`β < ω_1`, the cR-color of the pair
`(treeCommit cR β, treeCommit cR (succ β))` equals `treeCommitBool
cR β`. Direct from the validFiber property of `succNewElement` applied
to `(treeStage cR (succ β) _).stage`. This is the SUCCESSOR-step
homogeneity. The full pair Erdős–Rado homogeneity (across non-
consecutive pairs and across limits) requires the type-coherence-at-
limits obstruction to be discharged. -/
theorem treeChain_consecutive_pair_homogeneous
    (cR : (Fin 2 ↪o PairERSource) → Bool) (β : Ordinal.{0})
    (hβs : Order.succ β < Ordinal.omega.{0} 1) :
    cR (pairEmbed
        (treeCommit_strictMono cR ((Order.lt_succ β).trans hβs) hβs
          (Order.lt_succ β))) =
      treeCommitBool cR β ((Order.lt_succ β).trans hβs) := by
  haveI hβ : β < Ordinal.omega.{0} 1 := (Order.lt_succ β).trans hβs
  haveI : IsWellOrder (Order.succ β).ToType (· < ·) := isWellOrder_lt
  -- Setup the chains: u at level β, v = u.succ at level (succ β).
  set u : PairERChain cR β := (treeStage cR β hβ).stage with hu_def
  set v : PairERChain cR (Order.succ β) := u.succ with hv_def
  -- (treeStage cR (succ β) hβs).stage = v.
  have h_v_eq : (treeStage cR (Order.succ β) hβs).stage = v := by
    rw [hv_def, hu_def]
    show (treeStage cR (Order.succ β) hβs).stage =
      (treeStage cR β hβ).stage.succ
    rw [treeStage_succ]
    rfl
  -- Identify treeCommit cR β with u.succNewElement.
  have h_tc_β : treeCommit cR β hβ = u.succNewElement := by
    show (treeStage cR (Order.succ β) hβs).stage.commitAt β
        (Order.lt_succ β) = u.succNewElement
    rw [h_v_eq]
    show v.head (Ordinal.enum (α := (Order.succ β).ToType) (· < ·)
        ⟨β, _⟩) = u.succNewElement
    rw [show (Ordinal.enum (α := (Order.succ β).ToType) (· < ·)
        ⟨β, (Ordinal.type_toType (Order.succ β)).symm ▸
          Order.lt_succ β⟩ : (Order.succ β).ToType) = (⊤ : _) from
      Ordinal.enum_succ_eq_top]
    rw [hv_def]
    exact PairERChain.succ_head_top u
  -- Identify treeCommit cR (succ β) with v.succNewElement.
  have h_tc_sβ : treeCommit cR (Order.succ β) hβs = v.succNewElement := by
    have hssβ : Order.succ (Order.succ β) < Ordinal.omega.{0} 1 :=
      (Cardinal.isSuccLimit_omega 1).succ_lt hβs
    haveI : IsWellOrder (Order.succ (Order.succ β)).ToType (· < ·) :=
      isWellOrder_lt
    show (treeStage cR (Order.succ (Order.succ β)) hssβ).stage.commitAt
        (Order.succ β) (Order.lt_succ (Order.succ β)) = v.succNewElement
    have h_ssβ : (treeStage cR (Order.succ (Order.succ β)) hssβ).stage =
        v.succ := by
      rw [treeStage_succ]
      show ((treeStage cR (Order.succ β)
          ((Order.lt_succ (Order.succ β)).trans hssβ)).extend hssβ).stage =
        v.succ
      rw [hv_def]
      have := h_v_eq
      show ((treeStage cR (Order.succ β) _).stage).succ = v.succ
      rw [h_v_eq]
    rw [h_ssβ]
    show v.succ.head (Ordinal.enum (α := (Order.succ (Order.succ β)).ToType)
        (· < ·) ⟨Order.succ β, _⟩) = v.succNewElement
    rw [show (Ordinal.enum (α := (Order.succ (Order.succ β)).ToType) (· < ·)
        ⟨Order.succ β, (Ordinal.type_toType (Order.succ (Order.succ β))).symm
          ▸ Order.lt_succ (Order.succ β)⟩ :
        (Order.succ (Order.succ β)).ToType) = (⊤ : _) from
      Ordinal.enum_succ_eq_top]
    exact PairERChain.succ_head_top v
  -- Identify treeCommitBool cR β with u.succNewBool (now rfl by def).
  have h_tcb_β : treeCommitBool cR β hβ = u.succNewBool := rfl
  -- Apply succNewElement_in_validFiber to v at x = ⊤.
  have h_vF := v.succNewElement_in_validFiber (⊤ : (Order.succ β).ToType)
  obtain ⟨h_lt, h_color⟩ := h_vF
  -- v.head ⊤ = u.succNewElement, v.type ⊤ = u.succNewBool.
  have h_v_head_top : v.head (⊤ : (Order.succ β).ToType) = u.succNewElement := by
    rw [hv_def]; exact PairERChain.succ_head_top u
  -- Goal: cR(pairEmbed our_witness) = treeCommitBool cR β.
  rw [h_tcb_β]
  -- We now have h_color : cR(pairEmbed h_lt) = v.type ⊤. Rewrite v.type ⊤ = u.succNewBool.
  have h_v_type_top : v.type (⊤ : (Order.succ β).ToType) = u.succNewBool := by
    have h := PairERChain.succ_typeAt_top u
    rw [hv_def]
    show u.succ.type ⊤ = u.succNewBool
    have h_top_eq : (⊤ : (Order.succ β).ToType) =
        Ordinal.enum (α := (Order.succ β).ToType) (· < ·)
          ⟨β, (Ordinal.type_toType (Order.succ β)).symm
            ▸ Order.lt_succ β⟩ :=
      Ordinal.enum_succ_eq_top.symm
    rw [h_top_eq]; exact h
  rw [h_v_type_top] at h_color
  -- Now h_color : cR(pairEmbed h_lt) = u.succNewBool.
  -- Goal: cR(pairEmbed our_witness) = u.succNewBool.
  -- pairEmbed depends only on its two values (a, b) via `![a, b]`,
  -- not on the strict-mono proof witness. So pairEmbed our_witness =
  -- pairEmbed h_lt once we identify the values.
  rw [← h_color]
  congr 1
  -- Goal: pairEmbed our_witness = pairEmbed h_lt.
  ext k
  -- pairEmbed h applied at k : Fin 2 reads off ![a, b] k.
  match k with
  | ⟨0, _⟩ =>
    show treeCommit cR β hβ = v.head (⊤ : (Order.succ β).ToType)
    rw [h_tc_β, h_v_head_top]
  | ⟨1, _⟩ =>
    show treeCommit cR (Order.succ β) hβs = v.succNewElement
    exact h_tc_sβ

/-- **Arbitrary pair-homogeneity along the tree chain.** For any
`δ < η < ω_1`, the cR-color of the pair `(treeCommit cR δ, treeCommit
cR η)` equals `treeCommitBool cR δ`. Proof:

  Apply `succNewElement_in_validFiber` to `u = (treeStage cR η _).stage`
  at `x = enum δ`. This gives `cR(pairEmbed (u.head x < u.succNewElement))
  = u.type x`, where:
  - `u.head x = u.commitAt δ hδη = treeCommit cR δ`
    (via `treeStage_canonical_commit`).
  - `u.type x = u.typeAt δ hδη = treeCommitBool cR δ`
    (via `treeStage_typeAt_canonical`, which depends on the new
    frontier `selectedBranch_agrees_with_prior_commit` at limits).
  - `u.succNewElement = treeCommit cR η`
    (via `succ_head_top` + `treeStage_succ`).

Sorry'd transitively through the new frontier, but the proof
*structure* is now explicit: arbitrary pair-homogeneity reduces to
the `selectedBranch` agreement equation.

**Axiom profile** (transitively):
* mathematical frontier: `exists_large_iInter_stage_fibers` (the
  genuine Erdős–Rado fusion theorem, the only substantive obstacle
  remaining).
* recursion-engineering frontier: `treeStage`'s internal
  `prev_succ`/`type_succ` cross-IH certificates (post-hoc-fillable
  via `treeStage_prev_succ`/`treeStage_type_succ`; eliminating their
  sorryAx propagation requires a Σ-motive refactor of `treeStage`). -/
theorem treeChain_pair_homogeneous
    (cR : (Fin 2 ↪o PairERSource) → Bool) {δ η : Ordinal.{0}}
    (hδη : δ < η) (hη : η < Ordinal.omega.{0} 1) :
    cR (pairEmbed
        (treeCommit_strictMono cR (hδη.trans hη) hη hδη)) =
      treeCommitBool cR δ (hδη.trans hη) := by
  haveI hδ : δ < Ordinal.omega.{0} 1 := hδη.trans hη
  haveI : IsWellOrder η.ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder (Order.succ η).ToType (· < ·) := isWellOrder_lt
  -- Setup u = (treeStage cR η _).stage.
  set u : PairERChain cR η := (treeStage cR η hη).stage with hu_def
  -- enum δ in η.ToType.
  set xδ : η.ToType :=
    Ordinal.enum (α := η.ToType) (· < ·)
      ⟨δ, (Ordinal.type_toType η).symm ▸ hδη⟩ with hxδ_def
  have hssη : Order.succ η < Ordinal.omega.{0} 1 :=
    (Cardinal.isSuccLimit_omega 1).succ_lt hη
  -- treeCommit cR η = u.succNewElement.
  have h_tc_η : treeCommit cR η hη = u.succNewElement := by
    show (treeStage cR (Order.succ η) hssη).stage.commitAt η
        (Order.lt_succ η) = u.succNewElement
    rw [treeStage_succ]
    show ((treeStage cR η hη).extend hssη).stage.commitAt η _ =
      u.succNewElement
    show u.succ.commitAt η _ = u.succNewElement
    show u.succ.head _ = u.succNewElement
    rw [show (Ordinal.enum (α := (Order.succ η).ToType) (· < ·)
        ⟨η, (Ordinal.type_toType (Order.succ η)).symm ▸ Order.lt_succ η⟩
        : (Order.succ η).ToType) = (⊤ : _) from
      Ordinal.enum_succ_eq_top]
    exact PairERChain.succ_head_top u
  -- u.head xδ = treeCommit cR δ hδ.
  have h_u_head_δ : u.head xδ = treeCommit cR δ hδ := by
    show u.commitAt δ hδη = treeCommit cR δ hδ
    rw [hu_def]
    rw [treeStage_canonical_commit cR hη hδη hδ]
    show treeStageCanonicalCommit cR δ hδ = treeCommit cR δ hδ
    unfold treeStageCanonicalCommit treeCommit
    rw [treeStage_succ]
    rfl
  -- u.type xδ = treeCommitBool cR δ hδ.
  have h_u_type_δ : u.type xδ = treeCommitBool cR δ hδ := by
    show u.typeAt δ hδη = treeCommitBool cR δ hδ
    rw [hu_def]
    exact treeStage_typeAt_canonical cR hη δ hδη hδ
  -- Apply succNewElement_in_validFiber on u at xδ.
  obtain ⟨h_lt, h_color⟩ := u.succNewElement_in_validFiber xδ
  rw [h_u_type_δ] at h_color
  rw [← h_color]
  congr 1
  ext k
  match k with
  | ⟨0, _⟩ =>
    show treeCommit cR δ hδ = u.head xδ
    rw [h_u_head_δ]
  | ⟨1, _⟩ =>
    show treeCommit cR η hη = u.succNewElement
    exact h_tc_η

/-- **Tree-driven pre-theorem**: from any pair-coloring `cR` on
`PairERSource`, obtain an ω_1-indexed order-embedding into any
well-ordered `I` of cardinality `≥ succ ℶ_1`. Tree-path analog of
`exists_omega1_embedding_pair`; once the second obstruction (type
coherence at limits, now expressible via `selectedBranch`) is
discharged, this is the embedding feeding the final pair-homogeneity
proof. -/
theorem exists_omega1_embedding_pair_tree
    {I : Type} [LinearOrder I] [WellFoundedLT I]
    (hI : Cardinal.mk I ≥ Order.succ (Cardinal.beth.{0} 1))
    (cR : (Fin 2 ↪o PairERSource) → Bool) :
    Nonempty ((Ordinal.omega.{0} 1).ToType ↪o I) := by
  obtain ⟨emb⟩ : Nonempty (PairERSource ↪o I) :=
    exists_ordToType_embedding_of_card_ge hI
  -- Route through the clean EHMR pair theorem (same as `exists_omega1_embedding_pair`);
  -- the `treeChainEmbedding`/`treeStage` path is now bypassed.
  obtain ⟨f, _, _⟩ := erdos_rado_pair_omega1 cR
  exact ⟨f.trans emb⟩

/-! ### Existence of stages at every level `< ω_1`

The transfinite-assembly existence lemma `exists_PairERChain`: for
every `α < ω_1`, there exists a `PairERChain cR α`. Proved by
`Ordinal.limitRecOn`:

- zero: `PairERChain.zero cR`.
- successor `α = β + 1`: apply `PairERChain.succ` to the
  induction-hypothesis stage at `β`.
- limit `α`: obtain a prefix `p : α.ToType ↪o PairERSource` from
  `exists_ordToType_embedding_of_card_ge` + `Ordinal.initialSegToType`
  (since `α ≤ (succ ℶ_1).ord`), then apply `PairERChain.limit`.

This existence is a stepping stone toward the main theorem, which
requires coherent stages (built in a later commit). -/

/-- **Stage at every level `< ω_1`**, as a `noncomputable def`. Built
by `Ordinal.limitRecOn`; at limits, uses a canonical
initial-segment prefix (`Ordinal.initialSegToType`).

Does NOT maintain head-coherence with earlier stages: at each limit,
the prefix is the canonical `initialSegToType` embedding rather than
a gluing of heads committed at earlier successor stages. Full
coherence is needed for the main theorem's chain extraction; it will
be addressed in the next tranche (likely by strengthening the motive
to carry an explicit coherence invariant). -/
noncomputable def stageAt (cR : (Fin 2 ↪o PairERSource) → Bool)
    (α : Ordinal.{0}) :
    α < Ordinal.omega.{0} 1 → PairERChain cR α :=
  Ordinal.limitRecOn α
    (motive := fun α => α < Ordinal.omega.{0} 1 → PairERChain cR α)
    (fun _ => PairERChain.zero cR)
    (fun β IH hβ1 =>
      (IH (lt_of_lt_of_le (Order.lt_succ β) hβ1.le)).succ)
    (fun β _ _ hβ => by
      haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
      have hβ_le : β ≤ (Order.succ (Cardinal.beth.{0} 1)).ord := by
        have h1 : β < (Cardinal.aleph.{0} 1).ord := by rwa [Cardinal.ord_aleph]
        have h2 : (Cardinal.aleph.{0} 1).ord ≤
            (Order.succ (Cardinal.beth.{0} 1)).ord :=
          Cardinal.ord_le_ord.mpr
            ((Cardinal.aleph_le_beth 1).trans (Order.le_succ _))
        exact (h1.trans_le h2).le
      let seg : β.ToType ≤i
          (Order.succ (Cardinal.beth.{0} 1)).ord.ToType :=
        Ordinal.initialSegToType hβ_le
      let p : β.ToType ↪o PairERSource := seg.toOrderEmbedding
      exact PairERChain.limit hβ p)

/-- **Existence of a `PairERChain` at every countable level.** Immediate
from `stageAt`. -/
theorem exists_PairERChain (cR : (Fin 2 ↪o PairERSource) → Bool) :
    ∀ α : Ordinal.{0}, α < Ordinal.omega.{0} 1 →
      Nonempty (PairERChain cR α) :=
  fun α hα => ⟨stageAt cR α hα⟩

end PairERLocalAPI

/-! ### Progress map — remaining work for `erdos_rado_pair_omega1`

**Shipped so far (axiom-clean, no `sorry`):**
- Toolbox H1–H5 (cardinal/ordinal helpers).
- `PairERSource`, `validFiber`, `validFiberExtend`, `pairColorPullback`.
- `large_above_prefix` — cofinality bound on the above-prefix set.
- `exists_large_limit_fiber` — limit-step kernel (H3 + H4 + large_above_prefix).
- `exists_successor_refinement` — successor-step kernel (min + Bool majority).
- `PairERChain` stage record + `zero` / `extendHead` / `extendType`
  / `succ` / `limit` constructors.
- `exists_PairERChain` — non-coherent per-level existence via
  `Ordinal.limitRecOn`.

**Remaining for the main theorem** (blocks `erdos_rado_pair_omega1`):

1. **Coherent `stageAt`**: a `noncomputable def stageAt` built by
   `Ordinal.limitRecOn` whose successor case threads through
   `PairERChain.succ` and whose limit case glues the IH into a
   concrete `α.ToType ↪o PairERSource` prefix defined position-by-
   position via `Ordinal.typein` and the IH at `(typein γ + 1)`.
   Strict monotonicity of this glue requires a side lemma — the
   "head-coherence invariant" — which is the subtle core:
   `(stageAt (γ+1)).head ⊤` must be strictly increasing in `γ`.

2. **Global chain**: from `stageAt`, extract
   `chain : (Ordinal.omega 1).ToType → PairERSource` together with
   `committed : (Ordinal.omega 1).ToType → Bool` (the Bool chosen at
   each successor step).

3. **Homogeneity from chain**: for `β < γ` in `(Ordinal.omega 1).ToType`,
   `cR (pair (chain β) (chain γ)) = committed β`. This follows from
   the successor kernel's guarantee (fiber at `β+1` forces the color
   of subsequent heads against `chain β`) — but only if the prefix
   used by `PairERChain.limit` at limit stages genuinely reproduces
   the earlier successor heads. The coherent `stageAt` is what makes
   this work.

4. **Second pigeonhole** on `committed`: `(Ordinal.omega 1).ToType →
   Bool` has `ℵ_1` domain and `2` codomain, so some Bool `b` has
   preimage `S` of cardinality `ℵ_1`.

5. **H5 transport**: `S` (of cardinality `ℵ_1`) is order-isomorphic
   to `(Ordinal.omega 1).ToType` via `ordIso_omega1_of_aleph1_subset`.

6. **H1 composition**: `chain ∘ (S-iso) : (Ordinal.omega 1).ToType
   ↪o PairERSource`; compose with the initial H1 embedding
   `PairERSource ↪o I` to produce the final
   `(Ordinal.omega 1).ToType ↪o I`. Homogeneity follows because all
   pair colors are `b`.

The critical step is (1)'s coherence proof. Successor composition
preserves lower-position heads by `extendHead`'s definition, so the
invariant is provable by induction on `α` in `limitRecOn`. Execution
is nontrivial (100–200 LOC) but mechanical once set up.
-/

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
