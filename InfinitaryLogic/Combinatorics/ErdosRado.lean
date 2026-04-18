/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Order.InitialSeg

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

/-! ### Architecture of the main Erdős–Rado theorem (Phase 2d2)

The remaining unproved theorem:

```lean
theorem erdos_rado_omega1_of_countable_bool_family
    {I : Type} [LinearOrder I]
    (hI : Cardinal.mk I ≥ Cardinal.beth (Ordinal.omega 1))
    (c : ℕ → Σ n, (Fin n ↪o I) → Bool) :
    ∃ e : (Ordinal.omega 1).ToType ↪o I,
      HomogeneousSuborder c e
```

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
