/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ScottProcess.Basic
import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Data.Set.Finite.Range
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# The semantic entries of tuples and the Scott process of a structure

For a structure `M` over a relational language `L` and an injective tuple `a : Fin n ↪ M`,
the entry `sf L α a ∈ Ψ^n_α` of the free array `FreeArray.Ψ (relAtomic L)` is the Scott formula
`φ^M_{a,α}` of Larson, *Scott processes*, Definition 1.1, with the syntax stripped: at level `0`
it is the atomic type of `a`, at level `α + 1` it is the pair `(sf α a, {sf α (a ⌢ m) | m ∉ a})`,
and at a limit level it is the thread of the lower entries.  The levels
`Φ^n_α(M) = {sf L α a | a : Fin n ↪ M}` form a Scott process in the sense of Definition 3.1
(`scottProcessOf`), the initial segment of length `δ` of the Scott process of `M` of
Definition 1.3.

## Main declarations

* `atomicType L a`: the level-`0` entry of a tuple, the truth values of the relation atoms
  `AtomicIdx.rel` of `Scott/AtomicDiagram.lean`, characterized by
  `atomicType_down_eq_true_iff`; `H0_atomicType` (restriction) and
  `atomicType_eq_atomicType_iff` (comparison with `SameAtomicType` for injective tuples).
* `IsSf α a x`: `x ∈ Ψ^n_α` is the semantic entry of `a` at level `α`, defined by recursion on
  `α`, with the unfoldings `isSf_zero`, `isSf_add_one`, `isSf_limit`, uniqueness
  `IsSf.unique`, and existence `exists_isSf` for infinite `M`.
* `sf L α a`: the semantic entry of `a` at level `α`, for infinite `M`; the unfoldings
  `zeroEquiv_sf`, `succEquiv_sf_fst`, `E_sf`, `E_sf_snoc`, `limEquiv_sf` and `mem_E_sf_iff`;
  the projection laws `V_sf` (`V_{β,α}(sf α a) = sf β a`) and `H_sf`
  (`H^n_α(sf α a, j) = sf α (a ∘ j)`); and the level-`0` comparison
  `sf_zero_eq_sf_zero_iff` with `SameAtomicType`.  The projection laws and the unfoldings
  through `zeroEquiv`, `succEquiv` and `limEquiv` are `@[simp]`; `E_sf` and `E_sf_snoc`, two
  competing forms of the extension set, are not.
* `sf_trans_equiv`: semantic entries are invariant under `L`-isomorphisms, across universes.
* `exists_common_injective_extension`: two injective tuples of arities `n` and `m` are
  restrictions of one injective tuple of arity `n + m`, extending the first along `i_n`.
* `exists_embedding_comp_eq`: every tuple `a : Fin n → M` factors as `e ∘ g` through an
  enumeration `e : Fin k ↪ M` of its distinct entries, with `a i = a j ↔ g i = g j`;
  `exists_embedding_comp_eq_of_eq_iff`: two tuples with the same equality pattern factor
  through one common surjective `g`, so the two enumerations cover exactly the two ranges.
* `scottProcessOf L M δ hδ`: the Scott process of an infinite `M`, of length `δ > 0`.
* `not_isSf_add_one_of_card`: an enumeration of a finite `M` has no entry at any successor
  level.

## Interpretation choices

* **Tuples.** Larson's finite tuples of distinct elements are injective tuples `Fin n ↪ M`.
  The relabelling `a ∘ j` along `j : Fin m ↪ Fin n` is `j.trans a`, the one-point extension
  `a ⌢ m` for `m ∉ range a` is Mathlib's `Fin.Embedding.snoc a hm`, and "`b` extends `a` by one
  point" is `(Fin.castLEEmb (Nat.le_succ n)).trans b = a`, the inclusion `i_n` of condition
  (2a) in `ScottProcess/Basic.lean`.  Tuples with repeated coordinates are reduced to injective
  ones by `exists_embedding_comp_eq`.
* **Level `0`.** `atomicType L a` stores one truth value per relation atom, as `relAtomic L`
  does, read through `AtomicIdx.holds`; equality atoms are not stored, since the variables are
  distinct (`sf_zero_eq_sf_zero_iff` recovers the full `SameAtomicType` for injective tuples).
* **The entry as the witness of a predicate.** `Ordinal.limitRecOn` cannot build `sf`
  directly: the limit step must produce a coherent thread, and the coherence of the lower
  values is a property of the recursion that the step function does not see.  So the recursion
  defines the predicate `IsSf`, which needs no coherence, and `sf L α a` is its unique witness
  (`IsSf.unique`), chosen by `Classical.choose`.  All later use goes through the unfolding
  lemmas and `eq_sf_iff`.
* **Infinite structures.** Every element of a successor row has a nonempty extension set
  (Definition 2.1(2)), and for an enumeration `a` of a finite `M` the set `{m | m ∉ range a}`
  is empty, so `a` has no entry at any successor level (`not_isSf_add_one_of_card`).  Hence
  `sf` and `scottProcessOf` carry `[Infinite M]`, as Larson's Definitions 1.1 and 1.3 assume;
  `IsSf` itself is defined for every `M`.
* **Universes.** `M : Type w` is arbitrary, and the entries live in `Ψ (relAtomic L) α n`,
  which depends on `L` but not on `M`.  So entries of tuples of different structures are
  compared by equality, and isomorphism invariance (`sf_trans_equiv`) is an equation.
* **The row index.** Rows are indexed by `Ordinal.{0}`, as in `ScottProcess/FreeArray.lean`.
  The rank invariants of `Scott/OrbitRank.lean` take values in `Ordinal.{w}` for `M : Type w`;
  the comparison of the rank of `scottProcessOf L M δ hδ` with them is to go through
  `Ordinal.lift.{w}`, together with the Theorem 1.2 form of the entries (equality of entries at
  level `α` as back-and-forth equivalence at level `α`).  Neither the comparison nor any rank
  definition is part of this file.

## References

* Paul B. Larson, *Scott processes*, in *Beyond First Order Model Theory*, vol. I
  (J. Iovino, ed.), CRC Press, 2017, ch. 2.  Numbering follows the book: Definition 1.1 (the
  Scott formula of a tuple), Theorem 1.2 (equal Scott formulas as equal theories of quantifier
  depth `α`), Definition 1.3 (the Scott process of a structure), Definition 3.1 (Scott
  processes).
-/

open Order FirstOrder FirstOrder.Language InfinitaryLogic.ScottProcess.FreeArray

universe u v w w'

noncomputable section

namespace InfinitaryLogic.ScottProcess.Semantic

variable {L : Language.{u, v}} [L.IsRelational]
variable {M : Type w} [L.Structure M] {N : Type w'} [L.Structure N]

/-! ### Tuples -/

/-- `a ⌢ m` restricts to `a` along `i_n`: Mathlib's `Fin.Embedding.init_snoc`, since
`(Fin.castLEEmb (Nat.le_succ n)).trans b` is `Fin.Embedding.init b` by definition. -/
private theorem castLEEmb_trans_snoc {n : ℕ} (a : Fin n ↪ M) {m : M} (hm : m ∉ Set.range a) :
    (Fin.castLEEmb (Nat.le_succ n)).trans (Fin.Embedding.snoc a hm) = a :=
  Fin.Embedding.init_snoc a hm

/-- The last entry of a one-point extension of `a` lies outside the range of `a`. -/
private theorem last_not_mem_range {n : ℕ} {a : Fin n ↪ M} {b : Fin (n + 1) ↪ M}
    (hb : (Fin.castLEEmb (Nat.le_succ n)).trans b = a) : b (Fin.last n) ∉ Set.range a := by
  rintro ⟨i, hi⟩
  rw [← hb] at hi
  exact Fin.castSucc_ne_last i (b.injective hi)

/-- Every one-point extension of `a` is `a ⌢ m` for its last entry `m`. -/
private theorem eq_snoc {n : ℕ} {a : Fin n ↪ M} {b : Fin (n + 1) ↪ M}
    (hb : (Fin.castLEEmb (Nat.le_succ n)).trans b = a) :
    b = Fin.Embedding.snoc a (last_not_mem_range hb) := by
  subst hb
  exact DFunLike.coe_injective (Fin.snoc_init_self (α := fun _ ↦ M) b).symm

/-- **Repeated coordinates.** Every tuple `a : Fin n → M` factors as `e ∘ g`, where
`e : Fin k ↪ M` enumerates the distinct entries of `a` and `g : Fin n → Fin k` records the
equality pattern of `a`: `a i = a j ↔ g i = g j`. -/
theorem exists_embedding_comp_eq {n : ℕ} (a : Fin n → M) :
    ∃ (k : ℕ) (e : Fin k ↪ M) (g : Fin n → Fin k),
      ⇑e ∘ g = a ∧ Set.range e = Set.range a ∧ ∀ i j, a i = a j ↔ g i = g j := by
  let σ := Finite.equivFin (Set.range a)
  let e : Fin (Nat.card (Set.range a)) ↪ M :=
    σ.symm.toEmbedding.trans (Function.Embedding.subtype _)
  have he : ⇑e ∘ (σ ∘ Set.rangeFactorization a) = a := funext fun i ↦ by
    rw [Function.comp_apply, Function.comp_apply, Function.Embedding.trans_apply,
      Equiv.coe_toEmbedding, σ.symm_apply_apply, Function.Embedding.coe_subtype,
      Set.rangeFactorization_coe]
  refine ⟨_, e, σ ∘ Set.rangeFactorization a, he, ?_, fun i j ↦ ?_⟩
  · rw [Function.Embedding.coe_trans, Set.range_comp, Equiv.coe_toEmbedding,
      σ.symm.range_eq_univ, Set.image_univ, Function.Embedding.coe_subtype,
      Subtype.range_coe]
  · rw [← congrFun he i, ← congrFun he j]
    exact e.injective.eq_iff

/-- **Repeated coordinates, two tuples.** Tuples `a : Fin n → M` and `b : Fin n → N`, possibly
of structures in different universes, with the same equality pattern
(`a i = a j ↔ b i = b j`) factor through one common `g : Fin n → Fin k`, as `a = e ∘ g` and
`b = e' ∘ g` with `e : Fin k ↪ M` and `e' : Fin k ↪ N` injective.  `g` is surjective, so `e`
and `e'` enumerate exactly `Set.range a` and `Set.range b` (no padding). -/
theorem exists_embedding_comp_eq_of_eq_iff {n : ℕ} (a : Fin n → M) (b : Fin n → N)
    (hab : ∀ i j, a i = a j ↔ b i = b j) :
    ∃ (k : ℕ) (e : Fin k ↪ M) (e' : Fin k ↪ N) (g : Fin n → Fin k),
      ⇑e ∘ g = a ∧ ⇑e' ∘ g = b ∧ Function.Surjective g := by
  obtain ⟨k, e, g, he, hr, hp⟩ := exists_embedding_comp_eq a
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨i, hi⟩ : e x ∈ Set.range a := hr ▸ Set.mem_range_self x
    exact ⟨i, e.injective (by rw [← hi, ← he, Function.comp_apply])⟩
  refine ⟨k, e, ⟨fun x ↦ b (Function.surjInv hg x), fun x y h ↦ ?_⟩, g, he, funext fun i ↦ ?_,
    hg⟩
  · rw [← Function.surjInv_eq hg x, ← Function.surjInv_eq hg y]
    exact (hp _ _).1 ((hab _ _).2 h)
  · exact (hab _ _).1 ((hp _ _).2 (Function.surjInv_eq hg (g i)))

section Infinite

variable [Infinite M]

/-- In an infinite structure some element lies outside the range of a finite tuple. -/
private theorem exists_not_mem_range {n : ℕ} (a : Fin n → M) : ∃ m, m ∉ Set.range a :=
  (Set.finite_range a).infinite_compl.nonempty

/-- Every injective tuple of an infinite structure extends to any larger arity. -/
private theorem exists_castLEEmb_trans_eq {m n : ℕ} (h : m ≤ n) (a : Fin m ↪ M) :
    ∃ θ : Fin n ↪ M, (Fin.castLEEmb h).trans θ = a := by
  induction n, h using Nat.le_induction with
  | base => exact ⟨a, Function.Embedding.ext fun _ ↦ rfl⟩
  | succ k hk ih =>
    obtain ⟨θ, hθ⟩ := ih
    obtain ⟨x, hx⟩ := exists_not_mem_range θ
    refine ⟨Fin.Embedding.snoc θ hx, Function.Embedding.ext fun i ↦ ?_⟩
    rw [← hθ]
    exact Fin.Embedding.snoc_castSucc (ha := hx) (i := Fin.castLE hk i)

/-- **One-point extension along an admissible extension.** If `c : Fin (m + 1) ↪ M` extends
`a ∘ j` along `i_m`, then some one-point extension `b` of `a` and some admissible extension
`j' ∈ extSet j` satisfy `c = b ∘ j'`.  The last entry of `c` is either an entry `a k` of `a`
outside the image of `j`, reached by a fresh extension of `a` and the extension of `j` sending
the new coordinate to `k`, or fresh for `a`, reached by `a ⌢ c_m` and `extLast j`. -/
private theorem exists_snoc_extSet {n m : ℕ} (a : Fin n ↪ M) (j : Fin m ↪ Fin n)
    (c : Fin (m + 1) ↪ M) (hc : (Fin.castLEEmb (Nat.le_succ m)).trans c = j.trans a) :
    ∃ b : Fin (n + 1) ↪ M, ∃ j' ∈ extSet j,
      (Fin.castLEEmb (Nat.le_succ n)).trans b = a ∧ j'.trans b = c := by
  have hcj : ∀ i, c i.castSucc = a (j i) := fun i ↦ congrArg (fun e : Fin m ↪ M ↦ e i) hc
  by_cases hp : ∃ k, a k = c (Fin.last m)
  · obtain ⟨k, hk⟩ := hp
    obtain ⟨y, hy⟩ := exists_not_mem_range ⇑a
    have hkj : ∀ i, (k.castSucc : Fin (n + 1)) ≠ (j i).castSucc := by
      intro i h
      rw [Fin.castSucc_inj] at h
      rw [h, ← hcj] at hk
      exact Fin.castSucc_ne_last i (c.injective hk)
    refine ⟨_, _, extTo_mem j _ hkj, castLEEmb_trans_snoc a hy,
      Function.Embedding.ext fun i ↦ ?_⟩
    induction i using Fin.lastCases with
    | last => rw [Function.Embedding.trans_apply, extTo_last, Fin.Embedding.snoc_castSucc, hk]
    | cast i =>
      rw [Function.Embedding.trans_apply, extTo_castSucc, Fin.Embedding.snoc_castSucc, hcj]
  · have hp' : c (Fin.last m) ∉ Set.range a := fun ⟨k, hk⟩ ↦ hp ⟨k, hk⟩
    refine ⟨_, _, extLast_mem j, castLEEmb_trans_snoc a hp',
      Function.Embedding.ext fun i ↦ ?_⟩
    induction i using Fin.lastCases with
    | last => rw [Function.Embedding.trans_apply, extLast_last, Fin.Embedding.snoc_last]
    | cast i =>
      rw [Function.Embedding.trans_apply, extLast_castSucc, Fin.Embedding.snoc_castSucc, hcj]

/-- **Common injective extension.** For injective `a : Fin n ↪ M` and `b : Fin m ↪ M` in an
infinite structure there are an injective `θ : Fin (n + m) ↪ M` extending `a` along `i_n` and
an injection `j : Fin m ↪ Fin (n + m)` with `b = θ ∘ j`.  The arity `n + m` does not depend on
how the ranges of `a` and `b` overlap. -/
theorem exists_common_injective_extension {n m : ℕ} (a : Fin n ↪ M) (b : Fin m ↪ M) :
    ∃ (θ : Fin (n + m) ↪ M) (j : Fin m ↪ Fin (n + m)),
      (Fin.castLEEmb (Nat.le_add_right n m)).trans θ = a ∧ j.trans θ = b := by
  induction m with
  | zero => exact ⟨a, Function.Embedding.ofIsEmpty, Function.Embedding.ext fun _ ↦ rfl,
      Function.Embedding.ext fun i ↦ i.elim0⟩
  | succ m ih =>
    obtain ⟨θ, j, hθ, hj⟩ := ih ((Fin.castLEEmb (Nat.le_succ m)).trans b)
    obtain ⟨θ', j', -, hθ', hj'⟩ := exists_snoc_extSet θ j b hj.symm
    refine ⟨θ', j', Function.Embedding.ext fun i ↦ ?_, hj'⟩
    rw [← hθ, ← hθ']
    rfl

end Infinite

/-! ### Level `0` -/

variable (L) in
open scoped Classical in
/-- The **atomic type** of a tuple (Definition 1.1(1)): the level-`0` data of `relAtomic L`
assigning to each relation atom `AtomicIdx.rel R f` its truth value at `a`. -/
def atomicType {n : ℕ} (a : Fin n → M) : (relAtomic L).Ψ0 n :=
  ⟨fun i ↦ decide (i.1.holds a)⟩

/-- The atomic type of `a` assigns `true` to exactly the relation atoms that hold at `a`. -/
@[simp] theorem atomicType_down_eq_true_iff {n : ℕ} (a : Fin n → M) (i : AtomInst L n) :
    (atomicType L a).down i = true ↔ i.1.holds a := by
  classical
  exact decide_eq_true_iff

/-- Restricting the atomic type of `a` along `j` gives the atomic type of `a ∘ j`. -/
theorem H0_atomicType {n m : ℕ} (j : Fin m ↪ Fin n) (a : Fin n → M) :
    (relAtomic L).H0 n m j (atomicType L a) = atomicType L (a ∘ j) := by
  refine ULift.ext (funext fun i ↦ Bool.eq_iff_iff.2 ?_)
  rw [relAtomic_H0_down, atomicType_down_eq_true_iff, atomicType_down_eq_true_iff,
    AtomInst.coe_map, AtomicIdx.holds_comp_eq_holds_pushforward]

/-- For injective tuples, equal atomic types is `SameAtomicType`: the equality atoms, which
`atomicType` does not store, agree automatically. -/
theorem atomicType_eq_atomicType_iff {n : ℕ} (a : Fin n ↪ M) (b : Fin n ↪ N) :
    atomicType L ⇑a = atomicType L ⇑b ↔ SameAtomicType (L := L) ⇑a ⇑b := by
  constructor
  · intro h idx
    cases idx with
    | eq i j => simp only [AtomicIdx.holds, a.injective.eq_iff, b.injective.eq_iff]
    | rel R f =>
      have := Bool.eq_iff_iff.1 (congrFun (congrArg ULift.down h) ⟨.rel R f, trivial⟩)
      rwa [atomicType_down_eq_true_iff, atomicType_down_eq_true_iff] at this
  · intro h
    refine ULift.ext (funext fun i ↦ Bool.eq_iff_iff.2 ?_)
    rw [atomicType_down_eq_true_iff, atomicType_down_eq_true_iff]
    exact h i.1

/-- An `L`-isomorphism preserves atomic types. -/
private theorem atomicType_equiv (f : M ≃[L] N) {n : ℕ} (a : Fin n → M) :
    atomicType L (f ∘ a) = atomicType L a := by
  refine ULift.ext (funext fun i ↦ Bool.eq_iff_iff.2 ?_)
  rw [atomicType_down_eq_true_iff, atomicType_down_eq_true_iff]
  obtain ⟨i, hi⟩ := i
  cases i with
  | eq => exact hi.elim
  | rel R g => exact f.map_rel R (a ∘ g)

/-! ### The predicate -/

/-- The recursion behind `IsSf`, with the arity as an argument. -/
private def IsSfAux (α : Ordinal.{0}) : ∀ n, (Fin n ↪ M) → Ψ (relAtomic L) α n → Prop :=
  Ordinal.limitRecOn (motive := fun α ↦ ∀ n, (Fin n ↪ M) → Ψ (relAtomic L) α n → Prop) α
    (fun n a x ↦ zeroEquiv (relAtomic L) n x = atomicType L ⇑a)
    (fun α C n a x ↦ C n a (V (lt_add_one α).le x) ∧
      E x = {y | ∃ b : Fin (n + 1) ↪ M, (Fin.castLEEmb (Nat.le_succ n)).trans b = a ∧
        C (n + 1) b y})
    (fun lam _ C n a x ↦ ∀ β (hβ : β < lam), C β hβ n a (V hβ.le x))

/-- `IsSf α a x`: `x ∈ Ψ^n_α` is the **semantic entry** of the injective tuple `a` at level `α`
(Larson, Scott processes, Definition 1.1, with the syntax stripped).  At level `0`, `x` is the
atomic type of `a`; at level `α + 1`, `V_{α,α+1}(x)` is the entry of `a` at level `α` and `E(x)`
is the set of level-`α` entries of the one-point extensions of `a`; at a limit level, every
vertical projection of `x` is the entry of `a` at that level. -/
def IsSf (α : Ordinal.{0}) {n : ℕ} (a : Fin n ↪ M) (x : Ψ (relAtomic L) α n) : Prop :=
  IsSfAux α n a x

/-- Unfolding `IsSf` at level `0`. -/
theorem isSf_zero {n : ℕ} (a : Fin n ↪ M) (x : Ψ (relAtomic L) 0 n) :
    IsSf 0 a x ↔ zeroEquiv (relAtomic L) n x = atomicType L ⇑a := by
  rw [IsSf, IsSfAux, Ordinal.limitRecOn_zero]

/-- Unfolding `IsSf` at a successor level. -/
theorem isSf_add_one (α : Ordinal.{0}) {n : ℕ} (a : Fin n ↪ M)
    (x : Ψ (relAtomic L) (α + 1) n) :
    IsSf (α + 1) a x ↔ IsSf α a (V (lt_add_one α).le x) ∧
      E x = {y | ∃ b : Fin (n + 1) ↪ M, (Fin.castLEEmb (Nat.le_succ n)).trans b = a ∧
        IsSf α b y} := by
  rw [IsSf, IsSfAux, Ordinal.limitRecOn_add_one]
  rfl

/-- Unfolding `IsSf` at a limit level. -/
theorem isSf_limit {lam : Ordinal.{0}} (hlam : IsSuccLimit lam) {n : ℕ} (a : Fin n ↪ M)
    (x : Ψ (relAtomic L) lam n) :
    IsSf lam a x ↔ ∀ β (hβ : β < lam), IsSf β a (V hβ.le x) := by
  rw [IsSf, IsSfAux, Ordinal.limitRecOn_limit _ _ _ _ hlam]
  rfl

/-- The semantic entry of a tuple at a level is unique. -/
theorem IsSf.unique {α : Ordinal.{0}} {n : ℕ} {a : Fin n ↪ M} {x y : Ψ (relAtomic L) α n}
    (hx : IsSf α a x) (hy : IsSf α a y) : x = y := by
  induction α using Ordinal.limitRecOn generalizing n with
  | zero =>
    rw [isSf_zero] at hx hy
    exact (zeroEquiv _ n).injective (hx.trans hy.symm)
  | add_one α ih =>
    rw [isSf_add_one] at hx hy
    exact Ψ.ext_succ (ih hx.1 hy.1) (hx.2.trans hy.2.symm)
  | limit lam hlam ih =>
    rw [isSf_limit hlam] at hx hy
    exact Ψ.ext_limit hlam fun β hβ ↦ ih β hβ (hx β hβ) (hy β hβ)

/-- Vertical projections of semantic entries are semantic entries. -/
private theorem isSf_V {α β : Ordinal.{0}} (h : β ≤ α) {n : ℕ} {a : Fin n ↪ M}
    {x : Ψ (relAtomic L) α n} (hx : IsSf α a x) : IsSf β a (V h x) := by
  induction α using Ordinal.limitRecOn generalizing β with
  | zero =>
    obtain rfl := nonpos_iff_eq_zero.1 h
    rwa [V_self]
  | add_one α ih =>
    rcases h.eq_or_lt with rfl | hlt
    · rwa [V_self]
    have hβ : β ≤ α := lt_add_one_iff.1 hlt
    rw [V_succ_of_le hβ]
    exact ih hβ ((isSf_add_one α a x).1 hx).1
  | limit lam hlam _ =>
    rcases h.eq_or_lt with rfl | hlt
    · rwa [V_self]
    exact (isSf_limit hlam a x).1 hx β hlt

/-- Every injective tuple of an infinite structure has a semantic entry at every level. -/
theorem exists_isSf [Infinite M] (α : Ordinal.{0}) {n : ℕ} (a : Fin n ↪ M) :
    ∃ x : Ψ (relAtomic L) α n, IsSf α a x := by
  induction α using Ordinal.limitRecOn generalizing n with
  | zero =>
    exact ⟨(zeroEquiv _ n).symm (atomicType L ⇑a), by rw [isSf_zero, Equiv.apply_symm_apply]⟩
  | add_one α ih =>
    obtain ⟨m, hm⟩ := exists_not_mem_range ⇑a
    obtain ⟨y, hy⟩ := ih (Fin.Embedding.snoc a hm)
    obtain ⟨x, hx⟩ := ih a
    let E' : Set (Ψ (relAtomic L) α (n + 1)) :=
      {y | ∃ b : Fin (n + 1) ↪ M, (Fin.castLEEmb (Nat.le_succ n)).trans b = a ∧ IsSf α b y}
    have hE : E'.Nonempty := ⟨y, _, castLEEmb_trans_snoc a hm, hy⟩
    refine ⟨mkSucc x E' hE, ?_⟩
    rw [isSf_add_one, V_mkSucc, E_mkSucc]
    exact ⟨hx, rfl⟩
  | limit lam hlam ih =>
    choose f hf using fun β (hβ : β < lam) ↦ ih β hβ a
    obtain ⟨x, hx⟩ := exists_limit_of_thread (A := relAtomic L) hlam f
      (fun β h ↦ (isSf_V (lt_add_one β).le (hf (β + 1) h)).unique (hf β _))
      (fun β h _ δ hδ ↦ (isSf_V hδ.le (hf β h)).unique (hf δ _))
    refine ⟨x, (isSf_limit hlam a x).2 fun β hβ ↦ ?_⟩
    rw [hx]
    exact hf β hβ

/-! ### The semantic entry -/

section Infinite

variable [Infinite M]

variable (L) in
/-- The **semantic entry** `sf L α a ∈ Ψ^n_α` of an injective tuple `a` of an infinite structure:
the Scott formula `φ^M_{a,α}` of Larson, Scott processes, Definition 1.1, with the syntax
stripped; the unique `x` with `IsSf α a x`. -/
def sf (α : Ordinal.{0}) {n : ℕ} (a : Fin n ↪ M) : Ψ (relAtomic L) α n :=
  (exists_isSf α a).choose

/-- `sf L α a` is the semantic entry of `a` at level `α`. -/
theorem isSf_sf (α : Ordinal.{0}) {n : ℕ} (a : Fin n ↪ M) : IsSf α a (sf L α a) :=
  (exists_isSf α a).choose_spec

/-- `sf L α a` is characterized by `IsSf`. -/
theorem eq_sf_iff {α : Ordinal.{0}} {n : ℕ} {a : Fin n ↪ M} {x : Ψ (relAtomic L) α n} :
    x = sf L α a ↔ IsSf α a x :=
  ⟨fun h ↦ h ▸ isSf_sf α a, fun h ↦ h.unique (isSf_sf α a)⟩

/-- Level `0`: the semantic entry is the atomic type. -/
@[simp] theorem zeroEquiv_sf {n : ℕ} (a : Fin n ↪ M) :
    zeroEquiv (relAtomic L) n (sf L 0 a) = atomicType L ⇑a :=
  (isSf_zero a _).1 (isSf_sf 0 a)

/-- **Vertical projection law**: `V_{β,α}(sf α a) = sf β a`. -/
@[simp] theorem V_sf {α β : Ordinal.{0}} (h : β ≤ α) {n : ℕ} (a : Fin n ↪ M) :
    V h (sf L α a) = sf L β a :=
  eq_sf_iff.2 (isSf_V h (isSf_sf α a))

/-- The first component of a successor-level entry is the entry one level down. -/
@[simp] theorem succEquiv_sf_fst (α : Ordinal.{0}) {n : ℕ} (a : Fin n ↪ M) :
    (succEquiv (relAtomic L) α n (sf L (α + 1) a)).1 = sf L α a := by
  rw [← V_succ_eq_fst, V_sf]

/-- The extension set of `sf L (α + 1) a` is the set of level-`α` entries of the one-point
extensions of `a` (Definition 1.1(2)). -/
theorem E_sf (α : Ordinal.{0}) {n : ℕ} (a : Fin n ↪ M) :
    E (sf L (α + 1) a) =
      sf L α '' {b : Fin (n + 1) ↪ M | (Fin.castLEEmb (Nat.le_succ n)).trans b = a} := by
  rw [((isSf_add_one α a _).1 (isSf_sf _ a)).2]
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_image, ← eq_sf_iff]
  exact exists_congr fun b ↦ and_congr_right fun _ ↦ eq_comm

/-- The extension set of `sf L (α + 1) a` is `{sf α (a ⌢ m) | m ∉ range a}`
(Definition 1.1(2)). -/
theorem E_sf_snoc (α : Ordinal.{0}) {n : ℕ} (a : Fin n ↪ M) :
    E (sf L (α + 1) a) =
      Set.range fun m : {m // m ∉ Set.range a} ↦ sf L α (Fin.Embedding.snoc a m.2) := by
  rw [E_sf]
  ext y
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨_, last_not_mem_range hb⟩, congrArg (sf L α) (eq_snoc hb).symm⟩
  · rintro ⟨⟨m, hm⟩, rfl⟩
    exact ⟨_, castLEEmb_trans_snoc a hm, rfl⟩

/-- Membership in the extension set of `sf L (α + 1) a`: exactly the level-`α` entries of the
extensions of `a` by one fresh element. -/
theorem mem_E_sf_iff {α : Ordinal.{0}} {n : ℕ} {a : Fin n ↪ M} {y : Ψ (relAtomic L) α (n + 1)} :
    y ∈ E (sf L (α + 1) a) ↔ ∃ (m : M) (hm : m ∉ Set.range a),
      sf L α (Fin.Embedding.snoc a hm) = y := by
  rw [E_sf_snoc]
  exact ⟨fun ⟨⟨m, hm⟩, h⟩ ↦ ⟨m, hm, h⟩, fun ⟨m, hm, h⟩ ↦ ⟨⟨m, hm⟩, h⟩⟩

/-- At a limit level, the entries of the thread `sf L λ a` are the lower entries. -/
@[simp] theorem limEquiv_sf {lam β : Ordinal.{0}} (hlam : IsSuccLimit lam) (hβ : β < lam) {n : ℕ}
    (a : Fin n ↪ M) :
    (limEquiv (relAtomic L) hlam n (sf L lam a)).1 β hβ = sf L β a := by
  rw [← V_limit_eq_entry hlam hβ, V_sf]

/-- Horizontal projections of semantic entries are semantic entries of the relabelled tuple. -/
private theorem isSf_H {α : Ordinal.{0}} {n m : ℕ} (j : Fin m ↪ Fin n) {a : Fin n ↪ M}
    {x : Ψ (relAtomic L) α n} (hx : IsSf α a x) : IsSf α (j.trans a) (H j x) := by
  induction α using Ordinal.limitRecOn generalizing n m with
  | zero =>
    rw [isSf_zero] at hx ⊢
    rw [H_zero_eq_restrict, hx, H0_atomicType]
    rfl
  | add_one α ih =>
    rw [isSf_add_one] at hx ⊢
    rw [V_H_comm, E_H, hx.2]
    refine ⟨ih j hx.1, ?_⟩
    ext z
    constructor
    · rintro ⟨y, ⟨b, hb, hy⟩, j', hj', rfl⟩
      refine ⟨j'.trans b, Function.Embedding.ext fun i ↦ ?_, ih j' hy⟩
      rw [Function.Embedding.trans_apply, Function.Embedding.trans_apply, Fin.castLEEmb_apply,
        Function.Embedding.trans_apply, ← hb, Function.Embedding.trans_apply]
      exact congrArg b (hj'.1 i)
    · rintro ⟨c, hc, hz⟩
      obtain ⟨b, j', hj', hb, hbc⟩ := exists_snoc_extSet a j c hc
      refine ⟨sf L α b, ⟨b, hb, isSf_sf α b⟩, j', hj', ?_⟩
      have := ih j' (isSf_sf (L := L) α b)
      rw [hbc] at this
      exact this.unique hz
  | limit lam hlam ih =>
    rw [isSf_limit hlam] at hx ⊢
    intro β hβ
    rw [V_H_comm]
    exact ih β hβ j (hx β hβ)

/-- **Horizontal projection law**: `H^n_α(sf α a, j) = sf α (a ∘ j)`. -/
@[simp] theorem H_sf (α : Ordinal.{0}) {n m : ℕ} (j : Fin m ↪ Fin n) (a : Fin n ↪ M) :
    H j (sf L α a) = sf L α (j.trans a) :=
  eq_sf_iff.2 (isSf_H j (isSf_sf α a))

/-- Reassociation of a composite relabelling under `sf`, by `rfl`.  It is the join of the critical
pair `H_sf`/`H_comp`: `simp` rewrites `H k (H j (sf α a))` to the right-nested
`sf α (k.trans (j.trans a))` and `H (k.trans j) (sf α a)` to the left-nested form, and
Mathlib's `Function.Embedding.trans_assoc` is not a simp lemma. -/
@[simp] theorem sf_trans_trans (α : Ordinal.{0}) {n m l : ℕ} (k : Fin l ↪ Fin m)
    (j : Fin m ↪ Fin n) (a : Fin n ↪ M) :
    sf L α ((k.trans j).trans a) = sf L α (k.trans (j.trans a)) := rfl

/-- Level `0`: two injective tuples, possibly of different structures, have the same entry at
level `0` iff they have the same atomic type. -/
theorem sf_zero_eq_sf_zero_iff [Infinite N] {n : ℕ} (a : Fin n ↪ M) (b : Fin n ↪ N) :
    sf L 0 a = sf L 0 b ↔ SameAtomicType (L := L) ⇑a ⇑b := by
  rw [← atomicType_eq_atomicType_iff, ← (zeroEquiv (relAtomic L) n).apply_eq_iff_eq,
    zeroEquiv_sf, zeroEquiv_sf]

/-- **Isomorphism invariance**: for an `L`-isomorphism `f : M ≃[L] N`, possibly between
structures in different universes, `sf α (f ∘ a) = sf α a`.  Both sides live in
`Ψ (relAtomic L) α n`, which does not depend on the structure. -/
theorem sf_trans_equiv [Infinite N] (f : M ≃[L] N) (α : Ordinal.{0}) {n : ℕ} (a : Fin n ↪ M) :
    sf L α (a.trans f.toEquiv.toEmbedding) = sf L α a := by
  induction α using Ordinal.limitRecOn generalizing n with
  | zero =>
    apply (zeroEquiv (relAtomic L) n).injective
    rw [zeroEquiv_sf, zeroEquiv_sf]
    exact atomicType_equiv f a
  | add_one α ih =>
    refine Ψ.ext_succ (by rw [V_sf, V_sf, ih]) ?_
    rw [E_sf, E_sf]
    ext y
    constructor
    · rintro ⟨b', hb', rfl⟩
      refine ⟨b'.trans f.toEquiv.symm.toEmbedding, Function.Embedding.ext fun i ↦ ?_, ?_⟩
      · rw [← Function.Embedding.trans_assoc, Function.Embedding.trans_apply, hb',
          Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Equiv.coe_toEmbedding,
          f.toEquiv.symm_apply_apply]
      · rw [← ih]
        congr 1
        exact Function.Embedding.ext fun i ↦ f.toEquiv.apply_symm_apply (b' i)
    · rintro ⟨b, hb, rfl⟩
      refine ⟨b.trans f.toEquiv.toEmbedding, ?_, ih b⟩
      rw [Set.mem_ofPred_eq, ← Function.Embedding.trans_assoc, hb]
  | limit lam hlam ih =>
    exact Ψ.ext_limit hlam fun β hβ ↦ by rw [V_sf, V_sf, ih β hβ]

end Infinite

/-! ### Finite structures -/

/-- **Finite structures.** An enumeration `a : Fin n ↪ M` of a finite structure `M` of
cardinality `n` has no semantic entry at any successor level: every successor-row element has
a nonempty extension set, while `a` has no one-point extension.  This is why `sf` and
`scottProcessOf` assume `[Infinite M]`. -/
theorem not_isSf_add_one_of_card [Finite M] {n : ℕ} (hn : Nat.card M = n) (a : Fin n ↪ M)
    (α : Ordinal.{0}) (x : Ψ (relAtomic L) (α + 1) n) : ¬ IsSf (α + 1) a x := by
  intro hx
  obtain ⟨y, hy⟩ := E_nonempty x
  rw [((isSf_add_one α a x).1 hx).2] at hy
  obtain ⟨b, -, -⟩ := hy
  have := Finite.card_le_of_embedding b
  rw [Nat.card_eq_fintype_card, Fintype.card_fin, hn] at this
  omega

/-! ### The Scott process of a structure -/

variable (L M) in
/-- **The Scott process of `M`** of length `δ > 0` (Larson, Scott processes, Definition 1.3):
`Φ^n_α = {sf L α a | a : Fin n ↪ M}` for `α < δ`.  It satisfies Definition 3.1 by the
projection laws `V_sf` and `H_sf`, the description `E_sf` of the extension sets, and
`exists_common_injective_extension` for amalgamation. -/
def scottProcessOf [Infinite M] (δ : Ordinal.{0}) (hδ : 0 < δ) :
    ScottProcess (relAtomic L) δ where
  Φ α _ n := Set.range fun a : Fin n ↪ M ↦ sf L α a
  pos := hδ
  nonempty α _ := ⟨0, _, Function.Embedding.ofIsEmpty, rfl⟩
  E_subset α _ n := by
    rintro _ ⟨a, rfl⟩ y hy
    rw [E_sf] at hy
    obtain ⟨b, -, rfl⟩ := hy
    exact ⟨b, rfl⟩
  eq_image_V α β hαβ _ n := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun a ↦ (V_sf hαβ.le a).symm)
  H_mem α _ n j := by
    rintro _ ⟨a, rfl⟩
    exact ⟨j.trans a, (H_sf α j a).symm⟩
  eq_image_H α _ m n hmn := by
    ext φ
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨θ, hθ⟩ := exists_castLEEmb_trans_eq hmn.le a
      exact ⟨sf L α θ, ⟨θ, rfl⟩, by rw [H_sf, hθ]⟩
    · rintro ⟨_, ⟨θ, rfl⟩, rfl⟩
      exact ⟨_, (H_sf α _ θ).symm⟩
  E_eq α _ n := by
    rintro _ ⟨a, rfl⟩
    ext y
    constructor
    · rw [E_sf]
      rintro ⟨b, hb, rfl⟩
      exact ⟨sf L (α + 1) b, ⟨⟨b, rfl⟩, by rw [H_sf, hb]⟩, V_sf _ b⟩
    · rintro ⟨_, ⟨⟨b, rfl⟩, hb⟩, rfl⟩
      rw [H_sf] at hb
      rw [V_sf, ← hb, E_sf]
      exact ⟨b, rfl, rfl⟩
  E_V_subset α β hαβ _ n := by
    rintro _ ⟨a, rfl⟩
    rw [V_sf, E_sf]
    rintro _ ⟨b, hb, rfl⟩
    exact ⟨sf L β b, ⟨⟨b, rfl⟩, by rw [H_sf, hb]⟩, V_sf _ b⟩
  amalgamate α _ n m := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    obtain ⟨θ, j, hθ, hj⟩ := exists_common_injective_extension a b
    exact ⟨sf L α θ, ⟨θ, rfl⟩, j, by rw [H_sf, hθ], by rw [H_sf, hj]⟩

/-- The levels of the Scott process of `M` are the sets of semantic entries of its injective
tuples. -/
@[simp] theorem scottProcessOf_Φ [Infinite M] {δ : Ordinal.{0}} (hδ : 0 < δ) {α : Ordinal.{0}}
    (hα : α < δ) (n : ℕ) :
    (scottProcessOf L M δ hδ).Φ α hα n = Set.range fun a : Fin n ↪ M ↦ sf L α a :=
  rfl

end InfinitaryLogic.ScottProcess.Semantic

end
