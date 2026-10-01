/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.KleeneBrouwer
import InfinitaryLogic.Descriptive.BFEquivBorel
import InfinitaryLogic.Descriptive.StructureIsoSetoid
import Mathlib.Basic.Finite.Sum

/-!
# The forced back-and-forth tree of a pair of coded structures

For two codes `c d : StructureSpace L` of relational structures on `ℕ`, `bfTree c d` is the
tree of finite partial isomorphisms built by a **forced** schedule: step `2 i` puts element `i`
of the left structure into the domain, step `2 i + 1` puts element `i` of the right structure
into the range, and a node is a list of the opposite-side answers.  A node is in the tree iff
the two finite tuples it decodes have the same atomic type.

## Main declarations

* `CodeBFEquiv α c d`: the empty tuples of the decoded structures are `α`-back-and-forth
  equivalent.
* `bfLeft s`, `bfRight s`: the left and right tuples decoded from a node `s : List ℕ`; position
  `2 i` is `i` on the left and `s[2 i]` on the right, position `2 i + 1` is `s[2 i + 1]` on the
  left and `i` on the right.
* `bfNodes c d`, `bfTree c d`: the nodes whose decoded tuples have the same atomic type, and the
  tree they form (`bfNodes_prefix` is the prefix closure, `mem_bfTree_iff` the membership
  condition).
* `isClosed_setOf_mem_bfTree`: each node condition is closed in the product topology on
  `StructureSpace L × StructureSpace L`, for every relational `L`;
  `isClopen_setOf_mem_bfTree` when `L` has finitely many relation symbols;
  `measurableSet_setOf_mem_bfTree` and `measurable_bfTree` when it has countably many.
* `hasInfiniteBranch_bfTree_iff`: the tree has an infinite branch iff the two coded structures
  are isomorphic.
* `nil_mem_bfTree_iff`, `bfTree_eq_bot_iff`: the root is a node iff the empty tuples agree on
  every atom (the nullary relation symbols), and otherwise the tree is empty.
* `le_rank_bfTree_of_bfEquiv`, `lt_treeHeight_bfTree_of_codeBFEquiv`: back-and-forth
  equivalence bounds the rank of a node, and that of the empty tuples the height of the tree.

## Interpretation choices

* **Closed, not necessarily clopen.**  A node condition demands full agreement of all equality
  and relation atoms on the decoded tuples.  With infinitely many relation symbols this tests
  infinitely many atoms, so the node set is an intersection of infinitely many clopen sets: it
  is closed, not necessarily clopen, and the assignment `p ↦ bfTree p.1 p.2` need not be
  continuous.  It is clopen when there are finitely many relation symbols, and measurable (for
  the product σ-algebra on `Set (List ℕ)`) when there are countably many.
* **Rank convention.**  Ranks are `WellFounded.rank (extBelow (bfTree c d))`, where `extBelow`
  is strict extension: a node sits above its proper extensions.  One tree step is one forth or
  one back move, and there is **no ordinal offset at nodes**: `BFEquiv α` at the tuples of a
  node gives rank at least `α` (`le_rank_bfTree_of_bfEquiv`).  The height
  `treeHeight T = ⨆ x, succ (rank x)` is a strict supremum, which is the only offset: a tree
  consisting of the root alone has root rank `0` and height `1`, and `CodeBFEquiv α c d` gives
  `α < treeHeight (bfTree c d)` (`lt_treeHeight_bfTree_of_codeBFEquiv`).
* **The empty tree.**  Root membership is not assumed: it is obtained from atomic agreement of
  the empty tuples.  If a nullary relation symbol holds in one structure and fails in the
  other, the tree is empty (height `0`), and `CodeBFEquiv α c d` fails at every `α`, since it
  already fails at level `0` (`bfTree_eq_bot_iff`).
* **Universes.**  `L : Language.{u, v}` is arbitrary and only `[L.IsRelational]` is assumed;
  countability of the relation symbols enters only the measurability statements.  The carrier is
  `ℕ`, so ranks and back-and-forth levels are both `Ordinal.{0}` and no lift appears.

## References

* Trees on `ℕ`, their infinite branches, the ranks of well-founded trees and the
  Kleene–Brouwer order are standard in descriptive set theory; see A. S. Kechris, *Classical
  Descriptive Set Theory*, Graduate Texts in Mathematics 156, Springer, 1995.  The forced
  schedule is the usual back-and-forth enumeration of an isomorphism between countable
  structures, recorded here as a tree of finite partial isomorphisms.
-/

universe u v

namespace FirstOrder.Language

open Descriptive KleeneBrouwer Structure MeasureTheory

variable {L : Language.{u, v}} [L.IsRelational]

/-! ### The empty tuples and the node tuples -/

/-- `CodeBFEquiv α c d`: the empty tuples of the structures coded by `c` and `d` are
`α`-back-and-forth equivalent. -/
def CodeBFEquiv (α : Ordinal.{0}) (c d : StructureSpace L) : Prop :=
  @BFEquiv L ℕ c.toStructure ℕ d.toStructure α 0 Fin.elim0 Fin.elim0

/-- The left tuple of a node: position `2 i` holds `i` (element `i` of the left structure enters
the domain), position `2 i + 1` holds the node's entry (the left answer to element `i` of the
right structure). -/
def bfLeft (s : List ℕ) : Fin s.length → ℕ :=
  fun j ↦ if j.val % 2 = 0 then j.val / 2 else s[j.val]

/-- The right tuple of a node: position `2 i` holds the node's entry (the right answer to
element `i` of the left structure), position `2 i + 1` holds `i` (element `i` of the right
structure enters the range). -/
def bfRight (s : List ℕ) : Fin s.length → ℕ :=
  fun j ↦ if j.val % 2 = 0 then s[j.val] else j.val / 2

/-- Position `2 i` of the left tuple is `i`. -/
@[simp]
theorem bfLeft_two_mul (s : List ℕ) (i : ℕ) (h : 2 * i < s.length) :
    bfLeft s ⟨2 * i, h⟩ = i := by
  simp [bfLeft]

/-- Position `2 i + 1` of the left tuple is the node's entry there. -/
@[simp]
theorem bfLeft_two_mul_add_one (s : List ℕ) (i : ℕ) (h : 2 * i + 1 < s.length) :
    bfLeft s ⟨2 * i + 1, h⟩ = s[2 * i + 1] := by
  simp [bfLeft, Nat.add_mod]

/-- Position `2 i` of the right tuple is the node's entry there. -/
@[simp]
theorem bfRight_two_mul (s : List ℕ) (i : ℕ) (h : 2 * i < s.length) :
    bfRight s ⟨2 * i, h⟩ = s[2 * i] := by
  simp [bfRight]

/-- Position `2 i + 1` of the right tuple is `i`. -/
@[simp]
theorem bfRight_two_mul_add_one (s : List ℕ) (i : ℕ) (h : 2 * i + 1 < s.length) :
    bfRight s ⟨2 * i + 1, h⟩ = i := by
  simp [bfRight, Nat.add_mod]
  omega

/-- On a prefix, the decoded tuples are restrictions. -/
private theorem bfLeft_comp_castLE {s t : List ℕ} (hst : s <+: t) :
    bfLeft t ∘ Fin.castLE hst.length_le = bfLeft s := by
  funext j
  simp only [Function.comp_apply, bfLeft, Fin.val_castLE]
  split_ifs
  · rfl
  · exact (hst.getElem j.2).symm

private theorem bfRight_comp_castLE {s t : List ℕ} (hst : s <+: t) :
    bfRight t ∘ Fin.castLE hst.length_le = bfRight s := by
  funext j
  simp only [Function.comp_apply, bfRight, Fin.val_castLE]
  split_ifs
  · exact (hst.getElem j.2).symm
  · rfl

/-- The decoded tuples of a one-step extension: the left tuple gains the left move of position
`s.length`. -/
private theorem bfLeft_append_singleton (s : List ℕ) (x : ℕ) :
    bfLeft (s ++ [x]) = Fin.snoc (bfLeft s)
      (if s.length % 2 = 0 then s.length / 2 else x) ∘ Fin.cast (by simp) := by
  funext j
  obtain ⟨j, hj⟩ := j
  have hj' : j < s.length + 1 := by simpa using hj
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hlt | rfl
  · have : (Fin.cast (by simp) ⟨j, hj⟩ : Fin (s.length + 1)) = Fin.castSucc ⟨j, hlt⟩ := rfl
    simp only [Function.comp_apply, this, Fin.snoc_castSucc, bfLeft]
    rw [List.getElem_append_left hlt]
  · have : (Fin.cast (by simp) ⟨s.length, hj⟩ : Fin (s.length + 1)) = Fin.last _ := rfl
    simp only [Function.comp_apply, this, Fin.snoc_last, bfLeft]
    split_ifs <;> simp

private theorem bfRight_append_singleton (s : List ℕ) (x : ℕ) :
    bfRight (s ++ [x]) = Fin.snoc (bfRight s)
      (if s.length % 2 = 0 then x else s.length / 2) ∘ Fin.cast (by simp) := by
  funext j
  obtain ⟨j, hj⟩ := j
  have hj' : j < s.length + 1 := by simpa using hj
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hlt | rfl
  · have : (Fin.cast (by simp) ⟨j, hj⟩ : Fin (s.length + 1)) = Fin.castSucc ⟨j, hlt⟩ := rfl
    simp only [Function.comp_apply, this, Fin.snoc_castSucc, bfRight]
    rw [List.getElem_append_left hlt]
  · have : (Fin.cast (by simp) ⟨s.length, hj⟩ : Fin (s.length + 1)) = Fin.last _ := rfl
    simp only [Function.comp_apply, this, Fin.snoc_last, bfRight]
    split_ifs <;> simp

/-! ### The tree -/

/-- The nodes of the forced back-and-forth tree: the lists whose decoded left and right tuples
have the same atomic type (all equality and relation atoms agree). -/
def bfNodes (c d : StructureSpace L) : Set (List ℕ) :=
  {s | @SameAtomicType L ℕ c.toStructure s.length ℕ d.toStructure (bfLeft s) (bfRight s)}

/-- The node set is closed under one-step prefixes: restricting a partial isomorphism keeps the
atomic type (`SameAtomicType.relabel`). -/
theorem bfNodes_prefix (c d : StructureSpace L) ⦃s : List ℕ⦄ ⦃a : ℕ⦄
    (h : s ++ [a] ∈ bfNodes c d) : s ∈ bfNodes c d := by
  have hst : s <+: s ++ [a] := List.prefix_append s [a]
  have := @SameAtomicType.relabel L ℕ c.toStructure ℕ d.toStructure _ _ _ _ h
    (Fin.castLE hst.length_le)
  rwa [bfLeft_comp_castLE hst, bfRight_comp_castLE hst] at this

/-- **The forced back-and-forth tree** of a pair of codes. -/
def bfTree (c d : StructureSpace L) : tree ℕ :=
  ⟨bfNodes c d, fun _ _ h ↦ bfNodes_prefix c d h⟩

/-- Membership in the tree is atomic agreement of the decoded tuples. -/
theorem mem_bfTree_iff {c d : StructureSpace L} {s : List ℕ} :
    s ∈ bfTree c d ↔
      @SameAtomicType L ℕ c.toStructure s.length ℕ d.toStructure (bfLeft s) (bfRight s) :=
  Iff.rfl

private theorem mem_bfTree_of_bfEquiv {c d : StructureSpace L} {α : Ordinal.{0}}
    {s : List ℕ}
    (h : @BFEquiv L ℕ c.toStructure ℕ d.toStructure α s.length (bfLeft s) (bfRight s)) :
    s ∈ bfTree c d :=
  (@BFEquiv.zero L ℕ c.toStructure ℕ d.toStructure _ _ _).mp
    (@BFEquiv.monotone L ℕ c.toStructure ℕ d.toStructure _ _ _ zero_le _ _ h)

private theorem bfLeft_nil : bfLeft [] = Fin.elim0 := funext fun j ↦ absurd j.2 (by simp)

private theorem bfRight_nil : bfRight [] = Fin.elim0 := funext fun j ↦ absurd j.2 (by simp)

/-- `CodeBFEquiv` is back-and-forth equivalence at the root node. -/
private theorem codeBFEquiv_iff_root {α : Ordinal.{0}} {c d : StructureSpace L} :
    CodeBFEquiv α c d ↔ @BFEquiv L ℕ c.toStructure ℕ d.toStructure α ([] : List ℕ).length
      (bfLeft []) (bfRight []) := by
  rw [bfLeft_nil, bfRight_nil]
  rfl

/-- **The root is a node iff the empty tuples agree atomically**, i.e. iff every nullary
relation symbol has the same truth value in both structures. -/
theorem nil_mem_bfTree_iff {c d : StructureSpace L} :
    [] ∈ bfTree c d ↔ CodeBFEquiv 0 c d := by
  rw [codeBFEquiv_iff_root, @BFEquiv.zero L ℕ c.toStructure ℕ d.toStructure]
  rfl

/-- **The empty tree**: `bfTree c d` is the empty tree `⊥` iff the empty tuples already
disagree at level `0`. -/
theorem bfTree_eq_bot_iff {c d : StructureSpace L} :
    bfTree c d = ⊥ ↔ ¬ CodeBFEquiv 0 c d := by
  rw [Tree.tree_eq_bot, nil_mem_bfTree_iff]

/-! ### Closedness and measurability of the node conditions -/

/-- One atomic condition at fixed tuples is clopen on the pair space. -/
private theorem isClopen_setOf_holds_iff {n : ℕ} (a b : Fin n → ℕ) (idx : L.AtomicIdx n) :
    IsClopen {p : StructureSpace L × StructureSpace L |
      @AtomicIdx.holds L ℕ p.1.toStructure n idx a ↔
        @AtomicIdx.holds L ℕ p.2.toStructure n idx b} := by
  cases idx with
  | eq i j =>
    by_cases h : (a i = a j ↔ b i = b j) <;>
      simp [AtomicIdx.holds, h, isClopen_empty, isClopen_univ]
  | rel R f =>
    let g : StructureSpace L × StructureSpace L → Bool × Bool :=
      fun p ↦ (p.1 ⟨⟨_, R⟩, a ∘ f⟩, p.2 ⟨⟨_, R⟩, b ∘ f⟩)
    have hg : Continuous g :=
      ((continuous_apply _).comp continuous_fst).prodMk
        ((continuous_apply _).comp continuous_snd)
    exact (isClopen_discrete {x : Bool × Bool | x.1 = true ↔ x.2 = true}).preimage hg

/-- The node condition is the intersection, over all atoms, of the atomic conditions. -/
private theorem setOf_mem_bfTree_eq_iInter (s : List ℕ) :
    {p : StructureSpace L × StructureSpace L | s ∈ bfTree p.1 p.2} =
      ⋂ idx : L.AtomicIdx s.length, {p | @AtomicIdx.holds L ℕ p.1.toStructure _ idx (bfLeft s) ↔
        @AtomicIdx.holds L ℕ p.2.toStructure _ idx (bfRight s)} := by
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  rfl

/-- **Node conditions are closed**, for every relational `L`: the set of code pairs whose tree
contains `s` is an intersection of clopen atomic conditions.  It need not be clopen, and the
assignment `p ↦ bfTree p.1 p.2` need not be continuous, when there are infinitely many relation
symbols (compare `isClopen_setOf_mem_bfTree`). -/
theorem isClosed_setOf_mem_bfTree (s : List ℕ) :
    IsClosed {p : StructureSpace L × StructureSpace L | s ∈ bfTree p.1 p.2} := by
  rw [setOf_mem_bfTree_eq_iInter]
  exact isClosed_iInter fun idx ↦ (isClopen_setOf_holds_iff _ _ idx).isClosed

omit [L.IsRelational] in
/-- Finitely many relation symbols give finitely many atoms over a fixed tuple length. -/
private theorem finite_atomicIdx [Finite (Σ l, L.Relations l)] (n : ℕ) :
    Finite (L.AtomicIdx n) :=
  Finite.of_equiv (Fin n × Fin n ⊕ Σ R : (Σ l, L.Relations l), (Fin R.1 → Fin n))
    { toFun := fun | .inl ⟨i, j⟩ => .eq i j | .inr ⟨⟨_, R⟩, f⟩ => .rel R f
      invFun := fun | .eq i j => .inl ⟨i, j⟩ | .rel R f => .inr ⟨⟨_, R⟩, f⟩
      left_inv := fun | .inl ⟨_, _⟩ => rfl | .inr ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun | .eq _ _ => rfl | .rel _ _ => rfl }

/-- **Node conditions are clopen when there are finitely many relation symbols**: then a node
condition tests finitely many atoms. -/
theorem isClopen_setOf_mem_bfTree [Finite (Σ l, L.Relations l)] (s : List ℕ) :
    IsClopen {p : StructureSpace L × StructureSpace L | s ∈ bfTree p.1 p.2} := by
  have := finite_atomicIdx (L := L) s.length
  rw [setOf_mem_bfTree_eq_iInter]
  exact isClopen_iInter_of_finite fun idx ↦ isClopen_setOf_holds_iff _ _ idx

/-- **Node conditions are measurable** when there are countably many relation symbols: a node
condition is `BFEquiv 0` at the decoded tuples (`bfEquivSet_measurableSet`). -/
theorem measurableSet_setOf_mem_bfTree [Countable (Σ l, L.Relations l)] (s : List ℕ) :
    MeasurableSet {p : StructurePairSpace L | s ∈ bfTree p.1 p.2} := by
  have h := bfEquivSet_measurableSet (L := L) 0 (by simp [Ordinal.omega_pos])
    s.length (bfLeft s) (bfRight s)
  convert h using 1
  ext p
  exact (@BFEquiv.zero L ℕ p.1.toStructure ℕ p.2.toStructure _ _ _).symm

/-- **The tree assignment is measurable** when there are countably many relation symbols, for
the product σ-algebra on `Set (List ℕ)` (`Set.instMeasurableSpace`). -/
theorem measurable_bfTree [Countable (Σ l, L.Relations l)] :
    Measurable fun p : StructurePairSpace L ↦ (bfTree p.1 p.2 : Set (List ℕ)) :=
  measurable_set_iff.2 fun s ↦ measurableSet_setOfPred.1 (measurableSet_setOf_mem_bfTree s)

/-! ### Infinite branches are isomorphisms -/

/-- The left sequence along a branch `z`: even positions enumerate the left structure. -/
private def seqLeft (z : ℕ → ℕ) (j : ℕ) : ℕ := if j % 2 = 0 then j / 2 else z j

/-- The right sequence along a branch `z`: odd positions enumerate the right structure. -/
private def seqRight (z : ℕ → ℕ) (j : ℕ) : ℕ := if j % 2 = 0 then z j else j / 2

private theorem seqLeft_two_mul (z : ℕ → ℕ) (i : ℕ) : seqLeft z (2 * i) = i := by
  simp [seqLeft]

private theorem seqLeft_two_mul_add_one (z : ℕ → ℕ) (i : ℕ) :
    seqLeft z (2 * i + 1) = z (2 * i + 1) := by
  simp [seqLeft, Nat.add_mod]

private theorem seqRight_two_mul (z : ℕ → ℕ) (i : ℕ) : seqRight z (2 * i) = z (2 * i) := by
  simp [seqRight]

private theorem seqRight_two_mul_add_one (z : ℕ → ℕ) (i : ℕ) :
    seqRight z (2 * i + 1) = i := by
  simp [seqRight, Nat.add_mod]
  omega

private theorem bfLeft_ofFn (z : ℕ → ℕ) (n : ℕ)
    (j : Fin (List.ofFn fun i : Fin n ↦ z i).length) :
    bfLeft (List.ofFn fun i : Fin n ↦ z i) j = seqLeft z j := by
  simp [bfLeft, seqLeft]

private theorem bfRight_ofFn (z : ℕ → ℕ) (n : ℕ)
    (j : Fin (List.ofFn fun i : Fin n ↦ z i).length) :
    bfRight (List.ofFn fun i : Fin n ↦ z i) j = seqRight z j := by
  simp [bfRight, seqRight]

/-- Along a branch, every atom at every finite set of positions agrees: relabel a node long
enough to contain the positions. -/
private theorem holds_seq_of_branch {c d : StructureSpace L} {z : ℕ → ℕ}
    (hz : ∀ n, List.ofFn (fun i : Fin n ↦ z i) ∈ bfTree c d) {l : ℕ} (g : Fin l → ℕ)
    (idx : L.AtomicIdx l) :
    @AtomicIdx.holds L ℕ c.toStructure l idx (seqLeft z ∘ g) ↔
      @AtomicIdx.holds L ℕ d.toStructure l idx (seqRight z ∘ g) := by
  obtain ⟨N, hN⟩ : ∃ N, ∀ k, g k < N :=
    ⟨Finset.univ.sup g + 1, fun k ↦ Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ k))⟩
  have ht : ∀ k, g k < (List.ofFn fun i : Fin N ↦ z i).length := by simpa using hN
  let σ : Fin l → Fin (List.ofFn fun i : Fin N ↦ z i).length := fun k ↦ ⟨g k, ht k⟩
  have h := @SameAtomicType.relabel L ℕ c.toStructure ℕ d.toStructure _ _ _ _ (hz N) σ idx
  have hl : bfLeft (List.ofFn fun i : Fin N ↦ z i) ∘ σ = seqLeft z ∘ g :=
    funext fun k ↦ bfLeft_ofFn z N (σ k)
  have hr : bfRight (List.ofFn fun i : Fin N ↦ z i) ∘ σ = seqRight z ∘ g :=
    funext fun k ↦ bfRight_ofFn z N (σ k)
  rwa [hl, hr] at h

/-- **A branch gives an isomorphism**: `m ↦ z (2 m)`.  Equality atoms give injectivity, and
surjectivity by comparing position `2 n + 1` (where the right structure offers `n`) with
position `2 z(2 n + 1)`; relation atoms at long enough nodes give preservation. -/
private theorem nonempty_equiv_of_branch {c d : StructureSpace L} {z : ℕ → ℕ}
    (hz : ∀ n, List.ofFn (fun i : Fin n ↦ z i) ∈ bfTree c d) :
    Nonempty (@Language.Equiv L ℕ ℕ c.toStructure d.toStructure) := by
  have heq : ∀ i j, seqLeft z i = seqLeft z j ↔ seqRight z i = seqRight z j :=
    fun i j ↦ holds_seq_of_branch hz ![i, j] (.eq 0 1)
  let e : ℕ → ℕ := fun m ↦ z (2 * m)
  have hinj : Function.Injective e := by
    intro m m' hm
    have := (heq (2 * m) (2 * m')).mpr (by simpa [seqRight_two_mul] using hm)
    simpa [seqLeft_two_mul] using this
  have hsurj : Function.Surjective e := by
    intro n
    refine ⟨z (2 * n + 1), ?_⟩
    have := (heq (2 * z (2 * n + 1)) (2 * n + 1)).mp
      (by rw [seqLeft_two_mul, seqLeft_two_mul_add_one])
    rwa [seqRight_two_mul, seqRight_two_mul_add_one] at this
  refine ⟨@Language.Equiv.mk L ℕ ℕ c.toStructure d.toStructure (Equiv.ofBijective e ⟨hinj, hsurj⟩)
    (fun f ↦ isEmptyElim f) (fun {l} R v ↦ ?_)⟩
  have h := holds_seq_of_branch hz (fun k ↦ 2 * v k) (.rel R id)
  have hl : seqLeft z ∘ (fun k ↦ 2 * v k) = v := funext fun k ↦ seqLeft_two_mul z (v k)
  have hr : seqRight z ∘ (fun k ↦ 2 * v k) = e ∘ v := funext fun k ↦ seqRight_two_mul z (v k)
  simp only [AtomicIdx.holds, Function.comp_id, hl, hr] at h
  exact h.symm

omit [L.IsRelational] in
/-- An isomorphism preserves the atomic type of every tuple.  The structures are implicit
arguments, not instances, so that two structures on the same carrier can be supplied. -/
private theorem sameAtomicType_comp_equiv {M N : Type*} {iM : L.Structure M}
    {iN : L.Structure N} (e : @Language.Equiv L M N iM iN) {n : ℕ} (a : Fin n → M) :
    @SameAtomicType L M iM n N iN a (e.toEquiv ∘ a) := by
  let _ := iM
  let _ := iN
  intro idx
  cases idx with
  | eq i j => exact e.injective.eq_iff.symm
  | rel R f =>
    simp only [AtomicIdx.holds]
    exact (e.map_rel R (a ∘ f)).symm

/-- **An isomorphism gives a branch**: `z (2 i) = e i` answers element `i` of the left
structure, `z (2 i + 1) = e⁻¹ i` answers element `i` of the right structure; every initial
segment decodes a tuple and its image under `e`. -/
private theorem branch_of_equiv {c d : StructureSpace L}
    (e : @Language.Equiv L ℕ ℕ c.toStructure d.toStructure) :
    ∃ z : ℕ → ℕ, ∀ n, List.ofFn (fun i : Fin n ↦ z i) ∈ bfTree c d := by
  let f : ℕ ≃ ℕ := @Language.Equiv.toEquiv L ℕ ℕ c.toStructure d.toStructure e
  set z : ℕ → ℕ := fun j ↦ if j % 2 = 0 then f (j / 2) else f.symm (j / 2) with hz
  refine ⟨z, fun n ↦ ?_⟩
  have hR : ∀ j, seqRight z j = f (seqLeft z j) := by
    intro j
    by_cases hj : j % 2 = 0 <;> simp [seqLeft, seqRight, hz, hj]
  have hfun : bfRight (List.ofFn fun i : Fin n ↦ z i) =
      f ∘ bfLeft (List.ofFn fun i : Fin n ↦ z i) := by
    funext j
    rw [Function.comp_apply, bfLeft_ofFn, bfRight_ofFn, hR]
  show @SameAtomicType L ℕ c.toStructure _ ℕ d.toStructure _ _
  rw [hfun]
  exact sameAtomicType_comp_equiv e _

/-- **Branches are isomorphisms**: the forced back-and-forth tree of `c` and `d` has an infinite
branch iff the coded structures are isomorphic.  Every element of both structures is covered:
the left structure's element `i` enters at step `2 i`, the right structure's at step
`2 i + 1`. -/
theorem hasInfiniteBranch_bfTree_iff (c d : StructureSpace L) :
    HasInfiniteBranch (bfTree c d) ↔ (structureIsoSetoid L).r c d := by
  rw [hasInfiniteBranch_iff_exists_seq]
  constructor
  · rintro ⟨z, hz⟩
    exact nonempty_equiv_of_branch hz
  · rintro ⟨e⟩
    exact branch_of_equiv e

/-! ### Ranks -/

omit [L.IsRelational] in
/-- Reindexing along a cast of the tuple length does not change `BFEquiv`.  The structures are
implicit arguments, not instances. -/
private theorem bfEquiv_comp_cast {M N : Type*} {iM : L.Structure M} {iN : L.Structure N}
    {α : Ordinal.{0}} {n m : ℕ} (h : n = m) (a : Fin m → M) (b : Fin m → N) :
    @BFEquiv L M iM N iN α n (a ∘ Fin.cast h) (b ∘ Fin.cast h) ↔
      @BFEquiv L M iM N iN α m a b := by
  subst h
  rfl

/-- `BFEquiv` at the tuples of a one-step extension is `BFEquiv` at the extended tuples. -/
private theorem bfEquiv_append_singleton_iff {c d : StructureSpace L} {α : Ordinal.{0}}
    (s : List ℕ) (x : ℕ) :
    @BFEquiv L ℕ c.toStructure ℕ d.toStructure α (s ++ [x]).length (bfLeft (s ++ [x]))
      (bfRight (s ++ [x])) ↔
    @BFEquiv L ℕ c.toStructure ℕ d.toStructure α (s.length + 1)
      (Fin.snoc (bfLeft s) (if s.length % 2 = 0 then s.length / 2 else x))
      (Fin.snoc (bfRight s) (if s.length % 2 = 0 then x else s.length / 2)) := by
  rw [bfLeft_append_singleton, bfRight_append_singleton]
  exact bfEquiv_comp_cast _ _ _

/-- **Node rank comparison**: if the decoded tuples of a node are `α`-back-and-forth
equivalent, the node has rank at least `α`, with no offset.  Each tree step is one move: at
even length the forth property answers the next left element, at odd length the back property
answers the next right element. -/
theorem le_rank_bfTree_of_bfEquiv {c d : StructureSpace L} [WellFounded (extBelow (bfTree c d))]
    {α : Ordinal.{0}} {s : List ℕ} (hs : s ∈ bfTree c d)
    (h : @BFEquiv L ℕ c.toStructure ℕ d.toStructure α s.length (bfLeft s) (bfRight s)) :
    α ≤ WellFounded.rank (extBelow (bfTree c d)) ⟨s, hs⟩ := by
  induction α using Ordinal.limitRecOn generalizing s with
  | zero => exact zero_le
  | add_one β ih =>
    rw [← Order.succ_eq_add_one] at h ⊢
    have hex : ∃ x, @BFEquiv L ℕ c.toStructure ℕ d.toStructure β (s ++ [x]).length
        (bfLeft (s ++ [x])) (bfRight (s ++ [x])) := by
      by_cases hk : s.length % 2 = 0
      · obtain ⟨y, hy⟩ :=
          @BFEquiv.forth L ℕ c.toStructure ℕ d.toStructure _ _ _ _ h (s.length / 2)
        exact ⟨y, (bfEquiv_append_singleton_iff s y).mpr (by simpa [hk] using hy)⟩
      · obtain ⟨y, hy⟩ :=
          @BFEquiv.back L ℕ c.toStructure ℕ d.toStructure _ _ _ _ h (s.length / 2)
        exact ⟨y, (bfEquiv_append_singleton_iff s y).mpr (by simpa [hk] using hy)⟩
    obtain ⟨x, hx⟩ := hex
    have hmem : s ++ [x] ∈ bfTree c d := mem_bfTree_of_bfEquiv hx
    have hrel : extBelow (bfTree c d) ⟨s ++ [x], hmem⟩ ⟨s, hs⟩ :=
      ⟨List.prefix_append s [x], fun he ↦ by simpa using congrArg List.length he⟩
    exact Order.succ_le_of_lt ((ih hmem hx).trans_lt (WellFounded.rank_lt_of_rel hrel))
  | limit β hβ ih =>
    by_contra hlt
    have hsucc := hβ.succ_lt (not_le.mp hlt)
    exact (Order.lt_succ _).not_ge (ih _ hsucc hs
      (@BFEquiv.monotone L ℕ c.toStructure ℕ d.toStructure _ _ _ hsucc.le _ _ h))

/-- **Root rank comparison**: if the empty tuples are `α`-back-and-forth equivalent, then
`α < treeHeight (bfTree c d)`.  Root membership is obtained from atomic agreement of the empty
tuples (`nil_mem_bfTree_iff`), not assumed; the strict inequality is the `succ` in
`treeHeight`. -/
theorem lt_treeHeight_bfTree_of_codeBFEquiv {c d : StructureSpace L}
    [WellFounded (extBelow (bfTree c d))] {α : Ordinal.{0}} (h : CodeBFEquiv α c d) :
    α < treeHeight (bfTree c d) := by
  have hnil : [] ∈ bfTree c d := nil_mem_bfTree_iff.mpr
    (@BFEquiv.monotone L ℕ c.toStructure ℕ d.toStructure _ _ _ zero_le _ _ h)
  have hle := le_rank_bfTree_of_bfEquiv hnil (codeBFEquiv_iff_root.mp h)
  calc α < Order.succ (WellFounded.rank (extBelow (bfTree c d)) ⟨[], hnil⟩) :=
        Order.lt_succ_of_le hle
    _ ≤ treeHeight (bfTree c d) :=
        Ordinal.le_iSup (fun x : ↥(bfTree c d) ↦
          Order.succ (WellFounded.rank (extBelow (bfTree c d)) x)) ⟨[], hnil⟩

end FirstOrder.Language
