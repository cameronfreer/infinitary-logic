/-
Regression guard for the forced back-and-forth tree of a pair of coded structures
(`InfinitaryLogic/Descriptive/BFTree.lean`) and the branch-as-sequence lemma
`KleeneBrouwer.hasInfiniteBranch_iff_exists_seq`.

Every public theorem is *applied*, not only listed for its axioms.

* **Nullary disagreement gives the empty tree.**  In a language with one nullary relation
  symbol, true in one code and false in the other, the root is not a node
  (`nil_mem_bfTree_iff`), the tree is `⊥` (`bfTree_eq_bot_iff`), its height is `0`, and
  `CodeBFEquiv α` fails at every `α` (`lt_treeHeight_bfTree_of_codeBFEquiv`).
* **Agreement at level zero but no first move gives the root-only tree.**  One unary symbol,
  holding everywhere on the left and nowhere on the right: the empty tuples agree (there are no
  nullary symbols), but element `0` of the left structure has no answer.  The tree is `{[]}`, it
  is well-founded because the codes are not isomorphic (`hasInfiniteBranch_bfTree_iff`), the
  root has rank `0` and the tree height `1`, so `CodeBFEquiv 1` fails.
* **Isomorphisms and branches, both directions.**  An explicit identity branch of the code of
  `(ℕ, <)` read through `hasInfiniteBranch_bfTree_iff` gives an isomorphism, and the identity
  isomorphism gives a branch; the nontrivial automorphism of the pairs structure
  (`E x y ↔ x / 2 = y / 2`) swapping `2 k ↔ 2 k + 1` gives a branch, read back as an
  isomorphism.  The generic lemma `hasInfiniteBranch_iff_exists_seq` is applied to an arbitrary
  tree.
* **Repeated coordinates.**  In a language with no relation symbols, a node is a node exactly
  when its two decoded tuples have the same equality pattern: `[0, 0]` and `[3, 1, 0, 3]`
  (which repeat an element on both sides at the same positions) are nodes, while `[5, 0]` and
  `[3, 1, 7, 3]` (which repeat on the left only) are not.  The equality-pattern consequence is
  also stated for every node of every tree.
* **Rank comparisons.**  For one unary symbol holding on the even numbers on the left and on
  `{0, 1}` on the right (not isomorphic, so the tree is well-founded): `BFEquiv 1` at the
  non-root node `[0]` gives rank at least `1` there (`le_rank_bfTree_of_bfEquiv`), and
  `CodeBFEquiv 1` at the root gives height above `1`
  (`lt_treeHeight_bfTree_of_codeBFEquiv`); the root-only tree applies both at level `0`.
* **Topology and measurability.**  Closedness of node conditions for an arbitrary relational
  `Language.{u, v}` and for a language with infinitely many unary symbols; clopenness for one
  unary symbol; measurability of node conditions and of the tree assignment for countably many
  symbols.
* **Import closure** of `Descriptive/BFTree.lean`: it contains `KleeneBrouwer`, `BFEquivBorel`
  and `StructureIsoSetoid`, and no module whose name contains a López–Escobar, invariant
  separation, PC-class, well-ordering, tree-code, vocabulary-transport, interpolation or Henkin
  substring.

The headline declarations use only the standard axioms.

Run with: lake env lean scripts/check_bf_tree_regressions.lean
-/
import InfinitaryLogic.Descriptive.BFTree

open Lean FirstOrder FirstOrder.Language Descriptive KleeneBrouwer MeasureTheory

universe u v

noncomputable section

/-! ### The generic branch lemma and the generic topology -/

/-- `hasInfiniteBranch_iff_exists_seq` for an arbitrary tree. -/
theorem seq_branch_regression (T : tree ℕ) :
    HasInfiniteBranch T ↔ ∃ z : ℕ → ℕ, ∀ n, List.ofFn (fun i : Fin n ↦ z i) ∈ T :=
  hasInfiniteBranch_iff_exists_seq T

/-- Closed node conditions for an arbitrary relational language in independent universes,
with no countability. -/
theorem generic_closed_regression {L : Language.{u, v}} [L.IsRelational] (s : List ℕ) :
    IsClosed {p : StructureSpace L × StructureSpace L | s ∈ bfTree p.1 p.2} :=
  isClosed_setOf_mem_bfTree s

/-- **Every node has the same equality pattern on both sides**, for every pair of codes: a
repeated element on one side is repeated, at the same positions, on the other. -/
theorem eq_pattern_of_mem {L : Language.{u, v}} [L.IsRelational] {c d : StructureSpace L}
    {s : List ℕ} (hs : s ∈ bfTree c d) (i j : Fin s.length) :
    bfLeft s i = bfLeft s j ↔ bfRight s i = bfRight s j :=
  mem_bfTree_iff.mp hs (.eq i j)

/-! ### Nullary disagreement: the empty tree -/

/-- One nullary relation symbol, nothing else. -/
def nullLang : Language.{0, 0} where
  Functions _ := Empty
  Relations l := { _u : Unit // l = 0 }

instance : nullLang.IsRelational := fun _ ↦ inferInstanceAs (IsEmpty Empty)

/-- The nullary symbol. -/
def nullP : nullLang.Relations 0 := ⟨(), rfl⟩

/-- The code in which the nullary symbol holds. -/
def nullOn : StructureSpace nullLang := fun _ ↦ true

/-- The code in which the nullary symbol fails. -/
def nullOff : StructureSpace nullLang := fun _ ↦ false

/-- The root is not a node: the nullary atom disagrees on the empty tuples. -/
theorem null_nil_not_mem : [] ∉ bfTree nullOn nullOff := fun h ↦
  Bool.false_ne_true ((mem_bfTree_iff.mp h (.rel nullP Fin.elim0)).mp rfl)

/-- Level zero already fails. -/
theorem null_not_codeBFEquiv_zero : ¬ CodeBFEquiv 0 nullOn nullOff :=
  fun h ↦ null_nil_not_mem (nil_mem_bfTree_iff.mpr h)

/-- **The tree is empty.** -/
theorem null_bfTree_eq_bot : bfTree nullOn nullOff = ⊥ :=
  bfTree_eq_bot_iff.mpr null_not_codeBFEquiv_zero

instance : IsEmpty ↥(bfTree nullOn nullOff) :=
  ⟨fun x ↦ null_nil_not_mem (Tree.mem_of_prefix (List.nil_prefix) x.2)⟩

instance : WellFounded (extBelow (bfTree nullOn nullOff)) :=
  ⟨fun x ↦ isEmptyElim x⟩

/-- **The empty tree has height `0`.** -/
theorem null_treeHeight : treeHeight (bfTree nullOn nullOff) = 0 :=
  ciSup_of_empty _

/-- **`CodeBFEquiv` fails at every level**, read off the height. -/
theorem null_not_codeBFEquiv (α : Ordinal.{0}) : ¬ CodeBFEquiv α nullOn nullOff := by
  intro h
  have := lt_treeHeight_bfTree_of_codeBFEquiv h
  rw [null_treeHeight] at this
  exact absurd this (by simp)

/-! ### One unary symbol -/

/-- One unary relation symbol, nothing else. -/
def unaryLang : Language.{0, 0} where
  Functions _ := Empty
  Relations l := { _u : Unit // l = 1 }

instance : unaryLang.IsRelational := fun _ ↦ inferInstanceAs (IsEmpty Empty)

instance : Subsingleton (Σ l, unaryLang.Relations l) :=
  ⟨by rintro ⟨_, ⟨⟨⟩, rfl⟩⟩ ⟨_, ⟨⟨⟩, rfl⟩⟩; rfl⟩

instance : Finite (Σ l, unaryLang.Relations l) := Finite.of_subsingleton

/-- The unary symbol. -/
def uP : unaryLang.Relations 1 := ⟨(), rfl⟩

/-- The code of the unary predicate `P` (at arity `1`, the symbol holds of `v` iff `P (v 0)`). -/
def uCode (P : ℕ → Prop) [DecidablePred P] : StructureSpace unaryLang :=
  fun q ↦ decide (∀ i, P (q.2 i))

theorem relMap_uCode (P : ℕ → Prop) [DecidablePred P] (R : unaryLang.Relations 1)
    (v : Fin 1 → ℕ) : @Structure.RelMap unaryLang ℕ (uCode P).toStructure 1 R v ↔ P (v 0) := by
  simp [uCode, Fin.forall_fin_one]

/-- In the unary language, atomic agreement is agreement of the equality pattern and of the
predicate, position by position. -/
theorem unary_sameAtomicType_iff {P Q : ℕ → Prop} [DecidablePred P] [DecidablePred Q] {n : ℕ}
    (a b : Fin n → ℕ) :
    @SameAtomicType unaryLang ℕ (uCode P).toStructure n ℕ (uCode Q).toStructure a b ↔
      (∀ i j, a i = a j ↔ b i = b j) ∧ ∀ i, (P (a i) ↔ Q (b i)) := by
  constructor
  · intro h
    refine ⟨fun i j ↦ h (.eq i j), fun i ↦ ?_⟩
    have := h (.rel uP fun _ ↦ i)
    simp only [AtomicIdx.holds] at this
    rwa [relMap_uCode, relMap_uCode] at this
  · rintro ⟨heq, hP⟩ idx
    cases idx with
    | eq i j => exact heq i j
    | rel R f =>
      have hl := R.2
      subst hl
      simp only [AtomicIdx.holds]
      rw [relMap_uCode, relMap_uCode]
      exact hP (f 0)

/-! ### Agreement at level zero, no first move: the root-only tree -/

/-- The predicate holds everywhere on the left. -/
abbrev uAll : StructureSpace unaryLang := uCode fun _ ↦ True

/-- The predicate holds nowhere on the right. -/
abbrev uNone : StructureSpace unaryLang := uCode fun _ ↦ False

/-- The empty tuples agree: there is no nullary symbol. -/
theorem root_nil_mem : [] ∈ bfTree uAll uNone :=
  mem_bfTree_iff.mpr ((unary_sameAtomicType_iff _ _).mpr
    ⟨fun i ↦ i.elim0, fun i ↦ i.elim0⟩)

/-- Level zero holds at the root. -/
theorem root_codeBFEquiv_zero : CodeBFEquiv 0 uAll uNone := nil_mem_bfTree_iff.mp root_nil_mem

/-- No one-element node: element `0` of the left structure satisfies the predicate, and no
element of the right structure does. -/
theorem root_singleton_not_mem (x : ℕ) : [x] ∉ bfTree uAll uNone := by
  intro h
  have := ((unary_sameAtomicType_iff _ _).mp (mem_bfTree_iff.mp h)).2 ⟨0, by simp⟩
  simp at this

/-- **The tree is `{[]}`.** -/
theorem root_mem_iff (s : List ℕ) : s ∈ bfTree uAll uNone ↔ s = [] := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ root_nil_mem⟩
  cases s with
  | nil => rfl
  | cons x t => exact absurd (Tree.singleton_mem _ h) (root_singleton_not_mem x)

/-- The two codes are not isomorphic. -/
theorem root_not_iso : ¬ (structureIsoSetoid unaryLang).r uAll uNone := by
  rintro ⟨e⟩
  have := @Language.Equiv.map_rel unaryLang ℕ ℕ uAll.toStructure uNone.toStructure e 1 uP
    (fun _ ↦ 0)
  rw [relMap_uCode, relMap_uCode] at this
  simp at this

/-- **Well-founded**, because an infinite branch would be an isomorphism. -/
instance : WellFounded (extBelow (bfTree uAll uNone)) :=
  (wellFounded_extBelow_iff_not_hasInfiniteBranch _).mpr fun hb ↦
    root_not_iso ((hasInfiniteBranch_bfTree_iff _ _).mp hb)

/-- **The root has rank `0`**: it has no proper extension in the tree. -/
theorem root_rank : WellFounded.rank (extBelow (bfTree uAll uNone)) ⟨[], root_nil_mem⟩ = 0 := by
  rw [WellFounded.rank_eq]
  have : IsEmpty {b // extBelow (bfTree uAll uNone) b ⟨[], root_nil_mem⟩} :=
    ⟨fun b ↦ b.2.2 ((root_mem_iff b.1).mp b.1.2).symm⟩
  exact ciSup_of_empty _

instance : Unique ↥(bfTree uAll uNone) where
  toInhabited := ⟨⟨[], root_nil_mem⟩⟩
  uniq x := Subtype.ext ((root_mem_iff x).mp x.2)

/-- **The height is `1`.** -/
theorem root_treeHeight : treeHeight (bfTree uAll uNone) = 1 := by
  rw [treeHeight, ciSup_unique]
  change Order.succ (WellFounded.rank (extBelow (bfTree uAll uNone)) ⟨[], root_nil_mem⟩) = 1
  rw [root_rank, Order.succ_eq_add_one, zero_add]

/-- **`CodeBFEquiv 1` fails**: no first move. -/
theorem root_not_codeBFEquiv_one : ¬ CodeBFEquiv 1 uAll uNone := by
  intro h
  have := lt_treeHeight_bfTree_of_codeBFEquiv h
  rw [root_treeHeight] at this
  exact lt_irrefl _ this

/-- Both rank comparisons at level `0` on the root-only tree. -/
theorem root_rank_regression :
    (0 : Ordinal) ≤ WellFounded.rank (extBelow (bfTree uAll uNone)) ⟨[], root_nil_mem⟩ ∧
      (0 : Ordinal) < treeHeight (bfTree uAll uNone) :=
  ⟨le_rank_bfTree_of_bfEquiv root_nil_mem
      ((@BFEquiv.zero unaryLang ℕ uAll.toStructure ℕ uNone.toStructure _ _ _).mpr root_nil_mem),
    lt_treeHeight_bfTree_of_codeBFEquiv root_codeBFEquiv_zero⟩

/-! ### Rank comparisons at a node and at the root -/

/-- The predicate is "even" on the left. -/
abbrev uEven : StructureSpace unaryLang := uCode fun m ↦ m % 2 = 0

/-- The predicate is "at most `1`" on the right. -/
abbrev uLeOne : StructureSpace unaryLang := uCode fun m ↦ m ≤ 1

/-- Not isomorphic: three distinct even numbers cannot go to `{0, 1}`. -/
theorem even_not_iso : ¬ (structureIsoSetoid unaryLang).r uEven uLeOne := by
  rintro ⟨e⟩
  have hP : ∀ m, m % 2 = 0 → (@Language.Equiv.toEquiv unaryLang ℕ ℕ uEven.toStructure
      uLeOne.toStructure e) m ≤ 1 := by
    intro m hm
    have := @Language.Equiv.map_rel unaryLang ℕ ℕ uEven.toStructure uLeOne.toStructure e 1 uP
      (fun _ ↦ m)
    rw [relMap_uCode, relMap_uCode] at this
    exact this.mpr hm
  have hinj := (@Language.Equiv.toEquiv unaryLang ℕ ℕ uEven.toStructure
      uLeOne.toStructure e).injective
  have h0 := hP 0 rfl
  have h2 := hP 2 rfl
  have h4 := hP 4 rfl
  have h02 : (0 : ℕ) ≠ 2 := by decide
  have h04 : (0 : ℕ) ≠ 4 := by decide
  have h24 : (2 : ℕ) ≠ 4 := by decide
  have := hinj.ne h02
  have := hinj.ne h04
  have := hinj.ne h24
  omega

instance : WellFounded (extBelow (bfTree uEven uLeOne)) :=
  (wellFounded_extBelow_iff_not_hasInfiniteBranch _).mpr fun hb ↦
    even_not_iso ((hasInfiniteBranch_bfTree_iff _ _).mp hb)

/-- `(1 : Ordinal)` as a successor, for unfolding `BFEquiv`. -/
theorem one_eq_succ_zero : (1 : Ordinal.{0}) = Order.succ 0 := by simp

/-- **`BFEquiv 1` at the non-root node `[0]`** (left tuple `(0)`, right tuple `(0)`): forth
answers `0 ↦ 0`, a nonzero even number with `1`, an odd one with `2`; back answers `0 ↦ 0`,
`1 ↦ 2`, and anything else with `1`. -/
theorem node_bfEquiv_one :
    @BFEquiv unaryLang ℕ uEven.toStructure ℕ uLeOne.toStructure (1 : Ordinal.{0}) [0].length
      (bfLeft [0]) (bfRight [0]) := by
  rw [one_eq_succ_zero, @BFEquiv.succ unaryLang ℕ uEven.toStructure ℕ uLeOne.toStructure]
  simp only [@BFEquiv.zero unaryLang ℕ uEven.toStructure ℕ uLeOne.toStructure,
    unary_sameAtomicType_iff]
  have hl : bfLeft [0] 0 = 0 := rfl
  have hr : bfRight [0] 0 = 0 := rfl
  refine ⟨by simp [hl, hr], fun m ↦ ?_, fun n ↦ ?_⟩
  · refine ⟨if m = 0 then 0 else if m % 2 = 0 then 1 else 2, ?_⟩
    simp only [List.length_cons, List.length_nil, Fin.snoc]
    split_ifs <;> simp_all
    all_goals omega
  · refine ⟨if n = 0 then 0 else if n = 1 then 2 else 1, ?_⟩
    simp only [List.length_cons, List.length_nil, Fin.snoc]
    split_ifs <;> simp_all
    omega

theorem node_mem : [0] ∈ bfTree uEven uLeOne :=
  mem_bfTree_iff.mpr ((unary_sameAtomicType_iff _ _).mpr ⟨by decide, fun i ↦ by
    rw [Fin.fin_one_eq_zero i]; exact ⟨fun _ ↦ by decide, fun _ ↦ rfl⟩⟩)

/-- **Node rank comparison at a non-root node**: rank at least `1` at `[0]`. -/
theorem node_rank_regression :
    (1 : Ordinal) ≤ WellFounded.rank (extBelow (bfTree uEven uLeOne)) ⟨[0], node_mem⟩ :=
  le_rank_bfTree_of_bfEquiv node_mem node_bfEquiv_one

/-- **`CodeBFEquiv 1` at the root**: forth answers even with `0` and odd with `2`; back answers
`0, 1` with `0` and anything else with `1`. -/
theorem root_codeBFEquiv_one : CodeBFEquiv 1 uEven uLeOne := by
  unfold CodeBFEquiv
  rw [one_eq_succ_zero, @BFEquiv.succ unaryLang ℕ uEven.toStructure ℕ uLeOne.toStructure]
  simp only [@BFEquiv.zero unaryLang ℕ uEven.toStructure ℕ uLeOne.toStructure,
    unary_sameAtomicType_iff, IsEmpty.forall_iff, and_self, true_and]
  refine ⟨fun m ↦ ⟨if m % 2 = 0 then 0 else 2, ?_⟩, fun n ↦ ⟨if n ≤ 1 then 0 else 1, ?_⟩⟩ <;>
    simp only [Fin.snoc] <;> split_ifs <;> simp_all

/-- **Root rank comparison**: height above `1`. -/
theorem root_height_regression : (1 : Ordinal) < treeHeight (bfTree uEven uLeOne) :=
  lt_treeHeight_bfTree_of_codeBFEquiv root_codeBFEquiv_one

/-! ### Isomorphisms and branches -/

/-- One binary relation symbol (relation symbols of the other arities are absent). -/
def binLang : Language.{0, 0} where
  Functions _ := Empty
  Relations l := { _u : Unit // l = 2 }

instance : binLang.IsRelational := fun _ ↦ inferInstanceAs (IsEmpty Empty)

/-- The code of `(ℕ, <)`: the symbol holds of a tuple iff it is strictly increasing. -/
def ltCode : StructureSpace binLang :=
  fun q ↦ decide (∀ i j, i < j → q.2 i < q.2 j)

/-- The identity branch: `z (2 i) = z (2 i + 1) = i`. -/
def idBranch (j : ℕ) : ℕ := j / 2

/-- Along the identity branch the two decoded tuples coincide. -/
theorem bfLeft_eq_bfRight_idBranch (n : ℕ) :
    bfLeft (List.ofFn fun i : Fin n ↦ idBranch i) =
      bfRight (List.ofFn fun i : Fin n ↦ idBranch i) := by
  funext j
  simp only [bfLeft, bfRight, List.getElem_ofFn, idBranch]

/-- **Branch → isomorphism**, read through `hasInfiniteBranch_bfTree_iff` from an explicit
branch of the tree of `(ℕ, <)` with itself. -/
theorem lt_iso_of_branch : (structureIsoSetoid binLang).r ltCode ltCode :=
  (hasInfiniteBranch_bfTree_iff _ _).mp ((hasInfiniteBranch_iff_exists_seq _).mpr
    ⟨idBranch, fun n ↦ mem_bfTree_iff.mpr (by
      rw [bfLeft_eq_bfRight_idBranch]
      exact @SameAtomicType.refl binLang ℕ ltCode.toStructure _ _)⟩)

/-- **Isomorphism → branch** for `(ℕ, <)` with itself, via the identity isomorphism. -/
theorem lt_branch_of_refl : HasInfiniteBranch (bfTree ltCode ltCode) :=
  (hasInfiniteBranch_bfTree_iff _ _).mpr ⟨@Language.Equiv.refl binLang ℕ ltCode.toStructure⟩

/-- The pairs structure: the symbol holds of a tuple iff all its entries lie in one pair
`{2 k, 2 k + 1}`. -/
def pairCode : StructureSpace binLang :=
  fun q ↦ decide (∀ i j, q.2 i / 2 = q.2 j / 2)

/-- Swap within pairs. -/
def pairSwap (n : ℕ) : ℕ := if n % 2 = 0 then n + 1 else n - 1

theorem pairSwap_involutive : Function.Involutive pairSwap := by
  intro n
  unfold pairSwap
  split_ifs <;> omega

theorem pairSwap_div_two (n : ℕ) : pairSwap n / 2 = n / 2 := by
  unfold pairSwap
  split_ifs <;> omega

/-- **A nontrivial automorphism** of the pairs structure. -/
def pairAut : @Language.Equiv binLang ℕ ℕ pairCode.toStructure pairCode.toStructure :=
  @Language.Equiv.mk binLang ℕ ℕ pairCode.toStructure pairCode.toStructure
    (pairSwap_involutive.toPerm pairSwap) (fun f ↦ isEmptyElim f)
    (fun _ v ↦ by simp [pairCode, Function.Involutive.coe_toPerm, pairSwap_div_two])

theorem pairAut_nontrivial :
    (@Language.Equiv.toEquiv binLang ℕ ℕ pairCode.toStructure pairCode.toStructure pairAut) 0
      = 1 := rfl

/-- **Isomorphism → branch**, read through `hasInfiniteBranch_bfTree_iff`, and back. -/
theorem pair_branch_regression :
    HasInfiniteBranch (bfTree pairCode pairCode) ∧
      (structureIsoSetoid binLang).r pairCode pairCode :=
  have hb := (hasInfiniteBranch_bfTree_iff _ _).mpr ⟨pairAut⟩
  ⟨hb, (hasInfiniteBranch_bfTree_iff _ _).mp hb⟩

/-! ### Repeated coordinates -/

/-- No relation symbols at all. -/
def noRelLang : Language.{0, 0} where
  Functions _ := Empty
  Relations _ := Empty

instance : noRelLang.IsRelational := fun _ ↦ inferInstanceAs (IsEmpty Empty)

/-- The unique code. -/
def noRelCode : StructureSpace noRelLang := fun _ ↦ false

/-- Without relation symbols, a node is a node iff the equality patterns agree. -/
theorem noRel_mem_iff (s : List ℕ) :
    s ∈ bfTree noRelCode noRelCode ↔
      ∀ i j, (bfLeft s i = bfLeft s j ↔ bfRight s i = bfRight s j) := by
  refine ⟨fun h i j ↦ eq_pattern_of_mem h i j, fun h ↦ mem_bfTree_iff.mpr fun idx ↦ ?_⟩
  cases idx with
  | eq i j => exact h i j
  | rel R _ => exact R.elim

/-- `[0, 0]` decodes `(0, 0)` and `(0, 0)`: the repetition is on both sides. -/
theorem rep_mem_two : [0, 0] ∈ bfTree noRelCode noRelCode :=
  (noRel_mem_iff _).mpr (by decide)

/-- `[5, 0]` decodes `(0, 0)` and `(5, 0)`: repeated on the left only, so not a node. -/
theorem rep_not_mem_two : [5, 0] ∉ bfTree noRelCode noRelCode := fun h ↦
  absurd ((noRel_mem_iff _).mp h) (by decide)

/-- `[3, 1, 0, 3]` decodes `(0, 1, 1, 3)` and `(3, 0, 0, 1)`: positions `1, 2` repeat on both
sides. -/
theorem rep_mem_four : [3, 1, 0, 3] ∈ bfTree noRelCode noRelCode :=
  (noRel_mem_iff _).mpr (by decide)

/-- `[3, 1, 7, 3]` decodes `(0, 1, 1, 3)` and `(3, 0, 7, 1)`: the left repetition at positions
`1, 2` is not matched, so not a node. -/
theorem rep_not_mem_four : [3, 1, 7, 3] ∉ bfTree noRelCode noRelCode := fun h ↦
  absurd ((noRel_mem_iff _).mp h) (by decide)

/-! ### Topology and measurability on concrete languages -/

/-- Infinitely many unary relation symbols. -/
def natUnaryLang : Language.{0, 0} where
  Functions _ := Empty
  Relations l := { _n : ℕ // l = 1 }

instance : natUnaryLang.IsRelational := fun _ ↦ inferInstanceAs (IsEmpty Empty)

instance : Countable (Σ l, natUnaryLang.Relations l) :=
  inferInstanceAs (Countable (Σ l : ℕ, { _n : ℕ // l = 1 }))

/-- **Closed node conditions** with infinitely many symbols; **clopen** with one symbol;
**measurable** node conditions and tree assignment with countably many symbols. -/
theorem topology_regression :
    IsClosed {p : StructureSpace natUnaryLang × StructureSpace natUnaryLang |
        [0, 1] ∈ bfTree p.1 p.2} ∧
      IsClopen {p : StructureSpace unaryLang × StructureSpace unaryLang |
        [0, 1] ∈ bfTree p.1 p.2} ∧
      MeasurableSet {p : StructurePairSpace natUnaryLang | [0, 1] ∈ bfTree p.1 p.2} ∧
      Measurable fun p : StructurePairSpace natUnaryLang ↦ (bfTree p.1 p.2 : Set (List ℕ)) :=
  ⟨isClosed_setOf_mem_bfTree _, isClopen_setOf_mem_bfTree _, measurableSet_setOf_mem_bfTree _,
    measurable_bfTree⟩

end

/-! ### Import closure -/

/-- The import closure of a module, by walking the recorded imports. -/
partial def importClosure (env : Environment) (m : Name) : NameSet :=
  go [m] {}
where
  go : List Name → NameSet → NameSet
    | [], seen => seen
    | m :: rest, seen =>
      if seen.contains m then go rest seen
      else
        let deps := match env.getModuleIdx? m with
          | some idx => (env.header.moduleData[idx.toNat]!).imports.toList.map (·.module)
          | none => []
        go (deps ++ rest) (seen.insert m)

/-- Substrings no module of the closure may contain.  A substring match catches a module only
while its name keeps the substring, so a rename that drops it escapes the guard. -/
def forbiddenModuleSub : List String :=
  ["LopezEscobar", "InvariantSeparation", "PCSentence", "PCClass", "PCMem", "WellOrdering",
   "WellOrderBridge", "AnalyticWellOrderBoundedness", "TreeCodes", "SmallVocabularyTransport",
   "Interpolation", "Henkin"]

run_cmd do
  let env ← getEnv
  let target := `InfinitaryLogic.Descriptive.BFTree
  unless (env.getModuleIdx? target).isSome do
    throwError "module {target} is not in the environment"
  let cl := importClosure env target
  for m in [`InfinitaryLogic.Descriptive.KleeneBrouwer, `InfinitaryLogic.Descriptive.BFEquivBorel,
            `InfinitaryLogic.Descriptive.StructureIsoSetoid] do
    unless cl.contains m do throwError "[MISSING ROUTE] {m} is not in the closure of {target}"
  -- only library modules: Lean core has `Lean.Parser.StrInterpolation`, for instance
  let hits := cl.toList.filter fun m => (`InfinitaryLogic).isPrefixOf m &&
    forbiddenModuleSub.any fun s => (m.toString.splitOn s).length ≠ 1
  unless hits.isEmpty do
    throwError "[BROAD CONE] the closure of {target} reaches {hits}"

/-! ### Axiom hygiene -/

/-- The library declarations under test. -/
def libraryHeadline : List Name :=
  [`KleeneBrouwer.hasInfiniteBranch_iff_exists_seq] ++
  ([`bfLeft_two_mul, `bfLeft_two_mul_add_one, `bfRight_two_mul, `bfRight_two_mul_add_one,
    `bfNodes_prefix, `mem_bfTree_iff, `nil_mem_bfTree_iff, `bfTree_eq_bot_iff,
    `isClosed_setOf_mem_bfTree, `isClopen_setOf_mem_bfTree, `measurableSet_setOf_mem_bfTree,
    `measurable_bfTree, `hasInfiniteBranch_bfTree_iff, `le_rank_bfTree_of_bfEquiv,
    `lt_treeHeight_bfTree_of_codeBFEquiv]).map (`FirstOrder.Language ++ ·)

/-- The regressions. -/
def regressionHeadline : List Name :=
  [`seq_branch_regression, `generic_closed_regression, `eq_pattern_of_mem,
   `null_bfTree_eq_bot, `null_treeHeight, `null_not_codeBFEquiv,
   `root_mem_iff, `root_rank, `root_treeHeight, `root_not_codeBFEquiv_one, `root_rank_regression,
   `even_not_iso, `node_rank_regression, `root_height_regression,
   `lt_iso_of_branch, `lt_branch_of_refl, `pairAut_nontrivial, `pair_branch_regression,
   `rep_mem_two, `rep_not_mem_two, `rep_mem_four, `rep_not_mem_four, `topology_regression]

/-- The standard axioms. -/
def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in libraryHeadline ++ regressionHeadline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "forced back-and-forth tree regression guard: OK (nullary disagreement gives the \
    empty tree, of height 0, with CodeBFEquiv failing at every level; agreement at level 0 \
    with no first move gives the root-only tree, root rank 0, height 1; an explicit branch \
    gives an isomorphism and a nontrivial automorphism gives a branch; repeated coordinates \
    must repeat on both sides; node and root rank comparisons; closed, clopen and measurable \
    node conditions; minimal import closure; standard axioms)"
