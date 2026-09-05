/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.KleeneBrouwer
import InfinitaryLogic.Descriptive.WellOrderClass
import InfinitaryLogic.Descriptive.AnalyticWellOrderBoundedness
import Mathlib.Logic.Equiv.List
import Architect

/-!
# Tree codes, the continuous Kleene–Brouwer code, and analytic boundedness for well-founded trees

Classical background: Gao, *Invariant Descriptive Set Theory* (CRC Press, 2009), Theorem 1.6.11
(boundedness for well-founded trees) and Exercise 1.5.7 (the Kleene–Brouwer equivalence).

The code-level form of the Kleene–Brouwer material (issue #73), on top of the raw combinatorics in
`Descriptive/KleeneBrouwer.lean` and the analytic boundedness for coded well-orders (#64).

## Codes

A code `c : StructureSpace L` with a distinguished unary `mem : L.Relations 1` names the set of
finite sequences `x` whose node code `Equiv.listNatEquivNat x` satisfies `mem` (`nodeSet`).
`treeClass mem` is the set of codes naming a prefix-closed set; it is **closed**
(`isClosed_treeClass`, a countable intersection of clopen coordinate conditions) hence Borel.
`wellFoundedTreeClass mem` adds "no infinite branch", as a descending chain in strict extension;
no analyticity is claimed for it.

## The Kleene–Brouwer code

`kbCode mem c` is a code in the dedicated one-binary-relation language `kbLanguage`, whose symbol
`kbRelSym.lt` is a *strict* order: the nodes of the named set come first, in Kleene–Brouwer order,
and every other natural afterwards, in the usual order (`kbRel`).  A dedicated language, rather
than Mathlib's `Language.order`, so that no `≤`-named symbol is published with strict semantics.
Each coordinate of `kbCode mem c` is a function of two membership bits of `c` and the
two naturals, so `kbCode` is **continuous** (`continuous_kbCode`), not merely Borel.

For a well-founded tree code `kbRel` is the lexicographic sum of KB on the nodes and `<` on the
rest (`kbSumEmbedding`), hence a well-order: `kbCode_mem_wellOrderClass`.  The tree's rank,
`treeRank mem hwf`, is the height of strict extension on its tree and takes the well-foundedness
proof rather than defaulting on ill-founded codes; `treeRank_le_type_kbCode` bounds it by the order
type of the KB code, for any well-ordering proof, through the embedding of the nodes.

## Boundedness

`analytic_wellFoundedTree_rank_boundedness`: an analytic family of well-founded tree codes has
ranks bounded by one ordinal below `ω₁`.  The image under the continuous `kbCode` is an analytic
family of well-orders, so #64's `analytic_wellOrder_type_boundedness` bounds the KB order types,
hence the ranks.  `exists_rank_bound_of_dominated` is the domination adapter: parameters each
dominated by some tree of such a family have uniformly bounded assigned ranks, with no topology on
the parameter space.
-/

namespace FirstOrder.Language

open FirstOrder Structure Set Descriptive KleeneBrouwer

variable {L : Language.{0, 0}}

/-! ## The Kleene–Brouwer target language -/

/-- The single relation symbol of the KB language: a strict order. -/
inductive kbRelSym : ℕ → Type
  | lt : kbRelSym 2

/-- The dedicated one-binary-relation language the Kleene–Brouwer code lands in.  Its only symbol
is the strict order `kbRelSym.lt`. -/
def kbLanguage : Language := ⟨fun _ => Empty, kbRelSym⟩

namespace kbLanguage

instance : IsRelational kbLanguage := fun _ => inferInstanceAs (IsEmpty Empty)

instance instSubsingletonRelations (n : ℕ) : Subsingleton (kbLanguage.Relations n) :=
  ⟨by rintro ⟨⟩ ⟨⟩; rfl⟩

instance : Unique (Σ n, kbLanguage.Relations n) :=
  ⟨⟨⟨2, .lt⟩⟩, fun ⟨n, R⟩ =>
      match n, R with
      | 2, .lt => rfl⟩

instance : Countable (Σ n, kbLanguage.Relations n) := inferInstance

end kbLanguage

/-! ## Trees named by codes -/

/-- The node code of a finite sequence. -/
abbrev nodeCode (x : List ℕ) : ℕ := Equiv.listNatEquivNat x

/-- The set of sequences a code names through `mem`. -/
def nodeSet (mem : L.Relations 1) (c : StructureSpace L) : Set (List ℕ) :=
  {x | c ⟨⟨1, mem⟩, ![nodeCode x]⟩ = true}

/-- **The tree class**: codes whose named set is prefix-closed. -/
def treeClass (mem : L.Relations 1) : Set (StructureSpace L) :=
  {c | ∀ ⦃x : List ℕ⦄ ⦃a : ℕ⦄, x ++ [a] ∈ nodeSet mem c → x ∈ nodeSet mem c}

/-- The tree a code in the tree class names. -/
def treeOf (mem : L.Relations 1) (c : StructureSpace L) (hc : c ∈ treeClass mem) : tree ℕ :=
  ⟨nodeSet mem c, hc⟩

@[simp] theorem mem_treeOf {mem : L.Relations 1} {c : StructureSpace L} (hc : c ∈ treeClass mem)
    {x : List ℕ} : x ∈ treeOf mem c hc ↔ x ∈ nodeSet mem c := Iff.rfl

/-- **The well-founded tree class**: tree codes with no infinite branch. -/
def wellFoundedTreeClass (mem : L.Relations 1) : Set (StructureSpace L) :=
  {c | ∃ hc : c ∈ treeClass mem, ¬ HasInfiniteBranch (treeOf mem c hc)}

theorem treeClass_subset (mem : L.Relations 1) : wellFoundedTreeClass mem ⊆ treeClass mem :=
  fun _ ⟨hc, _⟩ => hc

/-! ## The Kleene–Brouwer relation on `ℕ` induced by a code -/

/-- The KB relation on node codes: nodes of the named set first, in KB order; the remaining
naturals afterwards, in their own order.  Depends only on the two membership bits and the two
naturals. -/
def kbRel (mem : L.Relations 1) (c : StructureSpace L) (x y : ℕ) : Prop :=
  let mx := c ⟨⟨1, mem⟩, ![x]⟩ = true
  let my := c ⟨⟨1, mem⟩, ![y]⟩ = true
  (mx ∧ my ∧ KBLT (Equiv.listNatEquivNat.symm x) (Equiv.listNatEquivNat.symm y)) ∨
    (mx ∧ ¬ my) ∨ (¬ mx ∧ ¬ my ∧ x < y)

instance (mem : L.Relations 1) (c : StructureSpace L) : DecidableRel (kbRel mem c) := by
  intro x y
  unfold kbRel
  infer_instance

/-- **The Kleene–Brouwer code**: the `kbLanguage`-code of `kbRel`. -/
def kbCode (mem : L.Relations 1) (c : StructureSpace L) : StructureSpace kbLanguage :=
  fun q => match q with
    | ⟨⟨2, .lt⟩, v⟩ => decide (kbRel mem c (v 0) (v 1))
    | _ => false

theorem kbCode_le (mem : L.Relations 1) (c : StructureSpace L) (v : Fin 2 → ℕ) :
    kbCode mem c ⟨⟨2, .lt⟩, v⟩ = decide (kbRel mem c (v 0) (v 1)) := rfl

/-! ## Continuity: each coordinate depends on two bits -/

theorem continuous_kbCode (mem : L.Relations 1) : Continuous (kbCode mem) := by
  apply continuous_pi
  rintro ⟨⟨n, R⟩, v⟩
  cases R with
  | lt =>
    -- the coordinate is a function of the two membership bits
    have h : (fun c : StructureSpace L => kbCode mem c ⟨⟨2, .lt⟩, v⟩) =
        (fun p : Bool × Bool => decide
          ((p.1 = true ∧ p.2 = true ∧
              KBLT (Equiv.listNatEquivNat.symm (v 0)) (Equiv.listNatEquivNat.symm (v 1))) ∨
            (p.1 = true ∧ ¬ p.2 = true) ∨ (¬ p.1 = true ∧ ¬ p.2 = true ∧ v 0 < v 1))) ∘
        (fun c : StructureSpace L => (c ⟨⟨1, mem⟩, ![v 0]⟩, c ⟨⟨1, mem⟩, ![v 1]⟩)) := by
      funext c; rfl
    rw [h]
    have h1 : Continuous fun c : StructureSpace L => c ⟨⟨1, mem⟩, ![v 0]⟩ :=
      continuous_apply (⟨⟨1, mem⟩, ![v 0]⟩ : RelQuery L)
    have h2 : Continuous fun c : StructureSpace L => c ⟨⟨1, mem⟩, ![v 1]⟩ :=
      continuous_apply (⟨⟨1, mem⟩, ![v 1]⟩ : RelQuery L)
    exact continuous_of_discreteTopology.comp (h1.prodMk h2)

/-! ## `kbRel` is a well-order on a well-founded tree code -/

/-- A natural is a node of the named set. -/
private def IsNode (mem : L.Relations 1) (c : StructureSpace L) (n : ℕ) : Prop :=
  c ⟨⟨1, mem⟩, ![n]⟩ = true

instance (mem : L.Relations 1) (c : StructureSpace L) : DecidablePred (IsNode mem c) :=
  fun _ => inferInstanceAs (Decidable (_ = true))

private theorem isNode_iff (mem : L.Relations 1) (c : StructureSpace L) (n : ℕ) :
    IsNode mem c n ↔ Equiv.listNatEquivNat.symm n ∈ nodeSet mem c := by
  simp [IsNode, nodeSet, nodeCode]

private theorem isNode_nodeCode (mem : L.Relations 1) (c : StructureSpace L) {x : List ℕ}
    (hx : x ∈ nodeSet mem c) : IsNode mem c (nodeCode x) := hx

section Embeddings

variable (mem : L.Relations 1) (c : StructureSpace L) (hc : c ∈ treeClass mem)

/-- `kbRel` is the lexicographic sum of KB on the nodes and `<` on the non-nodes. -/
private noncomputable def kbSumEmbedding :
    kbRel mem c ↪r Sum.Lex (kbLT (treeOf mem c hc)) ((· < ·) : ℕ → ℕ → Prop) where
  toFun n :=
    if h : IsNode mem c n then Sum.inl ⟨Equiv.listNatEquivNat.symm n, (isNode_iff mem c n).mp h⟩
    else Sum.inr n
  inj' := by
    intro x y hxy
    by_cases hx : IsNode mem c x <;> by_cases hy : IsNode mem c y <;> simp [hx, hy] at hxy
    · exact Equiv.listNatEquivNat.symm.injective (Subtype.mk.inj hxy)
    · exact hxy
  map_rel_iff' := by
    intro x y
    by_cases hx : IsNode mem c x <;> by_cases hy : IsNode mem c y <;>
      simp only [IsNode] at hx hy <;>
        simp [Function.Embedding.coeFn_mk, IsNode, hx, hy, kbRel, kbLT]

/-- The nodes embed into `kbRel` through their codes. -/
private noncomputable def kbNodeEmbedding : kbLT (treeOf mem c hc) ↪r kbRel mem c where
  toFun x := nodeCode (x : List ℕ)
  inj' := fun x y h => Subtype.ext (Equiv.listNatEquivNat.injective (by simpa [nodeCode] using h))
  map_rel_iff' := by
    intro x y
    show kbRel mem c (nodeCode (x : List ℕ)) (nodeCode (y : List ℕ)) ↔ kbLT (treeOf mem c hc) x y
    have hx := isNode_nodeCode mem c x.2
    have hy := isNode_nodeCode mem c y.2
    simp only [IsNode] at hx hy
    simp [kbRel, kbLT, hx, hy, nodeCode]

end Embeddings

theorem isWellOrder_kbRel (mem : L.Relations 1) {c : StructureSpace L}
    (hwf : c ∈ wellFoundedTreeClass mem) : IsWellOrder ℕ (kbRel mem c) := by
  obtain ⟨hc, hbr⟩ := hwf
  have := isWellOrder_kbLT (treeOf mem c hc)
    ((wellFounded_extBelow_iff_not_hasInfiniteBranch _).mpr hbr)
  exact (kbSumEmbedding mem c hc).isWellOrder

/-- The decoded relation of the KB code is `kbRel`. -/
theorem relMap_kbCode (mem : L.Relations 1) (c : StructureSpace L) (x y : ℕ) :
    @Structure.RelMap kbLanguage ℕ (kbCode mem c).toStructure 2 .lt ![x, y] ↔
      kbRel mem c x y := by
  show kbCode mem c ⟨⟨2, .lt⟩, ![x, y]⟩ = true ↔ _
  rw [kbCode_le]
  simp

/-- **A well-founded tree code has a well-ordered KB code.** -/
theorem kbCode_mem_wellOrderClass (mem : L.Relations 1) {c : StructureSpace L}
    (hwf : c ∈ wellFoundedTreeClass mem) :
    kbCode mem c ∈ wellOrderClass (L := kbLanguage) .lt := by
  show IsWellOrder ℕ fun x y : ℕ =>
    @Structure.RelMap kbLanguage ℕ (kbCode mem c).toStructure 2 .lt ![x, y]
  have : (fun x y : ℕ =>
        @Structure.RelMap kbLanguage ℕ (kbCode mem c).toStructure 2 .lt ![x, y])
      = kbRel mem c := by
    funext x y; exact propext (relMap_kbCode mem c x y)
  rw [this]
  exact isWellOrder_kbRel mem hwf

/-! ## The rank of a well-founded tree code -/

/-- The rank of a well-founded tree code: the height of strict extension on its tree.  Takes the
well-foundedness proof; no default value on ill-founded codes. -/
noncomputable def treeRank (mem : L.Relations 1) {c : StructureSpace L}
    (hwf : c ∈ wellFoundedTreeClass mem) : Ordinal :=
  @treeHeight (treeOf mem c hwf.choose)
    ⟨(wellFounded_extBelow_iff_not_hasInfiniteBranch _).mpr hwf.choose_spec⟩

/-- **The rank is at most the order type of the KB code.** -/
private theorem treeRank_le_type_kbRel (mem : L.Relations 1) {c : StructureSpace L}
    (hwf : c ∈ wellFoundedTreeClass mem) :
    treeRank mem hwf ≤ @Ordinal.type ℕ (kbRel mem c) (isWellOrder_kbRel mem hwf) := by
  have hwo := isWellOrder_kbRel mem hwf
  have : IsWellFounded ↥(treeOf mem c hwf.choose) (extBelow _) :=
    ⟨(wellFounded_extBelow_iff_not_hasInfiniteBranch _).mpr hwf.choose_spec⟩
  have hkb := isWellOrder_kbLT (treeOf mem c hwf.choose)
    ((wellFounded_extBelow_iff_not_hasInfiniteBranch _).mpr hwf.choose_spec)
  refine (treeHeight_le_type _).trans ?_
  exact Ordinal.type_le_iff'.mpr ⟨kbNodeEmbedding mem c hwf.choose⟩

/-! ## The tree class is closed (hence Borel) -/

/-- The tree class is a countable intersection of clopen coordinate conditions: for each `x`
and `a`, "`x ++ [a]` named implies `x` named". -/
theorem isClosed_treeClass (mem : L.Relations 1) : IsClosed (treeClass mem) := by
  have : treeClass mem = ⋂ (x : List ℕ) (a : ℕ),
      {c : StructureSpace L | c ⟨⟨1, mem⟩, ![nodeCode (x ++ [a])]⟩ = true →
        c ⟨⟨1, mem⟩, ![nodeCode x]⟩ = true} := by
    ext c
    simp only [treeClass, nodeSet, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [this]
  refine isClosed_iInter fun x => isClosed_iInter fun a => ?_
  have h1 : Continuous fun c : StructureSpace L => c ⟨⟨1, mem⟩, ![nodeCode (x ++ [a])]⟩ :=
    continuous_apply (⟨⟨1, mem⟩, ![nodeCode (x ++ [a])]⟩ : RelQuery L)
  have h2 : Continuous fun c : StructureSpace L => c ⟨⟨1, mem⟩, ![nodeCode x]⟩ :=
    continuous_apply (⟨⟨1, mem⟩, ![nodeCode x]⟩ : RelQuery L)
  have : {c : StructureSpace L | c ⟨⟨1, mem⟩, ![nodeCode (x ++ [a])]⟩ = true →
        c ⟨⟨1, mem⟩, ![nodeCode x]⟩ = true} =
      (fun c : StructureSpace L =>
          (c ⟨⟨1, mem⟩, ![nodeCode (x ++ [a])]⟩, c ⟨⟨1, mem⟩, ![nodeCode x]⟩))
        ⁻¹' {p : Bool × Bool | p.1 = true → p.2 = true} := by
    ext c; rfl
  rw [this]
  exact (isClosed_discrete _).preimage (h1.prodMk h2)

theorem measurableSet_treeClass (mem : L.Relations 1) [Countable (Σ l, L.Relations l)] :
    MeasurableSet (treeClass mem) :=
  (isClosed_treeClass mem).measurableSet

/-! ## Boundedness -/

/-- The decoded relation of the KB code, as a relation on `ℕ`. -/
abbrev kbCodeRel (mem : L.Relations 1) (c : StructureSpace L) (x y : ℕ) : Prop :=
  @Structure.RelMap kbLanguage ℕ (kbCode mem c).toStructure 2 .lt ![x, y]

/-- `kbRel` embeds (indeed, equals) the decoded relation. -/
private def kbRelEmbedding (mem : L.Relations 1) (c : StructureSpace L) :
    kbRel mem c ↪r kbCodeRel mem c :=
  ⟨Function.Embedding.refl ℕ, fun {a b} => relMap_kbCode mem c a b⟩

/-- **The rank is at most the order type of the KB code**, for any well-ordering proof. -/
theorem treeRank_le_type_kbCode (mem : L.Relations 1) {c : StructureSpace L}
    (hwf : c ∈ wellFoundedTreeClass mem) (h : IsWellOrder ℕ (kbCodeRel mem c)) :
    treeRank mem hwf ≤ @Ordinal.type ℕ (kbCodeRel mem c) h := by
  have : IsWellFounded ↥(treeOf mem c hwf.choose) (extBelow _) :=
    ⟨(wellFounded_extBelow_iff_not_hasInfiniteBranch _).mpr hwf.choose_spec⟩
  have hkb := isWellOrder_kbLT (treeOf mem c hwf.choose)
    ((wellFounded_extBelow_iff_not_hasInfiniteBranch _).mpr hwf.choose_spec)
  refine (treeHeight_le_type _).trans ?_
  exact Ordinal.type_le_iff'.mpr ⟨(kbNodeEmbedding mem c hwf.choose).trans (kbRelEmbedding mem c)⟩

/-- **Analytic boundedness for well-founded trees on a countable alphabet.**  An analytic family
of well-founded tree codes has ranks bounded below `ω₁`. -/
@[blueprint "thm:analytic-wellfounded-tree-boundedness"
  (title := /-- Boundedness for analytic families of well-founded trees -/)
  (statement := /-- If $A$ is an analytic set of codes, every one of which names a well-founded
    tree on $\mathbb{N}$, then a single countable ordinal strictly bounds the rank of every tree
    named by a code in $A$. -/)
  (proof := /-- Send each code to the code of its Kleene--Brouwer order: the nodes of the tree
    first, in Kleene--Brouwer order, and every other natural afterwards.  This map is continuous,
    each coordinate depending on two membership bits, so the image of $A$ is analytic; it
    consists of well-orders, since the Kleene--Brouwer order of a well-founded tree is a
    well-order and the remainder is a copy of $\omega$ placed after it.  The boundedness theorem
    for coded well-orders bounds the order types by one countable ordinal, and the rank of each
    tree is at most the order type of its Kleene--Brouwer code. -/)
  (uses := ["thm:analytic-wellorder-boundedness"])]
theorem analytic_wellFoundedTree_rank_boundedness [Countable (Σ l, L.Relations l)]
    (mem : L.Relations 1) {A : Set (StructureSpace L)} (hA : MeasureTheory.AnalyticSet A)
    (hWF : A ⊆ wellFoundedTreeClass mem) :
    ∃ β : Ordinal.{0}, β < (Cardinal.aleph 1).ord ∧
      ∀ c, ∀ hc : c ∈ A, treeRank mem (hWF hc) < β := by
  obtain ⟨β, hβ, hbound⟩ := analytic_wellOrder_type_boundedness (L := kbLanguage) .lt
    (hA.image_of_continuous (continuous_kbCode mem))
    (by rintro _ ⟨c, hc, rfl⟩; exact kbCode_mem_wellOrderClass mem (hWF hc))
  refine ⟨β, hβ, fun c hc => ?_⟩
  have h : IsWellOrder ℕ (kbCodeRel mem c) := kbCode_mem_wellOrderClass mem (hWF hc)
  exact (treeRank_le_type_kbCode mem (hWF hc) h).trans_lt (hbound (kbCode mem c) ⟨c, hc, rfl⟩ h)

/-- **The domination adapter**: parameters each dominated by some tree of an analytic family of
well-founded trees have uniformly bounded ranks.  No topology on the parameter space. -/
theorem exists_rank_bound_of_dominated [Countable (Σ l, L.Relations l)] (mem : L.Relations 1)
    {A : Set (StructureSpace L)} (hA : MeasureTheory.AnalyticSet A)
    (hWF : A ⊆ wellFoundedTreeClass mem) {X : Type*} {B : Set X} (rank : X → Ordinal.{0})
    (hdom : ∀ x ∈ B, ∃ c, ∃ hc : c ∈ A, rank x ≤ treeRank mem (hWF hc)) :
    ∃ β : Ordinal.{0}, β < (Cardinal.aleph 1).ord ∧ ∀ x ∈ B, rank x < β := by
  obtain ⟨β, hβ, hbound⟩ := analytic_wellFoundedTree_rank_boundedness mem hA hWF
  refine ⟨β, hβ, fun x hx => ?_⟩
  obtain ⟨c, hc, hle⟩ := hdom x hx
  exact hle.trans_lt (hbound c hc)

end FirstOrder.Language
