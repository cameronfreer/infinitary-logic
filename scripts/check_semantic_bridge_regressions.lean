/-
Regression guard for the bridge between semantic entries and back-and-forth equivalence
(`InfinitaryLogic/ScottProcess/SemanticBridge.lean`), the reflection of back-and-forth
equivalence along surjective relabelings (`BFEquiv.comp_iff_of_surjective` in
`InfinitaryLogic/Scott/BFEquivRelabel.lean`), and the upgrade at a self-stabilization level
(`BFEquiv_upgrade_at_selfStabilization` in `InfinitaryLogic/Scott/Sentence.lean`).

Every theorem below is *applied* to a concrete structure, not only listed for its axioms.  The
language `binLang.{u, v}` has one binary relation symbol and lives in arbitrary universes; the
carriers are `(ℕ, <)`, `ULift.{w} ℕ` with the lifted order, and `Pairs`, the natural numbers
with the equivalence relation whose classes are `{2k, 2k + 1}`.

* **The bridge at level `0`** (`sf_eq_iff_bfEquiv`): `(0, 1)` and `(1, 0)` in `(ℕ, <)` are not
  equivalent, so their entries differ; `(0)` and `(1)` are equivalent, so their entries agree,
  and conversely their equal entries (`sf_zero_eq_sf_zero_iff`) give the equivalence.
* **The bridge at level `1`**: `(0)` and `(1)` in `(ℕ, <)` are not equivalent (`1` has a
  predecessor), so their entries differ; conversely the entries differ by their extension sets
  (`mem_E_sf_iff`), so the tuples are not equivalent.
* **Level `ω`**: in `Pairs`, `(0)` and `(1)` have the same entry at every level
  (`sf_trans_equiv`), so they are equivalent at every level, including `ω`; the one-structure
  form `sf_eq_iff_bfEquiv_self`.
* **Universes**: `(0)` in `ULift.{w} ℕ` and `(1)` in `ℕ` are equivalent at level `0`, so their
  entries agree; `(0)` in `ULift.{w} ℕ` and `(0)` in `ℕ` have the same entry at `ω`, so they are
  equivalent at `ω`.
* **Fresh points** (`mem_range_iff_of_bfEquiv`): in `Pairs`, the equivalent `(0, 1)` and
  `(1, 0)` extend `(0)` and `(1)` by fresh points on both sides.
* **Repeated coordinates** (`bfEquiv_iff_exists_sf_eq`, `bfEquiv_iff_sf_eq_of_comp_eq`):
  `(5, 7, 5)` in `(ℕ, <)` and `(1, 2, 1)` in `ULift.{w} ℕ` are equivalent at level `0`, so the
  synchronized enumerations of `exists_embedding_comp_eq_of_eq_iff` have equal entries at level
  `0`; they are not equivalent at level `1` (`6` lies between `5` and `7`, nothing between `1`
  and `2`), so those entries differ at level `1`.
* **Relabeling** (`BFEquiv.relabel`, `BFEquiv.comp_iff_of_surjective`): in `Pairs`, the
  equivalence of `(0, 2)` and `(1, 3)` at every level passes to the repetition `(0, 0, 2)`,
  `(1, 1, 3)` and to the forgetful restriction `(2)`, `(3)`, and comes back from the repetition
  along the surjection.  **Negative**: `(0, 1)` and `(1, 2)` are not equivalent at any level,
  although their restrictions `(0)` and `(1)` along the non-surjective `Fin 1 → Fin 2` hitting
  `0` are equivalent at every level; so forgetting does not reflect equivalence.
* **Self-stabilization** (`BFEquiv_upgrade_at_selfStabilization`): at the countable
  self-stabilization level of `(ℕ, <)` given by `exists_complete_self_stabilization`,
  equivalence of tuples of `ℕ` persists to every higher level.

The headline declarations use only the standard axioms.

Run with: lake env lean scripts/check_semantic_bridge_regressions.lean
-/
import InfinitaryLogic.ScottProcess.SemanticBridge
import InfinitaryLogic.Scott.Sentence
import Mathlib.Tactic.FinCases

open Lean FirstOrder FirstOrder.Language InfinitaryLogic InfinitaryLogic.ScottProcess.FreeArray
  InfinitaryLogic.ScottProcess.Semantic

universe u v w

noncomputable section

/-! ### The language and the structures -/

/-- One binary relation symbol, in any universe. -/
inductive BinRel : ℕ → Type v
  /-- The binary relation symbol. -/
  | R : BinRel 2

/-- The language with one binary relation symbol, in any universes. -/
abbrev binLang : Language.{u, v} := ⟨fun _ ↦ PEmpty, BinRel⟩

/-- The relation symbols of `binLang` are countable. -/
instance : Countable (Σ l, binLang.{u, v}.Relations l) :=
  Function.Injective.countable (f := Sigma.fst) fun
    | ⟨_, .R⟩, ⟨_, .R⟩, _ => rfl

/-- `(ℕ, <)`. -/
instance ltStructure : binLang.{u, v}.Structure ℕ where
  funMap f := PEmpty.elim f
  RelMap r x := match r, x with | .R, x => x 0 < x 1

/-- `(ULift ℕ, <)`. -/
instance ltStructureULift : binLang.{u, v}.Structure (ULift.{w} ℕ) where
  funMap f := PEmpty.elim f
  RelMap r x := match r, x with | .R, x => (x 0).down < (x 1).down

/-- A copy of the natural numbers, to carry the equivalence relation whose classes are
`{2k, 2k + 1}`. -/
structure Pairs where
  /-- The underlying natural number. -/
  val : ℕ

instance : Infinite Pairs := Infinite.of_injective Pairs.mk fun _ _ h ↦ Pairs.mk.inj h

/-- `x E y ↔ x / 2 = y / 2`. -/
instance pairsStructure : binLang.{u, v}.Structure Pairs where
  funMap f := PEmpty.elim f
  RelMap r x := match r, x with | .R, x => (x 0).val / 2 = (x 1).val / 2

/-- Distinct naturals give distinct elements of `Pairs`. -/
theorem Pairs.mk_ne {x y : ℕ} (h : x ≠ y) : (⟨x⟩ : Pairs) ≠ ⟨y⟩ := fun e ↦ h (Pairs.mk.inj e)

/-- The one-element tuple `(x)`. -/
def tup1 {M : Type*} (x : M) : Fin 1 ↪ M := ⟨fun _ ↦ x, fun a b _ ↦ Subsingleton.elim a b⟩

/-- The two-element tuple `(x, y)` of distinct elements. -/
def tup2 {M : Type*} {x y : M} (h : x ≠ y) : Fin 2 ↪ M := Function.Embedding.embFinTwo h

/-- A two-element tuple of `Pairs`. -/
def ptup2 {x y : ℕ} (h : x ≠ y) : Fin 2 ↪ Pairs := tup2 (Pairs.mk_ne h)

/-- A tuple of `ℕ` and a tuple of `ULift ℕ` with the same equality and order pattern have the
same atomic type. -/
theorem sameAtomicType_ulift {n : ℕ} (a : Fin n → ℕ) (b : Fin n → ULift.{w} ℕ)
    (h : ∀ i j, (a i = a j ↔ (b i).down = (b j).down) ∧ (a i < a j ↔ (b i).down < (b j).down)) :
    SameAtomicType (L := binLang.{u, v}) a b := by
  intro idx
  cases idx with
  | eq i j => exact (h i j).1.trans ULift.ext_iff.symm
  | rel r f =>
    cases r
    exact (h (f 0) (f 1)).2

/-! ### The bridge at levels `0` and `1` in `(ℕ, <)` -/

/-- `1 = succ 0` in `Ordinal.{0}`, to unfold `BFEquiv 1` by `BFEquiv.succ`. -/
theorem one_eq_succ_zero : (1 : Ordinal.{0}) = Order.succ 0 := by
  rw [Order.succ_eq_add_one, zero_add]

/-- `0 ≠ 1` in `ℕ`. -/
theorem h01 : (0 : ℕ) ≠ 1 := zero_ne_one

/-- `(0, 1)` and `(1, 0)` are not equivalent at level `0`. -/
theorem pair_not_bfEquiv :
    ¬ BFEquiv (L := binLang.{u, v}) (0 : Ordinal.{0}) 2 ⇑(tup2 h01) ⇑(tup2 h01.symm) := by
  rw [BFEquiv.zero]
  intro h
  have := (h (.rel BinRel.R id)).1 (show (0 : ℕ) < 1 from zero_lt_one)
  exact absurd this (show ¬ (1 : ℕ) < 0 from Nat.not_lt_zero 1)

/-- **The bridge at level `0`, forward** (`sf_eq_iff_bfEquiv`): the entries of `(0, 1)` and
`(1, 0)` differ. -/
theorem pair_sf_ne :
    sf binLang.{u, v} 0 (tup2 h01) ≠ sf binLang.{u, v} 0 (tup2 h01.symm) :=
  fun h ↦ pair_not_bfEquiv ((sf_eq_iff_bfEquiv 0 _ _).1 h)

/-- All one-element tuples of `(ℕ, <)` have the same atomic type. -/
theorem sameAtomicType_one (x y : ℕ) :
    SameAtomicType (L := binLang.{u, v}) ⇑(tup1 x) ⇑(tup1 y) := by
  intro idx
  cases idx with
  | eq i j => exact iff_of_true rfl rfl
  | rel r f =>
    cases r
    exact iff_of_false (lt_irrefl x) (lt_irrefl y)

/-- **The bridge at level `0`, both directions**: `(0)` and `(1)` are equivalent, so their
entries agree; and their entries agree by `sf_zero_eq_sf_zero_iff`, so they are equivalent. -/
theorem one_level0 :
    sf binLang.{u, v} 0 (tup1 (0 : ℕ)) = sf binLang.{u, v} 0 (tup1 (1 : ℕ)) ∧
      BFEquiv (L := binLang.{u, v}) (0 : Ordinal.{0}) 1 ⇑(tup1 (0 : ℕ)) ⇑(tup1 (1 : ℕ)) :=
  ⟨(sf_eq_iff_bfEquiv 0 _ _).2 ((BFEquiv.zero _ _).2 (sameAtomicType_one 0 1)),
    (sf_eq_iff_bfEquiv 0 _ _).1 ((sf_zero_eq_sf_zero_iff _ _).2 (sameAtomicType_one 0 1))⟩

/-- `(0)` and `(1)` are not equivalent at level `1`: `0` extends `(1)` below it, and nothing
extends `(0)` below it. -/
theorem one_not_bfEquiv_one :
    ¬ BFEquiv (L := binLang.{u, v}) (1 : Ordinal.{0}) 1 ⇑(tup1 (0 : ℕ)) ⇑(tup1 (1 : ℕ)) := by
  rw [one_eq_succ_zero, BFEquiv.succ]
  rintro ⟨-, -, hb⟩
  obtain ⟨m, hm⟩ := hb 0
  have := ((BFEquiv.zero _ _).1 hm (.rel BinRel.R ![1, 0])).2 (show (0 : ℕ) < 1 from zero_lt_one)
  exact absurd this (Nat.not_lt_zero m)

/-- **The bridge at level `1`, forward**: the entries of `(0)` and `(1)` differ. -/
theorem one_sf_ne_one :
    sf binLang.{u, v} 1 (tup1 (0 : ℕ)) ≠ sf binLang.{u, v} 1 (tup1 (1 : ℕ)) :=
  fun h ↦ one_not_bfEquiv_one ((sf_eq_iff_bfEquiv 1 _ _).1 h)

/-- `0 ∉ {1}`. -/
theorem zero_not_mem : (0 : ℕ) ∉ Set.range (tup1 (1 : ℕ)) := fun ⟨_, h⟩ ↦ h01 h.symm

/-- The level-`0` entry of `(1, 0)` lies in the extension set of the level-`1` entry of `(1)`
(`mem_E_sf_iff`). -/
theorem mem_E_one : sf binLang.{u, v} 0 (tup2 h01.symm) ∈ E (sf binLang.{u, v} (0 + 1) (tup1 1)) :=
  mem_E_sf_iff.2 ⟨0, zero_not_mem, congrArg _ (Function.Embedding.ext fun i ↦ by
    fin_cases i <;> rfl)⟩

/-- The level-`0` entry of `(1, 0)` does not lie in the extension set of the level-`1` entry of
`(0)`: every fresh `m` is above `0` (`mem_E_sf_iff`, `sf_zero_eq_sf_zero_iff`). -/
theorem not_mem_E_zero :
    sf binLang.{u, v} 0 (tup2 h01.symm) ∉ E (sf binLang.{u, v} (0 + 1) (tup1 0)) := by
  intro h
  obtain ⟨m, hm, he⟩ := mem_E_sf_iff.1 h
  rw [sf_zero_eq_sf_zero_iff] at he
  have hm0 : m ≠ 0 := fun h ↦ hm ⟨0, h.symm⟩
  have := (he (.rel BinRel.R id)).1 (show (0 : ℕ) < m from Nat.pos_of_ne_zero hm0)
  exact absurd this (show ¬ (1 : ℕ) < 0 from Nat.not_lt_zero 1)

/-- **The bridge at level `1`, backward**: the entries of `(0)` and `(1)` differ by their
extension sets, so the tuples are not equivalent at level `1`. -/
theorem one_not_bfEquiv_one' :
    ¬ BFEquiv (L := binLang.{u, v}) ((0 : Ordinal.{0}) + 1) 1 ⇑(tup1 (0 : ℕ)) ⇑(tup1 (1 : ℕ)) :=
  fun h ↦ not_mem_E_zero (((sf_eq_iff_bfEquiv (0 + 1) _ _).2 h) ▸ mem_E_one)

/-! ### Level `ω` in `Pairs` -/

/-- The involution of `ℕ` swapping `2k` and `2k + 1`. -/
def pairFlip (x : ℕ) : ℕ := if x % 2 = 0 then x + 1 else x - 1

/-- `pairFlip` is an involution. -/
theorem pairFlip_pairFlip (x : ℕ) : pairFlip (pairFlip x) = x := by
  unfold pairFlip
  split_ifs <;> omega

/-- `pairFlip` preserves the classes `{2k, 2k + 1}`. -/
theorem pairFlip_div (x : ℕ) : pairFlip x / 2 = x / 2 := by
  unfold pairFlip
  split_ifs <;> omega

/-- The involution `pairFlip` as an automorphism of `Pairs`. -/
def flipIso : Pairs ≃[binLang.{u, v}] Pairs where
  toFun x := ⟨pairFlip x.val⟩
  invFun x := ⟨pairFlip x.val⟩
  left_inv x := congrArg Pairs.mk (pairFlip_pairFlip x.val)
  right_inv x := congrArg Pairs.mk (pairFlip_pairFlip x.val)
  map_fun' f := PEmpty.elim f
  map_rel' r x := by
    cases r
    exact show pairFlip (x 0).val / 2 = pairFlip (x 1).val / 2 ↔ (x 0).val / 2 = (x 1).val / 2 by
      rw [pairFlip_div, pairFlip_div]

/-- **Level `ω` through the bridge** (`sf_trans_equiv`, `sf_eq_iff_bfEquiv_self`): in `Pairs`,
`(0)` and `(1)` have the same entry at every level, so they are equivalent at every level. -/
theorem pairs_bfEquiv (α : Ordinal.{0}) :
    BFEquiv (L := binLang.{u, v}) α 1 ⇑(tup1 (⟨0⟩ : Pairs)) ⇑(tup1 (⟨1⟩ : Pairs)) := by
  refine (sf_eq_iff_bfEquiv_self α _ _).1 ?_
  rw [← sf_trans_equiv flipIso]
  rfl

/-- **Level `ω`**: in `Pairs`, `(0)` and `(1)` are equivalent at `ω`, although in `(ℕ, <)` they
are not equivalent already at level `1`. -/
theorem pairs_bfEquiv_ω :
    BFEquiv (L := binLang.{u, v}) (Ordinal.omega0 : Ordinal.{0}) 1 ⇑(tup1 (⟨0⟩ : Pairs))
      ⇑(tup1 (⟨1⟩ : Pairs)) :=
  pairs_bfEquiv _

/-! ### Universes -/

/-- The lifting isomorphism `ULift ℕ ≃ ℕ` of ordered structures. -/
def downIso : ULift.{w} ℕ ≃[binLang.{u, v}] ℕ where
  toEquiv := Equiv.ulift
  map_fun' f := PEmpty.elim f
  map_rel' r _ := by
    cases r
    exact Iff.rfl

/-- **Across carrier universes, both directions**: `(0)` in `ULift.{w} ℕ` and `(1)` in `ℕ` are
equivalent at level `0`, so their entries agree; `(0)` in `ULift.{w} ℕ` and `(0)` in `ℕ` have
the same entry at `ω` (`sf_trans_equiv`), so they are equivalent at `ω`. -/
theorem ulift_bridge :
    sf binLang.{u, v} 0 (tup1 (ULift.up.{w} 0 : ULift.{w} ℕ)) =
        sf binLang.{u, v} 0 (tup1 (1 : ℕ)) ∧
      BFEquiv (L := binLang.{u, v}) (Ordinal.omega0 : Ordinal.{0}) 1
        ⇑(tup1 (ULift.up.{w} 0 : ULift.{w} ℕ)) ⇑(tup1 (0 : ℕ)) := by
  refine ⟨(sf_eq_iff_bfEquiv 0 _ _).2 ((BFEquiv.zero _ _).2 fun idx ↦ ?_),
    (sf_eq_iff_bfEquiv _ _ _).1 ?_⟩
  · cases idx with
    | eq i j => exact iff_of_true rfl rfl
    | rel r f =>
      cases r
      exact iff_of_false (lt_irrefl 0) (lt_irrefl 1)
  · rw [← sf_trans_equiv downIso]
    rfl

/-! ### Fresh points -/

/-- `(0, 1)` and `(1, 0)` in `Pairs` are equivalent at every level (`sf_trans_equiv` and the
bridge). -/
theorem pairs_pair_bfEquiv (α : Ordinal.{0}) :
    BFEquiv (L := binLang.{u, v}) α 2 ⇑(ptup2 h01) ⇑(ptup2 h01.symm) := by
  refine (sf_eq_iff_bfEquiv α _ _).1 ?_
  rw [← sf_trans_equiv flipIso]
  congr 1
  exact Function.Embedding.ext fun i ↦ by fin_cases i <;> rfl

/-- **Fresh points** (`mem_range_iff_of_bfEquiv`): `(0, 1)` extends `(0)` by the fresh point
`1`, so in the equivalent `(1, 0)` the point `0` extending `(1)` is fresh as well. -/
theorem pairs_fresh (α : Ordinal.{0}) : (⟨0⟩ : Pairs) ∉ Set.range ![(⟨1⟩ : Pairs)] := by
  have h := pairs_pair_bfEquiv.{0, 0} α
  have ha : ⇑(ptup2 h01) = Fin.snoc ![(⟨0⟩ : Pairs)] ⟨1⟩ := funext fun i ↦ by fin_cases i <;> rfl
  have hb : ⇑(ptup2 h01.symm) = Fin.snoc ![(⟨1⟩ : Pairs)] ⟨0⟩ :=
    funext fun i ↦ by fin_cases i <;> rfl
  rw [ha, hb] at h
  intro hm
  obtain ⟨i, hi⟩ := (mem_range_iff_of_bfEquiv h).2 hm
  fin_cases i
  exact Pairs.mk_ne h01 hi

/-! ### Repeated coordinates -/

/-- `(5, 7, 5)` in `(ℕ, <)` and `(1, 2, 1)` in `ULift.{w} ℕ` are equivalent at level `0`. -/
theorem rep_bfEquiv_zero :
    BFEquiv (L := binLang.{u, v}) (0 : Ordinal.{0}) 3 ![5, 7, 5]
      ![ULift.up.{w} 1, ULift.up.{w} 2, ULift.up.{w} 1] := by
  rw [BFEquiv.zero]
  refine sameAtomicType_ulift _ _ fun i j ↦ ?_
  fin_cases i <;> fin_cases j <;> decide

/-- `(5, 7, 5)` in `(ℕ, <)` and `(1, 2, 1)` in `ULift.{w} ℕ` are not equivalent at level `1`:
`6` extends `(5, 7, 5)` strictly between `5` and `7`, and nothing lies strictly between `1` and
`2`. -/
theorem rep_not_bfEquiv_one :
    ¬ BFEquiv (L := binLang.{u, v}) (1 : Ordinal.{0}) 3 ![5, 7, 5]
      ![ULift.up.{w} 1, ULift.up.{w} 2, ULift.up.{w} 1] := by
  rw [one_eq_succ_zero, BFEquiv.succ]
  rintro ⟨-, hf, -⟩
  obtain ⟨m, hm⟩ := hf 6
  have h0 := (BFEquiv.zero _ _).1 hm
  have h1 := (h0 (.rel BinRel.R ![0, 3])).1 (show (5 : ℕ) < 6 by decide)
  have h2 := (h0 (.rel BinRel.R ![3, 1])).1 (show (6 : ℕ) < 7 by decide)
  change 1 < m.down at h1
  change m.down < 2 at h2
  omega

/-- **The repeated-coordinate bridge, both levels** (`exists_embedding_comp_eq_of_eq_iff`,
`bfEquiv_iff_sf_eq_of_comp_eq`): the synchronized enumerations `e` of `{5, 7}` and `e'` of
`{1, 2}` have equal entries at level `0` and different entries at level `1`. -/
theorem rep_bridge :
    ∃ (k : ℕ) (e : Fin k ↪ ℕ) (e' : Fin k ↪ ULift.{w} ℕ) (g : Fin 3 → Fin k),
      ⇑e ∘ g = ![5, 7, 5] ∧ ⇑e' ∘ g = ![ULift.up.{w} 1, ULift.up.{w} 2, ULift.up.{w} 1] ∧
        sf binLang.{u, v} 0 e = sf binLang.{u, v} 0 e' ∧
        sf binLang.{u, v} 1 e ≠ sf binLang.{u, v} 1 e' := by
  obtain ⟨k, e, e', g, he, he', hg⟩ :=
    exists_embedding_comp_eq_of_eq_iff (![5, 7, 5] : Fin 3 → ℕ)
      (![ULift.up.{w} 1, ULift.up.{w} 2, ULift.up.{w} 1] : Fin 3 → ULift.{w} ℕ) (by decide)
  exact ⟨k, e, e', g, he, he', (bfEquiv_iff_sf_eq_of_comp_eq 0 he he' hg).1 rep_bfEquiv_zero,
    fun h ↦ rep_not_bfEquiv_one ((bfEquiv_iff_sf_eq_of_comp_eq 1 he he' hg).2 h)⟩

/-- **Arbitrary tuples through entries** (`bfEquiv_iff_exists_sf_eq`), both directions:
`(5, 7, 5)` and `(1, 2, 1)` factor through one `g` with equal level-`0` entries, and any such
factorization gives back their equivalence at level `0`. -/
theorem rep_exists :
    (∃ (k : ℕ) (e : Fin k ↪ ℕ) (e' : Fin k ↪ ULift.{w} ℕ) (g : Fin 3 → Fin k),
      ⇑e ∘ g = ![5, 7, 5] ∧ ⇑e' ∘ g = ![ULift.up.{w} 1, ULift.up.{w} 2, ULift.up.{w} 1] ∧
        sf binLang.{u, v} 0 e = sf binLang.{u, v} 0 e') ∧
      BFEquiv (L := binLang.{u, v}) (0 : Ordinal.{0}) 3 ![5, 7, 5]
        ![ULift.up.{w} 1, ULift.up.{w} 2, ULift.up.{w} 1] :=
  have h := (bfEquiv_iff_exists_sf_eq 0 _ _).1 rep_bfEquiv_zero
  ⟨h, (bfEquiv_iff_exists_sf_eq 0 _ _).2 h⟩

/-! ### Relabeling: repeat, forget, and the negative example -/

/-- `0 ≠ 2` in `ℕ`. -/
theorem h02 : (0 : ℕ) ≠ 2 := by decide

/-- `1 ≠ 3` in `ℕ`. -/
theorem h13 : (1 : ℕ) ≠ 3 := by decide

/-- `(0, 2)` and `(1, 3)` in `Pairs` are equivalent at every level (`sf_trans_equiv` and the
bridge). -/
theorem pairs_02_13 (α : Ordinal.{0}) :
    BFEquiv (L := binLang.{u, v}) α 2 ⇑(ptup2 h02) ⇑(ptup2 h13) := by
  refine (sf_eq_iff_bfEquiv α _ _).1 ?_
  rw [← sf_trans_equiv flipIso]
  congr 1
  exact Function.Embedding.ext fun i ↦ by fin_cases i <;> rfl

/-- The surjective repetition `Fin 3 → Fin 2`, `(0, 0, 1)`. -/
def rep : Fin 3 → Fin 2 := ![0, 0, 1]

/-- `rep` is surjective. -/
theorem rep_surjective : Function.Surjective rep := by decide

/-- The non-surjective map `Fin 1 → Fin 2` hitting `1`; it forgets the coordinate `0`. -/
def forget1 : Fin 1 → Fin 2 := fun _ ↦ 1

/-- **Relabeling preserves equivalence** (`BFEquiv.relabel`), repeating and forgetting; and
**reflection along a surjection** (`BFEquiv.comp_iff_of_surjective`): the repetition gives back
the original equivalence. -/
theorem pairs_relabel (α : Ordinal.{0}) :
    BFEquiv (L := binLang.{u, v}) α 3 (⇑(ptup2 h02) ∘ rep) (⇑(ptup2 h13) ∘ rep) ∧
      BFEquiv (L := binLang.{u, v}) α 1 (⇑(ptup2 h02) ∘ forget1) (⇑(ptup2 h13) ∘ forget1) ∧
      BFEquiv (L := binLang.{u, v}) α 2 ⇑(ptup2 h02) ⇑(ptup2 h13) :=
  ⟨BFEquiv.relabel α (pairs_02_13 α) rep, BFEquiv.relabel α (pairs_02_13 α) forget1,
    (BFEquiv.comp_iff_of_surjective rep_surjective).1 (BFEquiv.relabel α (pairs_02_13 α) rep)⟩

/-- The non-surjective map `Fin 1 → Fin 2` hitting `0`; it forgets the coordinate `1`. -/
def forget0 : Fin 1 → Fin 2 := fun _ ↦ 0

/-- `1 ≠ 2` in `ℕ`. -/
theorem h12 : (1 : ℕ) ≠ 2 := by decide

/-- **Forgetting does not reflect equivalence**: `(0, 1)` and `(1, 2)` in `Pairs` are not
equivalent at any level (`0` and `1` are in one class, `1` and `2` are not), while their
restrictions `(0)` and `(1)` along `forget0` are equivalent at every level. -/
theorem forget_not_reflect (α : Ordinal.{0}) :
    BFEquiv (L := binLang.{u, v}) α 1 (⇑(ptup2 h01) ∘ forget0) (⇑(ptup2 h12) ∘ forget0) ∧
      ¬ BFEquiv (L := binLang.{u, v}) α 2 ⇑(ptup2 h01) ⇑(ptup2 h12) := by
  refine ⟨pairs_bfEquiv α, fun h ↦ ?_⟩
  have := (BFEquiv.zero _ _).1 (BFEquiv.monotone zero_le h) (.rel BinRel.R id)
  exact absurd (this.1 (show (0 : ℕ) / 2 = 1 / 2 by decide))
    (show ¬ (1 : ℕ) / 2 = 2 / 2 by decide)

/-! ### Self-stabilization -/

/-- **Upgrade at the self-stabilization level** (`BFEquiv_upgrade_at_selfStabilization`,
`exists_complete_self_stabilization`): `(ℕ, <)` has a countable level `α₀` past which the
equivalence of tuples of `ℕ` does not change. -/
theorem nat_upgrade :
    ∃ α₀ < (Ordinal.omega 1 : Ordinal.{0}), ∀ (n : ℕ) (a a' : Fin n → ℕ),
      BFEquiv (L := binLang.{u, v}) α₀ n a a' → ∀ β, α₀ ≤ β →
        BFEquiv (L := binLang.{u, v}) β n a a' := by
  obtain ⟨α₀, hα₀, hstab⟩ := exists_complete_self_stabilization (L := binLang.{u, v}) ℕ
  exact ⟨α₀, hα₀, fun _ _ _ h β hβ ↦ BFEquiv_upgrade_at_selfStabilization hstab h β hβ⟩

end

/-! ### Axiom hygiene -/

def headline : List Name :=
  [`InfinitaryLogic.ScottProcess.Semantic.mem_range_iff_of_bfEquiv,
   `InfinitaryLogic.ScottProcess.Semantic.sf_eq_iff_bfEquiv,
   `InfinitaryLogic.ScottProcess.Semantic.sf_eq_iff_bfEquiv_self,
   `InfinitaryLogic.ScottProcess.Semantic.bfEquiv_iff_sf_eq_of_comp_eq,
   `InfinitaryLogic.ScottProcess.Semantic.bfEquiv_iff_exists_sf_eq,
   `FirstOrder.Language.BFEquiv.comp_iff_of_surjective,
   `FirstOrder.Language.BFEquiv_upgrade_at_selfStabilization,
   `pair_not_bfEquiv, `pair_sf_ne, `one_level0, `one_not_bfEquiv_one, `one_sf_ne_one,
   `mem_E_one, `not_mem_E_zero, `one_not_bfEquiv_one', `pairs_bfEquiv, `pairs_bfEquiv_ω,
   `ulift_bridge, `pairs_pair_bfEquiv, `pairs_fresh, `rep_bfEquiv_zero, `rep_not_bfEquiv_one,
   `rep_bridge, `rep_exists, `pairs_02_13, `pairs_relabel, `forget_not_reflect, `nat_upgrade]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "semantic-bridge regression guard: OK (applied: sf_eq_iff_bfEquiv in both directions \
    at level 0 on (0, 1)/(1, 0) and (0)/(1) of (N, <), and at level 1 on (0)/(1) against a \
    direct non-equivalence and against the extension sets via mem_E_sf_iff; \
    sf_eq_iff_bfEquiv_self at every level including omega on Pairs; across carrier universes \
    on ULift N against N in both directions; mem_range_iff_of_bfEquiv on the fresh extensions \
    (0, 1)/(1, 0) of Pairs; the repeated-coordinate bridge bfEquiv_iff_sf_eq_of_comp_eq and \
    bfEquiv_iff_exists_sf_eq on (5, 7, 5) in N against (1, 2, 1) in ULift N, equal entries at \
    level 0 and different at level 1; BFEquiv.relabel repeating and forgetting and \
    BFEquiv.comp_iff_of_surjective on Pairs; forgetting does not reflect equivalence; \
    BFEquiv_upgrade_at_selfStabilization at the self-stabilization level of (N, <); headline \
    declarations on standard axioms)"
